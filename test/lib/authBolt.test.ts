// AuthBolt = MinSimple zero-funding + an owner-supplied/transaction negotiated/challenge based `authOrMiscData`: the FIRST unlock arg (deepest,
// never dropped, before the OP_CODESEPARATOR so it stays out of the fullCtx scriptCode). Port of the contract-level suite onto the b017 library (real txs, Spend engine).
//
// It is created in a commit and authenticated in the settle: the settle re-serialises its grandparent
// commit - whose scriptSig now LEADS with that commit's authOrMiscData push (Vin1AuthOrMiscData) - and
// hash-binds it to the grandparent txid. Properties under test:
//   - LIFECYCLE: any value from empty to 75 B (a direct push, 0x00..0x4b) survives mint -> commit -> settle
//     -> commit -> settle, funded or unfunded (zero-funding behaviour is inherited).
//   - LENGTH: > 75 B is refused at the tx that carries it (enforced in the LOCK), so no token can be frozen
//     by an ancestor the rebuild could not reproduce.
//   - BINDING: a settle that misdescribes its grandparent's authOrMiscData dies at the grandparent txid check.
//   - OWNER SIGNATURE (documented): the carrying commit's owner signature does NOT cover the value (it is
//     outside both ctx preimages); authentication is the settle's rebuild binding above.
//   - COVERAGE: every ancestor shape (funded+change / funded no-change / unfunded) x every settle2 shape x
//     auth (empty / 20 B / 75 B) has a fixture that RUNS.
import { describe, it, expect } from 'vitest'
import { UnlockingScript, type Transaction } from '@bsv/sdk'
import {
  buildChain, verifyChain, tamper, grandparentCheckPc, fromHex, UNFUNDED, FUNDED_NO_CHANGE,
  type ChainSpec, type Hop,
} from '../helpers/minSimpleChain.js'
import { authBolt as fam } from '../helpers/authBoltFamily.js'
import { scriptChunksFromBin } from '../../src/lib/boltLib.js'

const A20 = 'a5'.repeat(20)

// Every hop carries the same auth value; commit1's is the one settle2 rebuilds.
const withAuth = (auth: string | null, hops: ChainSpec = {}): ChainSpec => {
  const f: ChainSpec = {}
  for (const k of ['commit1', 'settle1', 'commit2', 'settle2'] as const) f[k] = { ...(hops[k] || {}), auth: auth === null ? [] : fromHex(auth) }
  return f
}

const AUTHS: [string, string | null][] = [
  ['empty (OP_0)', null],
  ['1 byte ff', 'ff'],
  ['1 byte 01 (OP_1 range)', '01'],
  ['1 byte 10 (OP_16 range)', '10'],
  ['1 byte 81 (OP_1NEGATE range)', '81'],
  ['20 bytes', 'a5'.repeat(20)],
  ['75 bytes (max direct push)', 'c3'.repeat(75)],
]

describe('AuthBolt', () => {
  // -- lifecycle: every value, funded and unfunded ancestor -------------------------------------
  const lifecycle: [string, string, string | null, ChainSpec][] = []
  for (const [name, auth] of AUTHS) {
    lifecycle.push([name, 'funded commit1', auth, {}])
    lifecycle.push([name, 'unfunded commit1', auth, { commit1: UNFUNDED }])
  }
  it.each(lifecycle)('lifecycle: auth %s, %s (settle2 rebuilds it)', async (_n, _c, auth, hops) => {
    expect(verifyChain(await buildChain(fam, withAuth(auth, hops)))).toEqual({ ok: true })
  })

  // -- length enforcement: > 75 B refused where it is carried ------------------------------------
  // The client-side guard stops an honest builder, so the oversize value is spliced into the signed tx's
  // first unlock push (it is outside the signature) and the covenant must refuse it at the carrying tx.
  const setAuth = (tx: Transaction, hex: string) => {
    const chunks = [...tx.inputs[0].unlockingScript!.chunks]
    chunks[0] = scriptChunksFromBin(fromHex(hex))[0]
    tx.inputs[0].unlockingScript = new UnlockingScript(chunks)
  }
  it.each([
    ['commit1', 1, 76], ['commit1', 1, 255], ['settle1', 2, 76], ['commit2', 3, 76],
  ] as const)('REFUSED: %s (tx #%i) carrying a %i-byte auth', async (_hop, idx, len) => {
    const txs = await buildChain(fam, withAuth('d4'.repeat(75)), idx + 1)
    expect(verifyChain(txs).ok).toBe(true) // 75 B is accepted on the same hop (control)
    setAuth(txs[idx], 'd4'.repeat(len))
    const r = verifyChain(txs)
    expect(r.ok).toBe(false)
    expect(r.failedTx).toBe(idx)
  })

  it('control: a 75-byte auth on the same hops is accepted', async () => {
    const f: ChainSpec = {}
    for (const k of ['commit1', 'settle1', 'commit2'] as const) f[k] = { auth: fromHex('d4'.repeat(75)) }
    expect(verifyChain(await buildChain(fam, f, 4)).ok).toBe(true)
  })

  // -- binding: settle2 misdescribes commit1's authOrMiscData -----------------------------------
  it.each([
    ['a different value, same length', A20, 'b6'.repeat(20)],
    ['nulled', A20, ''],
    ['one byte longer', A20, A20 + 'a5'],
    ['one byte shorter', A20, 'a5'.repeat(19)],
    ['invented where the ancestor had none', null, A20],
  ] as const)('REFUSED at the grandparent txid check: ancestor auth %s', async (_n, real, claimed) => {
    const txs = await buildChain(fam, withAuth(real))
    expect(verifyChain(txs).ok).toBe(true)
    tamper(fam, txs[4], { Vin1AuthOrMiscData: claimed })
    const r = verifyChain(txs)
    expect(r.ok).toBe(false)
    expect(r.failedTx).toBe(4)
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
    expect(r.pc).toBe(grandparentCheckPc(txs[3].outputs[0].lockingScript))
  })

  // -- owner signature: the commit does not sign authOrMiscData; the settle binds it -------------
  // commit1 (tx #1) built twice from the same keys and plan, differing only in its auth value. The sig
  // is the 4th current-tx arg (fund, change, beneficiary, sig): unlock index 1 + 27 + 3.
  const SIG_IDX = fam.ancestorStart + fam.pieceNames.length + 3
  async function commit1Sig(auth: string) {
    const txs = await buildChain(fam, { commit1: { auth: fromHex(auth) } }, 2)
    expect(verifyChain(txs).ok).toBe(true)
    return Buffer.from(txs[1].inputs[0].unlockingScript!.chunks[SIG_IDX].data as number[]).toString('hex')
  }

  it('control: the same auth twice gives the same owner signature (signing is deterministic)', async () => {
    expect(await commit1Sig(A20)).toBe(await commit1Sig(A20))
  })

  it("DOCUMENTED: the commit's owner signature is independent of its auth value (the settle binds it)", async () => {
    expect(await commit1Sig('b6'.repeat(20))).toBe(await commit1Sig(A20))
  })
})

// -- coverage gate: every covenant path RUNS (green never means covered) ------------------------------
describe('AuthBolt path coverage: ancestor shape x settle2 shape x auth', () => {
  const STATES: Record<string, (src: { tx: number; vout: number }) => Partial<Hop>> = {
    'funded+change': (src) => ({ fund: src, change: true }),
    'funded, no change': (src) => FUNDED_NO_CHANGE(src.tx, src.vout),
    'unfunded': () => UNFUNDED,
  }
  const COV_AUTHS: [string, number[]][] = [['empty', []], ['20 B', fromHex(A20)], ['75 B', fromHex('c3'.repeat(75))]]
  const cells: [string, string, string, number[]][] = []
  for (const a of Object.keys(STATES)) for (const s of Object.keys(STATES)) for (const [an, av] of COV_AUTHS) cells.push([a, s, an, av])

  it.each(cells)('ancestor commit1 %s, settle2 %s, auth %s', async (a, s, _an, auth) => {
    const c1 = STATES[a]({ tx: 0, vout: 1 })
    const s1 = { fund: c1.fund && c1.change ? { tx: 1, vout: 2 } : { tx: 0, vout: 2 }, change: true }
    const c2 = { fund: { tx: 2, vout: 1 }, change: true }
    const s2 = STATES[s]({ tx: 3, vout: 2 })
    const spec: ChainSpec = {
      commit1: { ...c1, auth }, settle1: { ...s1, auth }, commit2: { ...c2, auth }, settle2: { ...s2, auth },
    }
    expect(verifyChain(await buildChain(fam, spec))).toEqual({ ok: true })
  })
})
