// C2/C3/C4 — verifyEvents / verifyEvent: issuer pinning, commit/settle pairing, interface arrangement
// and fail-closed input handling. Restores the coverage the Discount/Balance golden suite provided
// before those contracts were cut, rebuilt over LIVE SimpleMultiBOLT chains (plus a MinSimpleBOLT
// mint for the mixed-type case) so no fixture is needed.
import { describe, it, expect, beforeAll } from 'vitest'
import { Hash, MerklePath, P2PKH, PrivateKey, Script, Transaction, Utils } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { verifyEvents, verifyEvent } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef, fromBeef } from '../../src/lib/scanner/beef.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import { appendOutput, assertOutputAdded } from '../helpers/counterfeit.js'

const T = 'SimpleMultiBOLT' as const
const MASK64 = (1n << 64n) - 1n
const bal = (amount: bigint): number[] => {
  const b = Buffer.alloc(16)
  b.writeBigUInt64LE(amount & MASK64, 0)
  b.writeBigUInt64LE((amount >> 64n) & MASK64, 8)
  return Array.from(b)
}
const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const issuerPub = issuerKey.toPublicKey().encode(true) as number[]
const child = (n: string) => issuerKey.deriveChild(issuerKey.toPublicKey(), n)
// A mined funding tx: it carries a (fake, single-tx-block) merkle path, as a BEEF root must.
const freshSource = () => {
  const t = new Transaction(1, [], [{
    satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(issuerPub)),
  }])
  t.merklePath = new MerklePath(1, [[{ offset: 0, hash: t.id('hex'), txid: true }]])
  return t
}
const EMPTY_TX = '01000000' + '00' + '00' + '00000000' // version + 0 inputs + 0 outputs + locktime

// One live transfer, as hex (what a peer receives on the wire): [mint, commit, settle].
let chain: string[]
let wire: string[] // the same txs as Atomic BEEF (V2) hex - what a peer receives: each tx WITH its ancestors
let txs: Transaction[]
beforeAll(async () => {
  const t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(1000n))
  await t.transfer(child('1'))
  txs = t.prevTxs
  chain = txs.map((tx) => tx.toHex())
  wire = txs.map((tx) => Utils.toHex(toAtomicBeef(tx)))
})

describe('C2/C3 — issuer + commit/settle event pairing', () => {
  it('accepts a genuine lifecycle (mint -> commit -> settle) received as Atomic BEEF', () => {
    const r = verifyEvents(wire)
    expect(r.ok, r.reason).toBe(true)
    expect(r.type).toBe(T)
    expect(r.issuerPubKeyHex).toBe(Utils.toHex(issuerPub))
    expect(r.events?.map((e) => e.kind).sort()).toEqual(['mint', 'transfer'])
  })

  it('refuses a lone genesis mint as UNAUTHENTICATED (a mint alone does not prove the issuer key; see unauthenticatedMint.test.ts)', () => {
    const r = verifyEvents([chain[0]])
    expect(r.ok).toBe(false)
    expect(r.unauthenticated).toBe(true)
    expect(r.reason).toMatch(/unauthenticated mint/)
  })

  it('C2: accepts a matching trusted issuer (hex or bytes); rejects a wrong one', () => {
    expect(verifyEvents(wire, { trustedIssuerPubKey: Utils.toHex(issuerPub).toUpperCase() }).ok).toBe(true)
    expect(verifyEvents(wire, { trustedIssuerPubKey: issuerPub }).ok).toBe(true)
    const r = verifyEvents(chain, { trustedIssuerPubKey: '02' + '00'.repeat(32) })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/trusted issuer/)
  })

  it('C3: rejects an orphan settle (mint + settle only)', () => {
    const r = verifyEvents([chain[0], chain[2]])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/orphan settle/)
  })

  it('C3: rejects an unsettled commit (mint + commit, no settle)', () => {
    const r = verifyEvents([chain[0], chain[1]])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/unsettled commit/)
  })

  it('rejects a wrong expectedType up front', () => {
    expect(verifyEvents(chain, { expectedType: 'MinSimpleBOLT' }).reason).toMatch(/no BOLT token output/)
    expect(verifyEvent(chain, { expectedType: 'MinSimpleBOLT' }).reason).toMatch(/no BOLT token recognised/)
  })

  it('rejects mixed token types in one batch', () => {
    const nft = new Transaction(1, [], [{
      satoshis: 1, lockingScript: new MinSimpleTemplate().lock(Hash.hash160(issuerPub), issuerPub),
    }])
    const r = verifyEvents([chain[0], nft])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/mixed token types/)
  })
})

describe('C4 — full input/output arrangement', () => {
  it('rejects an uninspected output (settle + an extra OP_RETURN)', () => {
    // The settle is the last tx (unreferenced), so appending keeps the lineage link intact but adds an
    // unclassifiable output. Raw-hex surgery: @bsv/sdk 2.x drops a mutate-after-parse output.
    const tampered = appendOutput(chain[2], Script.fromASM('OP_RETURN 6e6f').toHex())
    assertOutputAdded(chain[2], tampered)
    const r = verifyEvents([chain[0], chain[1], tampered])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/uninspected output/)
  })

  it('rejects a counterfeit token output (right push layout, wrong static code)', () => {
    const push = (n: number) => n.toString(16).padStart(2, '0') + '02'.repeat(n)
    const forgedHex = [16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33].map(push).join('') + '51' // + OP_1 suffix
    const tampered = appendOutput(chain[2], forgedHex, 1)
    assertOutputAdded(chain[2], tampered)
    const r = verifyEvents([chain[0], chain[1], tampered])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/uninspected output/)
  })

  it('rejects a settle carrying a p2Proof output in the change region', () => {
    const p2pHex = new Pay2ProofTemplate().lock(new Array(20).fill(0x11)).toHex()
    const tampered = appendOutput(chain[2], p2pHex, 1)
    assertOutputAdded(chain[2], tampered)
    expect(verifyEvent([chain[0], chain[1], tampered]).reason).toMatch(/change p2pkh/)
    expect(verifyEvents([chain[0], chain[1], tampered]).reason).toMatch(/change p2pkh/)
  })
})

describe('hardening — fail closed on bad input', () => {
  it('rejects a non-array input instead of throwing', () => {
    expect(verifyEvents(undefined as any).ok).toBe(false)
    expect(verifyEvent(null as any).ok).toBe(false)
  })

  it('rejects an empty batch / empty event', () => {
    expect(verifyEvents([]).reason).toMatch(/empty batch/)
    expect(verifyEvent([]).reason).toMatch(/empty event/)
  })

  it('rejects malformed transaction hex with a descriptive reason', () => {
    expect(verifyEvents(['not-hex-at-all']).reason).toMatch(/malformed transaction hex/)
    expect(verifyEvent(['not-hex-at-all']).reason).toMatch(/malformed transaction hex/)
  })

  it('rejects a well-formed tx that carries no BOLT token', () => {
    expect(verifyEvents([EMPTY_TX]).reason).toMatch(/no BOLT token output recognised/)
    expect(verifyEvent([EMPTY_TX]).reason).toMatch(/no BOLT token recognised/)
  })

  it('a non-token tx alongside a token is rejected', () => {
    expect(verifyEvent([chain[0], EMPTY_TX]).reason).toMatch(/is not a token tx/)
    expect(verifyEvents([chain[0], EMPTY_TX]).reason).toMatch(/not a BOLT token tx/)
  })

  it('verifyEvent reports a genuine transfer event from BEEF (the mint supplies the commit source)', () => {
    const r = verifyEvent([wire[0], wire[1], wire[2]])
    expect(r.ok, r.reason).toBe(true)
    expect(r.kind).toBe('transfer')
  })

  it('a settle whose parent field is truncated links to nothing (fails closed, no throw)', () => {
    // Same push count, but the 36-byte parentOutpoint (chunk 8) cut to 4 bytes: recognizeType rejects
    // the output, so the settle is no longer a token tx at all.
    const s = Transaction.fromHex(chain[2])
    const lock = s.outputs[0].lockingScript
    const chunks = lock.chunks.map((c, i) => (i === 8 ? { op: 4, data: [1, 2, 3, 4] } : c))
    const bad = new Transaction(2, [], [{ satoshis: 1, lockingScript: new Script(chunks) }])
    expect(verifyEvent([chain[1], bad]).ok).toBe(false)
  })
})

// Synthetic arrangement failures: txs assembled from genuine locks with a deliberately wrong
// interface layout, one per checkArrangement rejection branch. The scanner classifies interfaces and
// never runs scripts, so unsigned synthetic inputs are fine here.
describe('verifyEvent — malformed interface arrangement is rejected', () => {
  const lockOf = (i: number) => Transaction.fromHex(chain[i]).outputs[0].lockingScript
  const p2pLock = new Pay2ProofTemplate().lock(new Array(20).fill(0x11))
  const p2pkhLock = new P2PKH().lock(new Array(20).fill(0x22))
  const otherLock = Script.fromHex('006a') // OP_0 OP_RETURN -> "other"
  const out = (lock: Script) => ({ satoshis: 1, lockingScript: lock })
  const srcOf = (lock: Script) => new Transaction(1, [], [out(lock)])
  const inp = (src: Transaction): any =>
    ({ sourceTransaction: src, sourceOutputIndex: 0, unlockingScript: new Script([]), sequence: 0xffffffff })

  it('token output not at the expected position', () => {
    const tx = new Transaction(1, [], [out(p2pkhLock), out(lockOf(0))])
    expect(verifyEvent([tx]).reason).toMatch(/token output @0/)
  })

  it('a commit missing its p2Proof output', () => {
    const tx = new Transaction(1, [inp(srcOf(lockOf(0)))], [out(lockOf(1)), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/p2p output @1/)
  })

  it('a commit whose first input is not a token', () => {
    const tx = new Transaction(1, [inp(srcOf(p2pkhLock))], [out(lockOf(1)), out(p2pLock), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/token input @0/)
  })

  it('a p2Proof input on a commit (proofs are settle-only)', () => {
    const tx = new Transaction(1, [inp(srcOf(lockOf(0))), inp(srcOf(p2pLock))],
      [out(lockOf(1)), out(p2pLock), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/p2Proof input is only valid on a settle/)
  })

  it('an uninspected ("other") input', () => {
    const tx = new Transaction(1, [inp(srcOf(lockOf(0))), inp(srcOf(otherLock))],
      [out(lockOf(1)), out(p2pLock), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/uninspected input/)
  })

  it('an input whose source is supplied in the batch by txid (not attached) is classified', () => {
    // The commit's token input names the mint by sourceTXID only; the mint is in the batch.
    const mint = fromBeef(wire[0])
    const commit = fromBeef(wire[1])
    commit.inputs.forEach((i) => { i.sourceTransaction = undefined })
    const r = verifyEvents([mint, commit, fromBeef(wire[2])])
    expect(r.ok, r.reason).toBe(true)
  })

  it('a melt with no attached source resolves its type from a batch-supplied source', () => {
    // A melt-shaped tx spending the settle's token by txid; the settle is supplied in the event.
    const settle = Transaction.fromHex(chain[2])
    const melt = new Transaction(2, [{ sourceTXID: settle.id('hex'), sourceOutputIndex: 0, unlockingScript: new Script([]), sequence: 0xffffffff } as any],
      [out(p2pkhLock)])
    const r = verifyEvent([melt, settle])
    expect(r.type).toBe(T)
  })
})
