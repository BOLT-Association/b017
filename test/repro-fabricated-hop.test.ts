// ============================================================================
// REPRODUCTION: fabricated-hop forgery vs @bsv/sdk 2.1.6 (b017's own verifier).
//
// Run:  cd b017 && npx vitest run repro-fabricated-hop
//
// The chain in test/fixtures/fabricated-hop-chain.json was built by the sx
// simulator. This test does NOT trust the sx simulator: it decodes every tx
// with b017's own recognizeType/issuerPubKeyOf and verifies every input with
// b017's verifyTx (@bsv/sdk 2.1.6 Spend). It also runs the two controls that
// make a VALID verdict meaningful:
//   - positive: an honest transfer settle verifies;
//   - negative: a HEX-level one-byte tamper of a settle's output is REJECTED.
//
// What to look for in the decode:
//   tx0 mint            : genesis, real
//   tx1 transferCommit  : REAL commit, its proof (vout1) pays the recipient
//   tx2 transferSettle  : REAL settle, token -> recipient
//   tx3 forgedClonedSettle      : *** FABRICATED settled token: inputs are P2PKH ONLY
//                         (no token input), balance is arbitrary (2^100) ***
//   tx4 selfCommit      : commits the fabricated token (spends tx3's token)
//   tx5 forgedSettle    : settles it, co-spending tx1's REAL proof
//
// Decisive question: do tx4 (committing the fabricated token) and tx5 (settling
// it) verify on the consensus engine? If yes, the fabricated balance is
// spendable and the "back to genesis" chaining was not enforced.
//
// ---------------------------------------------------------------------------
// THIS FIXTURE IS A HISTORICAL RECORD, AND ITS ASSERTIONS ARE MEANT TO PASS.
//
// The hexes were built against the PRE-FIX bytecode (dd5e76f7), and that is the
// point: a regtest teranode running GoBDK consensus accepted this exact chain
// (576e31d4), and rejected a byte-tampered control. `expect(valid).toBe(true)`
// below is therefore the EVIDENCE, not a stale expectation - do not flip it.
//
// SimpleMultiBolt has since been fixed (the balance lineage anchor,
// SimpleMultiBolt.sx:688 and :891), so the live scanner REGISTRY now carries the
// new suffix hash and recognizeType() correctly refuses these old tokens. We
// therefore recognise the fixture against the pinned dd5e76f7 fingerprint below.
// The proof that the fix works lives elsewhere, against freshly built chains:
//   sx/tests/bolt/multi/simpleMultiBolt.fabricatedHop.test.js
// ============================================================================
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'fs'
import { dirname, join } from 'path'
import { fileURLToPath } from 'url'
import { Hash, P2PKH, PrivateKey, Transaction, Script } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../src/tokens/MultiBOLT.js'
import { verifyTx } from '../src/lib/boltLib.js'
import { recognizeType, recognizeP2P, sha256Hex } from '../src/lib/scanner/fingerprints.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const DUMP = JSON.parse(readFileSync(join(__dirname, 'fixtures', 'fabricated-hop-chain.json'), 'utf8'))

// sha256 of the SimpleMultiBOLT static contract suffix as it stood at dd5e76f7, the
// generation this fixture was built from. Derived two independent ways and checked to
// agree: from the fixture's own token output, and from the template blob in git at
// 849db10a~1. The leading push layout did not change across the fix (M2 landed back on
// the pre-lineage arg count), so ONLY this hash separates the two generations.
const LEGACY_SMB_SUFFIX_HASH = 'f1329fe588b05fd5212d6c5b54c69489880947a21d394e2f26f549a8535f8884'
const SMB_PUSH_LENGTHS = [16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33]

/** recognizeType() for the pre-fix generation: same push layout, the old suffix hash. */
function recognizeLegacySimpleMulti(lock: Script | null | undefined): boolean {
  if (!lock || !Array.isArray(lock.chunks)) return false
  const n = SMB_PUSH_LENGTHS.length
  if (lock.chunks.length <= n) return false
  const lens = lock.chunks.slice(0, n).map((c) => (c.data as number[] | undefined)?.length ?? 0)
  if (!lens.every((l, i) => l === SMB_PUSH_LENGTHS[i])) return false
  return sha256Hex(new Script(lock.chunks.slice(n)).toBinary()) === LEGACY_SMB_SUFFIX_HASH
}

/** A BOLT token of either generation: the shipped one, or the one this fixture froze. */
const isBoltToken = (lock: Script): boolean =>
  recognizeType(lock) !== null || recognizeLegacySimpleMulti(lock)

const balOf = (lock: Script): bigint => {
  const b = lock.chunks[0]?.data as number[] | undefined
  if (!b || b.length !== 16) return -1n
  const buf = Buffer.from(b)
  return buf.readBigUInt64LE(0) + (buf.readBigUInt64LE(8) << 64n)
}
const txoTypeOf = (lock: Script): string => {
  const t = lock.chunks[6]?.data as number[] | undefined
  return t && t.length ? t.map((x) => x.toString(16).padStart(2, '0')).join('') : '?'
}
function classify(lock: Script): string {
  if (recognizeType(lock)) return 'TOKEN(txoType=' + txoTypeOf(lock) + ', balance=' + balOf(lock) + ')'
  if (recognizeLegacySimpleMulti(lock))
    return 'TOKEN@dd5e76f7(txoType=' + txoTypeOf(lock) + ', balance=' + balOf(lock) + ')'
  if (recognizeP2P(lock)) return 'PROOF'
  const h = lock.toHex()
  if (h.length === 50 && h.startsWith('76a914') && h.endsWith('88ac')) return 'P2PKH'
  return 'other'
}
function linkGraph(): Transaction[] {
  const txs: Transaction[] = DUMP.hexes.map((h: string) => Transaction.fromHex(h))
  txs.forEach((tx, i) => tx.inputs.forEach((inp: any) => {
    // refs[i][k] but inputs are in order; map by position
  }))
  txs.forEach((tx, i) => tx.inputs.forEach((inp: any, k: number) => {
    const r = DUMP.refs[i]?.[k]
    if (r) { inp.sourceTransaction = txs[r[0]]; inp.sourceOutputIndex = r[1]; inp.sourceTXID = txs[r[0]].id('hex') }
  }))
  return txs
}
const tryVerify = (tx: Transaction): { valid: boolean; err: string } => {
  try { return { valid: verifyTx(tx, true).valid, err: '' } }
  catch (e: any) { return { valid: false, err: String(e.message).split(String.fromCharCode(10))[0].slice(0, 60) } }
}

describe('REPRO: fabricated-hop forgery on @bsv/sdk 2.1.6', () => {
  it('the forged tokens are owned/spent by a NON-issuer key (no issuer signature)', () => {
    const txs = linkGraph()
    // SimpleMultiBolt lock chunks: [0]=balance [2]=owner pubKeyHash(20) [6]=txoType [8]=parentOutpoint(36) [10]=issuerPubKey(33)
    const hex = (a?: number[]) => (a ? Buffer.from(a).toString('hex') : '-')
    const ownerOf = (lock: Script) => hex(lock.chunks[2]?.data as number[])
    const issuerPkhOf = (lock: Script) => { const pk = lock.chunks[10]?.data as number[] | undefined; return pk ? hex(Hash.hash160(pk)) : '-' }
    const parentNull = (lock: Script) => { const p = lock.chunks[8]?.data as number[] | undefined; return !p || p.every((b) => b === 0) }
    console.log('\n=== who owns each token, and is it the issuer? ===')
    for (const [i, vout] of [[0, 0], [1, 0], [3, 0], [4, 0], [5, 0]] as const) {
      const lock = txs[i].outputs[vout].lockingScript
      if (!recognizeType(lock)) continue
      const owner = ownerOf(lock), issuer = issuerPkhOf(lock)
      console.log(`tx${i}.${vout} ${(DUMP.names[i] || '?').padEnd(18)} owner=${owner.slice(0, 12)} issuerPKH=${issuer.slice(0, 12)} ownerIsIssuer=${owner === issuer} parentless(genesis)=${parentNull(lock)}`)
    }
    // The genesis (tx0) is owned by the issuer and is parentless -> its spend needs the issuer key.
    // The fabricated token (tx3) is NOT parentless and is owned by a NON-issuer key -> spending it
    // (tx4) needs only that owner's signature, never the issuer's.
    const g = txs[0].outputs[0].lockingScript, f = txs[3].outputs[0].lockingScript
    expect(parentNull(g)).toBe(true)                 // genesis is parentless
    expect(ownerOf(g)).toBe(issuerPkhOf(g))          // genesis owned by the issuer
    expect(parentNull(f)).toBe(false)                // fabricated token claims a non-genesis parent
    expect(ownerOf(f)).not.toBe(issuerPkhOf(f))      // fabricated token owned by a NON-issuer key
  })

  it('decodes every tx so the structure is inspectable', () => {
    const txs = linkGraph()
    console.log('\n=== forged chain, decoded with b017 recognizeType ===')
    txs.forEach((tx, i) => {
      const ins = tx.inputs.map((inp: any) => {
        const so = inp.sourceTransaction?.outputs[inp.sourceOutputIndex]
        return so ? classify(so.lockingScript).replace(/\(.*/, '') : 'external'
      })
      const outs = tx.outputs.map((o: any) => classify(o.lockingScript))
      console.log('tx' + i + ' ' + (DUMP.names[i] || '?').padEnd(18) + ' spends[' + ins.join(', ') + ']  ->  outs[' + outs.join(' | ') + ']')
    })
    const tx3 = txs[3]
    const tx3HasTokenInput = tx3.inputs.some((inp: any) =>
      inp.sourceTransaction && isBoltToken(inp.sourceTransaction.outputs[inp.sourceOutputIndex].lockingScript))
    console.log('\ntx3 (forgedClonedSettle) consumed a real token? ' + tx3HasTokenInput +
      '   ; its output token balance = ' + balOf(tx3.outputs[0].lockingScript))
    expect(tx3HasTokenInput).toBe(false)
    // shape-valid as a token of its own generation: fabricating the OUTPUT was never the
    // hard part, and that is the whole premise of the attack.
    expect(recognizeLegacySimpleMulti(tx3.outputs[0].lockingScript)).toBe(true)
    // and the live scanner refuses it, because the shipped contract is no longer this one.
    expect(recognizeType(tx3.outputs[0].lockingScript)).toBeNull()
  })

  it('verifies every tx on the consensus engine (the decisive result)', () => {
    const txs = linkGraph()
    txs.forEach((tx, i) => console.log('[VERIFY] tx' + i + ' ' + (DUMP.names[i] || '?').padEnd(18) + ' -> ' + JSON.stringify(tryVerify(tx))))
    // tx0 spends an external funding source not in this fixture (its verify throws on the missing
    // source) - a fixture limitation, not a covenant result. The covenant hops are tx4 and tx5.
    expect(tryVerify(txs[4]).valid).toBe(true) // committing the fabricated token
    expect(tryVerify(txs[5]).valid).toBe(true) // settling it, co-spending tx1's real proof
  })

  it('CONTROL: honest settle valid; hex-tampered honest settle INVALID (harness is faithful)', async () => {
    const issuer = PrivateKey.fromString('01'.padStart(64, '0'), 'hex')
    const alice = PrivateKey.fromString('02'.padStart(64, '0'), 'hex')
    const bob = PrivateKey.fromString('03'.padStart(64, '0'), 'hex')
    const src = (k: PrivateKey) => new Transaction(1, [], [{ satoshis: 100000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(k.toPublicKey().encode(true) as number[])) }])
    let t = await new SimpleMultiBOLT().mint(issuer, src(issuer), '', Array(16).fill(0).map((_, i) => (i === 0 ? 0xe8 : i === 1 ? 0x03 : 0)))
    t = await t.transfer(alice); t = await t.transfer(bob)
    const s = t.tx!
    console.log('[CTRL] honest settle          :', JSON.stringify(tryVerify(s)))
    expect(tryVerify(s).valid).toBe(true)
    const hex = s.toHex(); const o0 = s.outputs[0].lockingScript.toHex(); const pos = hex.indexOf(o0) + 2 + 8
    const flip = (parseInt(hex.substr(pos, 2), 16) ^ 0x01).toString(16).padStart(2, '0')
    const mut = Transaction.fromHex(hex.slice(0, pos) + flip + hex.slice(pos + 2))
    s.inputs.forEach((inp, k) => { mut.inputs[k].sourceTransaction = inp.sourceTransaction; mut.inputs[k].sourceOutputIndex = inp.sourceOutputIndex; mut.inputs[k].sourceTXID = inp.sourceTransaction?.id('hex') })
    console.log('[CTRL] honest settle TAMPERED :', JSON.stringify(tryVerify(mut)))
    expect(tryVerify(mut).valid).toBe(false)
  }, 120000)
})
