// B4 — the fingerprint registry recognises genuine tokens by [pushLengths] + sha256(staticCode),
// and rejects tampered contracts / non-token scripts.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, Script } from '@bsv/sdk'
import { REGISTRY, recognizeType, recognizeP2P, issuerPubKeyOf } from '../../src/lib/scanner/fingerprints.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { readFixtureJSON } from '../helpers/fixtures.js'

const goldenLock = (name: string): Script =>
  Transaction.fromHex(readFixtureJSON(`${name}.lifecycle.golden.json`).txs[0].hex).outputs[0].lockingScript

describe('B4 — fingerprint registry', () => {
  it('every type spec has a 64-hex suffixHash and issuerPubKey (33B) as the last push', () => {
    for (const spec of Object.values(REGISTRY)) {
      expect(spec.suffixHashHex).toMatch(/^[0-9a-f]{64}$/)
      expect(spec.pushLengths[spec.pushLengths.length - 1]).toBe(33)
      expect(spec.dataPushCount).toBe(spec.pushLengths.length)
    }
  })

  it('recognises each NFT golden mint as its own type', () => {
    expect(recognizeType(goldenLock('MinSimpleDiscountBolt'))).toBe('MinSimpleDiscountBOLT')
    expect(recognizeType(goldenLock('MinSimpleBalanceBolt'))).toBe('MinSimpleBalanceBOLT')
  })

  it('recognises a SimpleMultiBolt mint (the fungible flagship)', async () => {
    const k = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
    const src = new Transaction(1, [], [
      { satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(k.toPublicKey().encode(true))) },
    ])
    const token = await new SimpleMultiBOLT().mint(k, src, '')
    expect(recognizeType(token.tx!.outputs[0].lockingScript)).toBe('SimpleMultiBOLT')
  })

  it('rejects a plain P2PKH (not a BOLT token)', () => {
    expect(recognizeType(new P2PKH().lock(new Array(20).fill(0x11)))).toBeNull()
  })

  it('rejects a tampered static contract (extra opcode appended)', () => {
    const lock = goldenLock('MinSimpleDiscountBolt')
    const tampered = new Script([...lock.chunks, { op: 0x51 }]) // append OP_1
    expect(recognizeType(tampered)).toBeNull()
  })

  it('issuerPubKeyOf returns the 33-byte last push of a recognised token', () => {
    const lock = goldenLock('MinSimpleBalanceBolt')
    expect(issuerPubKeyOf(lock, 'MinSimpleBalanceBOLT').length).toBe(33)
  })

  it('recognizeType fails closed on null/empty/garbage scripts', () => {
    expect(recognizeType(null as any)).toBeNull()
    expect(recognizeType(undefined as any)).toBeNull()
    expect(recognizeType(new Script([]))).toBeNull()
  })
})

describe('B4 — p2Proof golden fingerprint (recognizeP2P)', () => {
  const pkh = new Array(20).fill(0x22)

  it('recognises a genuine Pay2ProofTemplate lock', () => {
    expect(recognizeP2P(new Pay2ProofTemplate().lock(pkh))).toBe(true)
  })

  it('rejects a tampered b017 marker (same shape, wrong marker bytes)', () => {
    const lock = new Pay2ProofTemplate().lock(pkh)
    const bad = new Script(lock.chunks.map((c, i) => (i === 0 ? { op: 2, data: [0xde, 0xad] } : c)))
    expect(recognizeP2P(bad)).toBe(false)
  })

  it('rejects a wrong pkh length and a plain P2PKH', () => {
    expect(recognizeP2P(new Pay2ProofTemplate().lock(new Array(19).fill(0x22)))).toBe(false)
    expect(recognizeP2P(new P2PKH().lock(pkh))).toBe(false)
  })

  it('rejects a token lock and null/empty', () => {
    expect(recognizeP2P(goldenLock('MinSimpleDiscountBolt'))).toBe(false)
    expect(recognizeP2P(null as any)).toBe(false)
    expect(recognizeP2P(new Script([]))).toBe(false)
  })
})
