// B4 — the fingerprint registry recognises genuine tokens by [pushLengths] + sha256(staticCode),
// and rejects tampered contracts / non-token scripts.
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, resolve } from 'node:path'
import { Hash, P2PKH, PrivateKey, Transaction, Script } from '@bsv/sdk'
import { REGISTRY, recognizeType, issuerPubKeyOf } from '../src/scan/fingerprints.js'
import { SimpleMultiBOLT } from '../src/SimpleMultiBolt.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const goldenLock = (name: string): Script =>
  Transaction.fromHex(
    JSON.parse(readFileSync(resolve(__dirname, `fixtures/${name}.lifecycle.golden.json`), 'utf8')).txs[0].hex,
  ).outputs[0].lockingScript

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
})
