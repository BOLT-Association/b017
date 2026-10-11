// Edges the coverage bar found reachable (plan: every reachable branch gets a test, only defensive TypeScript
// guards get a `v8 ignore` with a reason).
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import { p2pkhUnlock } from '../../src/lib/boltLib.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'

const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const pkh = Hash.hash160(key.toPublicKey().encode(true))
const fundingTx = () => new Transaction(1, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(pkh) }])

describe('p2pkhUnlock: where the sighash source comes from', () => {
  const spend = (input: any) => new Transaction(2, [input], [{ satoshis: 900, lockingScript: new P2PKH().lock(pkh) }])

  it('signs from the attached source when the input carries no sourceTXID (the txid is derived from it)', async () => {
    const src = fundingTx()
    const tx = spend({ sourceTransaction: src, sourceOutputIndex: 0, sequence: 0xffffffff })
    expect(tx.inputs[0].sourceTXID).toBeUndefined()
    const script = await p2pkhUnlock(key).sign(tx, 0)
    expect(script.chunks.length).toBe(2) // sig, pubkey
  })

  it('refuses an input that names a txid but has no attached source (no amount or script to sign over)', async () => {
    const tx = spend({ sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, sequence: 0xffffffff })
    await expect(p2pkhUnlock(key).sign(tx, 0)).rejects.toThrow(/requires the input's source transaction/)
  })
})

describe('merge to a public-key recipient', () => {
  const MASK64 = (1n << 64n) - 1n
  const bal = (n: bigint): number[] => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n & MASK64, 0); b.writeBigUInt64LE(n >> 64n, 8); return Array.from(b) }
  const child = (n: string) => key.deriveChild(key.toPublicKey(), n)
  const source = (sats: number) => new Transaction(1, [], [{ satoshis: sats, change: true, lockingScript: new P2PKH().lock(pkh) }])

  it('pays the merged token to a third party\'s key and keeps the builder\'s current signer (it has no key for the new owner)', async () => {
    const a = await new SimpleMultiBOLT().mint(key, source(1000), '', bal(BigInt('0x1ffffffffffffe')))
    const b = await new SimpleMultiBOLT().mint(key, source(1001), '', bal(1n))
    await a.transfer(child('1'))
    await b.transfer(child('2'))
    const before = a.signer
    const thirdParty = child('400').toPublicKey().encode(true) as number[]
    const merged = await a.merge(b, thirdParty)
    expect(merged.signer).toBe(before)
    expect(merged.pubKey).toEqual(thirdParty)
  }, 600000)
})
