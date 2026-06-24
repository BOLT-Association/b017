// pay2Proof template — the b017 marker proof output carried by commit txs and consumed by settle
// txs. Tests the lock layout, golden recognition, and a full sign -> Spend-verify round trip.
import { describe, it, expect } from 'vitest'
import { Hash, OP, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import { recognizeP2P } from '../../src/lib/scanner/fingerprints.js'
import { verifyTx } from '../../src/lib/boltLib.js'

const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const pubKey = key.toPublicKey().encode(true) as number[]
const pkh = Hash.hash160(pubKey)
const tpl = new Pay2ProofTemplate()

describe('pay2Proof template', () => {
  it('lock is [b017, EQUALVERIFY, DUP, HASH160, <pkh>, EQUALVERIFY, CHECKSIG]', () => {
    const lock = tpl.lock(pkh)
    const c = lock.chunks
    expect(c.length).toBe(7)
    expect(c[0].data).toEqual([0xb0, 0x17]) // the b017 marker
    expect(c[1].op).toBe(OP.OP_EQUALVERIFY)
    expect(c[2].op).toBe(OP.OP_DUP)
    expect(c[3].op).toBe(OP.OP_HASH160)
    expect(c[4].data).toEqual(pkh)
    expect(c[5].op).toBe(OP.OP_EQUALVERIFY)
    expect(c[6].op).toBe(OP.OP_CHECKSIG)
  })

  it('is recognised by the golden p2Proof fingerprint', () => {
    expect(recognizeP2P(tpl.lock(pkh))).toBe(true)
  })

  it('estimateLength is 111', async () => {
    expect(await tpl.unlock(key).estimateLength()).toBe(111)
  })

  it('a signed proof input Spend-verifies against its lock', async () => {
    const funding = new Transaction(1, [], [{ satoshis: 1000, lockingScript: tpl.lock(pkh) }])
    const spend = new Transaction(
      1,
      [{
        sourceTransaction: funding, sourceOutputIndex: 0,
        unlockingScriptTemplate: tpl.unlock(key), sequence: 0xffffffff,
      }],
      [{ satoshis: 1, lockingScript: new P2PKH().lock(pkh) }],
    )
    await spend.fee(0)
    await spend.sign()
    spend.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
    expect(verifyTx(spend, true).valid).toBe(true)
  })

  it('signs from explicit sourceSatoshis + lockingScript (no attached source tx)', async () => {
    const lock = tpl.lock(pkh)
    const tx = new Transaction(1,
      [{ sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, sequence: 0xffffffff } as any],
      [{ satoshis: 1, lockingScript: new P2PKH().lock(pkh) }])
    const us = await tpl.unlock(key, 1000, lock).sign(tx, 0)
    expect(us.chunks.length).toBe(3) // [sig, pubkey, b017]
    expect(us.chunks[2].data).toEqual([0xb0, 0x17])
  })

  it('throws when neither sourceTXID nor sourceTransaction is present', async () => {
    const tx = new Transaction(1, [{ sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    await expect(tpl.unlock(key).sign(tx, 0)).rejects.toThrow(/sourceTXID or sourceTransaction/)
  })

  it('throws when sourceSatoshis cannot be resolved', async () => {
    const tx = new Transaction(1, [{ sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    await expect(tpl.unlock(key).sign(tx, 0)).rejects.toThrow(/sourceSatoshis/)
  })

  it('throws when the lockingScript cannot be resolved', async () => {
    const tx = new Transaction(1, [{ sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    await expect(tpl.unlock(key, 1000).sign(tx, 0)).rejects.toThrow(/lockingScript/)
  })
})
