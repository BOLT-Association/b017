// FixedBOLT and OpenBOLT (genesis family): full lifecycles built by the library and verified on the @bsv/sdk Spend
// engine (every tx is executed by the class's own verifier, and again here), the two leading pushes on every hop,
// and the merge rules (FixedBOLT: one genesis only; OpenBOLT: across genesis roots, re-rooted; both: one issuer).
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, Utils } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { FixedBOLT, OpenBOLT } from '../../src/tokens/GenesisMultiBOLT.js'
import { verifyTx } from '../../src/lib/boltLib.js'
import { outpointOf } from '../../src/lib/genesis.js'

const MASK64 = (1n << 64n) - 1n
const bal = (n: bigint): number[] => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n & MASK64, 0); b.writeBigUInt64LE(n >> 64n, 8); return Array.from(b) }
const SIM = BigInt('0x1ffffffffffffe')
const MINT_DATA = 'Central Bank of Ireland ÉIR£ Currency Issuance'
const hex = (b: number[] | undefined) => Utils.toHex(b ?? [])

const issuer = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
const other = PrivateKey.fromString('a1b2c3d4e5f60718293a4b5c6d7e8f90112233445566778899aabbccddeeff00', 'hex')
const child = (k: PrivateKey, i: string) => k.deriveChild(k.toPublicKey(), i)
// distinct satoshis -> distinct source txids -> distinct mint outpoints (identical sources mint identical tokens)
const source = (k: PrivateKey, sats = 100000) => new Transaction(1, [], [
  { satoshis: sats, change: true, lockingScript: new P2PKH().lock(Hash.hash160(k.toPublicKey().encode(true))) },
])
const assertValid = (tx: Transaction) => {
  tx.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
  expect(verifyTx(tx, true).valid).toBe(true)
}
// Split piece B: the split settle's change pays piece A's key, so B's next commit is funded from its own source
// (a SimpleMultiBOLT builder trait, the same for every fungible type); its settle then uses that commit's change.
const transferPieceB = async (b: SimpleMultiBOLT, owner: PrivateKey, to: PrivateKey, sats: number) => {
  const fund = { sourceTransaction: source(owner, sats), sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(owner), sequence: 0xffffffff }
  await b.commit(to, undefined, false, fund as any)
  await b.settle(to)
}
const lead = (t: SimpleMultiBOLT) => t.tx!.outputs[t.voutIdx!].lockingScript.chunks
const field0 = (t: SimpleMultiBOLT) => hex(lead(t)[0].data as number[])
const mintDataOf = (t: SimpleMultiBOLT) => hex((lead(t)[1].data as number[]) ?? [])

for (const [name, Cls] of [['FixedBOLT', FixedBOLT], ['OpenBOLT', OpenBOLT]] as const) {
  describe(`${name} lifecycle (Spend engine)`, () => {
    it('mint (with mintData) -> transfer x3 -> split -> transfer each piece -> melt; leading pushes on every hop', async () => {
      const t = await new Cls().mint(issuer, source(issuer), MINT_DATA, bal(SIM))
      assertValid(t.tx!)
      expect(field0(t)).toBe('00'.repeat(36))                                    // mint: null field
      expect(mintDataOf(t)).toBe(hex(Array.from(Buffer.from(MINT_DATA, 'utf8')))) // mint: the issuer's bytes
      const mintOutpoint = hex(outpointOf(t.tx!, 0))

      await t.commit(child(issuer, '1'))                                         // the genesis spend
      assertValid(t.tx!)
      expect(field0(t)).toBe(mintOutpoint)
      expect(mintDataOf(t)).toBe('')                                             // OP_0 after the mint
      await t.settle(child(issuer, '1')); assertValid(t.tx!)
      await t.transfer(child(issuer, '2')); assertValid(t.tx!)                   // settle rebuilds the genesis spend
      await t.transfer(child(issuer, '3')); assertValid(t.tx!)
      expect(field0(t)).toBe(mintOutpoint)

      const [a, b] = await t.split(child(issuer, '10'), child(issuer, '11'), bal(1n))
      assertValid(a.tx!)
      expect(b).toBeInstanceOf(Cls)
      expect([field0(a), field0(b)]).toEqual([mintOutpoint, mintOutpoint])
      await a.transfer(child(issuer, '20')); assertValid(a.tx!)
      await transferPieceB(b, child(issuer, '11'), child(issuer, '21'), 50000); assertValid(b.tx!)
      expect([field0(a), field0(b)]).toEqual([mintOutpoint, mintOutpoint])
      await a.melt(); assertValid(a.tx!)
    }, 600000)
  })
}

describe('mintData', () => {
  it('may be given as bytes instead of a UTF-8 string', async () => {
    const bytes = [0x00, 0xff, 0x10, 0x20]
    const t = await new FixedBOLT().mint(issuer, source(issuer), bytes, bal(SIM))
    expect(lead(t)[1].data).toEqual(bytes)
    await t.commit(child(issuer, '1'))
    expect((lead(t)[1].data as number[] | undefined) ?? []).toEqual([])
  }, 600000)
})

describe('FixedBOLT merges: one genesis only', () => {
  it('two pieces of ONE genesis (split, each transferred) merge and settle', async () => {
    const t = await new FixedBOLT().mint(issuer, source(issuer), '', bal(SIM))
    await t.transfer(child(issuer, '1'))
    const [a, b] = await t.split(child(issuer, '10'), child(issuer, '11'), bal(1n))
    await a.transfer(child(issuer, '20'))
    await transferPieceB(b, child(issuer, '11'), child(issuer, '21'), 50000)
    const g = field0(a)
    const merged = await a.merge(b, child(issuer, '400'))
    assertValid(merged.tx!)
    expect(field0(merged)).toBe(g)
  }, 600000)

  it('two separate mints (same issuer, two genesis roots): refused before building', async () => {
    const a = await new FixedBOLT().mint(issuer, source(issuer, 100000), '', bal(SIM))
    const b = await new FixedBOLT().mint(issuer, source(issuer, 90000), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(issuer, '2'))
    expect(field0(a)).not.toBe(field0(b))
    await expect(a.merge(b, child(issuer, '400'))).rejects.toThrow(/different genesis/)
  }, 600000)

  it('...and the covenant itself refuses it: the merge commit built anyway is invalid', async () => {
    const a = await new FixedBOLT().mint(issuer, source(issuer, 100000), '', bal(SIM))
    const b = await new FixedBOLT().mint(issuer, source(issuer, 90000), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(issuer, '2'))
    await expect(SimpleMultiBOLT.prototype.merge.call(a, b, child(issuer, '400'))).rejects.toThrow(/MERGE COMMIT tx not valid|OP_EQUALVERIFY/)
  }, 600000)

  it('two issuers: refused before building', async () => {
    const a = await new FixedBOLT().mint(issuer, source(issuer), '', bal(SIM))
    const b = await new FixedBOLT().mint(other, source(other), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(other, '2'))
    await expect(a.merge(b, child(issuer, '400'))).rejects.toThrow(/different issuers/)
  }, 600000)
})

describe('OpenBOLT merges: across genesis roots, re-rooted; one issuer', () => {
  it('two separate mints (same issuer) merge; the merge commit re-roots to vin0\'s token outpoint, the settle copies it', async () => {
    const a = await new OpenBOLT().mint(issuer, source(issuer, 100000), '', bal(SIM))
    const b = await new OpenBOLT().mint(issuer, source(issuer, 90000), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(issuer, '2'))
    expect(field0(a)).not.toBe(field0(b))
    const vin0 = hex(outpointOf(a.tx!, a.voutIdx!))
    const merged = await a.merge(b, child(issuer, '400'))
    assertValid(merged.tx!)
    const commit = merged.prevTxs[merged.prevTxs.length - 2]
    expect(hex(commit.outputs[0].lockingScript.chunks[0].data as number[])).toBe(vin0) // re-rooted at the merge commit
    expect(field0(merged)).toBe(vin0)                                                // copied by the settle
    await merged.transfer(child(issuer, '500')); assertValid(merged.tx!)              // and spendable onward
    expect(field0(merged)).toBe(vin0)
  }, 600000)

  it('two issuers: refused before building', async () => {
    const a = await new OpenBOLT().mint(issuer, source(issuer), '', bal(SIM))
    const b = await new OpenBOLT().mint(other, source(other), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(other, '2'))
    await expect(a.merge(b, child(issuer, '400'))).rejects.toThrow(/different issuers/)
  }, 600000)

  it('...and the covenant itself refuses it: the merge commit built anyway is invalid', async () => {
    const a = await new OpenBOLT().mint(issuer, source(issuer), '', bal(SIM))
    const b = await new OpenBOLT().mint(other, source(other), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(other, '2'))
    await expect(SimpleMultiBOLT.prototype.merge.call(a, b, child(issuer, '400'))).rejects.toThrow(/MERGE COMMIT tx not valid|OP_EQUALVERIFY/)
  }, 600000)
})
