// No dead tokens: a fungible token whose index byte is not its output position stays spendable.
//
// The fungible script writes a token's index byte (lock chunk 7, `outputIndexN`) from the spender's `inputIndexN`
// argument, or from the `i2` interop slot for a split settle's second token, and never reads it back; with `pkh1`
// set a split settle's two tokens come out swapped. The Lean development found this and proved the script's
// reading (lean/README.md, Finding 6); its `smb_probe_idx_*` vectors judge the same transactions in Lean. This suite
// keeps the fact under the fast test run: every shape of mismatch, then every later operation on the mismatched
// token, built with the honest builders and judged by verifyTx (the @bsv/sdk Spend engine).
import { describe, it, expect } from 'vitest'
import { PrivateKey, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { verifyTx } from '../../src/lib/boltLib.js'
import {
  splitSettleWithFlags, tokenAt, spendIdx1, fundFor, sourceFor, last2, meltOf, indexByteAt,
} from '../helpers/indexByte.js'

const issuer = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000003', 'hex')
const child = (k: PrivateKey, n: string) => k.deriveChild(k.toPublicKey(), n)
const MASK64 = (BigInt(1) << BigInt(64)) - BigInt(1)
function bal(amount: bigint): number[] {
  const x = amount & ((BigInt(1) << BigInt(128)) - BigInt(1))
  const buf = Buffer.alloc(16)
  buf.writeBigUInt64LE(x & MASK64, 0)
  buf.writeBigUInt64LE((x >> BigInt(64)) & MASK64, 8)
  return Array.from(buf)
}

function assertValid(label: string, tx: Transaction) {
  tx.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
  const { valid, scriptExecutions } = verifyTx(tx, true)
  if (!valid) console.log(`${label}: input ${scriptExecutions.findIndex((e) => !e.valid)} failed`)
  expect(valid, label).toBe(true)
}

/** mint (1000) → transfer to `owner`, with the builder's own checks off so that verifyTx is the judge. */
async function minted(owner: PrivateKey, seed: string): Promise<SimpleMultiBOLT> {
  let t = await new SimpleMultiBOLT().mint(issuer, sourceFor(issuer), '', bal(BigInt(1000)))
  t = await t.transfer(owner)
  t.skipVerify = true
  void seed
  return t
}

/** An honest split of a fresh token into 600 and 400, then its settle rebuilt with the given flags. */
async function splitWith(seed: string, swapped: boolean, i2: boolean) {
  const owner = child(issuer, seed + '1'), keyA = child(issuer, seed + '2'), keyB = child(issuer, seed + '3')
  const piece = bal(BigInt(400))
  const t = await minted(owner, seed)
  const [main] = await t.split(keyA, keyB, piece)
  const r = await splitSettleWithFlags(main, owner, keyA, keyB, bal(BigInt(1000)), piece, swapped, i2)
  return { ...r, keyA, keyB, piece, main }
}

describe('index byte: a token whose index byte is not its position stays spendable (no dead tokens)', () => {
  it('S1: the swapped split settle (pkh1 set) verifies, and its second token at output 0 with index byte 1 transfers', async () => {
    const { settle, lineage, keyB, piece, main, bVout, aVout } = await splitWith('1', true, false)
    assertValid('swapped split settle', settle)
    expect(bVout).toBe(0)
    expect(indexByteAt(settle, bVout)).toBe(1)
    expect(indexByteAt(settle, aVout)).toBe(0)
    const b = tokenAt(settle, bVout, keyB, piece, lineage, main)
    const to = child(issuer, '14')
    await b.commit(to, '', false, fundFor(keyB))
    await b.settle(to, '', false, fundFor(keyB))
    const [c, s] = last2(b)
    assertValid('second token transfer commit', c)
    assertValid('second token transfer settle (rebuilds the swapped settle)', s)
  })

  it('S2: the i2 split settle verifies; its second token at output 1 with index byte 0 transfers, splits, merges as either input, and melts', async () => {
    const { settle, lineage, keyB, piece, main, bVout } = await splitWith('2', false, true)
    assertValid('i2 split settle', settle)
    expect(bVout).toBe(1)
    expect(indexByteAt(settle, bVout)).toBe(0)
    // transfer
    {
      const x = tokenAt(settle, bVout, keyB, piece, lineage, main)
      const to = child(issuer, '24')
      await x.commit(to, '', false, fundFor(keyB))
      await x.settle(to, '', false, fundFor(keyB))
      const [c, s] = last2(x)
      assertValid('transfer commit', c)
      assertValid('transfer settle (rebuilds the i2 settle)', s)
    }
    // split
    {
      const x = tokenAt(settle, bVout, keyB, piece, lineage, main)
      await x.split(child(issuer, '25'), child(issuer, '26'), bal(BigInt(100)), { tx: sourceFor(keyB), vout: 0, key: keyB })
      const [c, s] = last2(x)
      assertValid('split commit', c)
      assertValid('split settle', s)
    }
    // merge, as the second token input
    {
      const x = tokenAt(settle, bVout, keyB, piece, lineage, main)
      const a = await minted(child(issuer, '27'), '27')
      await a.merge(x, child(issuer, '28'))
      const [c, s] = last2(a)
      assertValid('merge commit (mismatched token second)', c)
      assertValid('merge settle (mismatched token second)', s)
    }
    // merge, as the first token input
    {
      const x = tokenAt(settle, bVout, keyB, piece, lineage, main)
      const o = await minted(child(issuer, '29'), '29')
      await x.merge(o, child(issuer, '30'), { tx: sourceFor(keyB), vout: 0, key: keyB })
      const [c, s] = last2(x)
      assertValid('merge commit (mismatched token first)', c)
      assertValid('merge settle (mismatched token first)', s)
    }
    // melt
    assertValid('melt', await meltOf(settle, bVout, keyB))
  })

  it('S3: a transfer commit with inputIndexN = 1 writes index byte 1 at output 0; its settle and a further transfer verify', async () => {
    const owner = child(issuer, '31'), to = child(issuer, '32'), next = child(issuer, '33')
    const t = await minted(owner, '3')
    const c1 = await spendIdx1(t, to, true)
    assertValid('commit with inputIndexN = 1', c1)
    expect(indexByteAt(c1, 0)).toBe(1)
    await t.settle(to)
    assertValid('its honest settle', t.prevTxs[t.prevTxs.length - 1])
    await t.transfer(next)
    const [c, s] = last2(t)
    assertValid('further transfer commit', c)
    assertValid('further transfer settle (rebuilds the index-1 commit)', s)
  })

  it('S4: a transfer settle with inputIndexN = 1 writes index byte 1 at output 0; a further transfer verifies', async () => {
    const owner = child(issuer, '41'), to = child(issuer, '42'), next = child(issuer, '43')
    const t = await minted(owner, '4')
    await t.commit(to)
    const s1 = await spendIdx1(t, to, false)
    assertValid('settle with inputIndexN = 1', s1)
    expect(indexByteAt(s1, 0)).toBe(1)
    await t.transfer(next)
    const [c, s] = last2(t)
    assertValid('further transfer commit', c)
    assertValid('further transfer settle', s)
  })
})
