// A1 — simplemultibolt must be elas-free and verify on @bsv/sdk only.
// (1) No source file imports @elas_co/ts.
// (2) The full SMB lifecycle (mint, transfer×2, split, merge, melt) verifies with verifyTx (bsv Spend) alone.
import { describe, it, expect } from 'vitest'
import { readFileSync, readdirSync } from 'fs'
import { join, dirname } from 'path'
import { fileURLToPath } from 'url'
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { verifyTx } from '../../src/lib/boltLib.js'

const __dirname = dirname(fileURLToPath(import.meta.url))

// 16-byte LE balance helpers
const MASK64 = (BigInt(1) << BigInt(64)) - BigInt(1)
function bal(amount: bigint): number[] {
  const x = amount & ((BigInt(1) << BigInt(128)) - BigInt(1))
  const buf = Buffer.alloc(16)
  buf.writeBigUInt64LE(x & MASK64, 0)
  buf.writeBigUInt64LE((x >> BigInt(64)) & MASK64, 8)
  return Array.from(buf)
}
function balToBig(b: number[]): bigint {
  const buf = Buffer.from(b.slice(0, 16))
  return buf.readBigUInt64LE(0) + (buf.readBigUInt64LE(8) << BigInt(64))
}

// bsv-only validity assertion (no elas fallback).
function assertValid(label: string, tx: Transaction) {
  tx.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
  const { valid, scriptExecutions } = verifyTx(tx, true)
  if (!valid) {
    const failedIdx = scriptExecutions.findIndex(e => !e.valid)
    console.log(`bsv FAILURE (${label}) input ${failedIdx}`)
  }
  expect(valid).toBe(true)
}

describe('A1 — simplemultibolt is elas-free + verifies on @bsv/sdk only', () => {
  it('no source file imports @elas_co/ts', () => {
    const srcDir = join(__dirname, '..', '..', 'src')
    const walk = (d: string): string[] =>
      readdirSync(d, { withFileTypes: true }).flatMap((e) =>
        e.isDirectory() ? walk(join(d, e.name)) : e.name.endsWith('.ts') ? [join(d, e.name)] : [])
    const offenders = walk(srcDir).filter((f) => /@elas_co\/ts/.test(readFileSync(f, 'utf8')))
    expect(offenders).toEqual([])
  })

  const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const SIM_BALANCE = BigInt('0x1ffffffffffffe')
  const freshSource = (): Transaction =>
    new Transaction(1, [], [{
      satoshis: 1000, change: true,
      lockingScript: new P2PKH().lock(Hash.hash160(issuerKey.toPublicKey().encode(true))),
    }])

  it('mint → transfer×2 → split verifies on verifyTx (bsv)', async () => {
    let token = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    assertValid('mint', token.tx!)
    token = await token.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '1'))
    assertValid('transfer1', token.tx!)
    token = await token.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '2'))
    assertValid('transfer2', token.tx!)
    const before = balToBig(token.balance)
    const [main, piece] = await token.split(
      issuerKey.deriveChild(issuerKey.toPublicKey(), '10'),
      issuerKey.deriveChild(issuerKey.toPublicKey(), '11'), bal(BigInt(1)))
    assertValid('split', main.tx!)
    expect(balToBig(main.balance) + balToBig(piece.balance)).toBe(before)
  })

  it('mint×2 → merge → melt verifies on verifyTx (bsv)', async () => {
    let tokenA = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    let tokenB = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(BigInt(1)))
    tokenA = await tokenA.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '1'))
    tokenB = await tokenB.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '2'))
    const sumIn = balToBig(tokenA.balance) + balToBig(tokenB.balance)
    const merged = await tokenA.merge(tokenB, issuerKey.deriveChild(issuerKey.toPublicKey(), '400'))
    assertValid('merge', merged.tx!)
    expect(balToBig(merged.balance)).toBe(sumIn)
    const melted = await merged.melt()
    assertValid('melt', melted.tx!)
  })

  // Builder option branches (forceNoChange / forceNoFund / fundOverride / melt-to-pkh). These modes
  // build zero-funding / overridden-funding shapes the mandatory-change contract would reject, so they
  // run under skipVerify (a supported builder mode) purely to drive the construction branches.
  it('exercises forceNoChange / forceNoFund / fundOverride / melt(pkh) construction paths', async () => {
    const k1 = issuerKey.deriveChild(issuerKey.toPublicKey(), '901')
    const k2 = issuerKey.deriveChild(issuerKey.toPublicKey(), '902')

    const a = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    a.skipVerify = true
    await a.transfer(k1, '', '', false, true, undefined, true) // forceNoChange + forceNoFund
    expect(a.tx).toBeDefined()

    const b = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    b.skipVerify = true
    const ov = freshSource()
    const fundOverride: any = {
      sourceTransaction: ov, sourceOutputIndex: 0,
      unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff,
    }
    await b.transfer(k2, '', '', false, false, fundOverride, false) // fundOverride path
    expect(b.tx).toBeDefined()

    const c = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    await c.melt(Hash.hash160(k1.toPublicKey().encode(true))) // melt to an explicit pkh
    assertValid('melt(pkh)', c.tx!)
  })

  it('split + merge accept an explicit fundingSource { tx, vout, key }', async () => {
    const fundingSource = () => ({ tx: freshSource(), vout: 0, key: issuerKey })

    let t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    t = await t.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '1'))
    const [main, piece] = await t.split(
      issuerKey.deriveChild(issuerKey.toPublicKey(), '10'),
      issuerKey.deriveChild(issuerKey.toPublicKey(), '11'), bal(BigInt(1)), fundingSource())
    assertValid('split(funded)', main.tx!)

    let a = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM_BALANCE))
    let b = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(BigInt(1)))
    a = await a.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '1'))
    b = await b.transfer(issuerKey.deriveChild(issuerKey.toPublicKey(), '2'))
    const merged = await a.merge(b, issuerKey.deriveChild(issuerKey.toPublicKey(), '400'), fundingSource())
    assertValid('merge(funded)', merged.tx!)
    void main; void piece
  })
})
