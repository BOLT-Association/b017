// B2a — MinSimpleDiscountBolt LOCK template: rebuilding the genesis lock from the sx golden
// mint's own args reproduces the golden token output byte-for-byte, and the static suffix
// is byte-identical to the sx-compiled contract. (The spend/unlock is B2b.)
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, resolve } from 'node:path'
import { Transaction, Script } from '@bsv/sdk'
import MinSimpleDiscountTemplate from '../src/templates/MinSimpleDiscount.sx.template.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const golden = JSON.parse(
  readFileSync(resolve(__dirname, 'fixtures/MinSimpleDiscountBolt.lifecycle.golden.json'), 'utf8'),
)
// Lock-suffix golden vendored by scripts/build-min-simple-discount-bolt.mjs (isolation: no sibling sx/).
const lockHexSuffix = readFileSync(resolve(__dirname, 'fixtures/MinSimpleDiscountBolt.lockSuffix.hex'), 'utf8').trim()

describe('B2a — MinSimpleDiscountBolt LOCK byte-equals the sx golden mint', () => {
  const mintTx = Transaction.fromHex(golden.txs[0].hex)
  const goldLock = mintTx.outputs[0].lockingScript
  const ch = goldLock.chunks
  const arg = (i: number): number[] => (ch[i].data as number[]) ?? []
  const [discount, pubKeyHash, commit, txoType, parent, grandparent, issuerPubKey] =
    [0, 1, 2, 3, 4, 5, 6].map(arg)

  const tpl = new MinSimpleDiscountTemplate()
  const rebuilt = tpl.lock(discount, pubKeyHash, issuerPubKey, commit, txoType, parent, grandparent)

  it('discount is the FIRST push (0x0a); issuerPubKey (33B) is the 7th; layout 20/20/36/36', () => {
    expect(discount).toEqual([0x0a])
    expect(issuerPubKey.length).toBe(33)
    expect([pubKeyHash.length, commit.length, parent.length, grandparent.length]).toEqual([20, 20, 36, 36])
  })

  it('rebuilt lock byte-equals the sx golden mint token output (vout 0)', () => {
    expect(rebuilt.toHex()).toBe(goldLock.toHex())
  })

  it('static suffix byte-identical to the sx-compiled contract (artifact)', () => {
    expect(new Script(rebuilt.chunks.slice(7)).toHex()).toBe(lockHexSuffix)
  })
})
