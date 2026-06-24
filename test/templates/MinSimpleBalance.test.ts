// B3 — MinSimpleBalanceBolt LOCK template: rebuilding the genesis lock from the sx golden
// mint's own args reproduces the golden token output byte-for-byte, and the static suffix
// is byte-identical to the sx-compiled contract. (The spend/unlock is B2b.)
import { describe, it, expect } from 'vitest'
import { Transaction, Script } from '@bsv/sdk'
import MinSimpleBalanceTemplate from '../../src/tokens/templates/MinSimpleBalance.sx.template.js'
import { readFixture, readFixtureJSON } from '../helpers/fixtures.js'

const golden = readFixtureJSON('MinSimpleBalanceBolt.lifecycle.golden.json')
// Lock-suffix golden vendored by scripts/build-min-simple-balance-bolt.mjs (isolation: no sibling sx/).
const lockHexSuffix = readFixture('MinSimpleBalanceBolt.lockSuffix.hex')

describe('B3 — MinSimpleBalanceBolt LOCK byte-equals the sx golden mint', () => {
  const mintTx = Transaction.fromHex(golden.txs[0].hex)
  const goldLock = mintTx.outputs[0].lockingScript
  const ch = goldLock.chunks
  const arg = (i: number): number[] => (ch[i].data as number[]) ?? []
  const [balance, pubKeyHash, commit, txoType, parent, grandparent, issuerPubKey] =
    [0, 1, 2, 3, 4, 5, 6].map(arg)

  const tpl = new MinSimpleBalanceTemplate()
  const rebuilt = tpl.lock(balance, pubKeyHash, issuerPubKey, commit, txoType, parent, grandparent)

  it('balance is the FIRST push (16B); issuerPubKey (33B) last; layout 20/20/36/36', () => {
    expect(balance.length).toBe(16)
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
