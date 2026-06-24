// B2b-2 — singleAncestorPieces must reproduce the canonical sx golden's ancestor block byte-for-byte.
// Golden truth: sx/tests/bolt/simple/zeroData/MinSimpleDiscountBolt.sim.json (minSimpleDiscountBolt.test.js),
// whose settleTx2 (#4) reaches back over a >=4-tx chain to reconstruct commit c1. The fixture is derived
// from that sim via spv-demo-wapps/libs/bolt/src/gen-sx-golden.ts.
import { describe, it, expect } from 'vitest'
import { Transaction } from '@bsv/sdk'
import { singleAncestorPieces } from '../../src/lib/single/singleAncestor.js'
import { readFixtureJSON } from '../helpers/fixtures.js'

const hx = (a: number[]) => Buffer.from(a).toString('hex')

describe('B2b-2 — singleAncestorPieces vs canonical sx golden settleTx2', () => {
  it('reproduces all 26 ancestor pieces byte-for-byte', () => {
    const golden = readFixtureJSON('MinSimpleDiscountBolt.ancestor.golden.json')
    const txs = golden.txs.map((t: any) => Transaction.fromHex(t.hex))
    const byId = new Map(txs.map((t: any) => [t.id('hex'), t]))
    for (const tx of txs) for (const inp of tx.inputs) { const s = byId.get(inp.sourceTXID); if (s) inp.sourceTransaction = s }
    const c1 = txs[1] // ancestor commit
    const s2 = txs[4] // settleTx2 — reaches back to c1
    const pieces = singleAncestorPieces(c1, 1) // discount = 1 leading value push
    const goldChunks = s2.inputs[0].unlockingScript!.chunks
    for (let i = 0; i < 26; i++) {
      const gold = goldChunks[i].data ? hx(goldChunks[i].data as number[]) : ''
      expect(hx(pieces[i]), `ancestor piece [${i}]`).toBe(gold)
    }
  })
})
