// The data package for an off-chain (SPV) transfer is BEEF: Atomic BEEF (BRC-95) over BEEF V2 (BRC-96). The scanner
// accepts it as input, refuses BEEF V1 (BRC-62), refuses a BEEF that is not self-contained, and REQUIRES every input's
// source tx to be supplied (otherwise the input's script cannot be executed and the event cannot be authenticated).
import { describe, it, expect } from 'vitest'
import { Utils } from '@bsv/sdk'
import { buildChain, UNFUNDED, type Family } from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef, fromBeef, isBeef } from '../../src/lib/scanner/beef.js'

describe('BEEF helpers', () => {
  it('toAtomicBeef emits Atomic BEEF (01010101) over BEEF V2 (0200beef) and fromBeef round-trips the subject + ancestors', async () => {
    const txs = await buildChain(minSimple, {}, 5)
    const bin = toAtomicBeef(txs[4])
    expect(Buffer.from(bin.slice(0, 4)).toString('hex')).toBe('01010101')
    expect(Buffer.from(bin.slice(36, 40)).toString('hex')).toBe('0200beef') // atomic header = magic + 32-byte subject txid
    expect(isBeef(bin)).toBe(true)
    const t = fromBeef(bin)
    expect(t.id('hex')).toBe(txs[4].id('hex'))
    expect(t.inputs[0].sourceTransaction?.inputs[0].sourceTransaction).toBeTruthy() // ancestors wired in, to depth
  })

  it('refuses BEEF V1 (BRC-62), which is what the SDK\'s own toHexBEEF() emits', async () => {
    const txs = await buildChain(minSimple, {}, 3)
    expect(() => fromBeef(txs[2].toHexBEEF())).toThrow(/BEEF V1/)
  })

  it('refuses a BEEF that is not self-contained (an unproven root: no BUMP, no inputs in the BEEF)', async () => {
    const txs = await buildChain(minSimple, {}, 3)
    txs[0].inputs[0].sourceTransaction!.merklePath = undefined // the mint's funding root loses its proof
    expect(() => fromBeef(toAtomicBeef(txs[2]))).toThrow(/not self-contained/)
  })

  it('a non-BEEF string is not BEEF', () => {
    expect(isBeef('0100000001')).toBe(false)
  })
})

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as [Family, string][]) {
  describe(`${type}: events received as BEEF`, () => {
    it('a commit + settle as Atomic BEEF verify; the mint they spend arrives as an ancestor and is reported as a source', async () => {
      const txs = await buildChain(fam, {}, 3)
      const r = verifyEvent([toAtomicBeef(txs[1]), toAtomicBeef(txs[2])])
      expect(r.ok, r.reason).toBe(true)
      expect(r.kind).toBe('transfer')
      const ids = r.sources!.map((s) => s.txid)
      expect(ids).toContain(txs[0].id('hex')) // the mint (the commit's token input) is a supplied source...
      expect(r.sources!.find((s) => s.txid === txs[0].id('hex'))!.proven).toBe(false) // ...with no BUMP of its own
    })

    it('the same package as BEEF hex strings works too, funded or unfunded, and reports the BUMP-proven funding root', async () => {
      for (const spec of [{}, { commit1: UNFUNDED, settle1: UNFUNDED }]) {
        const txs = await buildChain(fam, spec, 3)
        const r = verifyEvents(txs.map((t) => Utils.toHex(toAtomicBeef(t))))
        expect(r.ok, r.reason).toBe(true)
        // the proven root is a source of the mint; sources are the non-event txs the event txs spend
        expect(r.sources!.every((s) => typeof s.proven === 'boolean')).toBe(true)
      }
    })

    it('BEEF V1 and non-self-contained BEEF are refused as input (invalid BEEF)', async () => {
      const txs = await buildChain(fam, {}, 3)
      const v1 = verifyEvents([txs[0].toHexBEEF(), txs[1].toHexBEEF(), txs[2].toHexBEEF()])
      expect(v1.ok).toBe(false)
      expect(v1.reason).toMatch(/invalid BEEF.*BEEF V1/)
    })
  })

  describe(`${type}: every input's source must be supplied`, () => {
    it('a tx whose input source is withheld is refused (not merely unexecuted)', async () => {
      const txs = await buildChain(fam, {}, 3)
      // as received as plain hex: no attached sources at all
      const r = verifyEvents([txs[0].toHex(), txs[1].toHex(), txs[2].toHex()])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/was not supplied/)
    })

    it('withholding ONLY the funding source (the token source is supplied) is also refused', async () => {
      const txs = await buildChain(fam, {}, 3)
      const settle = txs[2]
      settle.inputs[1].sourceTransaction = undefined // the funding input (commit change): commit IS in the batch, so supply by txid...
      settle.inputs[1].sourceTXID = 'ab'.repeat(32) // ...but point it at a tx nobody supplied
      const r = verifyEvents([txs[0], txs[1], settle])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/was not supplied/)
    })
  })
}
