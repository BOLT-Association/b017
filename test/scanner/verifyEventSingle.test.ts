// verifyEvent takes its VERDICT from the same scan as verifyEvents, so the two entry points cannot disagree.
// Before: verifyEvent returned { ok: true, kind: "mint" } for a lone commit, a lone settle and two unrelated
// settles, and had no anchor step, so a forged history behind the event passed. An event is exactly ONE action
// (commit + settle, or a melt); its anchor and the mint it authenticates may ride along.
import { describe, it, expect } from 'vitest'
import { P2PKH, Transaction, UnlockingScript } from '@bsv/sdk'
import {
  buildChain, spendToken, meltToken, p2pb, proven, UNFUNDED, userKey, issuerPub, aPkh, attackerKey, ZERO20, ZERO36,
  type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvent, verifyEvents } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef } from '../../src/lib/scanner/beef.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const id = (t: Transaction) => t.id('hex')
// An anchor must be FUNDED (or SPV-proven, see anchorUnfunded.test.ts); the EVENTS standing on it may be unfunded.
const UNFUNDED_EVENTS = { commit2: UNFUNDED, settle2: UNFUNDED }

/** stranger's mint naming the victim issuer -> FORGED commit1 -> settle1 -> commit2 -> settle2 (all unfunded). */
async function forgedChain(fam: Family): Promise<Transaction[]> {
  const funding = proven(new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }]))
  const mint = new Transaction(); mint.version = 2
  mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  mint.addOutput({ satoshis: 1, lockingScript: fam.lock(aPkh, ZERO20, [0x00], ZERO36, ZERO36) })
  await mint.sign()
  const txs = [mint]
  const op = (t: number, v: number) => buildOutpoint(txs[t], v)
  const base = { fam, txs, actor: attackerKey, beneficiary: aPkh, fund: null, change: false }
  txs.push(await spendToken({ ...base, from: { tx: 0, vout: 0 }, outputs: [fam.lock(aPkh, aPkh, [0x21], op(0, 0), ZERO36), p2pb(aPkh)] }))
  txs.push(await spendToken({ ...base, from: { tx: 1, vout: 0 }, outputs: [fam.lock(aPkh, ZERO20, [0x00], op(1, 0), op(0, 0))] }))
  txs.push(await spendToken({ ...base, from: { tx: 2, vout: 0 }, outputs: [fam.lock(aPkh, aPkh, [0x21], op(2, 0), op(1, 0)), p2pb(aPkh)] }))
  txs.push(await spendToken({
    ...base, from: { tx: 3, vout: 0 }, proof: { src: { tx: 1, vout: 1 }, key: attackerKey },
    outputs: [fam.lock(aPkh, ZERO20, [0x00], op(3, 0), op(2, 0))],
  }))
  return txs
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: verifyEvent accepts exactly one event and names its anchor`, () => {
    for (const [label, spec] of [['funded', {}], ['unfunded events', UNFUNDED_EVENTS]] as const) {
      it(`[c2, s2] (${label}): a transfer standing on the anchor s1`, async () => {
        const txs = await buildChain(fam, spec, 5)
        const r = verifyEvent([txs[3], txs[4]])
        expect(r.ok, r.reason).toBe(true)
        expect(r.kind).toBe('transfer')
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
      })

      it(`[s1, c2, s2] (${label}): the anchor may ride along in the event`, async () => {
        const txs = await buildChain(fam, spec, 5)
        const r = verifyEvent([txs[2], txs[3], txs[4]])
        expect(r.ok, r.reason).toBe(true)
        expect(r.kind).toBe('transfer')
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
      })

      it(`[mint, c1, s1] (${label}): the mint rides with the commit that authenticates it; the event is the transfer`, async () => {
        const txs = await buildChain(fam, spec, 3)
        const r = verifyEvent(txs)
        expect(r.ok, r.reason).toBe(true)
        expect(r.kind).toBe('transfer')
        expect(r.anchors).toEqual([{ txid: id(txs[0]), kind: 'mint' }])
      })
    }

    it('a melt is one event, standing on the settle it spends', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      for (const event of [[melt], [txs[2], melt]]) {
        const r = verifyEvent(event)
        expect(r.ok, r.reason).toBe(true)
        expect(r.kind).toBe('melt')
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
      }
    })

    it('agrees with verifyEvents on the same txs', async () => {
      const txs = await buildChain(fam, {}, 5)
      const one = verifyEvent([txs[3], txs[4]])
      const batch = verifyEvents([txs[3], txs[4]])
      expect(one.ok).toBe(batch.ok)
      expect(one.kind).toBe(batch.events![0].kind)
      expect(one.anchors).toEqual(batch.anchors)
      expect(one.sources).toEqual(batch.sources)
    })
  })

  describe(`${type}: verifyEvent refuses what is not one whole event`, () => {
    it('a LONE COMMIT is refused (it used to return ok: true, kind "mint")', async () => {
      const txs = await buildChain(fam, {}, 5)
      for (const commit of [txs[1], txs[3]]) {
        const r = verifyEvent([commit])
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/unsettled commit/)
      }
    })

    it('a LONE SETTLE is refused (it used to return ok: true, kind "mint")', async () => {
      const txs = await buildChain(fam, {}, 5)
      for (const settle of [txs[2], txs[4]]) {
        const r = verifyEvent([settle])
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/orphan settle/)
      }
    })

    it('two settles with no commit are refused', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvent([txs[2], txs[4]])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/orphan settle/)
    })

    it('[mint, c1] without the settle is refused: the commit is unsettled', async () => {
      const txs = await buildChain(fam, {}, 2)
      const r = verifyEvent(txs)
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unsettled commit/)
    })

    it('TWO events are refused: verifyEvent is for one', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvent(txs) // mint, c1, s1, c2, s2 = two transfers
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/expected exactly one event, got 2/)
      expect(verifyEvents(txs).ok).toBe(true) // the batch verifier takes it
    })

    it('a commit paired with a settle of ANOTHER commit is refused', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvent([txs[1], txs[4]]) // commit1 with settle2
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/settle\.parent does not link to the commit token/)
    })

    it('the FORGED history is refused: the anchor s1 fails script execution', async () => {
      const txs = await forgedChain(fam)
      for (const event of [[txs[3], txs[4]], [txs[2], txs[3], txs[4]], [txs[3], txs[4]].map((t) => Uint8Array.from(toAtomicBeef(t)))]) {
        const r = verifyEvent(event, { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`script execution failed: tx ${id(txs[2]).slice(0, 8)} input 0`))
      }
    })

    it('trustedIssuerPubKey is honoured (it used to be ignored by verifyEvent)', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvent([txs[3], txs[4]], { trustedIssuerPubKey: '02' + '11'.repeat(32) })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/issuerPubKey != trusted issuer/)
    })

    it('an input pointing past its source outputs returns ok: false instead of throwing', () => {
      const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }])
      const tx = new Transaction(2, [{ sourceTransaction: funding, sourceOutputIndex: 5, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff }],
        [{ satoshis: 1, lockingScript: new P2PKH().lock(aPkh) }])
      let r: ReturnType<typeof verifyEvent> | undefined
      expect(() => { r = verifyEvent([tx]) }).not.toThrow()
      expect(r!.ok).toBe(false)
      expect(r!.reason).toMatch(/no BOLT token recognised/)
    })
  })
}
