// AN UNFUNDED ANCHOR. An anchor must be a tx the network has seen and will therefore mine. An unfunded tx (no
// funding input, so no fee) gives the network no reason to mine it, so being seen proves nothing. It CAN be mined
// (a friendly miner), so the scanner accepts an unfunded anchor only when it already has been: it must carry a
// merkle path into a block header the caller knows (ScanOpts.isKnownBlockRoot, or a chainTracker handed to
// verifyAndBroadcast). The EVENTS standing on an anchor may be unfunded: they stay off chain until someone funds
// and broadcasts them.
import { describe, it, expect } from 'vitest'
import { MerklePath, Transaction } from '@bsv/sdk'
import { buildChain, meltToken, proven, UNFUNDED, userKey, issuerPub } from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent, verifyAndBroadcast } from '../../src/lib/scanner/verifyEvents.js'

const id = (t: Transaction) => t.id('hex')
const ALL_UNFUNDED = { commit1: UNFUNDED, settle1: UNFUNDED, commit2: UNFUNDED, settle2: UNFUNDED }
const UNFUNDED_EVENTS = { commit2: UNFUNDED, settle2: UNFUNDED } // a FUNDED anchor s1 under unfunded events
const NEEDS_PROOF = /unfunded anchor [0-9a-f]{8}: it pays no fee.*accepted only with an SPV proof \(a merkle path\) to a known block header/
/** `proven(tx)` gives a single-tx-block merkle path at height 1, whose root is the txid itself. */
const headerFor = (tx: Transaction) => (root: string, height: number) => root === id(tx) && height === 1
const accept = async () => ({ status: 'accepted' as const })

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: an unfunded anchor with no SPV proof is refused`, () => {
    it('the anchor s1 really is unfunded (one input, no funding) and executes clean', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      expect(txs[2].inputs).toHaveLength(1)
      expect(txs[2].merklePath).toBeUndefined()
    })

    it('[s1, c2, s2] and [c2, s2] are refused by verifyEvents', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      for (const batch of [[txs[2], txs[3], txs[4]], [txs[3], txs[4]]]) {
        const r = verifyEvents(batch, { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(NEEDS_PROOF)
        expect(r.reason).toContain(id(txs[2]).slice(0, 8))
      }
    })

    it('verifyEvent refuses it the same way', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      const r = verifyEvent([txs[3], txs[4]])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(NEEDS_PROOF)
    })

    it('a melt standing on an unfunded anchor is refused', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      for (const batch of [[txs[2], melt], [melt]]) {
        const r = verifyEvents(batch)
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(NEEDS_PROOF)
      }
    })

    it('verifyAndBroadcast refuses it and broadcasts NOTHING: the network seeing an unfunded tx proves nothing', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      const sent: string[] = []
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(NEEDS_PROOF)
      expect(sent).toEqual([])
    })

    it('a funded settle1 whose COMMIT was unfunded is a funded anchor (only the anchor itself counts)', async () => {
      const txs = await buildChain(fam, { commit1: UNFUNDED, settle1: { fund: { tx: 0, vout: 2 }, change: true } }, 5)
      expect(txs[1].inputs).toHaveLength(1)
      expect(txs[2].inputs).toHaveLength(2)
      const r = verifyEvents([txs[2], txs[3], txs[4]])
      expect(r.ok, r.reason).toBe(true)
    })
  })

  describe(`${type}: unfunded EVENTS on a funded anchor are fine`, () => {
    it('[s1, c2, s2] with c2 and s2 unfunded: accepted, no headers needed', async () => {
      const txs = await buildChain(fam, UNFUNDED_EVENTS, 5)
      expect(txs[2].inputs).toHaveLength(2) // the anchor is funded
      expect(txs[3].inputs).toHaveLength(1) // the events are not
      let consulted = 0
      const r = verifyEvents([txs[2], txs[3], txs[4]], { isKnownBlockRoot: () => { consulted++; return false } })
      expect(r.ok, r.reason).toBe(true)
      expect(consulted).toBe(0) // a funded anchor never consults the headers
    })

    it('an unfunded genesis event [mint, c1, s1] stands on the MINT, which is always funded', async () => {
      const txs = await buildChain(fam, { commit1: UNFUNDED, settle1: UNFUNDED }, 3)
      const r = verifyEvents(txs, { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([{ txid: id(txs[0]), kind: 'mint' }])
    })

    it('an unfunded melt on a funded anchor is accepted', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      expect(melt.inputs).toHaveLength(1)
      expect(verifyEvents([txs[2], melt]).ok).toBe(true)
    })
  })

  describe(`${type}: an unfunded anchor WITH an SPV proof to a known block header is accepted`, () => {
    it('merkle path + a header the caller knows: accepted, and the header lookup sees the root and height', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      const asked: [string, number][] = []
      const r = verifyEvents([txs[2], txs[3], txs[4]], {
        trustedIssuerPubKey: issuerPub,
        isKnownBlockRoot: (root, height) => { asked.push([root, height]); return headerFor(txs[2])(root, height) },
      })
      expect(r.ok, r.reason).toBe(true)
      expect(asked).toEqual([[id(txs[2]), 1]])
      expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
    })

    it('the same through verifyEvent, and for a melt on the proven anchor', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      const opts = { isKnownBlockRoot: headerFor(txs[2]) }
      expect(verifyEvent([txs[3], txs[4]], opts).ok).toBe(true)
      const short = await buildChain(fam, ALL_UNFUNDED, 3)
      proven(short[2])
      const melt = await meltToken({ fam, txs: short, from: { tx: 2, vout: 0 }, actor: userKey })
      expect(verifyEvents([melt], { isKnownBlockRoot: headerFor(short[2]) }).ok).toBe(true)
    })

    it('REFUSED: a merkle path but NO headers supplied (a merkle path alone proves nothing)', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      const r = verifyEvents([txs[2], txs[3], txs[4]])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unfunded anchor [0-9a-f]{8}: it carries a merkle path, but no block headers were supplied/)
    })

    it('REFUSED: the merkle root is not a header the caller knows', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      const r = verifyEvents([txs[2], txs[3], txs[4]], { isKnownBlockRoot: () => false })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unfunded anchor [0-9a-f]{8}: its merkle root is not a known block header at height 1/)
    })

    it('REFUSED: the right root at the WRONG height', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      const r = verifyEvents([txs[2], txs[3], txs[4]], { isKnownBlockRoot: (root, height) => root === id(txs[2]) && height === 2 })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/not a known block header at height 1/)
    })

    it('REFUSED (fail closed): a header lookup that throws, or answers something other than true', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      for (const isKnownBlockRoot of [() => { throw new Error('headers offline') }, () => 'yes' as any, () => 1 as any]) {
        const r = verifyEvents([txs[2], txs[3], txs[4]], { isKnownBlockRoot })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/not a known block header/)
      }
    })

    it('REFUSED: a merkle path that proves a DIFFERENT tx', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      // the path of some other tx, attached to the anchor; every header "known", so only the path can refuse it
      txs[2].merklePath = new MerklePath(1, [[{ offset: 0, hash: id(txs[0]), txid: true }]])
      const r = verifyEvents([txs[2], txs[3], txs[4]], { isKnownBlockRoot: () => true })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unfunded anchor [0-9a-f]{8}: its merkle path does not prove it/)
    })
  })

  describe(`${type}: verifyAndBroadcast with a chainTracker (async block headers)`, () => {
    it('the tracker confirms the root: accepted, then the anchor is broadcast', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      const asked: [string, number][] = []
      const sent: string[] = []
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], async (tx) => { sent.push(id(tx)); return { status: 'already-seen' } }, {
        chainTracker: { isValidRootForHeight: async (root, height) => { asked.push([root, height]); return true } },
      })
      expect(r.ok, r.reason).toBe(true)
      expect(asked).toEqual([[id(txs[2]), 1]])
      expect(sent).toEqual([id(txs[2])])
      expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle', status: 'already-seen' }])
    })

    it('REFUSED when the tracker does not know the root, or throws; nothing is broadcast', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      for (const isValidRootForHeight of [async () => false, async () => { throw new Error('tracker down') }]) {
        const sent: string[] = []
        const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } }, { chainTracker: { isValidRootForHeight } })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/unfunded anchor [0-9a-f]{8}: its merkle root is not a known block header at height 1/)
        expect(sent).toEqual([])
      }
    })

    it('a tracker does not rescue an unfunded anchor that has NO merkle path', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      let asked = 0
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], accept, { chainTracker: { isValidRootForHeight: async () => { asked++; return true } } })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(NEEDS_PROOF)
      expect(asked).toBe(0)
    })

    it('a sync isKnownBlockRoot takes precedence over the tracker', async () => {
      const txs = await buildChain(fam, ALL_UNFUNDED, 5)
      proven(txs[2])
      let asked = 0
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], accept, {
        isKnownBlockRoot: headerFor(txs[2]),
        chainTracker: { isValidRootForHeight: async () => { asked++; return false } },
      })
      expect(r.ok, r.reason).toBe(true)
      expect(asked).toBe(0)
    })

    it('a FUNDED anchor never consults the tracker', async () => {
      const txs = await buildChain(fam, {}, 5)
      let asked = 0
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], accept, { chainTracker: { isValidRootForHeight: async () => { asked++; return false } } })
      expect(r.ok, r.reason).toBe(true)
      expect(asked).toBe(0)
    })
  })
}
