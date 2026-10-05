// THE ANCHOR: the token tx a batch stands on - settle N-1, or the mint when the batch starts at genesis. What
// travels p2p is [mint, c1, s1] or [sN-1, cN, sN]. verifyEvents validates the anchor like an event tx (golden
// fingerprint, issuer, arrangement, sources, script execution) and names it in `anchors`; the CALLER broadcasts it
// (verifyAndBroadcast), so the network is seen to accept (or already know) the tx the batch is built on.
//
// The case this closes: a stranger mints naming the victim's issuer key and signs commit1 themselves (refused by
// the issuer guard), then builds settle1 -> commit2 -> settle2 on top. commit2 and settle2 execute clean on their
// own, so [commit2, settle2] used to return ok: true. settle1 (the anchor) does NOT execute clean.
import { describe, it, expect } from 'vitest'
import { P2PKH, Transaction } from '@bsv/sdk'
import {
  buildChain, verifyChain, spendToken, p2pb, proven, UNFUNDED, issuerPub, aPkh, attackerKey, ZERO20, ZERO36, toHex,
  type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import {
  verifyEvents, verifyAndBroadcast, type AnchorBroadcaster, type AnchorBroadcastResult,
} from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef } from '../../src/lib/scanner/beef.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

// An anchor must be FUNDED (or SPV-proven, see anchorUnfunded.test.ts); the EVENTS standing on it may be unfunded.
const UNFUNDED_EVENTS = { commit2: UNFUNDED, settle2: UNFUNDED }

/** stranger's mint (naming the victim issuer) -> FORGED commit1 -> settle1 -> commit2 -> settle2, all unfunded. */
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

/** A broadcaster that records what it was sent and answers with `answer`. */
const recorder = (answer: AnchorBroadcastResult | (() => never)) => {
  const sent: string[] = []
  const broadcast: AnchorBroadcaster = async (tx) => {
    sent.push(tx.id('hex'))
    if (typeof answer === 'function') return answer()
    return answer
  }
  return { sent, broadcast }
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: verifyEvents validates the anchor`, () => {
    for (const [label, spec] of [['funded', {}], ['unfunded events', UNFUNDED_EVENTS]] as const) {
      it(`[s1, c2, s2] (${label}): s1 is the anchor, not an orphan settle and not an event`, async () => {
        const txs = await buildChain(fam, spec, 5)
        const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([{ txid: txs[2].id('hex'), kind: 'settle' }])
        expect(r.events).toEqual([{ kind: 'transfer', txids: [txs[3].id('hex'), txs[4].id('hex')] }])
      })

      it(`[c2, s2] (${label}) with s1 only attached: s1 is pulled in as the anchor`, async () => {
        const txs = await buildChain(fam, spec, 5)
        const r = verifyEvents([txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([{ txid: txs[2].id('hex'), kind: 'settle' }])
        expect(r.events).toEqual([{ kind: 'transfer', txids: [txs[3].id('hex'), txs[4].id('hex')] }])
      })

      it(`[mint, c1, s1] (${label}): the mint is the anchor`, async () => {
        const txs = await buildChain(fam, spec, 3)
        const r = verifyEvents(txs, { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([{ txid: txs[0].id('hex'), kind: 'mint' }])
      })

      it(`[c1, s1] (${label}) with the mint only attached: the mint is the anchor but not an event`, async () => {
        const txs = await buildChain(fam, spec, 3)
        const r = verifyEvents([txs[1], txs[2]], { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([{ txid: txs[0].id('hex'), kind: 'mint' }])
        expect(r.events).toEqual([{ kind: 'transfer', txids: [txs[1].id('hex'), txs[2].id('hex')] }])
      })
    }

    it('the whole chain in one batch has ONE anchor: the mint (s1 is paired, so it is an event)', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvents(txs, { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([{ txid: txs[0].id('hex'), kind: 'mint' }])
    })

    it('a settle nothing in the batch spends is still an orphan settle', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvents([txs[2]])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/orphan settle/)
    })

    it('an anchor settle sent as bare hex (its own commit not supplied) is refused', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvents([txs[2].toHex(), txs[3].toHex(), txs[4].toHex()])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/token input @0 \(got external\)/)
    })

    it('an anchor with a tampered unlock is refused on execution', async () => {
      const txs = await buildChain(fam, {}, 5)
      const anchor = txs[2]
      const chunks = [...anchor.inputs[0].unlockingScript!.chunks]
      const i = chunks.findIndex((c) => c.data?.length === 33) // the owner pubkey push
      chunks[i] = { ...chunks[i], data: chunks[i].data!.map((b, k) => (k === 5 ? b ^ 1 : b)) }
      const { UnlockingScript } = await import('@bsv/sdk')
      anchor.inputs[0].unlockingScript = new UnlockingScript(chunks)
      const r = verifyEvents([anchor, txs[3], txs[4]])
      expect(r.ok).toBe(false)
    })

    describe('the forged history (stranger-signed commit1 behind an honest-looking last pair)', () => {
      it('commit2 and settle2 execute clean on their own; commit1 is where the chain breaks', async () => {
        const txs = await forgedChain(fam)
        expect(verifyChain(txs).failedTx).toBe(1)
        expect(verifyChain([txs[3], txs[4]]).ok).toBe(true)
      })

      it('[s1, c2, s2] is REFUSED: the anchor s1 fails script execution', async () => {
        const txs = await forgedChain(fam)
        const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`script execution failed: tx ${txs[2].id('hex').slice(0, 8)} input 0`))
      })

      it('[c2, s2] with s1 only attached is REFUSED the same way', async () => {
        const txs = await forgedChain(fam)
        const r = verifyEvents([txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`script execution failed: tx ${txs[2].id('hex').slice(0, 8)} input 0`))
      })

      it('[c2, s2] as Atomic BEEF is REFUSED the same way (the anchor rides inside the BEEF)', async () => {
        const txs = await forgedChain(fam)
        const beefs = [txs[3], txs[4]].map((t) => Uint8Array.from(toAtomicBeef(t)))
        const r = verifyEvents(beefs, { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/script execution failed/)
      })

      it('verifyAndBroadcast refuses it and broadcasts NOTHING', async () => {
        const txs = await forgedChain(fam)
        const { sent, broadcast } = recorder({ status: 'accepted' })
        const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], broadcast, { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(sent).toEqual([])
      })
    })
  })

  describe(`${type}: verifyAndBroadcast = verifyEvents + the caller's anchor broadcast`, () => {
    for (const status of ['accepted', 'already-seen'] as const) {
      it(`ok when the network answers "${status}" for the anchor, and the anchor is what was broadcast`, async () => {
        const txs = await buildChain(fam, {}, 5)
        const { sent, broadcast } = recorder({ status })
        const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], broadcast, { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(sent).toEqual([txs[2].id('hex')])
        expect(r.anchors).toEqual([{ txid: txs[2].id('hex'), kind: 'settle', status }])
        expect(r.events).toEqual([{ kind: 'transfer', txids: [txs[3].id('hex'), txs[4].id('hex')] }])
        expect(r.issuerPubKeyHex).toBe(toHex(issuerPub))
      })
    }

    it('a genesis batch broadcasts the mint', async () => {
      const txs = await buildChain(fam, {}, 3)
      const { sent, broadcast } = recorder({ status: 'already-seen' })
      const r = await verifyAndBroadcast(txs, broadcast)
      expect(r.ok, r.reason).toBe(true)
      expect(sent).toEqual([txs[0].id('hex')])
      expect(r.anchors).toEqual([{ txid: txs[0].id('hex'), kind: 'mint', status: 'already-seen' }])
    })

    it('the broadcaster receives the anchor with its sources attached', async () => {
      const txs = await buildChain(fam, {}, 5)
      let got: Transaction | undefined
      await verifyAndBroadcast([txs[3], txs[4]], async (tx) => { got = tx; return { status: 'accepted' } }) // s1 only attached
      expect(got!.id('hex')).toBe(txs[2].id('hex'))
      expect(got!.inputs[0].sourceTransaction!.id('hex')).toBe(txs[1].id('hex'))
    })

    it('REFUSED when the network rejects the anchor, with the node detail in the reason', async () => {
      const txs = await buildChain(fam, {}, 5)
      const { broadcast } = recorder({ status: 'rejected', detail: 'missing inputs' })
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], broadcast)
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/anchor settle [0-9a-f]{8} was not accepted by the network: missing inputs/)
      expect(r.anchors).toEqual([{ txid: txs[2].id('hex'), kind: 'settle', status: 'rejected', detail: 'missing inputs' }])
      expect(r.events).toBeUndefined()
    })

    it('REFUSED (fail closed) when the broadcaster throws', async () => {
      const txs = await buildChain(fam, {}, 5)
      const { broadcast } = recorder(() => { throw new Error('network down') })
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], broadcast)
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/broadcast failed: network down/)
      expect(r.anchors![0].status).toBe('rejected')
    })

    it('REFUSED (fail closed) on an unknown status or an empty answer', async () => {
      const txs = await buildChain(fam, {}, 5)
      for (const answer of [{ status: 'maybe' }, undefined] as any[]) {
        const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], async () => answer)
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/unknown broadcast status/)
      }
    })

    it('REFUSED without a broadcaster', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], undefined as any)
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/anchor broadcaster is required/)
    })

    it('an offline failure is returned as-is and nothing is broadcast', async () => {
      const txs = await buildChain(fam, {}, 5)
      const { sent, broadcast } = recorder({ status: 'accepted' })
      const r = await verifyAndBroadcast([txs[3]], broadcast) // an unsettled commit
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unsettled commit/)
      expect(sent).toEqual([])
    })
  })
}
