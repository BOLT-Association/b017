// MELT for the NFT family (MinSimpleBOLT zero-funding, AuthBOLT): `template.melt(key)` is an owner spend with a
// null CTX and no token output. Two layers:
//   1. the covenant's melt branch, executed on the @bsv/sdk Spend engine (who may melt, funded and unfunded);
//   2. the scanner: a melt is an EVENT that stands on an anchor (the settle it spends); it is never an anchor.
// The Spend engine is not a node: these are script-level verdicts.
import { describe, it, expect } from 'vitest'
import { P2PKH, Transaction } from '@bsv/sdk'
import {
  buildChain, verifyChain, spendToken, meltToken, p2pb, proven, UNFUNDED, issuerKey, userKey, bucketKey, attackerKey,
  issuerPub, aPkh, uPkh, ZERO20, ZERO36, type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyAndBroadcast } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef } from '../../src/lib/scanner/beef.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const id = (t: Transaction) => t.id('hex')
const run = (tx: Transaction) => verifyChain([tx]).ok
const ALL_UNFUNDED = { commit1: UNFUNDED, settle1: UNFUNDED, commit2: UNFUNDED, settle2: UNFUNDED }

/** stranger's mint naming the victim issuer -> FORGED commit1 -> settle1 (all unfunded, all attacker-owned). */
async function forgedToSettle1(fam: Family): Promise<Transaction[]> {
  const funding = proven(new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }]))
  const mint = new Transaction(); mint.version = 2
  mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  mint.addOutput({ satoshis: 1, lockingScript: fam.lock(aPkh, ZERO20, [0x00], ZERO36, ZERO36) })
  await mint.sign()
  const txs = [mint]
  const base = { fam, txs, actor: attackerKey, beneficiary: aPkh, fund: null, change: false }
  txs.push(await spendToken({ ...base, from: { tx: 0, vout: 0 }, outputs: [fam.lock(aPkh, aPkh, [0x21], buildOutpoint(mint, 0), ZERO36), p2pb(aPkh)] }))
  txs.push(await spendToken({ ...base, from: { tx: 1, vout: 0 }, outputs: [fam.lock(aPkh, ZERO20, [0x00], buildOutpoint(txs[1], 0), buildOutpoint(mint, 0))] }))
  return txs
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: the melt branch on the Spend engine`, () => {
    it('the owner melts a settled token, UNFUNDED (one input, one p2pkh output)', async () => {
      const txs = await buildChain(fam, {}, 3) // settle1: owner = user
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      expect(melt.inputs).toHaveLength(1)
      expect(melt.outputs).toHaveLength(1)
      expect(run(melt)).toBe(true)
    })

    it('the owner melts a settled token, FUNDED (the funding input is a plain p2pkh spend)', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey, fund: { tx: 2, vout: 1 } })
      expect(melt.inputs).toHaveLength(2)
      expect(run(melt)).toBe(true)
    })

    it('the owner melts after a second hop (settle2: owner = bucket), funded and unfunded chains', async () => {
      for (const spec of [{}, ALL_UNFUNDED]) {
        const txs = await buildChain(fam, spec, 5)
        expect(run(await meltToken({ fam, txs, from: { tx: 4, vout: 0 }, actor: bucketKey }))).toBe(true)
      }
    })

    it('a key that is NOT the owner cannot melt', async () => {
      const txs = await buildChain(fam, {}, 3)
      for (const actor of [attackerKey, issuerKey, bucketKey])
        expect(run(await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor }))).toBe(false)
    })

    it('a melt whose signature no longer covers its outputs is refused', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      melt.outputs[0].lockingScript = new P2PKH().lock(aPkh) // redirect the payout after signing
      expect(run(melt)).toBe(false)
    })

    it('the ISSUER melts its own genesis mint; a stranger who owns a mint naming the issuer cannot', async () => {
      const honest = await buildChain(fam, {}, 1) // mint: owner = issuer = the named issuerPubKey
      expect(run(await meltToken({ fam, txs: honest, from: { tx: 0, vout: 0 }, actor: issuerKey }))).toBe(true)
      const forged = await forgedToSettle1(fam) // forged[0]: owner = the stranger, issuerPubKey = the victim's
      expect(run(await meltToken({ fam, txs: forged, from: { tx: 0, vout: 0 }, actor: attackerKey }))).toBe(false)
    })
  })

  describe(`${type}: a melt in the scanner stands on its anchor`, () => {
    // the anchor s1 is funded in both; an UNFUNDED anchor is refused without an SPV proof (anchorUnfunded.test.ts)
    for (const [label, spec, fund] of [['funded melt', {}, { tx: 2, vout: 1 }], ['unfunded melt', {}, null]] as const) {
      it(`[s1, melt] (${label}): s1 is the anchor, the melt is the event`, async () => {
        const txs = await buildChain(fam, spec, 3)
        const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey, fund })
        const r = verifyEvents([txs[2], melt], { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.type).toBe(type)
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
        expect(r.events).toEqual([{ kind: 'melt', txids: [id(melt)] }])
      })

      it(`[melt] alone (${label}) with s1 only attached: the anchor is pulled in and the type read off it`, async () => {
        const txs = await buildChain(fam, spec, 3)
        const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey, fund })
        const r = verifyEvents([melt], { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.type).toBe(type)
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
        expect(r.events).toEqual([{ kind: 'melt', txids: [id(melt)] }])
      })
    }

    it('[c2, s2, melt]: a transfer then a melt of its result; s1 is the only anchor (s2 is paired)', async () => {
      const txs = await buildChain(fam, {}, 5)
      const melt = await meltToken({ fam, txs, from: { tx: 4, vout: 0 }, actor: bucketKey })
      const r = verifyEvents([txs[3], txs[4], melt], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
      expect(r.events).toEqual([{ kind: 'transfer', txids: [id(txs[3]), id(txs[4])] }, { kind: 'melt', txids: [id(melt)] }])
    })

    it('genesis to melt in one batch: the mint is the only anchor', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const r = verifyEvents([...txs, melt], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([{ txid: id(txs[0]), kind: 'mint' }])
    })

    it('as Atomic BEEF: the anchor rides inside the melt BEEF', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const r = verifyEvents([Uint8Array.from(toAtomicBeef(melt))], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
    })

    it('verifyAndBroadcast broadcasts the anchor under the melt, never the melt', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const sent: string[] = []
      const r = await verifyAndBroadcast([melt], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } })
      expect(r.ok, r.reason).toBe(true)
      expect(sent).toEqual([id(txs[2])])
    })

    it('REFUSED: a melt by the wrong key fails script execution on the melt', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: attackerKey })
      const r = verifyEvents([txs[2], melt])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(new RegExp(`script execution failed: tx ${id(melt).slice(0, 8)} input 0`))
    })

    it('REFUSED: a melt sent as bare hex, its anchor not supplied', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const r = verifyEvents([melt.toHex()])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/no BOLT token output recognised/)
    })

    it('REFUSED: a melt of a token still in a COMMIT state (its anchor is not a settled token)', async () => {
      const txs = await buildChain(fam, {}, 2) // commit1: owner = issuer, mid-protocol
      const melt = await meltToken({ fam, txs, from: { tx: 1, vout: 0 }, actor: issuerKey })
      for (const batch of [[melt], [txs[1], melt]]) {
        const r = verifyEvents(batch)
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/is not a settled token or a mint \(it is a commit\)|unsettled commit/)
      }
    })

    it('REFUSED: a melt of a bare mint (only a commit authenticates a mint)', async () => {
      const txs = await buildChain(fam, {}, 1)
      const melt = await meltToken({ fam, txs, from: { tx: 0, vout: 0 }, actor: issuerKey })
      for (const batch of [[txs[0], melt], [melt]]) {
        const r = verifyEvents(batch)
        expect(r.ok).toBe(false)
        expect(r.unauthenticated).toBe(true)
      }
    })

    it('REFUSED: a melt standing on a FORGED history - the anchor s1 fails script execution', async () => {
      const txs = await forgedToSettle1(fam)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: attackerKey })
      expect(run(melt)).toBe(true) // the melt itself is a clean owner spend
      for (const batch of [[txs[2], melt], [melt]]) {
        const r = verifyEvents(batch, { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`script execution failed: tx ${id(txs[2]).slice(0, 8)} input 0`))
      }
    })

    it('a melt is never an anchor: nothing can stand on it', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      // a commit-shaped tx "spending" the melt's p2pkh output as if it were a token
      const x = new Transaction(2, [{ sourceTransaction: melt, sourceOutputIndex: 0, unlockingScript: new P2PKH().lock(uPkh) as any, sequence: 0xffffffff }],
        [{ satoshis: 1, lockingScript: fam.lock(uPkh, aPkh, [0x21], buildOutpoint(melt, 0), ZERO36) }, { satoshis: 1, lockingScript: p2pb(aPkh) }])
      const r = verifyEvents([txs[2], melt, x])
      expect(r.ok).toBe(false)
    })
  })
}
