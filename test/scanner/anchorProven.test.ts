// HEADER-PROVEN ANCHORS, AND THE FUNGIBLE TOKEN.
//
//   1. A header-proven anchor (a merkle path into a block header the caller knows) was validated by consensus:
//      its own inputs are not re-executed and its sources need not be supplied. That is what makes a proven anchor
//      deliverable as BEEF, which stops at proven txs.
//   2. SimpleMultiBOLT: the same rules. MultiBOLTs REQUIRE funding and change, so an unfunded MultiBOLT tx is
//      outside the protocol (a settle never has to rebuild an unfunded commit); the scanner refuses one offered as
//      an anchor all the same.
import { describe, it, expect } from 'vitest'
import { Hash, MerklePath, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import {
  buildChain, verifyChain, spendToken, p2pb, proven, UNFUNDED, issuerPub, aPkh, attackerKey, ZERO20, ZERO36, type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent, verifyAndBroadcast } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef, fromBeef } from '../../src/lib/scanner/beef.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const id = (t: Transaction) => t.id('hex')
const ALL_UNFUNDED = { commit1: UNFUNDED, settle1: UNFUNDED, commit2: UNFUNDED, settle2: UNFUNDED }
/** A single-tx "block" at `height` whose merkle root is the txid. The harness's funding root already sits at
 *  height 1, and one BEEF cannot carry two different roots for the same height, so anchors go at height 2. */
const provenAt = <T extends Transaction>(tx: T, height: number): T => {
  tx.merklePath = new MerklePath(height, [[{ offset: 0, hash: id(tx), txid: true }]])
  return tx
}
/** The caller's block headers: exactly the blocks of these (proven) txs. */
const headersFor = (...txs: Transaction[]) => (root: string, height: number) =>
  txs.some((t) => id(t) === root && t.merklePath?.blockHeight === height)
const beef = (t: Transaction) => Uint8Array.from(toAtomicBeef(t))

/** stranger's mint naming the victim issuer -> FORGED commit1 -> settle1 -> commit2 -> settle2, each hop funded. */
async function forgedChain(fam: Family): Promise<Transaction[]> {
  const funding = proven(new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }]))
  const mint = new Transaction(); mint.version = 2
  mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  mint.addOutput({ satoshis: 1, lockingScript: fam.lock(aPkh, ZERO20, [0x00], ZERO36, ZERO36) })
  for (let k = 0; k < 4; k++) mint.addOutput({ satoshis: 500, lockingScript: new P2PKH().lock(aPkh) })
  await mint.sign()
  const txs = [mint]
  const op = (t: number, v: number) => buildOutpoint(txs[t], v)
  const base = { fam, txs, actor: attackerKey, beneficiary: aPkh, change: false, fundKey: attackerKey }
  const fund = () => ({ tx: 0, vout: txs.length })
  txs.push(await spendToken({ ...base, fund: fund(), from: { tx: 0, vout: 0 }, outputs: [fam.lock(aPkh, aPkh, [0x21], op(0, 0), ZERO36), p2pb(aPkh)] }))
  txs.push(await spendToken({ ...base, fund: fund(), from: { tx: 1, vout: 0 }, outputs: [fam.lock(aPkh, ZERO20, [0x00], op(1, 0), op(0, 0))] }))
  txs.push(await spendToken({ ...base, fund: fund(), from: { tx: 2, vout: 0 }, outputs: [fam.lock(aPkh, aPkh, [0x21], op(2, 0), op(1, 0)), p2pb(aPkh)] }))
  txs.push(await spendToken({
    ...base, fund: fund(), from: { tx: 3, vout: 0 }, proof: { src: { tx: 1, vout: 1 }, key: attackerKey },
    outputs: [fam.lock(aPkh, ZERO20, [0x00], op(3, 0), op(2, 0))],
  }))
  return txs
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: a header-proven anchor delivered as BEEF`, () => {
    for (const [label, spec] of [['funded anchor', {}], ['unfunded anchor', ALL_UNFUNDED]] as const) {
      it(`${label}: the BEEF stops at the proven anchor (its own sources are NOT in the package)`, async () => {
        const txs = await buildChain(fam, spec, 5)
        provenAt(txs[2], 2)
        const commit2 = fromBeef(beef(txs[3]))
        const anchor = commit2.inputs[0].sourceTransaction!
        expect(id(anchor)).toBe(id(txs[2]))
        expect(anchor.merklePath).toBeDefined()
        expect(anchor.inputs[0].sourceTransaction).toBeUndefined() // commit1 did not travel
      })

      it(`${label}: [beef(c2), beef(s2)] is ACCEPTED when the header is known`, async () => {
        const txs = await buildChain(fam, spec, 5)
        provenAt(txs[2], 2)
        // settle2 also spends commit1's proof output, so commit1 rides in settle2's BEEF as a plain source
        const r = verifyEvents([beef(txs[3]), beef(txs[4])], { trustedIssuerPubKey: issuerPub, isKnownBlockRoot: headersFor(txs[2]) })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
        expect(r.events).toEqual([{ kind: 'transfer', txids: [id(txs[3]), id(txs[4])] }])
      })

      it(`${label}: the anchor sent as its own BEEF next to the events is accepted too`, async () => {
        const txs = await buildChain(fam, spec, 5)
        provenAt(txs[2], 2)
        const r = verifyEvents([beef(txs[2]), beef(txs[3]), beef(txs[4])], { isKnownBlockRoot: headersFor(txs[2]) })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([{ txid: id(txs[2]), kind: 'settle' }])
      })

      it(`${label}: REFUSED when the header is NOT known (the anchor is then unproven and its sources are missing)`, async () => {
        const txs = await buildChain(fam, spec, 5)
        provenAt(txs[2], 2)
        for (const opts of [{}, { isKnownBlockRoot: () => false }]) {
          const r = verifyEvents([beef(txs[3]), beef(txs[4])], opts)
          expect(r.ok).toBe(false)
          expect(r.reason).toMatch(/token input @0 \(got external\)/)
        }
      })

      it(`${label}: verifyAndBroadcast with a chainTracker accepts the BEEF package and broadcasts the anchor`, async () => {
        const txs = await buildChain(fam, spec, 5)
        provenAt(txs[2], 2)
        const asked: string[] = []
        const sent: string[] = []
        const r = await verifyAndBroadcast([beef(txs[3]), beef(txs[4])], async (tx) => { sent.push(id(tx)); return { status: 'already-seen' } }, {
          chainTracker: { isValidRootForHeight: async (root, height) => { asked.push(`${height}:${root}`); return headersFor(txs[2])(root, height) } },
        })
        expect(r.ok, r.reason).toBe(true)
        expect(asked).toContain(`2:${id(txs[2])}`)
        expect(sent).toEqual([id(txs[2])])
      })

      it(`${label}: verifyAndBroadcast with a tracker that does not know the header refuses, nothing broadcast`, async () => {
        const txs = await buildChain(fam, spec, 5)
        provenAt(txs[2], 2)
        const sent: string[] = []
        const r = await verifyAndBroadcast([beef(txs[3]), beef(txs[4])], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } }, {
          chainTracker: { isValidRootForHeight: async () => false },
        })
        expect(r.ok).toBe(false)
        expect(sent).toEqual([])
      })
    }

    it('a header-proven MINT anchor as BEEF: its funding source is not needed', async () => {
      const txs = await buildChain(fam, {}, 3)
      txs[0].inputs[0].sourceTransaction!.merklePath = undefined // the funding root is no longer the proven tx...
      proven(txs[0])                                             // ...the mint itself is
      const r = verifyEvents([beef(txs[1]), beef(txs[2])], { isKnownBlockRoot: headersFor(txs[0]) })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([{ txid: id(txs[0]), kind: 'mint' }])
    })

    it('verifyEvent accepts the same BEEF package', async () => {
      const txs = await buildChain(fam, {}, 5)
      provenAt(txs[2], 2)
      const r = verifyEvent([beef(txs[3]), beef(txs[4])], { isKnownBlockRoot: headersFor(txs[2]) })
      expect(r.ok, r.reason).toBe(true)
      expect(r.kind).toBe('transfer')
    })
  })

  describe(`${type}: a header-proven anchor is not re-executed (the header lookup is trusted)`, () => {
    it('with sources attached and NO header knowledge, the forged history is refused on execution', async () => {
      const txs = await forgedChain(fam)
      expect(verifyChain([txs[2]]).ok).toBe(false)
      const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/script execution failed/)
    })

    it('a merkle path alone does not switch execution off: unknown header, still refused on execution', async () => {
      const txs = await forgedChain(fam)
      provenAt(txs[2], 2) // a fabricated single-tx "block"
      for (const opts of [{}, { isKnownBlockRoot: () => false }]) {
        const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub, ...opts })
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(/script execution failed/)
      }
    })

    it('if the caller VOUCHES for the header, the anchor is taken as mined: the lookup must be real headers', async () => {
      const txs = await forgedChain(fam)
      provenAt(txs[2], 2)
      const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub, isKnownBlockRoot: () => true })
      expect(r.ok).toBe(true) // pinned: isKnownBlockRoot is the trust root for a header-proven anchor
    })

    it('only ANCHORS are exempt: a header-"proven" EVENT tx is still executed', async () => {
      const txs = await forgedChain(fam)
      provenAt(txs[1], 2); provenAt(txs[2], 3) // the forged commit1 and settle1, as events of the batch
      const r = verifyEvents(txs, { isKnownBlockRoot: () => true })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/script execution failed/)
    })
  })
}

// ---------------------------------------------------------------- SimpleMultiBOLT
const T = 'SimpleMultiBOLT' as const
const smbKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const child = (n: string) => smbKey.deriveChild(smbKey.toPublicKey(), n)
const pkhOf = (k: PrivateKey) => Hash.hash160(k.toPublicKey().encode(true) as number[])
const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
const srcFor = (k: PrivateKey) => new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(pkhOf(k)) }])

/** mint -> transfer 1 -> transfer 2 (funded by a fresh source). Returns [mint, c1, s1, c2, s2]. */
async function smbChain(): Promise<Transaction[]> {
  const t = await new SimpleMultiBOLT().mint(smbKey, srcFor(smbKey), '', bal(1000n))
  await t.transfer(child('1'))
  await t.commit(child('2'), '', false, {
    sourceTransaction: srcFor(child('1')), sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(child('1')), sequence: 0xffffffff,
  } as any)
  await t.settle(child('2'))
  return t.prevTxs
}

/** OUT OF PROTOCOL (MultiBOLTs require funding and change): mint -> a force-unfunded transfer (s1 has the token
 *  input only), then an unfunded MELT of s1 by its owner. Used only to show the scanner refuses such an anchor. */
async function smbUnfundedAnchorAndMelt(): Promise<{ s1: Transaction; melt: Transaction }> {
  const t = await new SimpleMultiBOLT().mint(smbKey, srcFor(smbKey), '', bal(1000n))
  await t.transfer(child('1'), '', '', false, true, undefined, true)
  const s1 = t.tx!
  const melt = new Transaction(2, [{
    sourceTransaction: s1, sourceOutputIndex: 0, unlockingScriptTemplate: new SimpleMultiTemplate().melt(child('1')), sequence: 0xffffffff,
  }], [{ satoshis: s1.outputs[0].satoshis as number, lockingScript: new P2PKH().lock(pkhOf(child('1'))) }])
  await melt.sign()
  return { s1, melt }
}

describe('SimpleMultiBOLT: unfunded and zero-fee anchors', () => {
  it('forceNoFund yields an out-of-protocol unfunded transfer', async () => {
    const { s1 } = await smbUnfundedAnchorAndMelt()
    expect(s1.inputs).toHaveLength(1) // the token input only
  })

  it('MultiBOLTs require funding and change: a settle is never asked to rebuild an unfunded commit, and the builder refuses to', async () => {
    const t = await new SimpleMultiBOLT().mint(smbKey, srcFor(smbKey), '', bal(1000n))
    await t.transfer(child('1'), '', '', false, true, undefined, true)
    await t.commit(child('2'), '', false, {
      sourceTransaction: srcFor(child('1')), sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(child('1')), sequence: 0xffffffff,
    } as any)
    await expect(t.settle(child('2'))).rejects.toThrow()
  })

  it('a FUNDED anchor is accepted', async () => {
    const [, , s1, c2, s2] = await smbChain()
    const r = verifyEvents([s1, c2, s2], { expectedType: T })
    expect(r.ok, r.reason).toBe(true)
    expect(r.anchors).toEqual([{ txid: id(s1), kind: 'settle' }])
  })

  it('an out-of-protocol UNFUNDED anchor is REFUSED without an SPV proof', async () => {
    const { s1, melt } = await smbUnfundedAnchorAndMelt()
    expect(verifyChain([melt]).ok).toBe(true) // the melt itself is a clean owner spend
    for (const batch of [[s1, melt], [melt]]) {
      const r = verifyEvents(batch, { expectedType: T })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unfunded anchor [0-9a-f]{8}: it pays no fee.*accepted only with an SPV proof/)
    }
  })

  it('an UNFUNDED anchor with a merkle path into a known header is accepted', async () => {
    const { s1, melt } = await smbUnfundedAnchorAndMelt()
    proven(s1)
    const r = verifyEvents([s1, melt], { expectedType: T, isKnownBlockRoot: headersFor(s1) })
    expect(r.ok, r.reason).toBe(true)
    expect(r.anchors).toEqual([{ txid: id(s1), kind: 'settle' }])
    expect(verifyEvents([s1, melt], { expectedType: T }).ok).toBe(false)                              // no headers
    expect(verifyEvents([s1, melt], { expectedType: T, isKnownBlockRoot: () => false }).ok).toBe(false) // unknown header
  })

  it('verifyAndBroadcast refuses the unfunded anchor and broadcasts nothing', async () => {
    const { s1, melt } = await smbUnfundedAnchorAndMelt()
    const sent: string[] = []
    const r = await verifyAndBroadcast([s1, melt], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } }, { expectedType: T })
    expect(r.ok).toBe(false)
    expect(sent).toEqual([])
  })
})
