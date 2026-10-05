// VALUE CONSERVATION. The scanner checks that a tx's outputs do not exceed its inputs.
//
//   - An EVENT tx that creates value is REPORTED (`offChainOnly`), not refused: an off-chain commit / settle that is
//     never broadcast (AuthBOLT events certifying auth data) executes fine and is valid between the parties; it just
//     cannot be broadcast as built. `requireBroadcastable: true` turns the report into a refusal.
//   - An ANCHOR that creates value is REFUSED: an anchor must be a tx the network will mine, and no node accepts a
//     tx that creates value. (A header-proven anchor was validated by consensus and is not re-checked.)
//
// The harness's UNFUNDED commit is exactly such an event: a 1 sat token in, a 1 sat token + a 1 sat proof out.
import { describe, it, expect } from 'vitest'
import { MerklePath, P2PKH, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import {
  buildChain, verifyChain, meltToken, UNFUNDED, issuerKey, userKey, issuerPub, iPkh, uPkh, ZERO20, type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent, verifyAndBroadcast } from '../../src/lib/scanner/verifyEvents.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const id = (t: Transaction) => t.id('hex')
const UNFUNDED_EVENTS = { commit2: UNFUNDED, settle2: UNFUNDED } // a funded anchor s1 under unfunded events
const accept = async () => ({ status: 'accepted' as const })

/** mint -> commit1 -> a FUNDED settle1 whose change output pays out MORE than the tx takes in. */
async function chainWithInflatingSettle(fam: Family): Promise<Transaction[]> {
  const txs = await buildChain(fam, {}, 2)
  const s1 = new Transaction(); s1.version = 2
  s1.addInput({ sourceTransaction: txs[1], sourceOutputIndex: 0, unlockingScriptTemplate: fam.unlock(issuerKey, uPkh, txs), sequence: 0xffffffff })
  s1.addInput({ sourceTransaction: txs[0], sourceOutputIndex: 2, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
  s1.addOutput({ satoshis: 1, lockingScript: fam.lock(uPkh, ZERO20, [0x00], buildOutpoint(txs[1], 0), buildOutpoint(txs[0], 0)) })
  s1.addOutput({ satoshis: 5000, lockingScript: new P2PKH().lock(iPkh) }) // inputs: 1 + 1000 sat; outputs: 5001 sat
  await s1.sign()
  return [...txs, s1]
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: an EVENT tx that creates value is reported, not refused`, () => {
    it('a fully funded batch conserves value: nothing is reported', async () => {
      const txs = await buildChain(fam, {}, 5)
      for (const batch of [txs, [txs[2], txs[3], txs[4]]]) {
        const r = verifyEvents(batch, { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.offChainOnly).toBeUndefined()
      }
    })

    it('an unfunded commit (1 sat in, 2 sat out) is accepted and listed in offChainOnly', async () => {
      const txs = await buildChain(fam, UNFUNDED_EVENTS, 5)
      const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      // commit2 creates value; settle2 (the token + the proof in, one token out) does not
      expect(r.offChainOnly).toEqual([{ txid: id(txs[3]), inputSats: 1, outputSats: 2 }])
      expect(r.events).toEqual([{ kind: 'transfer', txids: [id(txs[3]), id(txs[4])] }])
    })

    it('an unfunded genesis event on a funded mint is accepted and reported the same way', async () => {
      const txs = await buildChain(fam, { commit1: UNFUNDED, settle1: UNFUNDED }, 3)
      const r = verifyEvents(txs, { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.offChainOnly).toEqual([{ txid: id(txs[1]), inputSats: 1, outputSats: 2 }])
    })

    it('verifyEvent and verifyAndBroadcast report it too', async () => {
      const txs = await buildChain(fam, UNFUNDED_EVENTS, 5)
      const want = [{ txid: id(txs[3]), inputSats: 1, outputSats: 2 }]
      const one = verifyEvent([txs[3], txs[4]])
      expect(one.ok, one.reason).toBe(true)
      expect(one.offChainOnly).toEqual(want)
      const sent = await verifyAndBroadcast([txs[2], txs[3], txs[4]], accept)
      expect(sent.ok, sent.reason).toBe(true)
      expect(sent.offChainOnly).toEqual(want)
    })

    it('an unfunded melt (1 sat in, 1 sat out) conserves value and is not reported', async () => {
      const txs = await buildChain(fam, {}, 3)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const r = verifyEvents([txs[2], melt])
      expect(r.ok, r.reason).toBe(true)
      expect(r.offChainOnly).toBeUndefined()
    })

    it('requireBroadcastable: true REFUSES the batch, names the tx, and still returns the report', async () => {
      const txs = await buildChain(fam, UNFUNDED_EVENTS, 5)
      const batch = [txs[2], txs[3], txs[4]]
      const sent: string[] = []
      const results = [
        verifyEvents(batch, { requireBroadcastable: true }),
        verifyEvent(batch, { requireBroadcastable: true }),
        await verifyAndBroadcast(batch, async (tx) => { sent.push(id(tx)); return { status: 'accepted' } }, { requireBroadcastable: true }),
      ]
      for (const r of results) {
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`tx ${id(txs[3]).slice(0, 8)} creates value \\(inputs 1 sat, outputs 2 sat\\): it cannot be broadcast as built`))
        expect(r.offChainOnly).toEqual([{ txid: id(txs[3]), inputSats: 1, outputSats: 2 }])
      }
      expect(sent).toEqual([])
    })

    it('requireBroadcastable: true accepts a batch that conserves value', async () => {
      const txs = await buildChain(fam, {}, 5)
      expect(verifyEvents([txs[2], txs[3], txs[4]], { requireBroadcastable: true }).ok).toBe(true)
    })
  })

  describe(`${type}: an ANCHOR that creates value is refused`, () => {
    it('the inflating settle executes clean on the Spend engine (scripts do not see amounts across inputs)', async () => {
      const txs = await chainWithInflatingSettle(fam)
      expect(verifyChain([txs[2]]).ok).toBe(true)
    })

    it('as an EVENT it is only reported', async () => {
      const txs = await chainWithInflatingSettle(fam)
      const r = verifyEvents(txs)
      expect(r.ok, r.reason).toBe(true)
      expect(r.offChainOnly).toEqual([{ txid: id(txs[2]), inputSats: 1001, outputSats: 5001 }])
    })

    it('as the ANCHOR of a later event it is REFUSED, by all three entry points', async () => {
      const txs = await chainWithInflatingSettle(fam)
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const sent: string[] = []
      const results = [
        verifyEvents([txs[2], melt]),
        verifyEvents([melt]),
        verifyEvent([melt]),
        await verifyAndBroadcast([txs[2], melt], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } }),
      ]
      for (const r of results) {
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`anchor ${id(txs[2]).slice(0, 8)} creates value \\(inputs 1001 sat, outputs 5001 sat\\): the network will never accept it`))
      }
      expect(sent).toEqual([])
    })

    it('a header-proven anchor is not re-checked: consensus validated it', async () => {
      const txs = await chainWithInflatingSettle(fam)
      txs[2].merklePath = new MerklePath(2, [[{ offset: 0, hash: id(txs[2]), txid: true }]])
      const melt = await meltToken({ fam, txs, from: { tx: 2, vout: 0 }, actor: userKey })
      const r = verifyEvents([txs[2], melt], { isKnownBlockRoot: (root, height) => root === id(txs[2]) && height === 2 })
      expect(r.ok, r.reason).toBe(true) // the header lookup is the trust root
    })
  })
}

describe('SimpleMultiBOLT: funded with change, so its txs conserve value', () => {
  it('a transfer chain built by the library reports nothing', async () => {
    const { Hash, PrivateKey } = await import('@bsv/sdk')
    const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
    const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
    const src = new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(key.toPublicKey().encode(true) as number[])) }])
    const t = await new SimpleMultiBOLT().mint(key, src, '', bal(1000n))
    await t.transfer(key.deriveChild(key.toPublicKey(), '1'))
    const r = verifyEvents(t.prevTxs, { expectedType: 'SimpleMultiBOLT', requireBroadcastable: true })
    expect(r.ok, r.reason).toBe(true)
    expect(r.offChainOnly).toBeUndefined()
  })
})
