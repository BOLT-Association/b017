// The anchor across every event shape, and the refusals around it. See anchor.test.ts for the definition.
//
//   - SimpleMultiBOLT: transfer / split / spending either piece of a split / merge (TWO anchors) / melt.
//   - An anchor is a settle N-1 or a mint whose token output is SPENT BY a commit or a melt of the batch; it is never
//     a melt (a melt has no token output) and never a token still in a commit state.
//   - BEEF, mismatched sources, a foreign issuer behind the anchor, several anchors through the broadcaster.
//   - THE LIMIT, pinned: offline execution reaches the anchor's own inputs only. A forgery two events back is
//     accepted offline and is caught by the anchor BROADCAST alone.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, UnlockingScript } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import {
  buildChain, verifyChain, spendToken, p2pb, proven, issuerPub, aPkh, uPkh, userKey, attackerKey, ZERO20, ZERO36,
  type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyAndBroadcast, type AnchorStatus } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef } from '../../src/lib/scanner/beef.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const id = (t: Transaction) => t.id('hex')
const settleAnchor = (t: Transaction) => ({ txid: id(t), kind: 'settle' })
const mintAnchor = (t: Transaction) => ({ txid: id(t), kind: 'mint' })
const byTxid = (a: { txid: string }, b: { txid: string }) => a.txid.localeCompare(b.txid)

// ---------------------------------------------------------------- SimpleMultiBOLT (fungible) shapes
const MASK64 = (1n << 64n) - 1n
const bal = (amount: bigint): number[] => {
  const b = Buffer.alloc(16)
  b.writeBigUInt64LE(amount & MASK64, 0)
  b.writeBigUInt64LE((amount >> 64n) & MASK64, 8)
  return Array.from(b)
}
const smbKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const smbIssuerHex = Buffer.from(smbKey.toPublicKey().encode(true) as number[]).toString('hex')
const otherIssuerKey = PrivateKey.fromString('00000000000000000000000000000000000000000000000000000000000000a5', 'hex')
const child = (n: string) => smbKey.deriveChild(smbKey.toPublicKey(), n)
const srcFor = (k: PrivateKey) =>
  new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(k.toPublicKey().encode(true) as number[])) }])
const T = 'SimpleMultiBOLT' as const
/** mint + one transfer: prevTxs = [mint, c1, s1]. Distinct `amount`s give distinct txids. */
const settled = async (amount: bigint, to = '1', key = smbKey) => {
  const t = await new SimpleMultiBOLT().mint(key, srcFor(key), '', bal(amount))
  return t.transfer(key === smbKey ? child(to) : key.deriveChild(key.toPublicKey(), to))
}

describe('SimpleMultiBOLT: the anchor across every event shape', () => {
  it('transfer: [s1, c2, s2] and [c2, s2] both stand on the anchor s1', async () => {
    const t = await (await settled(1000n)).transfer(child('2'))
    const [, , s1, c2, s2] = t.prevTxs
    for (const batch of [[s1, c2, s2], [c2, s2]]) {
      const r = verifyEvents(batch, { expectedType: T })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([settleAnchor(s1)])
      expect(r.events).toEqual([{ kind: 'transfer', txids: [id(c2), id(s2)] }])
    }
  })

  it('split: the split commit stands on the anchor s1', async () => {
    const [main] = await (await settled(1000n)).split(child('10'), child('11'), bal(1n))
    const [, , s1, splitC, splitS] = main.prevTxs
    for (const batch of [[s1, splitC, splitS], [splitC, splitS]]) {
      const r = verifyEvents(batch, { expectedType: T })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([settleAnchor(s1)])
      expect(r.events).toEqual([{ kind: 'split', txids: [id(splitC), id(splitS)] }])
    }
  })

  it('a split settle (two token outputs) is the anchor for a spend of EITHER piece', async () => {
    for (const piece of [0, 1]) {
      const pieces = await (await settled(1000n)).split(child('10'), child('11'), bal(1n))
      const splitS = pieces[0].tx!
      const moved = pieces[piece]
      if (piece === 0) await moved.transfer(child('20'))
      else {
        // the split settle's change pays piece A, so piece B brings its own funding
        const fundB = new Transaction(1, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(Hash.hash160(child('11').toPublicKey().encode(true) as number[])) }])
        await moved.commit(child('20'), '', false, {
          sourceTransaction: fundB, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(child('11')), sequence: 0xffffffff,
        } as any)
        await moved.settle(child('20'))
      }
      const c = moved.prevTxs[moved.prevTxs.length - 2], s = moved.prevTxs[moved.prevTxs.length - 1]
      expect(c.inputs[0].sourceOutputIndex).toBe(piece)
      for (const batch of [[splitS, c, s], [c, s]]) {
        const r = verifyEvents(batch, { expectedType: T })
        expect(r.ok, r.reason).toBe(true)
        expect(r.anchors).toEqual([settleAnchor(splitS)])
        expect(r.events).toEqual([{ kind: 'transfer', txids: [id(c), id(s)] }])
      }
    }
  })

  it('merge: TWO anchors, one per merged token', async () => {
    const a = await settled(1000n, '1')
    const b = await settled(7n, '2')
    const sA = a.tx!, sB = b.tx!
    const merged = await a.merge(b, child('400'))
    const mergeC = merged.prevTxs[merged.prevTxs.length - 2], mergeS = merged.prevTxs[merged.prevTxs.length - 1]
    for (const batch of [[sA, sB, mergeC, mergeS], [mergeC, mergeS], [sB, mergeC, mergeS]]) {
      const r = verifyEvents(batch, { expectedType: T })
      expect(r.ok, r.reason).toBe(true)
      expect([...r.anchors!].sort(byTxid)).toEqual([settleAnchor(sA), settleAnchor(sB)].sort(byTxid))
      expect(r.events).toEqual([{ kind: 'merge', txids: [id(mergeC), id(mergeS)] }])
    }
  })

  it('melt: [sN-1, melt] stands on the anchor sN-1; the melt is the event, never the anchor', async () => {
    const t = await settled(1000n)
    const s1 = t.tx!
    const melt = (await t.melt()).tx!
    const r = verifyEvents([s1, melt], { expectedType: T })
    expect(r.ok, r.reason).toBe(true)
    expect(r.anchors).toEqual([settleAnchor(s1)])
    expect(r.events).toEqual([{ kind: 'melt', txids: [id(melt)] }])
  })

  it('melt: a lone [melt] with its anchor only attached pulls the anchor in (type read off the spent token)', async () => {
    const t = await settled(1000n)
    const s1 = t.tx!
    const melt = (await t.melt()).tx!
    for (const opts of [{ expectedType: T }, {}]) {
      const r = verifyEvents([melt], opts)
      expect(r.ok, r.reason).toBe(true)
      expect(r.type).toBe(T)
      expect(r.anchors).toEqual([settleAnchor(s1)])
      expect(r.events).toEqual([{ kind: 'melt', txids: [id(melt)] }])
    }
  })

  it('melt of a bare MINT is refused: the mint is unauthenticated (only a COMMIT authenticates a mint)', async () => {
    const t = await new SimpleMultiBOLT().mint(smbKey, srcFor(smbKey), '', bal(1000n))
    const mint = t.tx!
    const melt = (await t.melt()).tx!
    for (const batch of [[mint, melt], [melt]]) {
      const r = verifyEvents(batch, { expectedType: T })
      expect(r.ok).toBe(false)
      expect(r.unauthenticated).toBe(true)
    }
  })

  it('a melt whose anchor was not supplied at all is refused', async () => {
    const t = await settled(1000n)
    const melt = (await t.melt()).tx!
    const r = verifyEvents([melt.toHex()], { expectedType: T })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/no BOLT token output recognised/)
  })

  it('melt after merge: the merge settle is the anchor', async () => {
    const merged = await (await settled(1000n, '1')).merge(await settled(7n, '2'), child('400'))
    const mergeS = merged.tx!
    const melt = (await merged.melt()).tx!
    const r = verifyEvents([mergeS, melt], { expectedType: T })
    expect(r.ok, r.reason).toBe(true)
    expect(r.anchors).toEqual([settleAnchor(mergeS)])
  })

  it('two independent chains in one batch: two anchors, two events', async () => {
    const a = await (await settled(1000n)).transfer(child('2'))
    const b = await (await settled(7n)).transfer(child('3'))
    const [, , aS1, aC2, aS2] = a.prevTxs
    const [, , bS1, bC2, bS2] = b.prevTxs
    const r = verifyEvents([aS1, aC2, aS2, bS1, bC2, bS2], { expectedType: T, trustedIssuerPubKey: smbIssuerHex })
    expect(r.ok, r.reason).toBe(true)
    expect(r.anchors).toEqual([settleAnchor(aS1), settleAnchor(bS1)])
    expect(r.events).toHaveLength(2)
  })

  it('a full genesis-to-tip batch has the mint as its only anchor, whatever the events', async () => {
    const [main] = await (await settled(1000n)).split(child('10'), child('11'), bal(1n))
    const r = verifyEvents(main.prevTxs, { expectedType: T })
    expect(r.ok, r.reason).toBe(true)
    expect(r.anchors).toEqual([mintAnchor(main.prevTxs[0])])
  })

  it('an anchor from ANOTHER issuer behind the batch is refused (the issuer pin covers the anchor)', async () => {
    const honest = await (await settled(1000n)).transfer(child('2'))
    const [, , , c2] = honest.prevTxs
    const foreign = await settled(1000n, '1', otherIssuerKey) // same shape, minted by another issuer
    // a commit-shaped tx naming OUR issuer in its outputs, but spending the foreign issuer's settled token
    const x = new Transaction(2, [{ sourceTransaction: foreign.tx!, sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff }], c2.outputs)
    const r = verifyEvents([x], { expectedType: T, trustedIssuerPubKey: smbIssuerHex })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/inconsistent issuerPubKey/)
  })

  describe('verifyAndBroadcast with several anchors', () => {
    const run = async (answers: AnchorStatus[]) => {
      const a = await settled(1000n, '1')
      const b = await settled(7n, '2')
      const sA = a.tx!, sB = b.tx!
      const merged = await a.merge(b, child('400'))
      const batch = [sA, sB, ...merged.prevTxs.slice(-2)]
      const sent: string[] = []
      const r = await verifyAndBroadcast(batch, async (tx) => ({ status: answers[sent.push(id(tx)) - 1] }), { expectedType: T })
      return { r, sent, sA, sB }
    }

    it('every anchor is broadcast, in `anchors` order, and each status is recorded', async () => {
      const { r, sent, sA, sB } = await run(['accepted', 'already-seen'])
      expect(r.ok, r.reason).toBe(true)
      expect(sent).toEqual([id(sA), id(sB)])
      expect(r.anchors).toEqual([{ ...settleAnchor(sA), status: 'accepted' }, { ...settleAnchor(sB), status: 'already-seen' }])
    })

    it('ONE rejected anchor refuses the whole batch', async () => {
      const { r, sent, sA, sB } = await run(['accepted', 'rejected'])
      expect(r.ok).toBe(false)
      expect(sent).toEqual([id(sA), id(sB)])
      expect(r.reason).toMatch(new RegExp(`anchor settle ${id(sB).slice(0, 8)} was not accepted`))
      expect(r.anchors!.map((c) => c.status)).toEqual(['accepted', 'rejected'])
    })

    it('broadcasting stops at the first rejected anchor', async () => {
      const { r, sent, sA } = await run(['rejected', 'accepted'])
      expect(r.ok).toBe(false)
      expect(sent).toEqual([id(sA)])
      expect(r.anchors!.map((c) => c.status)).toEqual(['rejected'])
    })
  })

  it('verifyAndBroadcast broadcasts the anchor under a melt', async () => {
    const t = await settled(1000n)
    const s1 = t.tx!
    const melt = (await t.melt()).tx!
    const sent: string[] = []
    const r = await verifyAndBroadcast([melt], async (tx) => { sent.push(id(tx)); return { status: 'already-seen' } })
    expect(r.ok, r.reason).toBe(true)
    expect(sent).toEqual([id(s1)])
  })
})

// ---------------------------------------------------------------- NFT family: refusals, BEEF, and the limit
/** stranger's mint (naming the victim issuer) -> FORGED commit1 -> settle1 -> c2 -> s2 -> c3 -> s3. Every hop is
 *  FUNDED by the stranger (from the mint's spare outputs), so no anchor here is refused merely for being unfunded. */
async function forgedChain(fam: Family): Promise<Transaction[]> {
  const funding = proven(new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }]))
  const mint = new Transaction(); mint.version = 2
  mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  mint.addOutput({ satoshis: 1, lockingScript: fam.lock(aPkh, ZERO20, [0x00], ZERO36, ZERO36) })
  for (let k = 0; k < 6; k++) mint.addOutput({ satoshis: 500, lockingScript: new P2PKH().lock(aPkh) }) // one funding per hop
  await mint.sign()
  const txs = [mint]
  const op = (t: number, v: number) => buildOutpoint(txs[t], v)
  const base = { fam, txs, actor: attackerKey, beneficiary: aPkh, change: false, fundKey: attackerKey }
  const fund = () => ({ tx: 0, vout: txs.length }) // hop k spends the mint's k-th spare output
  const commit = async (from: number, gp: number[]) =>
    txs.push(await spendToken({ ...base, fund: fund(), from: { tx: from, vout: 0 }, outputs: [fam.lock(aPkh, aPkh, [0x21], op(from, 0), gp), p2pb(aPkh)] }))
  const settle = async (from: number, proofFrom?: number) =>
    txs.push(await spendToken({
      ...base, fund: fund(), from: { tx: from, vout: 0 }, ...(proofFrom === undefined ? {} : { proof: { src: { tx: proofFrom, vout: 1 }, key: attackerKey } }),
      outputs: [fam.lock(aPkh, ZERO20, [0x00], op(from, 0), op(from - 1, 0))],
    }))
  await commit(0, ZERO36)      // 1: FORGED (stranger-signed) commit1
  await settle(1)              // 2: settle1
  await commit(2, op(1, 0))    // 3: commit2
  await settle(3, 1)           // 4: settle2 (rebuilds commit1, spends its proof)
  await commit(4, op(3, 0))    // 5: commit3
  await settle(5, 3)           // 6: settle3 (rebuilds commit2, spends its proof)
  return txs
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: anchor refusals`, () => {
    it('an anchor still in a COMMIT state is refused (pulled in from a source)', async () => {
      const txs = await buildChain(fam, {}, 5)
      // commit-shaped tx spending commit1's token output (a token that was never settled)
      const x = new Transaction(2, [{ sourceTransaction: txs[1], sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff }], txs[3].outputs)
      const r = verifyEvents([x])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/is not a settled token or a mint \(it is a commit\)/)
    })

    it('an anchor still in a COMMIT state is refused (supplied in the batch)', async () => {
      const txs = await buildChain(fam, {}, 5)
      const x = new Transaction(2, [{ sourceTransaction: txs[1], sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff }], txs[3].outputs)
      const r = verifyEvents([txs[1], x])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/unsettled commit/)
    })

    it('an anchor with a tampered unlock is refused on script execution', async () => {
      const txs = await buildChain(fam, {}, 3)
      const anchor = txs[2]
      const chunks = [...anchor.inputs[0].unlockingScript!.chunks]
      const i = chunks.findIndex((c) => c.data?.length === 33) // the owner pubkey push
      chunks[i] = { ...chunks[i], data: chunks[i].data!.map((b, k) => (k === 5 ? b ^ 1 : b)) }
      anchor.inputs[0].unlockingScript = new UnlockingScript(chunks)
      // build the next event ON the tampered anchor (its txid changed), so the batch is otherwise self-consistent
      const next = [...txs]
      next.push(await spendToken({
        fam, txs: next, from: { tx: 2, vout: 0 }, actor: userKey, beneficiary: aPkh, fund: null, change: false,
        outputs: [fam.lock(uPkh, aPkh, [0x21], buildOutpoint(anchor, 0), buildOutpoint(txs[1], 0)), p2pb(aPkh)],
      }))
      next.push(await spendToken({
        fam, txs: next, from: { tx: 3, vout: 0 }, actor: userKey, beneficiary: aPkh, fund: null, change: false,
        proof: { src: { tx: 1, vout: 1 }, key: userKey },
        outputs: [fam.lock(aPkh, ZERO20, [0x00], buildOutpoint(next[3], 0), buildOutpoint(anchor, 0))],
      }))
      for (const batch of [[anchor, next[3], next[4]], [next[3], next[4]]]) {
        const r = verifyEvents(batch)
        expect(r.ok).toBe(false)
        expect(r.reason).toMatch(new RegExp(`script execution failed: tx ${anchor.id('hex').slice(0, 8)} input 0`))
      }
    })

    it('an attached source that is NOT the tx the outpoint names is refused', async () => {
      const txs = await buildChain(fam, {}, 5)
      const other = await buildChain(fam, { commit1: { fund: null, change: false }, settle1: { fund: null, change: false } }, 3)
      const c2 = Transaction.fromHex(txs[3].toHex()) // sourceTXID = the real s1
      c2.inputs.forEach((inp, k) => { inp.sourceTransaction = txs[3].inputs[k].sourceTransaction })
      c2.inputs[0].sourceTransaction = other[2] // a DIFFERENT settle1 swapped in behind the same outpoint
      expect(other[2].id('hex')).not.toBe(txs[2].id('hex'))
      const r = verifyEvents([c2, txs[4]])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/orphan settle|is not the tx its outpoint names/)
    })

    it('a swapped PROOF source (not a token input) is refused: the attached tx is not the one the outpoint names', async () => {
      const txs = await buildChain(fam, {}, 5)
      const other = await buildChain(fam, { commit1: { fund: null, change: false } }, 2) // a different commit1, same p2pb at vout 1
      expect(other[1].id('hex')).not.toBe(txs[1].id('hex'))
      const s2 = Transaction.fromHex(txs[4].toHex())
      s2.inputs.forEach((inp, k) => { inp.sourceTransaction = txs[4].inputs[k].sourceTransaction })
      s2.inputs[1].sourceTransaction = other[1]
      const r = verifyEvents([txs[2], txs[3], s2])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/is not the tx its outpoint names/)
    })

    it('BEEF: [beef(c2), beef(s2)] is accepted and the anchor inside the BEEF is named once', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvents([txs[3], txs[4]].map((t) => Uint8Array.from(toAtomicBeef(t))), { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([settleAnchor(txs[2])])
    })

    it('BEEF: the anchor sent as its own BEEF next to the events is still ONE anchor', async () => {
      const txs = await buildChain(fam, {}, 5)
      const r = verifyEvents([txs[2], txs[3], txs[4]].map((t) => Uint8Array.from(toAtomicBeef(t))), { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.anchors).toEqual([settleAnchor(txs[2])])
      expect(r.events).toEqual([{ kind: 'transfer', txids: [id(txs[3]), id(txs[4])] }])
    })

    it('verifyAndBroadcast with the mint only attached broadcasts the mint', async () => {
      const txs = await buildChain(fam, {}, 3)
      const sent: string[] = []
      const r = await verifyAndBroadcast([txs[1], txs[2]], async (tx) => { sent.push(id(tx)); return { status: 'accepted' } })
      expect(r.ok, r.reason).toBe(true)
      expect(sent).toEqual([id(txs[0])])
      expect(r.anchors).toEqual([{ ...mintAnchor(txs[0]), status: 'accepted' }])
    })
  })

  describe(`${type}: THE LIMIT - a forgery two events back is caught by the broadcast alone`, () => {
    it('the forged chain: commit1 and settle1 fail execution; everything after executes clean', async () => {
      const txs = await forgedChain(fam)
      expect(verifyChain(txs).failedTx).toBe(1)
      expect(verifyChain([txs[2]]).ok).toBe(false)
      expect(verifyChain(txs.slice(3)).ok).toBe(true)
    })

    it('one event back ([s1, c2, s2]): refused OFFLINE, the anchor s1 fails execution', async () => {
      const txs = await forgedChain(fam)
      const r = verifyEvents([txs[2], txs[3], txs[4]], { trustedIssuerPubKey: issuerPub })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/script execution failed/)
    })

    it('two events back ([s2, c3, s3]): ACCEPTED offline - the anchor s2 is valid on its own', async () => {
      const txs = await forgedChain(fam)
      const r = verifyEvents([txs[4], txs[5], txs[6]], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true) // the documented limit of the offline check
      expect(r.anchors).toEqual([settleAnchor(txs[4])])
    })

    it('two events back: REFUSED by verifyAndBroadcast when the network rejects the anchor', async () => {
      const txs = await forgedChain(fam)
      // a node cannot accept s2: its ancestor commit1 is invalid. Modelled by a rejecting broadcaster.
      const r = await verifyAndBroadcast([txs[4], txs[5], txs[6]], async () => ({ status: 'rejected', detail: 'missing inputs' }), { trustedIssuerPubKey: issuerPub })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/anchor settle [0-9a-f]{8} was not accepted by the network: missing inputs/)
    })
  })
}
