// Edges of the scanner and the BEEF package that the lifecycle suites never send:
//   - a Transaction OBJECT that cannot even be serialised (the scanner must refuse, never throw);
//   - inputs with no explicit sequence, raw txs as bytes;
//   - a split settle / merge commit that is missing its second token interface;
//   - verifyEvent refusing on a missing NON-token source;
//   - BEEF shapes: a missing source, a plain (non-Atomic) BEEF V2, an empty BEEF.
import { describe, it, expect } from 'vitest'
import { Beef, Hash, P2PKH, PrivateKey, Script, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { buildChain, issuerPub } from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent, verifyAndBroadcast } from '../../src/lib/scanner/verifyEvents.js'
import { toAtomicBeef, fromBeef, isBeef } from '../../src/lib/scanner/beef.js'

const id = (t: Transaction) => t.id('hex')
const BEEF_V2 = 4022206466
/** Re-parse a tx from its bytes (so every input carries sourceTXID) and re-attach the original sources. */
const clone = (t: Transaction): Transaction => {
  const c = Transaction.fromHex(t.toHex())
  c.inputs.forEach((inp, k) => { inp.sourceTransaction = t.inputs[k].sourceTransaction })
  return c
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: a Transaction object that cannot be serialised is refused, never thrown`, () => {
    const breakIt: [string, (c2: Transaction, s2: Transaction) => void][] = [
      ['an input with neither sourceTXID nor sourceTransaction', (c2) => { (c2.inputs[1] as any).sourceTXID = undefined; c2.inputs[1].sourceTransaction = undefined }],
      ['an input with no unlocking script', (c2) => { (c2.inputs[0] as any).unlockingScript = undefined }],
      ['an output with no locking script', (_c2, s2) => { (s2.outputs[0] as any).lockingScript = undefined }],
    ]
    for (const [label, mutate] of breakIt) {
      it(label, async () => {
        const txs = await buildChain(fam, {}, 5)
        const c2 = clone(txs[3]), s2 = clone(txs[4])
        mutate(c2, s2)
        const batch = [txs[2], c2, s2]
        const sent: string[] = []
        const results: { ok: boolean; reason?: string }[] = []
        expect(() => { results.push(verifyEvents(batch)) }).not.toThrow()
        expect(() => { results.push(verifyEvent(batch)) }).not.toThrow()
        results.push(await verifyAndBroadcast(batch, async (tx) => { sent.push(id(tx)); return { status: 'accepted' } }))
        for (const r of results) {
          expect(r.ok).toBe(false)
          expect(r.reason).toMatch(/^unverifiable input: /)
        }
        expect(sent).toEqual([])
      })
    }
  })

  describe(`${type}: input forms the lifecycle suites do not send`, () => {
    it('inputs with NO explicit sequence are final (0xffffffff): same txids, same verdict', async () => {
      const txs = await buildChain(fam, {}, 5)
      const c2 = clone(txs[3]), s2 = clone(txs[4])
      for (const tx of [c2, s2]) tx.inputs.forEach((inp) => { (inp as any).sequence = undefined })
      expect([id(c2), id(s2)]).toEqual([id(txs[3]), id(txs[4])])
      const r = verifyEvents([txs[2], c2, s2], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
    })

    it('raw (non-BEEF) txs as BYTES are parsed like raw hex', async () => {
      const txs = await buildChain(fam, {}, 3)
      const r = verifyEvents([txs[0], Uint8Array.from(txs[1].toBinary()), Uint8Array.from(txs[2].toBinary())], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
      expect(r.events).toContainEqual({ kind: 'transfer', txids: [id(txs[1]), id(txs[2])] })
    })

    it('verifyEvent refuses when a NON-token source is missing (the structure passes, the sources do not)', async () => {
      const txs = await buildChain(fam, {}, 5)
      const s2 = clone(txs[4])
      s2.inputs[1].sourceTransaction = undefined // the proof input: commit1 is neither attached nor in the event
      const r = verifyEvent([txs[3], s2])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(new RegExp(`source tx ${id(txs[1]).slice(0, 8)} of tx ${id(s2).slice(0, 8)} input 1 was not supplied`))
    })
  })

  describe(`${type}: BEEF shapes`, () => {
    it('a tx parsed from bytes (sourceTXID already set) with every source attached round-trips', async () => {
      const txs = await buildChain(fam, {}, 5)
      const back = fromBeef(toAtomicBeef(clone(txs[3])))
      expect(id(back)).toBe(id(txs[3]))
      expect(id(back.inputs[0].sourceTransaction!)).toBe(id(txs[2]))
    })

    it('inputs that name their source ONLY by the attached tx get their txid filled in for the BEEF', async () => {
      const txs = await buildChain(fam, {}, 5)
      const c2 = clone(txs[3])
      c2.inputs.forEach((inp) => { (inp as any).sourceTXID = undefined }) // attached sources only
      const back = fromBeef(toAtomicBeef(c2))
      expect(c2.inputs.every((inp) => typeof inp.sourceTXID === 'string')).toBe(true)
      expect(id(back)).toBe(id(txs[3]))
    })

    it('a source withheld from one input is restored when the BEEF reaches it another way', async () => {
      const txs = await buildChain(fam, {}, 5)
      const s2 = clone(txs[4])
      s2.inputs[1].sourceTransaction = undefined // commit1 (the proof source) is not attached to THIS input...
      const back = fromBeef(toAtomicBeef(s2))    // ...but commit2 -> settle1 -> commit1 carries it into the BEEF
      expect(back.inputs.map((i) => !!i.sourceTransaction)).toEqual([true, true, true])
      expect(id(back.inputs[1].sourceTransaction!)).toBe(id(txs[1]))
    })

    it('a tx whose ONLY route to a source is withheld still serialises, but the BEEF is not self-contained and is refused', async () => {
      const txs = await buildChain(fam, {}, 3)
      const mint = clone(txs[0])
      mint.inputs[0].sourceTransaction = undefined // the mint's funding root: nothing else in the graph reaches it
      const bytes = toAtomicBeef(mint)
      expect(isBeef(bytes)).toBe(true)
      expect(() => fromBeef(bytes)).toThrow(/not self-contained/)
      const r = verifyEvents([Uint8Array.from(bytes), txs[1], txs[2]])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/invalid BEEF: BEEF is not self-contained/)
    })

    it('a plain BEEF V2 (not Atomic) is accepted: its subject is the last tx', async () => {
      const txs = await buildChain(fam, {}, 5)
      const c2 = clone(txs[3])
      toAtomicBeef(c2) // fills sourceTXID across the attached graph, which the SDK orders the BEEF by
      const plain = new Beef(BEEF_V2)
      plain.mergeTransaction(c2)
      const bytes = plain.toBinary()
      expect(plain.atomicTxid).toBeUndefined()
      expect(id(fromBeef(bytes))).toBe(id(txs[3]))
      const r = verifyEvents([Uint8Array.from(bytes), Uint8Array.from(toAtomicBeef(txs[4]))], { trustedIssuerPubKey: issuerPub })
      expect(r.ok, r.reason).toBe(true)
    })

    it('an EMPTY BEEF has no subject and is refused', () => {
      const empty = new Beef(BEEF_V2).toBinary()
      expect(() => fromBeef(empty)).toThrow(/BEEF has no subject transaction/)
      const r = verifyEvents([Uint8Array.from(empty)])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/invalid BEEF: BEEF has no subject transaction/)
    })
  })
}

// ---------------------------------------------------------------- a missing SECOND token interface
describe('SimpleMultiBOLT: a split settle / merge commit missing its second token interface', () => {
  const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const child = (n: string) => key.deriveChild(key.toPublicKey(), n)
  const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
  const src = () => new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(key.toPublicKey().encode(true) as number[])) }])
  const settled = async (n: bigint, to: string) => (await new SimpleMultiBOLT().mint(key, src(), '', bal(n))).transfer(child(to))
  const out = (lock: Script) => ({ satoshis: 1, lockingScript: lock })
  const spending = (lock: Script): any =>
    ({ sourceTransaction: new Transaction(1, [], [out(lock)]), sourceOutputIndex: 0, unlockingScript: new Script([]), sequence: 0xffffffff })

  it('a split settle with only ONE output: the second token output is "none"', async () => {
    const [main] = await (await settled(1000n, '1')).split(child('10'), child('11'), bal(1n))
    const splitC = main.prevTxs[main.prevTxs.length - 2], splitS = main.prevTxs[main.prevTxs.length - 1]
    const tx = new Transaction(2, [spending(splitC.outputs[0].lockingScript)], [out(splitS.outputs[0].lockingScript)])
    const r = verifyEvent([tx], { expectedType: 'SimpleMultiBOLT' })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/settle [0-9a-f]{8}: token output @1 \(got none\)/)
  })

  it('a merge commit with only ONE input: the second token input is "none"', async () => {
    const a = await settled(1000n, '1')
    const tokenLock = a.tx!.outputs[0].lockingScript
    const merged = await a.merge(await settled(7n, '2'), child('400'))
    const mergeC = merged.prevTxs[merged.prevTxs.length - 2]
    const tx = new Transaction(2, [spending(tokenLock)], mergeC.outputs.map((o) => out(o.lockingScript)))
    const r = verifyEvent([tx], { expectedType: 'SimpleMultiBOLT' })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/commit [0-9a-f]{8}: token input @1 \(got none\)/)
  })
})
