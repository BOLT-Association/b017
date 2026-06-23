// B2b-2 — NFT ancestor reconstruction: a live coupon 2-hop transfer (mint -> c1/s1 -> c2/s2) where the
// 2nd settle (s2) reaches back over a >=4-tx chain and reconstructs the ancestor commit c1. Gated on
// verifyTx. Mirrors the canonical sx golden truth sx/tests/bolt/simple/zeroData/MinSimpleDiscountBolt.sim.json
// (mint, commitTx1, settleTx1, commitTx2, settleTx2), whose settleTx2 has the identical 3-input
// ancestor structure [token, p2pb-proof, funding] and whose 26 ancestor pieces nftAncestorPieces
// reproduces byte-for-byte (see the fixture-derived test). Lineage: issuer(0) -> user(1) -> bucket(2).
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Script, Transaction, TransactionSignature, UnlockingScript } from '@bsv/sdk'
import { verifyTx, buildOutpoint, createSignature } from '../src/lib/boltLib.js'
import { scriptChunksFromBin } from '../src/lib/boltLib.js'
import MinSimpleDiscountTemplate from '../src/templates/MinSimpleDiscount.sx.template.js'

const SCOPE = TransactionSignature.SIGHASH_FORKID | TransactionSignature.SIGHASH_ALL
const issuerKey = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
const userKey = PrivateKey.fromString('a1b2c3d4e5f60718293a4b5c6d7e8f90112233445566778899aabbccddeeff00', 'hex')
const bucketKey = PrivateKey.fromString('5566778899aabbccddeeff00112233445566778899aabbccddeeff0011223344', 'hex')
const pub = (k: PrivateKey) => k.toPublicKey().encode(true) as number[]
const pkh = (k: PrivateKey) => Hash.hash160(pub(k))
const issuerPub = pub(issuerKey)
const [iPkh, uPkh, bPkh] = [pkh(issuerKey), pkh(userKey), pkh(bucketKey)]
const ZERO20 = new Array(20).fill(0), ZERO36 = new Array(36).fill(0)
const hx = (a: number[]) => Buffer.from(a).toString('hex')
const p2pb = (h: number[]) => Script.fromHex('02b0178876a914' + hx(h) + '88ac')

// Spend a p2pb output: unlock = [sig, pubkey, push(b017)], signed by the p2pb owner over the p2pb lock.
const p2pbUnlock = (key: PrivateKey) => ({
  sign: async (tx: Transaction, i: number) => {
    const inp = tx.inputs[i]
    const src = inp.sourceTransaction!.outputs[inp.sourceOutputIndex]
    const preimage = TransactionSignature.format({
      sourceTXID: inp.sourceTransaction!.id('hex'), sourceOutputIndex: inp.sourceOutputIndex,
      sourceSatoshis: src.satoshis as number, transactionVersion: tx.version,
      otherInputs: tx.inputs.filter((_, j) => j !== i), inputIndex: i, outputs: tx.outputs,
      inputSequence: inp.sequence as number, subscript: src.lockingScript, lockTime: tx.lockTime, scope: SCOPE,
    })
    const { sigForScript, pubkeyForScript } = createSignature(key, preimage, SCOPE)
    return new UnlockingScript([
      ...scriptChunksFromBin(sigForScript), ...scriptChunksFromBin(pubkeyForScript), ...scriptChunksFromBin([0xb0, 0x17]),
    ])
  },
  estimateLength: async () => 120,
})

function assertValid(label: string, tx: Transaction) {
  tx.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
  const { valid, scriptExecutions } = verifyTx(tx, true)
  if (!valid) console.log(`${label}: input ${scriptExecutions.findIndex((e) => !e.valid)} failed`)
  expect(valid, label).toBe(true)
}

describe('B2b-2 — coupon 2-hop: settleTx2 ancestor reconstruction passes verifyTx', () => {
  const tpl = new MinSimpleDiscountTemplate()
  const d = [0x0a]
  const tok = (owner: number[], commit: number[], type: number[], parent: number[], gp: number[]) =>
    tpl.lock(d, owner, issuerPub, commit, type, parent, gp)

  it('mint -> c1 -> s1 -> c2 -> s2 (issuer -> user -> bucket), s2 reconstructs c1', async () => {
    const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(iPkh) }])

    const mint = new Transaction(); mint.version = 2
    mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
    mint.addOutput({ satoshis: 1, lockingScript: tok(iPkh, ZERO20, [0x00], ZERO36, ZERO36) })
    mint.addOutput({ satoshis: 4000, lockingScript: new P2PKH().lock(iPkh) })
    await mint.sign(); assertValid('mint', mint)

    // c1: issuer commits to user
    const c1 = new Transaction(); c1.version = 2
    c1.addInput({ sourceTransaction: mint, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(issuerKey, uPkh, [mint]), sequence: 0xffffffff })
    c1.addInput({ sourceTransaction: mint, sourceOutputIndex: 1, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
    c1.addOutput({ satoshis: 1, lockingScript: tok(iPkh, uPkh, [0x21], buildOutpoint(mint, 0), ZERO36) })
    c1.addOutput({ satoshis: 1, lockingScript: p2pb(uPkh) })
    c1.addOutput({ satoshis: 3000, lockingScript: new P2PKH().lock(iPkh) })
    await c1.sign(); assertValid('c1', c1)

    // s1: issuer settles to user
    const s1 = new Transaction(); s1.version = 2
    s1.addInput({ sourceTransaction: c1, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(issuerKey, uPkh, [mint, c1]), sequence: 0xffffffff })
    s1.addInput({ sourceTransaction: c1, sourceOutputIndex: 2, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
    s1.addOutput({ satoshis: 1, lockingScript: tok(uPkh, ZERO20, [0x00], buildOutpoint(c1, 0), buildOutpoint(mint, 0)) })
    s1.addOutput({ satoshis: 2000, lockingScript: new P2PKH().lock(uPkh) })
    await s1.sign(); assertValid('s1', s1)

    // c2: user commits to bucket (user now signs the bolt)
    const c2 = new Transaction(); c2.version = 2
    c2.addInput({ sourceTransaction: s1, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(userKey, bPkh, [mint, c1, s1]), sequence: 0xffffffff })
    c2.addInput({ sourceTransaction: s1, sourceOutputIndex: 1, unlockingScriptTemplate: new P2PKH().unlock(userKey), sequence: 0xffffffff })
    c2.addOutput({ satoshis: 1, lockingScript: tok(uPkh, bPkh, [0x21], buildOutpoint(s1, 0), buildOutpoint(c1, 0)) })
    c2.addOutput({ satoshis: 1, lockingScript: p2pb(bPkh) })
    c2.addOutput({ satoshis: 1000, lockingScript: new P2PKH().lock(uPkh) })
    await c2.sign(); assertValid('c2', c2)

    // s2: user settles to bucket — 3 inputs [token@c2.0, p2pb-proof@c1.1, funding@c2.2]; ancestor = c1
    const s2 = new Transaction(); s2.version = 2
    s2.addInput({ sourceTransaction: c2, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(userKey, bPkh, [mint, c1, s1, c2]), sequence: 0xffffffff })
    s2.addInput({ sourceTransaction: c1, sourceOutputIndex: 1, unlockingScriptTemplate: p2pbUnlock(userKey), sequence: 0xffffffff })
    s2.addInput({ sourceTransaction: c2, sourceOutputIndex: 2, unlockingScriptTemplate: new P2PKH().unlock(userKey), sequence: 0xffffffff })
    s2.addOutput({ satoshis: 1, lockingScript: tok(bPkh, ZERO20, [0x00], buildOutpoint(c2, 0), buildOutpoint(s1, 0)) })
    s2.addOutput({ satoshis: 500, lockingScript: new P2PKH().lock(bPkh) })
    await s2.sign(); assertValid('s2 (ancestor reconstruction)', s2)
  })
})
