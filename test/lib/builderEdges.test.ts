// Edges of the builders and the low-level verifier that the lifecycle suites never take:
//   - verifyTx on zero-satoshi sources, inputs with no explicit sequence, a pre-set sourceTXID, an output with
//     no amount;
//   - the NFT unlocker (singleSpendUnlock) with a change output but no funding, an AuthBolt spend with no
//     authOrMiscData, and a proof input whose source tx is not attached;
//   - the fungible builder's forceNoFund / forceNoChange flags (OUT OF PROTOCOL: MultiBOLTs require funding and
//     change; the flags stay on the builder, so their branches are exercised here), and two private helpers;
//   - both templates signing from a tx that names its source by txid, by attached tx, or by both.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Script, Transaction, UnlockingScript } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import AuthBoltTemplate from '../../src/tokens/templates/AuthBolt.sx.template.js'
import { singleSpendUnlock } from '../../src/lib/single/singleSpend.js'
import { AUTH_BOLT_LAYOUT } from '../../src/lib/single/singleAncestor.js'
import { ancestorPiece } from '../../src/lib/multi/multiBoltLib.js'
import { verifyTx, buildOutpoint } from '../../src/lib/boltLib.js'
import { buildChain, verifyChain, userKey, issuerKey, iPkh, uPkh, bPkh, ZERO20, p2pb } from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'

const id = (t: Transaction) => t.id('hex')

describe('verifyTx: forms the builders never produce', () => {
  const anyoneCanSpend = Script.fromASM('OP_1')
  const spend = (source: Transaction, extra: object = {}) =>
    new Transaction(2, [{ sourceTransaction: source, sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), ...extra } as any],
      [{ satoshis: 0, lockingScript: new P2PKH().lock(iPkh) }])

  it('a ZERO-satoshi source, an input with no sequence: valid', () => {
    const source = new Transaction(1, [], [{ satoshis: 0, lockingScript: anyoneCanSpend }])
    const tx = spend(source)
    expect(tx.inputs[0].sequence).toBeUndefined()
    expect(verifyTx(tx, true).valid).toBe(true)
    expect(tx.inputs[0].sourceTXID).toBe(id(source)) // verifyTx fills it in when absent
  })

  it('an input whose sourceTXID is already set is left as it is', () => {
    const source = new Transaction(1, [], [{ satoshis: 0, lockingScript: anyoneCanSpend }])
    const tx = spend(source, { sourceTXID: id(source), sequence: 0xffffffff })
    expect(verifyTx(tx, true).valid).toBe(true)
    expect(tx.inputs[0].sourceTXID).toBe(id(source))
  })

  it('an output with no amount is refused', () => {
    const source = new Transaction(1, [], [{ satoshis: 0, lockingScript: anyoneCanSpend }])
    const tx = spend(source)
    ;(tx.outputs[0] as any).satoshis = undefined
    expect(() => verifyTx(tx, true)).toThrow(/Every output must have a defined amount/)
  })

  it('an input with no attached source tx is refused', () => {
    const source = new Transaction(1, [], [{ satoshis: 0, lockingScript: anyoneCanSpend }])
    const tx = spend(source, { sourceTXID: id(source) })
    tx.inputs[0].sourceTransaction = undefined
    expect(() => verifyTx(tx, true)).toThrow(/missing its source transaction/)
  })
})

describe('singleSpendUnlock: the NFT unlocker', () => {
  it('a change output with NO funding input is refused (change needs a funding input)', async () => {
    const txs = await buildChain(minSimple, {}, 1)
    const tx = new Transaction(); tx.version = 2
    tx.addInput({ sourceTransaction: txs[0], sourceOutputIndex: 0, unlockingScriptTemplate: minSimple.unlock(issuerKey, uPkh, txs), sequence: 0xffffffff })
    tx.addOutput({ satoshis: 1, lockingScript: minSimple.lock(iPkh, uPkh, [0x21], buildOutpoint(txs[0], 0), new Array(36).fill(0)) })
    tx.addOutput({ satoshis: 1, lockingScript: p2pb(uPkh) })
    tx.addOutput({ satoshis: 1, lockingScript: new P2PKH().lock(iPkh) }) // a "change" output with nothing funding it
    await expect(tx.sign()).rejects.toThrow(/an unfunded spend has no change to return/)
  })

  it('AuthBolt with NO authOrMiscData pushes OP_0 as its first unlock arg, and the chain still executes', async () => {
    const txs = await buildChain(authBolt, {}, 1)
    const tpl = new AuthBoltTemplate()
    const unlocker = singleSpendUnlock({
      privateKey: issuerKey, beneficiaryPubKeyHash: uPkh, prevTxs: txs, layout: AUTH_BOLT_LAYOUT,
      unlockScriptSuffixASM: (tpl as any).UNLOCK_SCRIPT_SUFFIX, // authOrMiscData deliberately omitted
    })
    const tx = new Transaction(); tx.version = 2
    tx.addInput({ sourceTransaction: txs[0], sourceOutputIndex: 0, unlockingScriptTemplate: unlocker, sequence: 0xffffffff })
    tx.addOutput({ satoshis: 1, lockingScript: authBolt.lock(iPkh, uPkh, [0x21], buildOutpoint(txs[0], 0), new Array(36).fill(0)) })
    tx.addOutput({ satoshis: 1, lockingScript: p2pb(uPkh) })
    await tx.sign()
    const first = tx.inputs[0].unlockingScript!.chunks[0]
    expect(first.op).toBe(0)
    expect(first.data ?? []).toHaveLength(0)
    expect(verifyChain([tx]).ok).toBe(true)
  })

  it('a back-reaching settle whose PROOF input has no attached source is still read as [token, proof]', async () => {
    const txs = await buildChain(minSimple, { commit2: { fund: null, change: false } }, 4) // mint, c1, s1, unfunded c2
    const honest = await buildChain(minSimple, { commit2: { fund: null, change: false }, settle2: { fund: null, change: false } }, 5)
    const tx = new Transaction(); tx.version = 2
    tx.addInput({ sourceTransaction: txs[3], sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff })
    tx.addInput({ sourceTXID: id(txs[1]), sourceOutputIndex: 1, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff }) // proof, by txid only
    tx.addOutput({ satoshis: 1, lockingScript: minSimple.lock(bPkh, ZERO20, [0x00], buildOutpoint(txs[3], 0), buildOutpoint(txs[2], 0)) })
    const unlock = await minSimple.unlock(userKey, bPkh, txs).sign(tx, 0)
    // identical to the unlock the harness builds with the proof source attached: unfunded, so fundOutpoint is OP_0
    expect(unlock.toHex()).toBe(honest[4].inputs[0].unlockingScript!.toHex())
  })
})

describe('SimpleMultiBOLT builder: forceNoFund / forceNoChange (out of protocol) and private helpers', () => {
  const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const child = (n: string) => key.deriveChild(key.toPublicKey(), n)
  const pkhOf = (k: PrivateKey) => Hash.hash160(k.toPublicKey().encode(true) as number[])
  const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
  const src = (k: PrivateKey = key) => new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(pkhOf(k)) }])
  const minted = () => new SimpleMultiBOLT().mint(key, src(), '', bal(1000n))

  it('forceNoFund on a first transfer: commit and settle carry the token input only', async () => {
    const t = await minted()
    await t.transfer(child('1'), '', '', false, true, undefined, true)
    const [, commit, settle] = t.prevTxs
    expect(commit.inputs).toHaveLength(1)
    expect(settle.inputs).toHaveLength(1)
  })

  it('forceNoFund on a SECOND transfer: the settle carries [token, proof] and no funding input', async () => {
    const t = await minted()
    await t.transfer(child('1'))
    t.skipVerify = true // out of protocol: only the builder's input arrangement is under test here
    await t.transfer(child('2'), '', '', false, true, undefined, true)
    const settle2 = t.prevTxs[t.prevTxs.length - 1]
    expect(settle2.inputs).toHaveLength(2)
    expect(id(settle2.inputs[1].sourceTransaction!)).toBe(id(t.prevTxs[1])) // commit1's proof
  })

  it('forceNoChange on a funded transfer: no change output on the commit or the settle', async () => {
    const t = await minted()
    t.skipVerify = true
    await t.transfer(child('1'), '', '', false, true)
    const [, commit, settle] = t.prevTxs
    expect(commit.inputs).toHaveLength(2)
    expect(commit.outputs).toHaveLength(2) // token + proof
    expect(settle.outputs).toHaveLength(1) // token
  })

  it('findProofVout falls back to vout 1 when no proof output pays the key', async () => {
    const t = await minted()
    const ancestor = new Transaction(2, [], [
      { satoshis: 1, lockingScript: t.tx!.outputs[0].lockingScript },
      { satoshis: 1, lockingScript: Script.fromASM('OP_0 OP_RETURN') }, // two chunks: no chunk 4 to read
      { satoshis: 1, lockingScript: new Pay2ProofTemplate().lock(pkhOf(child('99'))) }, // a proof for someone else
      { satoshis: 1, lockingScript: new P2PKH().lock(pkhOf(key)) },
    ])
    expect((t as any).findProofVout(ancestor, child('1'))).toBe(1)
    expect((t as any).findProofVout(ancestor, child('99'))).toBe(2)
  })

  it('verifyAndLogTransaction fills a missing sourceTXID before verifying, and skips when skipVerify is set', async () => {
    const t = await minted()
    const anyone = new Transaction(1, [], [{ satoshis: 0, lockingScript: Script.fromASM('OP_1') }])
    const tx = new Transaction(2, [{ sourceTransaction: anyone, sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff } as any],
      [{ satoshis: 0, lockingScript: new P2PKH().lock(pkhOf(key)) }])
    expect(tx.inputs[0].sourceTXID).toBeUndefined()
    ;(t as any).verifyAndLogTransaction(tx, 'TEST')
    expect(tx.inputs[0].sourceTXID).toBe(id(anyone))
    const untouched = new Transaction(2, [{ sourceTransaction: anyone, sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff } as any], tx.outputs)
    t.skipVerify = true
    ;(t as any).verifyAndLogTransaction(untouched, 'TEST')
    expect(untouched.inputs[0].sourceTXID).toBeUndefined()
  })

  it('ancestorPiece reads an OP_0 lock field, and a field past the end of the scriptCode, as empty', () => {
    // An unlock with the CTX pieces where the fungible layout expects them (chunk 192 on): a 104-byte header, then
    // a scriptCode that is the single opcode OP_0, so lock field 0 is OP_0 and every later field is absent.
    const chunks: any[] = []
    for (let k = 0; k < 192; k++) chunks.push({ op: 0 })
    const push = (data: number[]) => new Script().writeBin(data).chunks[0]
    chunks.push(push(new Array(104).fill(0))) // 192: ctxHeader
    chunks.push({ op: 0 }, { op: 0 })         // 193, 194
    chunks.push(push([0x00]))                 // 195: ctxCodeLockScriptCode = OP_0
    chunks.push({ op: 0 })                    // 196: ctxFooter
    chunks.push(push([0x01]))                 // 197: ctxCodeLockLen (varint 1)
    const source = new Transaction(1, [], [{ satoshis: 1, lockingScript: Script.fromASM('OP_1') }])
    const tx = new Transaction(2, [{ sourceTransaction: source, sourceOutputIndex: 0, unlockingScript: new UnlockingScript(chunks), sequence: 0xffffffff } as any],
      [{ satoshis: 1, lockingScript: Script.fromASM('OP_1') }])
    expect(ancestorPiece('Vin1CTXBalance', tx)).toEqual([])                  // lock field 0 is OP_0
    expect(ancestorPiece('Vin1CTXOtherGrandparentOutpoint', tx)).toEqual([]) // lock field 5 does not exist
  })

  it('ancestorPiece reads an absent or OP_0 CTX field as empty', async () => {
    const t = await minted()
    await t.transfer(child('1'))
    const commit = t.prevTxs[1]
    // a real commit: every CTX field reads back as bytes
    expect(ancestorPiece('Vin1CTXPubKeyHash', commit).length).toBe(20)
    // a tx whose input-0 unlock is too short to hold a CTX at all
    const bare = new Transaction(2, [{ sourceTransaction: t.prevTxs[0], sourceOutputIndex: 0, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff } as any], commit.outputs)
    expect(ancestorPiece('Vin1CTXPubKeyHash', bare)).toEqual([])
  })
})

describe('templates sign from a tx that names its source by txid, by attached tx, or by both', () => {
  const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const pkh = Hash.hash160(key.toPublicKey().encode(true) as number[])
  const proofSource = new Transaction(1, [], [{ satoshis: 1, lockingScript: new Pay2ProofTemplate().lock(pkh) }])
  const forms: [string, object][] = [
    ['attached source only', { sourceTransaction: proofSource }],
    ['txid and attached source', { sourceTXID: proofSource.id('hex'), sourceTransaction: proofSource }],
  ]
  for (const [label, ref] of forms) {
    it(`pay2Proof: ${label}`, async () => {
      const tx = new Transaction(2, [{ ...ref, sourceOutputIndex: 0, unlockingScriptTemplate: new Pay2ProofTemplate().unlock(key), sequence: 0xffffffff } as any],
        [{ satoshis: 1, lockingScript: new P2PKH().lock(pkh) }])
      await tx.sign()
      expect(verifyTx(tx, true).valid).toBe(true)
    })
  }

  it('pay2Proof: txid only, with the amount and lock given explicitly', async () => {
    const tx = new Transaction(2, [{
      sourceTXID: proofSource.id('hex'), sourceOutputIndex: 0, sequence: 0xffffffff,
      unlockingScriptTemplate: new Pay2ProofTemplate().unlock(key, 1, proofSource.outputs[0].lockingScript),
    } as any], [{ satoshis: 1, lockingScript: new P2PKH().lock(pkh) }])
    await tx.sign()
    tx.inputs[0].sourceTransaction = proofSource
    expect(verifyTx(tx, true).valid).toBe(true)
  })

  it('pay2Proof: the unlocker called directly on an input with an attached source and no txid', async () => {
    const tx = new Transaction(2, [{ sourceTransaction: proofSource, sourceOutputIndex: 0, sequence: 0xffffffff } as any],
      [{ satoshis: 1, lockingScript: new P2PKH().lock(pkh) }])
    expect(tx.inputs[0].sourceTXID).toBeUndefined()
    tx.inputs[0].unlockingScript = await new Pay2ProofTemplate().unlock(key).sign(tx, 0)
    expect(verifyTx(tx, true).valid).toBe(true)
  })

  it('SimpleMulti melt: the unlocker called directly on an input with an attached source and no txid', async () => {
    const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
    const src = new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(pkh) }])
    const t = await new SimpleMultiBOLT().mint(key, src, '', bal(1000n))
    await t.transfer(key.deriveChild(key.toPublicKey(), '1'))
    const owner = key.deriveChild(key.toPublicKey(), '1')
    const tx = new Transaction(2, [{ sourceTransaction: t.tx!, sourceOutputIndex: 0, sequence: 0xffffffff } as any],
      [{ satoshis: 1, lockingScript: new P2PKH().lock(Hash.hash160(owner.toPublicKey().encode(true) as number[])) }])
    expect(tx.inputs[0].sourceTXID).toBeUndefined()
    tx.inputs[0].unlockingScript = await new SimpleMultiTemplate().melt(owner).sign(tx, 0)
    expect(verifyTx(tx, true).valid).toBe(true)
  })

  it('SimpleMulti melt: the same signature whether the input names its source by txid or not', async () => {
    const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
    const src = new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(pkh) }])
    const t = await new SimpleMultiBOLT().mint(key, src, '', bal(1000n))
    await t.transfer(key.deriveChild(key.toPublicKey(), '1'))
    const owner = key.deriveChild(key.toPublicKey(), '1')
    const ownerPkh = Hash.hash160(owner.toPublicKey().encode(true) as number[])
    const build = async (ref: object) => {
      const tx = new Transaction(2, [{ ...ref, sourceOutputIndex: 0, unlockingScriptTemplate: new SimpleMultiTemplate().melt(owner), sequence: 0xffffffff } as any],
        [{ satoshis: 1, lockingScript: new P2PKH().lock(ownerPkh) }])
      await tx.sign()
      return tx
    }
    const byTx = await build({ sourceTransaction: t.tx! })
    const byBoth = await build({ sourceTXID: t.tx!.id('hex'), sourceTransaction: t.tx! })
    expect(verifyTx(byTx, true).valid).toBe(true)
    expect(verifyTx(byBoth, true).valid).toBe(true)
  })
})
