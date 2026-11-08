// Lean vector exporter — `npm run lean:vectors`.
//
// Builds the honest lifecycles and the adversarial transactions of the test suite with the real
// builders (every tx is signed and, where the builder allows it, verified on the @bsv/sdk Spend
// engine), then writes them as Lean source for the bsv-script-lean bridge:
//   lean/BoltProof/Bridge/Generated/Vectors.lean         the transactions, prevouts and expectations
//   lean/BoltProof/Bridge/Generated/VectorTheorems.lean  one `native_decide` theorem per vector
//   lean/BoltProof/Bridge/Generated/Bytes.lean           the covenant suffixes + REGISTRY fingerprints
//   lean/vectors/vectors.json                            the same data for humans and other tools
//
// Expectations come from the @bsv/sdk Spend engine (valid / invalid per input). An invalid input is
// `anyInvalid` until its exact bsv-script-lean `ScriptError` is pinned in PINNED below, after a
// triage run of `lake exe boltvectors`. A change in an expectation is a reviewed regeneration.
//
// Signatures are RFC6979-deterministic and every key is fixed, so the output is byte-for-byte
// reproducible: CI regenerates and `git diff --exit-code`s the Generated/ directory.
import { it, expect } from 'vitest'
import { readFileSync, writeFileSync, mkdirSync } from 'fs'
import { join, dirname } from 'path'
import { fileURLToPath } from 'url'
import { Hash, LockingScript, P2PKH, PrivateKey, Script, Spend, Transaction } from '@bsv/sdk'
import {
  buildChain, meltToken, spendToken, p2pb, issuerKey, userKey, bucketKey, attackerKey,
  iPkh, uPkh, aPkh, bPkh, ZERO20, ZERO36, pub, type Family,
} from '../../test/helpers/minSimpleChain.js'
import { minSimple } from '../../test/helpers/minSimpleFamily.js'
import { authBolt } from '../../test/helpers/authBoltFamily.js'
import { serialBolt } from '../../test/helpers/serialBoltFamily.js'
import { fabricate, commitFabricated, settleFabricated, commitWith } from '../../test/helpers/minSimpleAttacks.js'
import { appendOutput } from '../../test/helpers/counterfeit.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { REGISTRY } from '../../src/lib/scanner/fingerprints.js'
import { buildOutpoint, buildChangeOutput } from '../../src/lib/boltLib.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import AuthBoltTemplate from '../../src/tokens/templates/AuthBolt.sx.template.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import SerialBoltTemplate from '../../src/tokens/templates/SerialBolt.sx.template.js'
import { emitBytes, emitChunks, emitTheorems, emitVectors, type Expect, type Vec } from './leanEmit.js'
import { cutSections, EXTRA_CUTS, LANDMARKS } from './sections.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const ROOT = join(__dirname, '..', '..')
const GENERATED = join(ROOT, 'lean', 'BoltProof', 'Bridge', 'Generated')

/** Pinned bsv-script-lean error codes, keyed `<vector>#<input>`. Filled from a triage run. */
const PINNED: Record<string, string> = {
  // the NFT family (triage run: lake exe boltvectors, bsv-script-lean v1.2.0, post-Chronicle block path)
  'minsimple_melt_by_non_owner#0': 'SCRIPT_ERR_EQUALVERIFY',
  'auth_melt_by_non_owner#0': 'SCRIPT_ERR_EQUALVERIFY',
  'serial_melt_by_non_owner#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b1_resting_settle#0': 'SCRIPT_ERR_EQUALVERIFY', // the grandparent txid check
  'nft_b1_2_genesis_shape_commit#0': 'SCRIPT_ERR_EQUALVERIFY', // issuerPubKey == pubKey
  'nft_b1_3_nonzero_type_commit#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b2_1_owner_substituted_at_settle#0': 'SCRIPT_ERR_EQUALVERIFY', // hashOutputs
  'nft_b2_2_owner_substituted_at_commit#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b3_1_non_issuer_genesis_spend#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b4_1_settle_to_settle#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b4_2_commit_to_commit#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b4_3_undefined_type_02#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b4_3_undefined_type_20#0': 'SCRIPT_ERR_EQUALVERIFY',
  'nft_b4_3_undefined_type_ff#0': 'SCRIPT_ERR_EQUALVERIFY',
  // the fungible family
  'smb_inflated_commit#0': 'SCRIPT_ERR_EQUALVERIFY', // hashOutputs
  'smb_split_overtake_commit#0': 'SCRIPT_ERR_VERIFY', // `sub 0 greaterThanOrEqual verify`
  'smb_split_overtake_settle#0': 'SCRIPT_ERR_VERIFY',
  'smb_merge_overflow_commit#0': 'SCRIPT_ERR_VERIFY', // the sum bound, in both covenants
  'smb_merge_overflow_commit#1': 'SCRIPT_ERR_VERIFY',
  'smb_merge_overflow_settle#0': 'SCRIPT_ERR_VERIFY',
  'smb_cross_issuer_merge_commit#1': 'SCRIPT_ERR_EQUALVERIFY', // the OTHER token's covenant pins its issuer
  'smb_cross_issuer_merge_settle#0': 'SCRIPT_ERR_EQUALVERIFY',
  'smb_extra_output_settle#0': 'SCRIPT_ERR_CHECKSIGVERIFY', // the unlocking script's own OP_PUSH_TX (before the lock runs): its preimage no longer matches
  'smb_extra_output_settle#1': 'SCRIPT_ERR_EVAL_FALSE', // the funding P2PKH signature covered the outputs
  'smb_wrong_key_commit#0': 'SCRIPT_ERR_EQUALVERIFY', // the prologue's issuer guard (suffix 13): at genesis the signer must be the issuer
  'smb_wrong_key_commit#1': 'SCRIPT_ERR_EQUALVERIFY',
  // the glue plan's probes (lean/GLUE-PLAN.md, M1 and §7)
  'smb_probe_type27_commit#0': 'SCRIPT_ERR_EQUALVERIFY', // the written type is derived from the mode flags, not copied
  'smb_probe_q8_melt_other_inflated_settle#0': 'SCRIPT_ERR_EQUALVERIFY', // the merge settle anchors the carried balance to the other lineage's rebuilt ancestor (the honest-balance control passes)
}

// ---------------------------------------------------------------------------------------------
// Verdicts on the @bsv/sdk Spend engine, per input (the same construction as verifyTx).
// ---------------------------------------------------------------------------------------------
function sdkVerdict(tx: Transaction, i: number): { ok: true } | { ok: false; message: string } {
  const input = tx.inputs[i]
  const sourceOutput = input.sourceTransaction!.outputs[input.sourceOutputIndex]
  const spend = new Spend({
    sourceTXID: input.sourceTXID ?? input.sourceTransaction!.id('hex'),
    sourceOutputIndex: input.sourceOutputIndex,
    lockingScript: sourceOutput.lockingScript,
    sourceSatoshis: sourceOutput.satoshis || 0,
    transactionVersion: tx.version,
    otherInputs: tx.inputs.filter((_, idx) => idx !== i),
    unlockingScript: input.unlockingScript!,
    inputSequence: input.sequence ?? 0xffffffff,
    inputIndex: i,
    outputs: tx.outputs,
    lockTime: tx.lockTime,
  })
  try {
    return spend.validate() ? { ok: true } : { ok: false, message: 'validate() returned false' }
  } catch (e: any) {
    return { ok: false, message: String(e?.message ?? e) }
  }
}

const vectors: Vec[] = []

/** Export one transaction: every input with its prevout and its Spend-engine expectation. */
function add(name: string, family: string, tx: Transaction, note: string, opts: { skip?: number[] } = {}): void {
  if (vectors.some((v) => v.name === name)) throw new Error(`duplicate vector ${name}`)
  tx.inputs.forEach((inp) => { if (!inp.sourceTXID && inp.sourceTransaction) inp.sourceTXID = inp.sourceTransaction.id('hex') })
  const prevouts = tx.inputs.map((inp, i) => {
    if (opts.skip?.includes(i)) return { script: '', satoshis: 0 }
    const src = inp.sourceTransaction!.outputs[inp.sourceOutputIndex]
    return { script: src.lockingScript.toHex(), satoshis: src.satoshis || 0 }
  })
  const sdk: string[] = []
  const expect: Expect[] = tx.inputs.map((_, i) => {
    if (opts.skip?.includes(i)) return 'skip'
    const v = sdkVerdict(tx, i)
    if (v.ok) { sdk.push(`${i}:valid`); return 'valid' }
    sdk.push(`${i}:invalid(${v.message.replace(/\s+/g, ' ').slice(0, 80)})`)
    const code = PINNED[`${name}#${i}`]
    return code ? { invalid: code } : 'anyInvalid'
  })
  vectors.push({ name, family, txHex: tx.toHex(), prevouts, expect, note: `${note} [sdk: ${sdk.join(' ')}]` })
}

/** Export a whole chain with per-tx names. */
function addChain(prefix: string, family: string, txs: Transaction[], labels: string[], note: string): void {
  txs.forEach((tx, i) => add(`${prefix}_${labels[i] ?? `tx${i}`}`, family, tx, `${note}: ${labels[i] ?? `tx${i}`}`))
}

const NFT_LABELS = ['mint', 'commit1', 'settle1', 'commit2', 'settle2']

// ---------------------------------------------------------------------------------------------
// The fungible builders of test/tokens/MultiBOLT.test.ts.
// ---------------------------------------------------------------------------------------------
const MASK64 = (BigInt(1) << BigInt(64)) - BigInt(1)
function bal(amount: bigint): number[] {
  const x = amount & ((BigInt(1) << BigInt(128)) - BigInt(1))
  const buf = Buffer.alloc(16)
  buf.writeBigUInt64LE(x & MASK64, 0)
  buf.writeBigUInt64LE((x >> BigInt(64)) & MASK64, 8)
  return Array.from(buf)
}
const smbIssuer = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const smbIssuer2 = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000002', 'hex')
const child = (k: PrivateKey, n: string) => k.deriveChild(k.toPublicKey(), n)
const SIM_BALANCE = BigInt('0x1ffffffffffffe')
const freshSource = (key = smbIssuer): Transaction =>
  new Transaction(1, [], [{
    satoshis: 1000, change: true,
    lockingScript: new P2PKH().lock(Hash.hash160(key.toPublicKey().encode(true) as number[])),
  }])

// ---------------------------------------------------------------------------------------------
it('exports the Lean vectors', async () => {
  // ---- NFT family: honest lifecycles -------------------------------------------------------------
  for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT'], [serialBolt, 'SerialBOLT']] as const) {
    const tag = type.replace('BOLT', '').toLowerCase()
    const txs = await buildChain(fam, {}, 5)
    addChain(`${tag}_honest`, type, txs, NFT_LABELS, `${type} honest lifecycle (test/helpers/minSimpleChain.ts buildChain)`)
    add(`${tag}_melt_unfunded`, type, await meltToken({ fam, txs: txs.slice(0, 3), from: { tx: 2, vout: 0 }, actor: userKey }),
      `${type} owner melts settle1, unfunded (test/lib/minSimpleMelt.test.ts)`)
    add(`${tag}_melt_funded`, type, await meltToken({ fam, txs: txs.slice(0, 3), from: { tx: 2, vout: 0 }, actor: userKey, fund: { tx: 2, vout: 1 } }),
      `${type} owner melts settle1, funded`)
    add(`${tag}_melt_by_non_owner`, type, await meltToken({ fam, txs: txs.slice(0, 3), from: { tx: 2, vout: 0 }, actor: attackerKey }),
      `${type} §8.2 melt by non-owner: refused (Lemma 1 on the melt path)`)
  }

  // ---- NFT family: the red-team suite (test/lib/minSimpleAttack.test.ts) ---------------------------
  const fam = minSimple
  const type = 'MinSimpleBOLT'
  const op = (txs: Transaction[], t: number, v: number) => buildOutpoint(txs[t], v)
  const tpl = new MinSimpleTemplate()
  {
    const txs = await settleFabricated(await commitFabricated(await fabricate()))
    addChain('nft_b1_resting', type, txs, ['fund', 'fabricate', 'commit', 'settle'],
      'B1.0/B1.1 a fabricated RESTING token (txoType 00, parent != 0, gp = 0) naming the victim issuer: its commit is accepted, its settle dies in the grandparent reconstruction')
  }
  {
    const txs = await commitFabricated(await fabricate({ parent: false }))
    add('nft_b1_2_genesis_shape_commit', type, txs[2], 'B1.2 a fabricated GENESIS shape (parent = 0) re-arms the issuer guard: the commit is refused')
  }
  {
    const txs = await commitFabricated(await fabricate({ txoType: 0x02 }))
    add('nft_b1_3_nonzero_type_commit', type, txs[2], 'B1.3/B4.4 any non-zero txoType on a fabricated token re-arms the issuer guard (is2ndTx): the commit is refused')
  }
  {
    // B2.1 substituting the settle-revealed owner
    const txs = await buildChain(fam, {}, 2)
    txs.push(await spendToken({
      fam, txs, from: { tx: 1, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 1, vout: 2 }, change: true,
      outputs: [fam.lock(aPkh, ZERO20, [0x00], op(txs, 1, 0), op(txs, 0, 0))],
    }))
    add('nft_b2_1_owner_substituted_at_settle', type, txs[2], 'B2.1 the settle names an owner other than the committed recipient: refused (Lemma 2, hashOutputs)')
  }
  {
    // B2.2 substituting the commit-carried owner
    const txs = await buildChain(fam, {}, 1)
    txs.push(await spendToken({
      fam, txs, from: { tx: 0, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 0, vout: 1 }, change: true,
      outputs: [fam.lock(aPkh, uPkh, [0x21], op(txs, 0, 0), ZERO36), p2pb(uPkh)],
    }))
    add('nft_b2_2_owner_substituted_at_commit', type, txs[1], 'B2.2 the commit output carries an owner other than the spender: refused (Lemma 2)')
  }
  {
    // B3.1 a non-issuer spending the genesis
    const other = pub(userKey)
    const bad: Family = { ...fam, lock: (o, c, t, p, g) => tpl.lock(o, other, c, t, p, g) }
    const txs = await buildChain(bad, {}, 2)
    add('nft_b3_1_non_issuer_genesis_spend', type, txs[1], 'B3.1 the genesis names another issuer than the spending key: refused (Lemma 5)')
  }
  {
    // B4: the txoType machine
    add('nft_b4_1_settle_to_settle', type, (await commitWith(0x00))[1], 'B4.1 a 00 token forced to emit a 00 output: refused (Lemma 7)')
    const txs = await buildChain(fam, {}, 2)
    txs.push(await spendToken({
      fam, txs, from: { tx: 1, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 1, vout: 2 }, change: true,
      outputs: [fam.lock(uPkh, ZERO20, [0x21], op(txs, 1, 0), op(txs, 0, 0))],
    }))
    add('nft_b4_2_commit_to_commit', type, txs[2], 'B4.2 a 21 token forced to emit a 21 output: refused (Lemma 7)')
    for (const t of [0x02, 0x20, 0xff]) {
      add(`nft_b4_3_undefined_type_${t.toString(16).padStart(2, '0')}`, type, (await commitWith(t))[1],
        `B4.3 an undefined output txoType 0x${t.toString(16)}: refused (Lemma 7)`)
    }
  }

  // ---- Fungible: honest lifecycles (test/tokens/MultiBOLT.test.ts) -------------------------------
  {
    let token = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(SIM_BALANCE))
    token = await token.transfer(child(smbIssuer, '1'))
    token = await token.transfer(child(smbIssuer, '2'))
    const [main, piece] = await token.split(child(smbIssuer, '10'), child(smbIssuer, '11'), bal(BigInt(1)))
    addChain('smb_honest_a', 'SimpleMultiBOLT', main.prevTxs,
      ['mint', 'commit1', 'settle1', 'commit2', 'settle2', 'splitCommit', 'splitSettle'],
      'SimpleMultiBOLT honest lifecycle A: mint → transfer ×2 → split')
    void piece
  }
  {
    let a = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(SIM_BALANCE))
    let b = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1)))
    a = await a.transfer(child(smbIssuer, '1'))
    b = await b.transfer(child(smbIssuer, '2'))
    const bLineage = [...b.prevTxs]
    const merged = await a.merge(b, child(smbIssuer, '400'))
    addChain('smb_honest_b_lineageB', 'SimpleMultiBOLT', bLineage, ['mint', 'commit1', 'settle1'],
      'SimpleMultiBOLT honest lifecycle B, second token: mint → transfer')
    const aTxs = merged.prevTxs
    addChain('smb_honest_b', 'SimpleMultiBOLT', aTxs, ['mint', 'commit1', 'settle1', 'mergeCommit', 'mergeSettle'],
      'SimpleMultiBOLT honest lifecycle B: mint ×2 → transfer → merge')
    const melted = await merged.melt()
    add('smb_honest_b_melt', 'SimpleMultiBOLT', melted.tx!, 'SimpleMultiBOLT honest lifecycle B: melt of the merged token')
  }

  // ---- Fungible: adversarial builds (skipVerify lets the builder emit what the covenant refuses) ----
  {
    const t = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    t.skipVerify = true
    t.balance = bal(BigInt(1001))
    await t.transfer(child(smbIssuer, '1'))
    add('smb_inflated_commit', 'SimpleMultiBOLT', t.prevTxs[1], '§8.3 the commit output claims 1001 on a 1000 token: refused (Lemma 2/6, hashOutputs)')
  }
  {
    const t0 = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    const t = await t0.transfer(child(smbIssuer, '1'))
    t.skipVerify = true
    const [main] = await t.split(child(smbIssuer, '10'), child(smbIssuer, '11'), bal(BigInt(1001)))
    const n = main.prevTxs.length
    add('smb_split_overtake_commit', 'SimpleMultiBOLT', main.prevTxs[n - 2], '§8.3 split with piece 1001 > balance 1000: the commit is refused (Lemma 6 over-take guard)')
    add('smb_split_overtake_settle', 'SimpleMultiBOLT', main.prevTxs[n - 1], '§8.3 split with piece 1001 > balance 1000: the settle re-asserts remainder ≥ 0')
  }
  {
    const big = (BigInt(1) << BigInt(127)) - BigInt(1)
    let a = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(big))
    let b = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1)))
    a = await a.transfer(child(smbIssuer, '1'))
    b = await b.transfer(child(smbIssuer, '2'))
    a.skipVerify = true
    b.skipVerify = true
    const merged = await a.merge(b, child(smbIssuer, '400'))
    const n = merged.prevTxs.length
    add('smb_merge_overflow_commit', 'SimpleMultiBOLT', merged.prevTxs[n - 2], '§8.3 merge whose sum exceeds 2^127 − 1: the commit is refused (Lemma 6 range)')
    add('smb_merge_overflow_settle', 'SimpleMultiBOLT', merged.prevTxs[n - 1], '§8.3 merge whose sum exceeds 2^127 − 1: the settle re-asserts the bound')
  }
  {
    let a = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(500)))
    let b = await new SimpleMultiBOLT().mint(smbIssuer2, freshSource(smbIssuer2), '', bal(BigInt(7)))
    a = await a.transfer(child(smbIssuer, '1'))
    b = await b.transfer(child(smbIssuer2, '2'))
    a.skipVerify = true
    b.skipVerify = true
    const merged = await a.merge(b, child(smbIssuer, '400'))
    const n = merged.prevTxs.length
    add('smb_cross_issuer_merge_commit', 'SimpleMultiBOLT', merged.prevTxs[n - 2], 'merge of tokens of two different issuers: what the bytes say (interface clause l_merge_same_issuer)')
    add('smb_cross_issuer_merge_settle', 'SimpleMultiBOLT', merged.prevTxs[n - 1], 'merge of tokens of two different issuers, the settle')
  }
  {
    // §8.5 an extra output appended at the raw-byte level to an honest settle
    const t0 = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    const t = await t0.transfer(child(smbIssuer, '1'))
    const settle = t.prevTxs[2]
    const tampered = Transaction.fromHex(appendOutput(settle.toHex(), '6a04b01700ff', 0))
    tampered.inputs.forEach((inp, i) => { inp.sourceTransaction = settle.inputs[i].sourceTransaction })
    add('smb_extra_output_settle', 'SimpleMultiBOLT', tampered, '§8.5 an OP_RETURN output appended to an honest settle: refused (Lemma 2, hashOutputs)')
  }
  {
    // §8.2 wrong-key spend: the commit is signed by a key that is not the owner
    const t = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    t.skipVerify = true
    t.signer = child(smbIssuer, '99') as any
    await t.transfer(child(smbIssuer, '1'), undefined, undefined, true)
    add('smb_wrong_key_commit', 'SimpleMultiBOLT', t.prevTxs[1], '§8.2 the genesis spent with a key whose hash160 is not the owner: refused (Lemma 1)')
  }

  // ---- The glue plan's probes (lean/GLUE-PLAN.md §2 Finding 1 and §4.1): what the bytes do NOT enforce -------
  {
    // A melt whose transaction also carries a covenant-shaped output. The melt branch checks only the owner key
    // (singleSpend.ts: "a null CTX takes the lock's melt branch, which checks only the owner's signature and
    // pubKey"), so the interface clause `l2_melt` (melt outputs are P2PKH-only) is not enforced by the bytes.
    const txs = await buildChain(minSimple, {}, 3)
    const tx = new Transaction()
    tx.version = 2
    tx.addInput({ sourceTransaction: txs[2], sourceOutputIndex: 0, unlockingScriptTemplate: minSimple.melt(userKey), sequence: 0xffffffff })
    tx.addInput({ sourceTransaction: txs[2], sourceOutputIndex: 1, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
    const sats = (txs[2].outputs[0].satoshis as number) + (txs[2].outputs[1].satoshis as number) - 10
    tx.addOutput({ satoshis: sats - 1, lockingScript: new P2PKH().lock(uPkh) })
    tx.addOutput({ satoshis: 1, lockingScript: minSimple.lock(aPkh, ZERO20, [0x00], op(txs, 2, 0), op(txs, 1, 0)) })
    await tx.sign()
    add('nft_probe_melt_token_output', type, tx, 'GLUE-PLAN probe: a melt that also emits a covenant-shaped token output; the melt branch constrains no output, so `l2_melt` is not enforced by the bytes')
  }
  {
    // A commit whose `changeOutput` argument carries TWO serialised outputs, one of them covenant-shaped. The
    // covenant concatenates the blob into the hashOutputs preimage unparsed, so the "change carries no token" half
    // of the interface clause `l2_outs` is not enforced by the bytes. Built honestly, then the unlock's change
    // argument (index 27 of the MinSimple layout) is widened to cover both trailing outputs; the owner signature
    // does not cover the unlocking script, so it stays valid.
    const txs = await buildChain(minSimple, {}, 3)
    const tx = await spendToken({
      fam: minSimple, txs, from: { tx: 2, vout: 0 }, actor: userKey, beneficiary: bPkh, fund: { tx: 2, vout: 1 }, change: true,
      outputs: [minSimple.lock(uPkh, bPkh, [0x21], op(txs, 2, 0), op(txs, 1, 0)), p2pb(bPkh),
        minSimple.lock(aPkh, ZERO20, [0x00], op(txs, 2, 0), op(txs, 1, 0))],
    })
    const blob = [...buildChangeOutput(tx, 2), ...buildChangeOutput(tx, 3)]
    const chunks = tx.inputs[0].unlockingScript!.chunks
    if (chunks[27].data!.length !== buildChangeOutput(tx, 2).length) throw new Error('unexpected unlock layout for the change blob probe')
    chunks[27] = new Script().writeBin(blob).chunks[0] // a PUSHDATA push: the blob is longer than 75 bytes
    add('nft_probe_change_blob_token', type, tx, 'GLUE-PLAN probe: a commit whose change blob carries two outputs, one covenant-shaped; the blob is unparsed, so the change half of `l2_outs` is not enforced by the bytes')
  }
  {
    // Variants that pin down what the covenant checks about the change slot: (a) the single change output is
    // covenant-shaped (honest unlock, no patch); (b) the blob carries two P2PKH outputs.
    const txs = await buildChain(minSimple, {}, 3)
    const single = await spendToken({
      fam: minSimple, txs, from: { tx: 2, vout: 0 }, actor: userKey, beneficiary: bPkh, fund: { tx: 2, vout: 1 }, change: false,
      outputs: [minSimple.lock(uPkh, bPkh, [0x21], op(txs, 2, 0), op(txs, 1, 0)), p2pb(bPkh),
        minSimple.lock(aPkh, ZERO20, [0x00], op(txs, 2, 0), op(txs, 1, 0))],
    })
    add('nft_probe_change_single_token', type, single, 'GLUE-PLAN probe: the single change output is covenant-shaped (honest unlock): does the covenant constrain the change script?')
    const two = await spendToken({
      fam: minSimple, txs, from: { tx: 2, vout: 0 }, actor: userKey, beneficiary: bPkh, fund: { tx: 2, vout: 1 }, change: true,
      outputs: [minSimple.lock(uPkh, bPkh, [0x21], op(txs, 2, 0), op(txs, 1, 0)), p2pb(bPkh), new P2PKH().lock(aPkh)],
    })
    const blob2 = [...buildChangeOutput(two, 2), ...buildChangeOutput(two, 3)]
    two.inputs[0].unlockingScript!.chunks[27] = new Script().writeBin(blob2).chunks[0]
    add('nft_probe_change_two_p2pkh', type, two, 'GLUE-PLAN probe: the change blob carries two P2PKH outputs: does the covenant constrain the change count?')
  }
  {
    // A fungible transfer commit asking for nextTxoType 0x27 (undefined) off-genesis: refused, because the written
    // type comes from the mode flags, not from the byte (GLUE-PLAN §2 Finding 3). Pinned as a regression.
    const patchLock = (lock: Script, patches: Record<number, number[]>): LockingScript =>
      new LockingScript(lock.chunks.map((c, i) => (patches[i] ? { op: patches[i].length, data: patches[i] } : c)))
    let t = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    t = await t.transfer(child(smbIssuer, '1'))
    const to = child(smbIssuer, '2')
    const inputs = (t as any).createTransferInputs(to, '', true, false, undefined, false)
    inputs[0].unlockingScriptTemplate = (t as any).template().unlock((t as any).signer, to.toPublicKey().encode(true) as number[], t.prevTxs, false, false, [], [0x27], [0x00], [], [])
    const outputs = (t as any).createTransferOutputs(to, true, false)
    outputs[0].lockingScript = patchLock(outputs[0].lockingScript, { 6: [0x27] })
    const commit = new Transaction(2, inputs, outputs)
    await commit.fee(0)
    await commit.sign()
    const parsed = Transaction.fromHex(commit.toHex())
    commit.inputs.forEach((inp, i) => { parsed.inputs[i].sourceTransaction = inp.sourceTransaction })
    add('smb_probe_type27_commit', 'SimpleMultiBOLT', parsed, 'GLUE-PLAN probe: an off-genesis transfer commit with nextTxoType 0x27 (undefined) and a matching output type: refused, the written type is derived from the mode flags')
  }

  // ---- The glue plan's open questions Q8 and Q3 (lean/GLUE-PLAN.md §7): probes -----------------------------------
  {
    // Q8. A merge commit whose second token input takes the melt branch (the six CTX pieces empty), while the first
    // input's covenant takes the other token's balance from the interop argument `nbc`. The first input's run
    // constrains `hashPrevouts` (this outpoint, `i2`, the funding outpoint) and nothing about the other input's
    // unlocking script. Built twice: with `nbc` the other token's real balance (the control) and with `nbc` =
    // 1,000,000 for a token of balance 1 (the attack). The settle then rebuilds both lineages: whether its second
    // rebuild anchors the carried balance to the other token's real one is what the two settles, side by side, show.
    const tpl = new SimpleMultiTemplate()
    const proofTpl = new Pay2ProofTemplate()
    const z = (n: number): number[] => new Array(n).fill(0x00)
    const clean = (tx: Transaction): Transaction => {
      const c = Transaction.fromHex(tx.toHex())
      tx.inputs.forEach((inp, i) => { c.inputs[i].sourceTransaction = inp.sourceTransaction })
      return c
    }
    const keyA = child(smbIssuer, '1')
    const keyB = child(smbIssuer, '2')
    let a = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    let b = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1)))
    a = await a.transfer(keyA)
    b = await b.transfer(keyB)
    const toKey = child(smbIssuer, '400')
    const toPub = toKey.toPublicKey().encode(true) as number[]
    const toPkh = Hash.hash160(toPub)
    const q8 = async (tag: string, claimed: number[], what: string): Promise<void> => {
      const commitTx = new Transaction(2, [
        { sourceTransaction: a.tx, sourceOutputIndex: a.voutIdx as number, sequence: 0xffffffff,
          unlockingScriptTemplate: tpl.unlock(keyA, toPub, a.prevTxs, false, false, claimed, [0x25], [0x00], [], [], [], [],
            buildOutpoint(b.tx!, b.voutIdx!), (b as any).getParentOutpoint()) },
        { sourceTransaction: b.tx, sourceOutputIndex: b.voutIdx as number, sequence: 0xffffffff,
          unlockingScriptTemplate: tpl.melt(keyB) },
        { sourceTransaction: a.tx, sourceOutputIndex: a.tx!.outputs.length - 1, sequence: 0xffffffff,
          unlockingScriptTemplate: new P2PKH().unlock(keyA) },
      ], [
        { satoshis: 1, lockingScript: tpl.lock(a.pubKey, a.prevTxs, a.balance, claimed, toPkh, z(20), (b as any).getParentOutpoint(), [0x25], [0x00], a.voutIdx) },
        { satoshis: 1, lockingScript: proofTpl.lock(toPkh) },
        { change: true, lockingScript: new P2PKH().lock(a.pubKeyHash as number[]) },
      ])
      await commitTx.fee(0)
      await commitTx.sign()
      const commit = clean(commitTx)
      add(`smb_probe_q8_melt_other_${tag}_commit`, 'SimpleMultiBOLT', commit,
        `GLUE-PLAN §7 Q8 probe: a merge commit whose other token input takes the melt branch, this input's nbc ${what}`)
      const aTxs = [...a.prevTxs, commit]
      const bTxs = [...b.prevTxs, commit]
      const thisAnc = aTxs[aTxs.length - 3]
      const otherAnc = bTxs[bTxs.length - 3]
      const thisProof = (a as any).findProofVout(thisAnc, keyA) as number
      const otherProof = (b as any).findProofVout(otherAnc, keyB) as number
      const merged = (a as any).addBalances(a.balance, claimed) as number[]
      const settleTx = new Transaction(2, [
        { sourceTransaction: commit, sourceOutputIndex: 0, sequence: 0xffffffff,
          unlockingScriptTemplate: tpl.unlock(keyA, toPub, aTxs, false, false, z(16), [0x24], [0x00], [],
            (a as any).voutLE(thisProof), (a as any).voutLE(otherProof), [], [], [], otherAnc) },
        { sourceTransaction: thisAnc, sourceOutputIndex: thisProof, sequence: 0xffffffff, unlockingScriptTemplate: proofTpl.unlock(keyA) },
        { sourceTransaction: otherAnc, sourceOutputIndex: otherProof, sequence: 0xffffffff, unlockingScriptTemplate: proofTpl.unlock(keyB) },
        { sourceTransaction: commit, sourceOutputIndex: commit.outputs.length - 1, sequence: 0xffffffff, unlockingScriptTemplate: new P2PKH().unlock(keyA) },
      ], [
        { satoshis: 1, lockingScript: tpl.lock(toPub, aTxs, merged, z(16), z(20), z(20), z(36), [0x24], [0x00], 0) },
        { change: true, lockingScript: new P2PKH().lock(toPkh) },
      ])
      await settleTx.fee(0)
      await settleTx.sign()
      add(`smb_probe_q8_melt_other_${tag}_settle`, 'SimpleMultiBOLT', clean(settleTx),
        `GLUE-PLAN §7 Q8 probe: the settle of that merged token, carrying nbc ${what}`)
    }
    await q8('honest_balance', b.balance, '= the other token\'s real balance (1), the control')
    await q8('inflated', bal(BigInt(1000000)), '= 1,000,000 for a token of balance 1, the attack')
  }
  {
    // Q3. A split settle with `pkh1` non-empty, which the bytes read as a flag that puts the second token first (the
    // honest builder leaves it empty): the two token outputs are swapped, so each carries an index byte that is not
    // its position. The first token, now at output 1 with index byte 0, is then spent again: a transfer commit and
    // its settle, which rebuilds the swapped settle as the grandparent.
    const tpl = new SimpleMultiTemplate()
    const proofTpl = new Pay2ProofTemplate()
    const z = (n: number): number[] => new Array(n).fill(0x00)
    const clean = (tx: Transaction): Transaction => {
      const c = Transaction.fromHex(tx.toHex())
      tx.inputs.forEach((inp, i) => { c.inputs[i].sourceTransaction = inp.sourceTransaction })
      return c
    }
    const owner = child(smbIssuer, '1')
    const keyA = child(smbIssuer, '10')
    const keyB = child(smbIssuer, '11')
    const pubA = keyA.toPublicKey().encode(true) as number[]
    const pubB = keyB.toPublicKey().encode(true) as number[]
    const piece = bal(BigInt(1))
    let t = await new SimpleMultiBOLT().mint(smbIssuer, freshSource(), '', bal(BigInt(1000)))
    t = await t.transfer(owner)
    const [main] = await t.split(keyA, keyB, piece) // the honest split: its commit is reused, its settle replaced
    const n = main.prevTxs.length
    const txs = main.prevTxs.slice(0, n - 1) // up to and including the split commit
    const commit = txs[txs.length - 1]
    const anc = txs[txs.length - 3]
    const ancProof = (main as any).findProofVout(anc, owner) as number
    const mainBal = (main as any).subtractBalances(bal(BigInt(1000)), piece) as number[]
    const outA = tpl.lock(pubA, txs, mainBal, z(16), z(20), z(20), z(36), [0x22], [0x00], 0)
    const outB = tpl.lock(pubB, txs, piece, z(16), z(20), z(20), z(36), [0x22], [0x01], 0)
    const settleTx = new Transaction(2, [
      { sourceTransaction: commit, sourceOutputIndex: 0, sequence: 0xffffffff,
        unlockingScriptTemplate: tpl.unlock(owner, pubA /* non-empty: pkh1 = hash160(pubA), read as the flag */, txs,
          false, false, [], [0x22], [0x00], [], (main as any).voutLE(ancProof)) },
      { sourceTransaction: anc, sourceOutputIndex: ancProof, sequence: 0xffffffff, unlockingScriptTemplate: proofTpl.unlock(owner) },
      { sourceTransaction: commit, sourceOutputIndex: commit.outputs.length - 1, sequence: 0xffffffff, unlockingScriptTemplate: new P2PKH().unlock(owner) },
    ], [
      { satoshis: 1, lockingScript: outB },
      { satoshis: 1, lockingScript: outA },
      { change: true, lockingScript: new P2PKH().lock(Hash.hash160(pubA)) },
    ])
    await settleTx.fee(0)
    await settleTx.sign()
    const swapped = clean(settleTx)
    add('smb_probe_q3_swapped_split_settle', 'SimpleMultiBOLT', swapped,
      'GLUE-PLAN §7 Q3 probe: a split settle with pkh1 non-empty and its two token outputs swapped, each index byte off its position')
    const tokA = new SimpleMultiBOLT()
    tokA.tx = swapped
    tokA.voutIdx = 1
    tokA.prevTxs = [...txs, swapped]
    tokA.signer = keyA as any
    tokA.pubKey = pubA
    tokA.pubKeyHash = Hash.hash160(pubA)
    tokA.issuerPubKey = main.issuerPubKey
    tokA.genesisOutpoint = main.genesisOutpoint
    tokA.mintData = main.mintData
    tokA.balance = mainBal
    tokA.skipVerify = true
    await tokA.transfer(child(smbIssuer, '20'))
    const m = tokA.prevTxs.length
    add('smb_probe_q3_swapped_respend_commit', 'SimpleMultiBOLT', tokA.prevTxs[m - 2],
      'GLUE-PLAN §7 Q3 probe: the swapped first token (output 1, index byte 0) spent again, the commit')
    add('smb_probe_q3_swapped_respend_settle', 'SimpleMultiBOLT', tokA.prevTxs[m - 1],
      'GLUE-PLAN §7 Q3 probe: the swapped first token spent again, the settle that rebuilds the swapped split settle')
  }

  // ---- History: the fabricated-hop chain against the PRE-FIX bytes --------------------------------
  {
    const fx = JSON.parse(readFileSync(join(ROOT, 'test', 'fixtures', 'fabricated-hop-chain.json'), 'utf8')) as {
      names: string[]; hexes: string[]; refs: [number, number][][]
    }
    const txs = fx.hexes.map((h) => Transaction.fromHex(h))
    fx.refs.forEach((refs, i) => {
      refs.forEach(([t, v], j) => {
        txs[i].inputs[j].sourceTransaction = txs[t]
        txs[i].inputs[j].sourceOutputIndex = v
      })
    })
    fx.names.forEach((name, i) => {
      const skip = txs[i].inputs.map((_, j) => j).filter((j) => !fx.refs[i][j])
      add(`fabhop_prefix_${name.replace(/[^a-zA-Z0-9]+/g, '_')}`, 'SimpleMultiBOLT(pre-fix)', txs[i],
        `test/fixtures/fabricated-hop-chain.json ${name}: the historical chain a regtest Teranode ACCEPTED against the pre-fix covenant; valid here reproduces that acceptance in Lean`,
        { skip })
    })
  }

  // ---- Emit ---------------------------------------------------------------------------------------
  const entries = [
    { ident: 'simpleMulti', type: 'SimpleMultiBOLT', suffixHex: new SimpleMultiTemplate().staticSuffix().toHex(), fingerprintHex: REGISTRY.SimpleMultiBOLT.suffixHashHex },
    { ident: 'minSimple', type: 'MinSimpleBOLT', suffixHex: new MinSimpleTemplate().staticSuffix().toHex(), fingerprintHex: REGISTRY.MinSimpleBOLT.suffixHashHex },
    { ident: 'authBolt', type: 'AuthBOLT', suffixHex: new AuthBoltTemplate().staticSuffix().toHex(), fingerprintHex: REGISTRY.AuthBOLT.suffixHashHex },
    { ident: 'serialBolt', type: 'SerialBOLT', suffixHex: new SerialBoltTemplate().staticSuffix().toHex(), fingerprintHex: REGISTRY.SerialBOLT.suffixHashHex },
  ]
  mkdirSync(GENERATED, { recursive: true })
  writeFileSync(join(GENERATED, 'Vectors.lean'), emitVectors(vectors))
  writeFileSync(join(GENERATED, 'VectorTheorems.lean'), emitTheorems(vectors))
  writeFileSync(join(GENERATED, 'Bytes.lean'), emitBytes(entries))
  const NAMESPACE: Record<string, string> = { simpleMulti: 'SimpleMulti', minSimple: 'MinSimple', authBolt: 'AuthBolt', serialBolt: 'SerialBolt' }
  const chunkEntries = entries.map((e) => {
    const bytes = Array.from(Buffer.from(e.suffixHex, 'hex'))
    return { ident: e.ident, type: e.type, namespace: `BoltProof.Bridge.Generated.${NAMESPACE[e.ident]}`, bytes, sections: cutSections(bytes, LANDMARKS[e.ident], EXTRA_CUTS[e.ident]) }
  })
  writeFileSync(join(GENERATED, 'Chunks.lean'), emitChunks(chunkEntries))
  writeFileSync(join(__dirname, 'vectors.json'), JSON.stringify({ vectors, suffixes: entries }, null, 1))
  expect(vectors.length).toBeGreaterThan(40)
  console.log(`exported ${vectors.length} vectors`)
})
