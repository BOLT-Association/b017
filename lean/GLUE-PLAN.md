# Closing the glue gap: a plan for a symbolic proof that the covenant bytes enforce `Accepts`

Status: **M1–M4 delivered, M5 in progress (the five fungible fragments are reached), M6–M7 open** (see "Progress" at the end). Written against branch `lean-proof` at `3e4880f` (PR #7) and
bsv-script-lean v1.2.0 (`6139161c`). Everything marked *(trace)* comes from a symbolic trace of the shipped
suffix bytes in `BoltProof/Bridge/Generated/Bytes.lean` and is confirmed by execution or by a block lemma
before it is relied on; everything else was checked against the source.

## 1. The gap, precisely

`lean/README.md` ("What is still trusted") and `lean-proof-todo.md` state it: the fragment lemmas in
`BoltProof/Bridge/Gadgets/` are proved over a *free* interpreter state whose stack layout is a hypothesis
(`st.stack = s`, `s.getD 26 [] = ty`, `37 < s.length` in `parityCheck_edge_iff`, `Parity.lean:851`), and
nothing shows the covenant reaches each fragment in such a state. Concretely, today:

- No theorem ties a fragment literal (`parityCheck`, `nftTypeSel d`, `boundCheck d`, …) to the shipped
  suffix at an offset. The offsets (528, 610, 621, 781, 935, 534/543/589, …) live in docstrings and the README.
- No Bridge file imports `Spend`, `Token`, `Covenant`, `Run` or `Assumptions`; the only Layer-1 contact is
  `Fam.edge` in `Parity.lean` and `NftType.lean`. Nothing builds a `Spend` from transaction bytes and no
  concrete `Prims` exists.
- `Accepts` (`Model/Covenant.lean:19-87`) has 26 clauses. The theorems rely on `l1_*`, `l2_outs`, `l2_melt`,
  `commit_type/commit_mode/settle_type/settle_mode`, `l3_rebuild`, `l6_settle_split`, `l6_merge` (existence
  only) and the `other_*` merge clauses. The fragments proved so far (L4, L6 bounds and guards, L7) mostly back
  clauses the theorems do not use; **L1, L2, L3 and L5 carry the theorems and have no fragment proof.**

The target is therefore not "reach the fragments" alone but, per covenant family,

> for every transaction input spending a token of that family, if `verifyScript` under Chronicle rules accepts
> the input, then `Accepts P fam (spendOf tx i …)` holds for the spend the input denotes,

stated symbolically (standard axioms only on the symbolic path), with the explicit residual assumptions listed in
§5. The literal reviewer ask (each fragment is reached with the stated fields at the stated depths) is a corollary
of the block lemmas and is delivered first (M3, §8).

## 2. Findings that shape the plan

1. **Two `Accepts` clauses are not enforced by the bytes.**
   - The melt branch (`OP_IFDUP OP_IF … OP_ELSE`, MinSimpleBOLT suffix 1103–1118, SimpleMultiBOLT 4680–4695)
     checks only the sighash byte `0x41`, `HASH160(pubKey) = pubKeyHash`, `CHECKSIG`, and the prologue issuer
     guard; outputs are unconstrained (`src/lib/single/singleSpend.ts:141-142`). So `l2_melt` (all melt outputs
     P2PKH) is unenforced.
   - `changeOutput` is an unlocking-script argument concatenated unparsed into the hashOutputs preimage
     (MinSimple 597, SimpleMulti 1394, *trace*). `buildChangeOutput` (`src/lib/boltLib.ts:104`) serialises one
     output, but the covenant never parses the blob, so a spender can put several serialised outputs in it,
     token-shaped ones included. The "change carries no token" half of `l2_outs` is unenforced.
   - **Confirmed by execution (M1).** Four probe vectors built with the production builders and judged on the
     SDK Spend engine are all `valid`: `nft_probe_melt_token_output` (a melt whose transaction also emits a
     covenant-shaped output), `nft_probe_change_single_token` (the single change output is covenant-shaped,
     honest unlock), `nft_probe_change_two_p2pkh` (the change blob carries two outputs) and
     `nft_probe_change_blob_token` (two outputs, one covenant-shaped). They are registered with the kernel like
     every other vector.
   - A refinement to `Accepts` as written is therefore false without an extra hypothesis or a model change
     (§5, decision gate after M1).
2. **The NFT `nftFlag` docstring is wrong.** `76 81 92` at suffix offset 6 (`OP_DUP OP_BIN2NUM OP_0NOTEQUAL`)
   runs on `grandparentOutpoint`, so it computes `gp ≠ 0`, not `txoType ≠ 0`. From the ASM: entry stack (top
   first) is `issuer, gp, parent, txoType, commitment, pkh, …`; `2 PICK BIN2NUM NOT` = `parent = 0`; `SWAP 2SWAP`
   leaves `gp` on top; then `DUP BIN2NUM 0NOTEQUAL`. The selector `0x17 PICK` at 534/543 (`0x18` at 589) picks
   the **raw** `txoType` byte (`[0x00]` (settle) or `[0x21]` (commit), *trace*), so the hypotheses `s.getD n [] = [1]` / `= []` of
   `nftTypeSel_run_commit` / `nftTypeSel_run_settle` (`NftType.lean`) never hold on the real stack. The lemmas are
   true as stated; the glue needs a selector lemma on `castToBool`, and relies on MINIMALIF being off
   (`requireMinimal = false`, the block path).
3. **SimpleMultiBOLT does have an `is2ndTx`-style issuer guard.** The suffix opens with
   `2 PICK BIN2NUM NOT, 2 PICK BIN2NUM NOT, BOOLOR, TUCK, IF 13 PICK EQUALVERIFY, 15 PICK DUP 25 EQUAL NOT VERIFY,
   27 EQUAL NOT VERIFY, ELSE DROP ENDIF` (offsets 0–29), i.e.
   `parent = 0 ∨ gp = 0 → issuerPubKey = pubKey ∧ nextTxoType ∉ {0x25, 0x27}`, i.e. the next type may be neither
   `0x25` (merge-commit) nor `0x27` (undefined). This contradicts the README's
   `is2ndTx` observation ("the fungible family, which lacks it") and `docs/formal-proof.md`'s 2026-09-02
   correction. The model's `issuerMustSign .fungible = isGenesis` is weaker, so `l5_issuer` is still derivable;
   only the prose is wrong. `0x27` (undefined) is not a protocol type: the fungible type set is `0x20`
   (transfer-settle, also genesis), `0x21` (transfer-commit), `0x22` (split-settle), `0x23` (split-commit), `0x24`
   (merge-settle) and `0x25` (merge-commit) (`docs/unforgeability.md`, `docs/formal-proof.md` §7). A probe on the
   SDK Spend engine (mint → transfer → commit with `nextTxoType = 0x27` (undefined) and the output type patched to
   match) is refused off-genesis with `SCRIPT_ERR_EQUALVERIFY`, as is every byte other than `0x21`
   (transfer-commit) in the transfer shape, so the covenant derives the written type from its mode flags rather
   than copying the byte, and `commit_mode` is not a mismatch. At genesis `0x25` (merge-commit) and `0x27`
   (undefined) fail on the guard's `OP_VERIFY`; `0x29` (undefined) fails later. Why the guard names `0x27`
   (undefined) specifically is not answerable from this repository (the sx source is not vendored).
4. **Vector attribution.** `smb_wrong_key_commit#0` is rejected by the prologue issuer guard (offset 13), not the
   final `hash160` check at 4698 (comment in `lean/vectors/export.test.ts`); `smb_extra_output_settle#0` is
   rejected by the *unlocking* script's own OP_PUSH_TX, not by the covenant (*trace*). Pinned codes are unchanged.
5. **The unlocking script's OP_PUSH_TX proves nothing**; it is attacker-controlled. The binding check is the lock's
   own OP_PUSH_TX block (MinSimple 25–413, SimpleMulti 36–422) on the preimage item the unlock leaves on the stack.
   The refinement must quantify over whatever stack phase 1 leaves, and never execute the unlock suffix.
6. **Axiom-audit namespace rule.** `scripts/lean-axiom-check.mjs` holds every theorem whose name does not start with
   `BoltProof.Bridge` to Layer-1 rules (three standard axioms) and scrapes `^theorem` lines under
   `lean/BoltProof/Bridge/**` only. Symbolic glue must live outside `BoltProof.Bridge.*`; the few `native_decide`
   identities must live inside it; both under the `Bridge/` directory.

## 3. Proof style: inversion lemmas, nothing framed

Every step lemma is stated on the *remaining program*:

```
run Eval.opExec env (op :: g) t st = r → r.IsOk → (fact the op checks) ∧ ∃ m' k', run Eval.opExec env g t st' = r
```

`run.eq_2` gives exactly this. Chunk concatenation normalises by `List.cons_append`, so `framed`/`run_append`
never enter the soundness path (they stay available for forward, equational use). The limit hypotheses of the
existing forward lemmas (`hops`, `hmem`, `hnum`) disappear: a limit violation returns `.err`, which `r.IsOk`
refutes, and `run` never recovers from an error, so `IsOk` of the final result forces every step to succeed.
`memUsed` and `opCount` are existentially abstracted after each step; `stack`, `alt`, `cond`, `codeSep` are tracked
exactly, with the stack an explicit cons-list of named variables so `PICK n` / `ROLL n` resolve by `simp`.

Consequence: the existing `_accepts` / `_next_iff` fragment lemmas are reused as **specifications** (the fragment
literals, their stack shapes, their predicates); each gets a short `_inv` corollary in the same style. Their proof
terms are not reused.

## 4. Components

### 4.1 Offsets and decomposition (M1)

- `lean/vectors/sections.ts` (hand-maintained): per family, named `[start, end)` byte sections of the static
  suffix, cut so that each fragment literal is exactly one section and every `IF`/`ELSE`/`ENDIF` arm is its own
  section. The MinSimpleBOLT table, from the trace: 0–25 prologue, 25–28 push-tx gate, 28–414 OP_PUSH_TX,
  414–448 preimage split, 448–453 version, 453–480 scriptCode split, 480–603 output build (split per arm),
  603–614 rebuild condition, 614–968 rebuild, 968–969 else, 969–1072 null-ancestor pick/cat, 1072–1076
  `nullTail`, 1076–1077 endif, 1077–1085 hashPrevouts, 1085–1104 sig byte (main), 1104–1119 sig byte (melt),
  1119–1123 owner check.
- `lean/vectors/export.test.ts` validates that every boundary is an instruction start (walk
  `Script.fromBinary(suffix).chunks`) and that sections tile `[0, length)`; `lean/vectors/leanEmit.ts` gains
  `emitChunks`, writing `Generated/Chunks.lean`:
  `def c00_prologue : Bytes := [0x52, 0x79, …]`, …, `def suffix := c00_prologue ++ (c01 ++ (… ++ cNN))`
  in namespace `BoltProof.Bridge.Generated.<Family>`. `Generated/Chunks.lean` joins the CI drift diff.
- `Bridge/Bytes.lean` (namespace `BoltProof.Bridge`):
  `hexDecode! Generated.minSimpleSuffixHex = Generated.MinSimple.suffix := by native_decide`, one per family.
  This is the only evaluator-trusted identity in the glue; it is also cross-checked by the exporter.
- `Bridge/Glue/Sections.lean` (namespace `BoltProof.Glue`, standard axioms): the literal offset theorems, by
  `decide`/`rfl` on list literals: `(SimpleMulti.suffix.drop 528).take 29 = Gadgets.parityCheck`,
  `(MinSimple.suffix.drop 534).take 13 = Gadgets.nftTypeSel 0x17`, `boundCheck` at 610/621, `mergeGuard` 672,
  `splitGuard` 687, `mergeSettle` 781, `splitSettle` 935, `nullTail` at 4648 (SimpleMulti), 1072 (MinSimple),
  1094 (AuthBOLT), 1232 (SerialBOLT), and the suffix lengths 4700/1123/1145/1283.
- Optional: `framedB` (fuel = length, structural) with `framedB_eq_framed`, so `framed cNN = true` is `decide`.
- **Probe vectors** for Finding 1, in the exporter with expectation `valid` (all confirmed, see Finding 1): a melt
  whose transaction carries a covenant-shaped output; a commit whose single change output is covenant-shaped; a
  commit whose `changeOutput` blob carries two outputs; the same with one of them covenant-shaped. A fifth vector
  pins the Finding 3 probe (`smb_probe_type27_commit`, an off-genesis transfer commit with `nextTxoType = 0x27`
  (undefined), `SCRIPT_ERR_EQUALVERIFY`) so the type-derivation fact stays regression-tested.

### 4.2 Symbolic-execution infrastructure (M2), `lean/BoltProof/Bridge/Glue/Sym/`, namespace `BoltProof.Glue`

- `Basic.lean`: `GOut.IsOk`; `structure EnvOK env` (post-Genesis UTXO, `requireMinimal = false`, MINIMALIF off,
  Chronicle, forkid, `checksigData = none`; field names from bsv-script-lean's `Flags`), with `envOK_phase2` for the
  Chronicle `params` (by `decide`/`simp [params, derive]`; fallback: one `native_decide` fact in `BoltProof.Bridge`).
  Every symbolic theorem is abstract in `env` under `EnvOK env`.
- `Steps.lean`: about 45 inversion lemmas, one per opcode the suffixes use: pushes (`OP_0`, one byte, `n` bytes for
  the widths used: 1, 2, 3, 4, 8, 16, 20, 30, 33, 35, 36), `OP_1`–`OP_16`, `DUP`, `DROP`, `NIP`, `OVER`, `SWAP`,
  `TUCK`, `ROT`, `2SWAP`, `2DROP`, `IFDUP`, `PICK`, `ROLL`, `SIZE`, `CAT`, `SPLIT`, `NUM2BIN`, `BIN2NUM`, `EQUAL`,
  `EQUALVERIFY`, `VERIFY`, `NOT`, `0NOTEQUAL`, `BOOLAND`, `BOOLOR`, `1ADD`, `1SUB`, `ADD`, `SUB`, `MOD`, `LESSTHAN`,
  `LESSTHANOREQUAL`, `GREATERTHANOREQUAL`, `HASH160`, `HASH256`, `SHA256` (opaque function applications),
  `TOALTSTACK`, `FROMALTSTACK`, `IF`/`NOTIF` on a symbolic value (`cond := C.opIf (castToBool x)`), `ELSE`,
  `ENDIF`, `CHECKSIG`/`CHECKSIGVERIFY` generic in `env.ctx.checkSig` (with `scriptCodeOf_phase2 : scriptCodeOf env
  st = st.codeSep` under Chronicle in phase 2). Proof pattern, reusing the `step_simp` set of
  `Gadgets/Steps.lean`: `rw [run.eq_2] at h; step_simp at h; split_ifs at h <;> simp_all [GOut.IsOk]`.
  `castToBool_iff_decode_ne` reconciles `OP_IF` on the raw `txoType` with the `BIN2NUM`-derived flags;
  `decode_lit`/`decode_lit2` replace the ad-hoc `decode_1a`-style table.
- `Skip.lean`: `balancedB` (IF/NOTIF open, ENDIF closes, ELSE needs depth > 0) and one lemma
  `inv_skip_balanced : C.isActive = false → balancedB g = true → run (g ++ k) t st = r → r.IsOk → ∃ m' k', run k t
  {st with memUsed := m', opCount := k'} = r`, by strong induction on `g.length`, generalised over the nesting depth
  with the `Cond` lemmas of `Parity.lean`. It subsumes every per-opcode skip lemma.
- `Loops.lean`: lemmas over `List.flatten (List.replicate n body) ++ k`, by induction on `n`, instantiated by `rfl`:
  `OP_1 OP_SPLIT`×n, `OP_SWAP OP_CAT`×n, `OP_DUP OP_0NOTEQUAL OP_SPLIT`×n, `d OP_PICK`×n / `OP_CAT`×(n−1) with the
  closed form `concatPieces`, and the 16× `OP_SIZE 10 OP_LESSTHAN OP_IF 00 OP_CAT OP_ENDIF` pad (`padTo16`).
- `Tactic.lean`: `sym_step` (dispatch on the head byte to the matching `inv_*`, then `sym_norm`, a `simp only` with
  `List.cons_append`, `take`/`drop`, `getD_cons_*`, `getD_append*`, `decode_lit*`) and `sym_run := repeat sym_step`.
  Facts accumulate as anonymous hypotheses; a block lemma closes with `refine ⟨…⟩ <;> assumption`.
- Elaboration control: blocks of at most ~150 instructions; the ancestor-piece lists stay abstract (`ps : List
  Bytes`, `ps.length = 26`; a `PICK` into them yields an opaque `ps.getD j []`), so the stack literal stays about 40
  entries (NFT) or 30 plus opaque (fungible); one family spread over several files so `lake` elaborates in
  parallel; `maxHeartbeats` per heavy file. **M2 exit criterion: the 389-byte OP_PUSH_TX block elaborates in
  acceptable time.** A computable fuel evaluator (`runB`) is not planned: the stacks are symbolic, and constant
  folding is already `decide`-able.

### 4.3 MinSimpleBOLT block lemmas and `Enforced` (M3), `Bridge/Glue/MinSimple/`

`Spec.lean`:
- `Fields` (pkh, commitment, txoType, parent, gp, issuer) with `WF` (widths 20/20/1/36/36/33, `txoType` is
  `[0x00]` (settle) or `[0x21]` (commit)); `pushesOf f` (the six lock pushes).
- `Args` (preimage, pubKey, sig, benefPKH, changeOutput, fundOutpoint, 26 ancestor pieces);
  `entryStack f a below` = `[issuer, gp, parent, txoType, commitment, pkh, preimage, pubKey, sig, benefPKH,
  changeOutput, fundOutpoint] ++ pieces ++ below` (top first; `below` is whatever the unlocking script left
  underneath, where AuthBOLT's `authOrMiscData` lives).
- `isGen := decode parent = 0`, `hasGp := decode gp ≠ 0`, `isSettle := castToBool txoType = true`.
- `Preimage` (version, hashPrevouts, hashSequence, outpoint, scriptCode, value, sequence, hashOutputs, lockTime,
  sighashType) and `Preimage.bytes` with the `fd` scriptCode varint the bytes assume; `pushTxKey`
  (`038ff83d…`); `pushTxSig : Bytes → Bytes`, the DER the 28–413 block assembles from `hash256 preimage`;
  `expectedOutBytes f a p` (the L2 build, by case on `isSettle`/`isGen`); `rebuiltRaw ps` (the L3 assembly).

`structure Enforced (ctx : Context) (lock : Bytes) (f : Fields) (a : Args) : Prop`:
- `preimage`: ∃ p, `a.preimage = p.bytes` ∧ `p.scriptCode = lock` ∧ sighash type `0x41` ∧ `2 ≤ decode p.version` ∧
  `decode p.value = 1` ∧ `p.hashOutputs = hash256 (expectedOutBytes f a p ++ a.changeOutput)` ∧
  `p.hashPrevouts = hash256 (p.outpoint ++ (if isSettle ∧ hasGp then gpTxid ++ [1,0,0,0] else []) ++ a.fundOutpoint)`;
- `pushTx : ctx.checkSig (pushTxSig a.preimage) pushTxKey lock true = true`;
- `rebuild : isSettle f ∧ hasGp f → hash256 (rebuiltRaw a.pieces) = gpTxid f`;
- `null : ¬ (isSettle f ∧ hasGp f) → ∀ x ∈ a.pieces, x = []`;
- `issuer : isGen f ∨ (¬ hasGp f ∧ decode f.txoType ≠ 0) → a.pubKey = f.issuer`;
- `sigType : a.sig.getLast? = some 0x41`; `owner : hash160 a.pubKey = f.pkh`;
- `ownerSig : ctx.checkSig a.sig a.pubKey lock true = true`.

`EnforcedMelt` is `issuer`, `sigType`, `owner`, `ownerSig` only (the 1104–1122 path; outputs unconstrained).

Thirteen block lemmas, one per section, each `∀ k`, concluding `∃ m' k', run k t {…} = r` plus the section's facts:
B0 prologue (also corrects Finding 2 in Lean: the flag is `hasGp`), B1 gate (case split on `castToBool preimage`),
B2 OP_PUSH_TX (loop lemmas + `inv_checksigverify`; yields `pushTx`), B3 preimage split (yields `preimage =
p.bytes` and the type byte), B4 version, B5 scriptCode split (yields `value = 1`; the suffix goes to the altstack),
B6 output build per path with the selector handled by `inv_if` on the raw `txoType`, B7 rebuild condition, B8
rebuild (yields `rebuild`), B9 null (pick/cat loop + `nullTail_inv`), B10 hashPrevouts, B11/B11′ sig byte (main /
melt), B12 owner check.

**The literal reviewer ask** is stated and proved here as `reaches_*` theorems, one per fragment, of the form
`run (c00 ++ … ++ (Gadgets.nftTypeSel 0x17 ++ k)) t st = r → r.IsOk → ∃ st₁ s acc, st₁.stack = acc :: s ∧
s.getD 23 [] = f.txoType ∧ 23 < s.length ∧ run (Gadgets.nftTypeSel 0x17 ++ k) t st₁ = r`: `reaches_nftTypeSel`,
`reaches_nullTail` (NFT), and in M5 `reaches_parityCheck` (`s.getD 26 [] = txoType ∧ s.getD 37 [] = nextTxoType ∧
37 < s.length`), `reaches_boundCheck_610`, `reaches_boundCheck_621`, `reaches_splitGuard`, `reaches_mergeGuard`,
`reaches_mergeSettle`, `reaches_splitSettle`. Each discharges exactly the stack-shape hypotheses of the existing
fragment lemma.

The fragment `_inv` corollaries live beside the originals in `Gadgets/`: `nullTail_inv`, `parityCheck_inv`,
`boundCheck_inv`, `mergeSettle_inv`, `splitSettle_inv`, `splitGuard_inv`, `mergeGuard_inv`, and `nftTypeSel_inv`
on `castToBool (s.getD n [])`, of which `nftTypeSel_run_commit` / `nftTypeSel_run_settle` become corollaries.

`Suffix.lean`: `minSimple_sound : EnvOK env → WF f → run (pushesOf f ++ Generated.MinSimple.suffix) []
{stack := argsStack a ++ below, alt := [], cond := {}, codeSep := pushesOf f ++ suffix, …} = r → r.IsOk →
∃ st', r = .next st' ∧ st'.cond = {} ∧ (a.preimage ≠ [] → Enforced env.ctx lock f a ∧ st'.stack.head? = some
(encode 1)) ∧ (a.preimage = [] → EnforcedMelt env.ctx lock f a ∧ …)`. Five paths (melt; settle/commit × genesis ×
grandparent). No symbolic converse is planned; §4.5 guards against vacuity.

### 4.4 Refinement to Layer 1 (M4), `Bridge/Glue/Refine/`

- `Verify.lean`: `verifyScript_valid_iff : Eval.verifyScript params ctx sig lock = .valid ↔ ∃ st1, evalScript …
  sig [] 0 = (.ok, st1) ∧ lock.length ≤ maxScriptSize ∧ ∃ st2, run … lock [] {stack := st1.stack, memUsed :=
  st1.memUsed, codeSep := lock} = .next st2 ∧ st2.cond.empty = true ∧ castToBool st2.stack.head = true`, by
  unfolding `verifyScript`, `phase2`, `evalScript`, `loop_eq_run` and `phase2_stack_mem_only`; the concrete flag
  facts by `decide` (fallback: a native identity in `BoltProof.Bridge`).
- `Abs.lean`, `Spend.lean` (`Txid := Bytes`): `decodeLock fam : Bytes → Option (Token Bytes)` (fixed-width pushes,
  remainder must equal the family suffix; 36 zero bytes ↦ `none`) with its inverse `lockOf`; `outOf fam : TxOut →
  Out Bytes` (pay-to-proof template ↦ `.proof`, p2pkh ↦ `.p2pkh`, a decodable lock at value 1 ↦ `.token`, else
  `.other`); `absTx fam : Tx → TxDesc Bytes`; `spendOf fam tx i lock S : Option (Spend Bytes)` (kind: empty
  preimage ↦ melt, else by the NFT flag / fungible parity; mode from `nextTxoType` or `modeOfCommitType`; `anc :=
  (decodeTx (rebuiltRaw ps)).map absTx` when the rebuild fires; `sigHashType := sig.getLast`; `spentOutpoint` from
  `tx.inputs[i]`).
- `Serial.lean`: `serializeTx`, `serializeOutputs`, `encodeVarInt`, `decodeTx_serializeTx`,
  `serializeOutputs_prefix_cancel`, and `sighash_eq : Sighash.sighash sc tx i ⟨0x41⟩ amt true = hash256
  (preimageOf sc tx i amt).bytes`, matched field by field with the upstream builder.
- `Crypto.lean`, the residual assumptions, each stated once:
  - `PushTxSound : ∀ pre dig, Secp256k1.verify pushTxKey (pushTxSig pre).dropLast dig = true → hash256 pre = dig`.
    This is the ECDSA algebra for the fixed key (`r = Gx`, `s = z + 1`) plus second-preimage resistance of
    hash256 (the other root `z' ≡ −z − 2 (mod n)` and the high-`s` mirror). The secp256k1 algebra is out of scope
    and is *stated*, not proved.
  - `Hash256CR : ∀ a b, hash256 a = hash256 b → a = b` (the Assumption 1 idealisation, as `CollisionFree`).
  - `GpReal f`: the grandparent outpoint names a real transaction (`spent_live` in a `Run.Valid`).
  - `HonestOutputs fam s`: melt outputs are P2PKH-only, and outputs beyond `expectedOuts` are non-token (Finding 1).
- `MinSimple.lean`, **Option B** (no Layer-1 change): `minSimple_refines (P : Prims Bytes) … : run … = .next st' →
  st'.cond.empty → castToBool top → (P agrees pointwise with hash160, Secp256k1 verify, this spend's sighash and the
  rebuilt transaction's hash256) → PushTxSound → Hash256CR → GpReal f → (spendOf … = some s → HonestOutputs .nft s)
  → ∃ s, spendOf .minSimple tx i lock S = some s ∧ Accepts P .nft s`, plus the corollary through
  `verifyScript_valid_iff` and `txContext`. Proof outline: `Enforced.pushTx` + `txCheckSig` + `PushTxSound` give
  `hash256 preimage = sighash`; `Hash256CR` + `sighash_eq` make the parsed preimage the real one (`input_is_spent`,
  `version`, `l1_type`, the value); `hashOutputs` + collision resistance + prefix cancellation give `l2_outs` (the
  change half via `HonestOutputs`); `rebuild` + `GpReal` + collision resistance + `decodeTx_serializeTx` give
  `l3_rebuild`, `null` gives `l4_null`; `owner`/`ownerSig` give `l1_owner`/`l1_sig`; `issuer` gives `l5_issuer`
  (`issuerMustSign .nft` is exactly `isGen ∨ (txoType ≠ 0 ∧ gp = none)`); the type clauses follow from `WF`.
- **Option A** (follow-up; needed to compose the per-input theorems into one `P` for a whole run, i.e. to
  instantiate Theorems 1–5 on a real chain): make `TxDesc` lossless and canonical (`Out.p2pkh pkh value`,
  `Out.other script value`, inputs with scriptSig and sequence), `Prims.sighash : Spend → Msg`, `CollisionFree` on
  canonical descs, a computable `P_fam`, and `Hash256CR → CollisionFree P_fam` as a theorem. Touches about nine
  `.inputs` uses (Covenant, ProofGating), three `sighash` uses (Ownership), and about 23 `Out` constructor uses
  (Theorems, Example). One to two weeks, on its own branch, after the pilot.

### 4.5 Regression and vacuity guards (M4), `Bridge/Glue/Regress.lean`, namespace `BoltProof.Bridge.Glue`

`Vec.spendOf v i` (decode the vector, run phase 1 with `evalScript`, then `spendOf`); one `native_decide` theorem
per honest vector pinning `(kind, mode, anc.isSome, sigHashType)` and `tx.outputs.take n = expectedOuts`; optionally
emitted by the exporter, which knows kind and mode when it builds each transaction. One end-to-end instance per
family: `check_*` (native) composed with `*_refines` gives `Accepts` for a concrete vector under the universal
hypotheses. These show the `argsStack` shape hypothesis is met by real spends, so `*_sound` is not vacuous.

### 4.6 SimpleMultiBOLT (M5), AuthBOLT and SerialBOLT (M6)

- SimpleMultiBOLT (4700 B, 3611 instructions, 125 `OP_IF`, entry stack depth 176): `inv_pushEncode d` for the
  per-piece `SIZE == n` push-encoding in the rebuilds (applied 75 times per rebuild; the section table is cut per
  piece so each application is a chunk equality by `rfl`); `inv_rebuild (base)` shared by rebuild A (pieces at
  depths 101–175, txid compare at 2637, balance anchor 2660–2706) and rebuild B (26–100, 3815, 3835–3881);
  `inv_pad16_loop` twice; balance-by-mode proved per (transfer/split/merge × commit/settle), plugging
  `mergeSettle_inv`, `splitSettle_inv`, `splitGuard_inv`, `mergeGuard_inv` and `boundCheck_inv` at the reached
  depths and `parityCheck_inv` at 528; the varint arms `ff`/`fe`/`fd` of the preimage parse (441/451/461).
  `Enforced` adds parity (`Fam.edge .fungible`), bounds, mode flags, the welded balance fields
  (`settledBalance`/piece/merged sum), the L5 guard of Finding 3, merge input order, and the balance anchor. For a
  merge the per-input theorem takes "the other token input's run also accepted" and derives `other_settle_typed`,
  `l_merge_same_issuer` and `other_input` from the other input's `Enforced` (as the
  `smb_cross_issuer_merge_commit#1` vector shows, those clauses are enforced by the other covenant).
- AuthBOLT = MinSimpleBOLT plus `authOrMiscData` under `below` and the `SIZE < 0x4c` guard, 27 pieces;
  SerialBOLT = 8 lock pushes (genesisOutpoint and mintData first), the 39-byte prologue, selector depth `0x18`,
  the mintData rules. The NFT blocks are parameterised by a `Layout` record (nPieces, extraBelow, selDepth, …) from
  the start of M3 so M6 is instantiation, not re-proof.

## 5. The spec-gap decision (gate at the end of M1)

Finding 1 must be resolved for `*_refines` to be true. Two routes:

- **Explicit hypothesis.** Keep `Accepts` as it is and add `HonestOutputs` to the refinement theorem, documented as
  the residual the recipient's off-chain check (`docs/verification-scaling.md`) discharges. Cheapest; makes the gap
  precise instead of hidden.
- **Model change.** Drop `l2_melt`, weaken `l2_outs` to a prefix statement, define `Spend.produced` from
  `expectedOuts` rather than `tx.outputs` (tokens carried in the change blob become fabrications outside the run,
  the way covenant-less tokens are treated in the Theorem 5 note), and re-check Theorems 1, 3 and 5. One to two
  weeks on top of the glue work.

The real fix (parse `changeOutput`; constrain melt outputs) is in the bytes and out of scope here. The M1 probe
vectors decide whether the finding holds by execution; the route is chosen then and recorded in `lean/README.md`.

## 6. Repository integration

- Directory `lean/BoltProof/Bridge/Glue/` (so the audit script scans it). Namespaces: `BoltProof.Glue` for
  everything symbolic (Layer-1 rules), `BoltProof.Bridge.Glue` and `BoltProof.Bridge` for the native identities
  only. Use the `theorem` keyword and column-0 `namespace`/`end` lines, which the audit script requires. Add the
  top-level theorems (`*_sound`, `*_refines`, the `reaches_*` set) to `lean/AxiomCheck.lean`. Act on the reviewer's
  minor point at the same time: have Lean enumerate the Bridge declarations instead of scraping `^theorem`.
- Lake: one umbrella module `BoltProof.Bridge.Glue` imported from `Bridge.lean`; split a `BoltProofGlue` library and
  CI step only if the build passes about 20 minutes. CI today is about 8.5 minutes with a 90-minute timeout; expect
  5–15 minutes of added elaboration, spread over files. Measure with `lake build -v`.
- Exporter: `sections.ts`, `emitChunks`, boundary validation, the two probe vectors, optional `spendOf`
  expectation emission; `npm run lean:vectors` unchanged.
- Documentation at the end (M7): the "What is still trusted" row of `lean/README.md` and its Layout table;
  `lean-proof-todo.md`; `docs/formal-proof.md` §1.6 ("not a symbolic proof over the 5 KB bytecode"); CHANGELOG;
  and the corrections of Findings 2–4 (`NftType.lean` header and `nftFlag` docstring, the README `is2ndTx`
  observation, the 2026-09-02 correction in `formal-proof.md`, the `smb_wrong_key_commit#0` comment).

## 7. Open questions

1. Hypothesis or model change for Finding 1 (§5).
2. Does the token input have to be input 0? The hashPrevouts weld (`outpoint ++ [proof] ++ fundOutpoint`) suggests
   the spent outpoint is first for the NFT family; `fundOutpoint` is itself an unparsed blob, so `tx.inputs` is
   `[spent, (proof)] ++ parse fundOutpoint`. The refinement should derive `i = 0` where the bytes force it rather
   than assume it. For the fungible family (M5) the bytes do force it: `inputIndexN` is only an argument, and
   `hashPrevouts` begins with this outpoint on every path except a merge commit's second token input, where it
   begins with the other token's outpoint `i2` and this one follows (input 1).
4. Undefined next types off genesis (M5). The parity check only requires `nextTxoType` to flip the spent type's
   parity, so a settled token's spend may name any odd byte. Probing a commit to `0x27` or `0x29`, the run leaves
   the six protocol types' paths at the output builder (suffix 1112, where it tests the zero `ogp` push) and then
   runs on a misaligned stack: given the facts it needs (`decode (36 :: x) ≠ 0`, `castToBool (encode 39)`), it
   tests the scriptCode's own suffix bytes as flags at 550 and 580. Whether any such run succeeds is open; the
   SDK probe vector `smb_probe_type27_commit` (an honest-shaped transaction) fails with `SCRIPT_ERR_EQUALVERIFY`.
   Settling it needs the driver to split on an undecided condition and close the failing branches. Until then
   `simpleMulti_sound` covers the six protocol next types and states the restriction.
5. Settle mode against commit type: retracted. An earlier probe of the six mismatched settle pairs (a commit-typed
   token settled into another mode's settled type) reported every run reaching the end with the outputs of the mode
   `nextTxoType` names. Those runs carried the parity check's `OP_EQUALVERIFY` fact `encode (nextTxoType + 1) =
   txoType`, false for every mismatched pair, which the symbolic driver records as a fact without checking it. The
   parity check does enforce `Accepts.settle_mode` (`parityCheck_refuses_commit`), and `SimpleMulti/Refute.lean`
   proves the 24 refused type pairs fail. Every probe is now scanned for false literal facts: the split-flag,
   merge-index, input-index and merge-commit findings carry none.
3. The split settle's flags (§Progress, M5): with `pkh1` or `i2` non-empty the bytes accept a split settle whose
   two tokens are swapped or whose second token carries index byte 0. The balances are the honest ones. Open:
   whether such a token can be spent again (the next spend's rebuild reads its parent's output at the index byte),
   and whether the refinement maps these spends to the model's split settle, needs a hypothesis, or should be
   reported as a covenant defect with a probe vector.

## 8. Milestones and effort

| M | Deliverable (independently mergeable) | Effort |
|---|---|---|
| M1 | Sections table, `emitChunks`, `Generated/Chunks.lean`, native suffix identities, `Glue/Sections.lean` offset theorems, two probe vectors; **spec-gap decision** | 3–4 days |
| M2 | `EnvOK`, `GOut.IsOk`, the inversion step lemmas, `inv_skip_balanced`, loop lemmas, `sym_step`/`sym_run`; fragment `_inv` corollaries; exit criterion: the OP_PUSH_TX block elaborates in acceptable time | 2 weeks |
| M3 | MinSimpleBOLT `Spec`, thirteen block lemmas, `reaches_nftTypeSel`, `reaches_nullTail`, `minSimple_sound` (**the literal reviewer ask closes here**) | 3 weeks |
| M4 | `verifyScript_valid_iff`, `absTx`/`spendOf`/serialisation lemmas, the residual assumptions, `minSimple_refines` (Option B), `Regress.lean` | 2–3 weeks (+1–2 for Option A) |
| M5 | SimpleMultiBOLT sections, piece/pad/rebuild lemmas, about thirty block lemmas, the five fungible `reaches_*`, `simpleMulti_sound`, `simpleMulti_refines` | 4–6 weeks |
| M6 | AuthBOLT and SerialBOLT through `Layout` | 1–2 weeks |
| M7 | Documentation, CHANGELOG, `AxiomCheck.lean`, the Findings 2–4 corrections, audit enumeration | 3 days |

Risks and mitigations: elaboration time (bounded chunks, abstract piece lists, parallel files, measured in M2 before
committing to the design); `decide` not reducing `params`/`derive` or literal `take`/`drop` (env-abstract theorems,
width-specific push lemmas, one native flag identity); further bytes/model mismatches surfacing in M3/M5 (treat each
as a finding with a vector; never weaken a theorem silently); `PushTxSound` remains an assumption; Option A touches
the Theorem 1 and 5 proofs; the CI Mathlib cache and the 90-minute ceiling (the optional separate library keeps the
vector build isolated).

## 9. How to check this plan against the checkout

```sh
# the bytes behind Findings 2 and 3 (first opcodes of each lock suffix)
grep -oP 'LOCK_SCRIPT_SUFFIX: string = "[^"]{0,220}' src/tokens/templates/SimpleMulti.sx.template.ts
grep -oP '(?<!UN)LOCK_SCRIPT_SUFFIX = "[^"]{0,220}' src/tokens/templates/MinSimple.sx.template.ts
# the fragment offsets quoted in §4.1 (python3 -I; reads the hex in Generated/Bytes.lean and searches each literal)
```

## Progress

- **M1** (`Bridge/Generated/Chunks.lean`, `Bridge/Bytes.lean`, `Bridge/Glue/Sections.lean`, `vectors/sections.ts`):
  as planned, plus a cut at the end of each lock's own `OP_PUSH_TX` block (`EXTRA_CUTS`) so M3 can name that block;
  the five probe vectors of §8 confirm Finding 1 and refuse `0x27` (§7).
- **M2** (`Bridge/Glue/Sym/`): as planned, except that the general skip lemma over `balancedB` was replaced by
  generated per-opcode inactive lemmas (`SkipSteps.lean`) walked by `sym_skip`, and the loop lemmas of
  `Loops.lean` were not needed: `sym_all` runs the whole `MinSimpleBOLT` suffix (about 860 instructions) in
  under two minutes per path, so blocks are not cut by hand.
- **M3** (`Bridge/Glue/MinSimple/`): `minSimple_sound`, `reaches_nftTypeSel` and `reaches_nullTail` are proved
  (`Sound.lean`). Deviations from §4.3: the theorem starts at the suffix with the six pushed fields on the stack
  (`Fields.stack`; the lock pushes and the `lockOf` decoder belong to M4), the preimage fields are `take`/`drop`
  accessors rather than a `Preimage` record, and the lock's `OP_PUSH_TX` block is abstracted to `PushTxReached`
  (it ran without failing from the preimage on top: `PushTx.lean`, by the library's `run_append`) instead of a
  `pushTxSig` term, so M4's `PushTxSound` is to be stated about that block run. There are no thirteen block
  lemmas: eleven whole-suffix path theorems (`Paths/`), one per combination of type, genesis, grandparent and
  preimage presence, each a `sym_all` run that stops at the block and at the two fragments to record `Reached`,
  and closes `Enforced` from the facts the run leaves. The `reaches_*` theorems say the fragment literal itself is
  executed from the stack its `Gadgets/` lemma assumes (depth 23 for the type byte, the concatenated pieces on
  top for the null tail), so the `_inv` corollaries were not needed. Two more byte-level findings: the covenant
  never checks the `fd` of the preimage's scriptCode varint (it drops the byte at 104 and reads two length bytes),
  and a settle at genesis takes the signing key as the new token's issuer push (suffix 559–569), like a commit.
- **M4, the refinement** (`Bridge/Glue/Refine/`, `Bridge/Glue/MinSimple/Abs.lean`): `minSimple_refines` is proved
  (`Refine/MinSimple.lean`): a spend of a `MinSimpleBOLT` token that `Eval.verifyScript` judges valid under the
  judging parameters, read into the model by `spendOf`, satisfies `Accepts P .nft`, under `Residual`: `PushTxSound`
  (stated about the block run, as M3 left it), second-preimage freedom of the four byte strings the spend hashes
  (A1 stated on the spend's own data: a global injectivity of `hash256` is false, and a theorem assuming it empty),
  `GpReal` (the named grandparent is a real, well-formed transaction with the token at the named index and a proof
  output at index 1, whose abstract id the primitives agree on; the run-level argument discharges it), `Agrees`
  (the primitives compute `hash160` and this spend's `OP_CHECKSIG`), and `HonestOutputs`/`HonestMelt` for
  Finding 1. Route B, with one representation change in Layer 1: a settle-typed token's commitment is `zeroPKH`
  (the twenty zero bytes the bytes write) rather than `[]`, so the abstraction of the new lock is the model's
  `settleToken` byte for byte. `Refine/Verify.lean` reads the verdict (`run_of_valid`, `envOK_phase2`),
  `Refine/Serial.lean` round-trips the node's serialisation (`decodeTx_serTx`, `readTxOut_serTxOut`,
  `preimage_fields`), `Refine/Weld.lean` reads the covenant's output templates as the model's locks, and
  `Refine/Facts.lean` discharges the twenty-six clauses from the facts. Three more byte-level findings: the melt arm
  checks neither the version nor anything about the outputs (so `version` joins `l2_melt` among the clauses a melt
  does not enforce; `HonestMelt` carries both); the recipient hash and, at genesis, the signing key are copied into
  the new token's pushes without a width check (`ArgsWF`); and only the txid half of `grandparentOutpoint` is bound
  by the rebuild (the index half is `GpReal`'s). The guards of D6 are `Bridge/Glue/Regress.lean`: the five real
  `MinSimpleBOLT` spends read through `spendOf` have the kinds, sighash bytes, output shapes and ancestors the model
  expects, and `minSimple_refines` applies to the first commit, the second settle (with its rebuild) and the melt,
  every decidable hypothesis checked on the vector's data, so `Accepts` follows for them from `Residual` alone.
  Open from M4: Option A (a lossless `TxDesc`), for the run-level composition.
- **M5, first step** (`Bridge/Glue/SimpleMulti/`): `Spec.lean` (the eleven lock fields in push order, `balance`,
  `balanceCommit`, `pkh`, `com`, `com2`, `ogp`, `ty`, `outIdx`, `parent`, `gp`, `issuer`, and the fifteen unlocking
  arguments above the 150 ancestor pieces), `PushTx.lean`, and `Reaches.lean`: `prologue` (the issuer guard
  `parent = 0 ∨ gp = 0`, by cases) and `reaches_parityCheck`, `reaches_boundCheck_610`, `reaches_boundCheck_621`,
  `reaches_mergeGuard`, `reaches_splitGuard`, `reaches_mergeSettle`, `reaches_splitSettle`: the run reaches each
  fragment with the stack its `Gadgets/` lemma assumes (the type bytes at depths 26 and 37; the balance at 39 and
  the bound at 4; `nextBalanceCommit` at 45; the balance at 45, the other balance at 51 and the bound at 10; the
  balance at 47 and the carried balance at 46), each a prefix run of at most 400 instructions. The driver now
  evaluates integer literals (`Int.reduceTMod`, …) and the empty push. Findings: the fungible parse accepts every
  varint width of the scriptCode (`ff`/`fe`/`fd`/one byte), so the symbolic run takes the `fd` byte as a hypothesis;
  the issuer guard reads pushes 8 and 9 (`parent`, `gp`), as §3 says. Next: the full paths (the two pad-to-16
  loops and the sixty width-dependent optional pushes of the rebuilds need block lemmas or width hypotheses,
  §4.7), `simpleMulti_sound`, and the refinement.
- **M5, second step** (the fungible rebuild's blocks): three pieces of the `SimpleMultiBOLT` suffix branch on the
  ancestor's data rather than on the arguments, so no path hypothesis decides them: the pad-to-16 loop after a
  balance sum or difference (`SIZE 16 LESSTHAN IF 00 CAT ENDIF` sixteen times, suffix 797 and 950), the
  width-dependent optional push of an ancestor piece inside the rebuilds (`SWAP SIZE ROT EQUAL IF SIZE SWAP CAT
  ELSE DROP 00 ENDIF CAT`, fifty times), and the balance anchor on the ancestor's type (2660 and 3835). The
  exporter now cuts every occurrence of such a literal as its own chunk (`sections.ts`, the `auto` landmarks, with
  the occurrence count checked), `SimpleMulti/Blocks.lean` reads each chunk as one step whose result is a function
  of the stack (`padN 16`; `optPush w p`, the piece push-encoded when its size is `w`, else `OP_0`; the predicate
  `AnchorOK`, the three arms' balance relations) together with a skip lemma for the chunk inside an inactive arm,
  and the drivers gained the hooks `sym_block`/`sym_skipblock` (`Sym/Tactic.lean`): at a folded chunk, `sym_all`
  and `sym_skip` try the rules registered by `macro_rules` next to the block lemmas, so a path proof keeps these
  chunks folded and never cases on the ancestor's shape. The hooks fire only when the program is syntactically a
  constant appended to a tail: unifying a block lemma's `c ++ k` against a bare variable makes the unifier unfold
  `List.append` and does not return. The 150 ancestor pieces are now explicit in the fungible `Args` (`Pieces75`
  twice, `psA` above `psB`), so the rebuilds' `PICK`s resolve on the literal stack; `Reaches.lean` is regenerated
  for the new chunk set (the pad loop inside the skipped merge-settle arm of `reaches_splitSettle` is stepped over
  by its skip lemma).
- **M5, third step** (the rebuilds' conditional arms and the first full fungible paths): the two rebuilds also
  branch on the ancestor's data in four whole arms (the rebuilt transaction's second input, suffix 1961–2425 and
  3186–3621; its second output, 2591–2607 and 3773–3788) and in two conditional counts (`IF 3 ELSE 2 ENDIF`,
  `IF 4 ELSE 3 ENDIF`). The counts are landmarks with block lemmas (`ite32_shape`, `ite43_shape`, `Blocks.lean`);
  each arm is read as one step by `SimpleMulti/Arms.lean`, generated from an isolated symbolic run of the arm on an
  abstract stack: the flag popped, the accumulator extended by the arm's bytes (`secondInA`, `secondOutA`, …, with
  `rest[n]?.getD []` the item at depth `n` below it) under the widths its `OP_NUM2BIN`s fix and the size bounds it
  checks, else unchanged. A folded flow chunk's rule is keyed by its full name (`c1961_if`). The driver also reads
  two-byte script-number literals (`decode_lit2`, the rebuilds' `PICK` depths past 127) and the truth of a byte
  string by its tail (`castToBool_append_of_right`: the covenant tests a built output with `OP_IF`). Full paths now
  run end to end without case analysis on the ancestor's shape: a commit from a settled transfer token
  (`ty = 0x20`, `nty = 0x21`, 2334 instructions) and into a split (`nty = 0x23`, 2315) leave the facts the fungible
  `Enforced` will state: version, sighash byte, the one-satoshi value, the balance bounds, the split guard
  `bal − nbc ≥ 0`, `hashOutputs` over the new token (the old balance push, `balanceCommit` zero or `nbc`, the old
  owner, `com = pkh1`, `com2 = pkh2` for a split, `ogp` zero, the next type, this outpoint, the old parent, the
  issuer, the suffix) and the tagged pay-to-proof outputs, the 150 pieces empty, `hashPrevouts` over this outpoint
  and the funding outpoint, the sighash byte of the signature and the owner's hash. Findings: a commit, not a
  settle, is what rebuilds the ancestors in this family (the gate at 1419 is "spent type odd and `gp ≠ 0`", so the
  even types are the settled states and the odd ones the commits, the reverse of the NFT family's `0x00`/`0x21`);
  the token's input index (`inputIndexN`) decides the prevouts order at 1149–1416 and is a path hypothesis.
- **M5, fourth step** (`Enforced` and the commit paths): `SimpleMulti/Enforced.lean` is the fungible family's
  vocabulary, as `MinSimple/Spec.lean` is the NFT family's: the spent lock's pushes read off the scriptCode in the
  preimage (`scBalPush`, `scPkhPush`, `scComPush`, `scParentPush`, `scIssuerPush`, `scSuffix`), the new token's lock
  (`commitLock`, by the next type: `balanceCommit` zero, `nbc` for a split or a merge; `com = pkh1`; `com2` zero or
  `pkh2`; `ogp` zero or the other lineage's outpoint `i1` for a merge; `settleLock` for a settle), the outputs a spend
  hashes to (`expectedOuts`: the token output with its `fd` varint and a tagged pay-to-proof output per recipient),
  the 150 pieces concatenated (`nullCat`), and the structure `Enforced`: the `OP_PUSH_TX` block, version, sighash
  byte, the one-satoshi value, the four balance bounds, the split and merge guards, `hashOutputs`, the null pieces,
  `hashPrevouts` over this outpoint and the funding outpoint, the issuer guard, the owner's hash, the signature's
  sighash byte and the two encodings. The path theorems close by `enforced_normF` (the flags as propositions, the
  zero widths substituted, the appends right-nested on both sides) and `factF` (reducible matching), exactly as the
  NFT family's, and `gen_sm.py` generates them: `Paths/Commit{Transfer,Split,Merge}.lean`, the nine commit spends
  (each settled type into each commit type) with the token at input 0, one run of about 1850 instructions each.
  Still to probe: the split and merge settles (their runs stop on `pkh1`, reused as a flag, and on the spent lock's
  `outputIndexN`), the no-grandparent settles, the token at input 1 (`inputIndexN ≠ 0` flips the prevouts), the
  genesis variants and the melt; the settle spends also need the rebuild clause (the first rebuild's term over `psB`
  with the arms' widths, as the transfer settle's probe gives it).
- **M5, the path proofs' size (finding):** a full fungible path theorem (one symbolic run of about 1850
  instructions on a stack of some 230 explicit items, the 150 pieces among them) elaborates in five to six minutes
  and peaks at 8 GB of memory, since every step's state is retained in the proof: four such files in parallel
  exhaust a 16 GB runner (two were killed), and the thirty-odd paths the family needs would not fit the CI budget.
  The remedy is the arm lemmas' pattern applied to the whole rebuild-or-null conditional (suffix 1425–4652): one
  block lemma on an abstract stack, keyed by its first chunk (`c1425_if`), proved once by cases on the gate, the
  merge gate and the spent lock's output index, whose facts read the pieces as `T[n]?.getD []`; a path then runs
  only its prefix (suffix 423–1424, with the pieces folded) and the epilogue, and the block's facts are instantiated
  on its explicit stack. Done as three regions rather than one block (`SimpleMulti/Regions.lean`, generated from
  isolated runs on an abstract stack `t0 :: T`): the first rebuild with its anchor (suffix 1426–2714, key `c1426`,
  eleven widths, thirteen facts, the merge flag left on top), the second rebuild's arm (2715–3896, key `c2715_if`,
  three cases: the merge flag off, on with the spent lock's `outputIndexN` zero, on with it non-zero) and the null
  arm (3899–4651, key `c3899`, the 150 pieces at depths 62–211 of `T` concatenate to nothing, the stack unchanged);
  the gate at 1425 and the merge flag at 2714 stay with the path, whose type hypotheses decide them. The path
  theorems then run their prefix with the pieces folded (`a.psA.stack ++ (a.psB.stack ++ S)` never unfolded, the
  prefix's deepest `PICK` is 61), step over the regions by their rules, and run the epilogue; the regions' facts are
  instantiated on the explicit stack by `enforced_normF`. The region lemmas' statements name their stack items
  through a reducible accessor (`item T n`), since a nine-kilobyte statement that spells `T[n]?.getD []` a hundred
  times spends twenty seconds in instance resolution; with it the whole region file compiles in two minutes. Two
  generator defects found on the way: the branches of a many-case proof must not share named holes, and each case's
  `OP_NUM2BIN` widths need their own names, or the later binders shadow the earlier. With the regions folded a
  commit path is 628 instructions and one block step, and a file of three such theorems builds in about 100 s;
  the nine commit paths are in the tree (`Paths/Commit{Transfer,Split,Merge}.lean`, pushed with `Enforced.lean` and
  `Regions.lean`). Next: the settle paths on the same design (their prefix stops at the gate, the regions' facts
  supply the rebuild clause), the no-grandparent settles, the genesis and input-1 variants, the melt,
  `simpleMulti_sound`, and the refinement.
- **M5, fifth step** (the settle paths): `SimpleMulti/Settle.lean` proves the three settle spends of a token
  with a grandparent at input 0: transfer (`0x21` into `0x20`), split (`0x23` into `0x22`, with `pkh1`, reused as a
  flag, and `i2` zero) and merge (`0x25` into `0x24`, with the spent lock's `outputIndexN` zero). `EnforcedSettle`
  keeps `Enforced`'s prefix clauses and replaces the commit clauses by the settle ones: the carried balance
  non-negative (split and merge), the split's remainder non-negative, the merge's sum within the bound, the settled
  token (two for a split) and the change hashing to `hashOutputs`, and the rebuild clause. The rebuild clause reads
  the regions' facts on the stack at the gate (`gateT`, by mode, the stack the probe gives): the first rebuild's
  thirteen facts, the second rebuild's facts under the merge flag and the spent lock's output index, and
  `hashPrevouts` over this outpoint, the outpoints the rebuilds derive (`gpOutA`, `gpOutB_1/2`) and the funding
  outpoint. Each path is one run of about 625 instructions with two or three block steps; the file builds in about
  100 s. Three closing findings: a normaliser that runs `simp (config := {decide := true})` at every hypothesis
  hangs, because it tries to evaluate the run hypothesis and the hash equations (the flags it was needed for reduce
  by `castToBool_nil`/`castToBool_one`); the gate stack keeps unfused drops (`drop 41 (drop 246 _)`) that the driver
  fused in the facts, so the normaliser carries `List.drop_drop` and the literal-arithmetic simprocs, which
  `simp only` does not include by itself; and `simp` keeps an `if`'s decidability instance under a cast when it
  rewrites the condition, so a rebuilt outpoint's instance still names an unread gate-stack item, and the run's
  facts are equations in `Bytes` where `simp` rebuilds the goal's in `List Nat`. Both are invisible in printed goals
  and defeat reducible matching; `factD` closes such an equation by the one hypothesis with the same right-hand side,
  matched at default transparency. The generators (`gen_sm.py`, `gen_region.py`, `gen_settle.py`) and the probe
  harness still live outside the tree; M7 adds them under `lean/scripts/`.
- **M5, sixth step** (the settles without a grandparent): with `gp = 0` the gate at 1419 sends the run through
  the null arm (3899–4651), so `EnforcedSettle0` has the 150 pieces empty and `hashPrevouts` over this outpoint
  and the funding outpoint, and otherwise the same clauses as `EnforcedSettle` (the settle outputs are the same
  terms: the probes' output equations agree character for character). `settle0_21/23/25` are runs of about 625
  instructions with one or two block steps. The merge settle needs no output-index hypothesis without a
  grandparent (the index only selects the second rebuild's case); the split settle still branches on `i2` and
  `pkh1` (its run stops at 512 without them), so those values stay fixed for now.
- **M5, the split settle's flags (finding):** the split settle reads two unlock arguments as flags that the bytes
  leave to the spender: `pkh1` (the run's condition at 542) and the second interop slot `i2` (at 512). The honest
  spend has both empty. Probing the other three cases, every run reaches the end, and the outputs are the same two
  token outputs in all four: the remainder `bal - balCommit` to the first commitment (`splitOutA`) and the
  committed balance to the second (`splitOutB`). A non-empty `pkh1` puts the second token first; a non-empty `i2`
  writes 0 instead of 1 into the second token's output-index byte (`splitIdx`). No balance is created or lost in
  any case, but a settled token can carry an index byte that is not its output position. `settleOuts_22` now states
  the outputs for all four cases, and `settle_23`/`settle0_23` case on both flags instead of assuming them, so the
  split settle theorems take no flag hypotheses. Whether a token whose index byte disagrees with its position can
  be spent again, and how the model's split settle should read such a spend, is §7's third open question.
- **M5, the merge settle's two cases:** with a grandparent the merge settle's second rebuild branches on the spent
  lock's output index (`rebuildB`'s cases 1 and 2). `settle_25` now cases on it instead of assuming it zero. The
  probe of case 2 corrected the statement: when the index is not zero the other lineage's input precedes this one,
  so `hashPrevouts` runs over this outpoint, the other lineage's rebuilt outpoint, then this lineage's, then the
  funding outpoint (`gpOutB_2 ++ gpOutA`), where case 1 has `gpOutA ++ gpOutB_1`. All six settle theorems now take
  no flag or index hypotheses beyond the path's types, the grandparent's presence and the token's input index.
- **M5, the input-index argument:** `inputIndexN` is an unlock argument, not the input's position; `hashPrevouts`
  beginning with this outpoint is what places the token at input 0. Probing the settles with the argument
  non-zero, every run reaches the end and the only change is the new token's index byte, 1 instead of 0
  (`inIdxByte`), in the outputs and in the gate stack the regions read; the split's second token keeps the byte
  `i2` selects. The six settle theorems now case on the argument as well, so they take no hypothesis on any
  unlock argument; the settle file builds in about twenty minutes.
- **M5, the commits' input-index cases:** the transfer and split commits with the argument non-zero change only the
  new token's index byte, now `inIdxByte` in `commitLock` (moved to `Enforced.lean`). The merge commit is different:
  with the argument non-zero the run is the merge's second token input, which builds the merged token from the
  interop arguments (`mergeLock1`: the other token's balance `nbc` and its own as `balanceCommit`, the other's owner
  `i3`, its own parent as `ogp`, the other's outpoint `i2` as parent and its parent `i1` as grandparent, index 0) and
  whose `hashPrevouts` begins with the other token's outpoint (`prevoutsOf`: `i2 ++ outpoint`). With honest interop
  arguments both inputs pin the same merged output; with dishonest ones they must still agree on one `hashOutputs`.
  The nine commit theorems case on the argument; none takes an unlock-argument hypothesis.
- **M5, genesis and the melt:** the runs never branch on the parent; only the prologue's issuer guard reads it, as
  the implication every structure carries (`issuer : GuardF f → …`). The settle theorems therefore drop their
  parent hypothesis (the gate stack keeps the guard flag symbolic, `encode (if decode f.parent = 0 then 1 else 0)`),
  and with the commit theorems, which never had one, they cover genesis tokens. The melt (`SimpleMulti/Melt.lean`)
  skips the spend arm and runs the melt branch, about a thousand instructions with the arm skipped; it reads no type,
  so one theorem `melt` covers every spent type, cased on the guard's two conditions, with `EnforcedMelt` (the
  guard, the owner's key hash, the sighash byte, the encodings).
- **M5, `simpleMulti_sound`:** for a lock whose type is one of the six and a next type among them, a successful run
  enforces `SpendEnforced` (`Sound.lean`): with a preimage, a commit of a settle-typed token (`Enforced`, the nine
  commit paths), a settle of a commit-typed token into its own settle type (`EnforcedSettle` with a grandparent,
  `EnforcedSettle0` without, `Settle/{Transfer,Split,Merge}.lean`), and the 24 other pairs refused by the parity
  check (`Refute.lean`: the run carries an `OP_EQUALVERIFY` fact `decide` refutes, closed by `refuteLit`); without
  one, the melt. The only hypothesis on an unlock argument is that the next type is one of the six (§7, question 4).
  A lesson for the remaining families: the driver records `OP_EQUALVERIFY` and `OP_VERIFY` facts without checking
  them, so a path theorem can be vacuous; every probe is scanned for false literal facts, and the soundness theorem's
  case split shows each path's hypotheses are the ones a real run meets. Next for M5: the refinement to `Accepts`.
- **M5, the refinement (design and first step):** `SimpleMulti/Lock.lean` is the lock as eleven pushes and the
  suffix (`lockScript`, 246 bytes of pushes), `lock_pushes` (a run of the lock is a run of the suffix from
  `Fields.stack`), `decodeLock` and `decodeLock_lockScript`. The refinement follows M4's route B, with these fungible
  specifics. (1) The abstraction reads the balances as script numbers and normalises the zero second commitment the
  bytes write to the model's `[]` (`Spend.commitToken` and `settleToken` write `[]` where the bytes write twenty
  zero bytes). (2) A merge commit is one model spend that consumes two tokens, so the theorem is per input: at the
  primary input `Accepts` holds of `spendOf`; a merge commit's second token input (`inputIndexN` non-zero) builds the
  merged token from the interop arguments, and the two inputs' agreement on one `hashOutputs` pins those arguments
  to the other token's real fields, which gives `balanceCommit = other.balance`, `other_settle_typed`,
  `l_merge_same_issuer` and `other_input` for the primary spend. (3) The residual gains a scope assumption for the
  split settle's output order (`pkh1` and `i2` empty on a split settle, the split-flag finding above), alongside
  `HonestOutputs`/`HonestMelt` (the decision for Finding 1). (4) `PushTxSound`, `NoSecondPreimage` (now also of the
  two rebuilt ancestors) and `GpReal` for both lineages, as for the NFT family.
- **M5, the refinement's abstraction and first welds:** `SimpleMulti/Abs.lean` reads a fungible spend into the model
  (`tokenOf` with `balOf` and `com2Of`, `outOf`, `absTx`, `kindOf`, `modeOf`, `spendOf`). `spendOf` takes the merge's
  other token input and the two rebuilt ancestors as arguments, so the refinement states that the choice the run's
  facts determine makes `Accepts` hold; the model's `l3_rebuild` pins an ancestor by its txid, so under collision
  resistance nothing is lost against computing the rebuilt bytes as the NFT family's `rebuiltOf` does.
  `SimpleMulti/Weld.lean` reads each push off the scriptCode as the spent lock's field (`scPush_*`, once
  `sc pre = lockScript f`) and proves the commit lock the covenant builds is the fungible lock of `commitFields`.
  Next: the settled tokens' fields and the outputs' serialisation, the facts that assemble `Accepts`, the residual,
  and `simpleMulti_refines` (first for the commits, the settles and the melt at the primary input, then the merge
  commit's two-input argument).
- **The model's output clauses (decision for Finding 1):** the melt-output clause `l2_melt`, the "change carries
  no token" half of `l2_outs`, and the version test on a melt are not enforced by the bytes and are not security
  properties: anyone can create a token-shaped output in any transaction, and the lineage check at spend time,
  which is proved, carries the security. They are the model's scope (the run model admits only covenant-built
  token outputs; `Theorems/ProofGating.lean` says so, and the off-chain lineage check refuses the rest), and the
  refinement carries them as the explicit hypotheses `HonestOutputs`/`HonestMelt`. They stay in `Accepts`: the
  theorems are proved with them, and moving `Spend.produced` onto `expectedOuts` would touch five theorem files
  for no change in what is proved. `Residual` therefore reads: the cryptographic assumptions, the lineage link,
  and the scope assumptions.
