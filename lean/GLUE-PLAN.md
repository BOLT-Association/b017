# Closing the glue gap: a plan for a symbolic proof that the covenant bytes enforce `Accepts`

Status: **plan, no proof work started.** Written against branch `lean-proof` at `3e4880f` (PR #7) and
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
- **Two probe vectors** for Finding 1, added to the exporter with expectation `valid`: a melt whose transaction
  carries a covenant-shaped output; a commit whose `changeOutput` blob carries two serialised outputs, one
  token-shaped. If both are accepted by the bytes, Finding 1 is confirmed by execution and the §5 decision can
  be taken at the end of M1. A third vector pins the Finding 3 probe (an off-genesis transfer commit with
  `nextTxoType = 0x27` (undefined), expected `SCRIPT_ERR_EQUALVERIFY`) so the type-derivation fact stays regression-tested.

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
   than assume it.

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
