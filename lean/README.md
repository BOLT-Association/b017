# BoltProof — the machine-checked companion to `docs/formal-proof.md`

A Lean 4 development that checks the security argument of the BOLT token protocol as shipped
in this package: the fungible `SimpleMultiBOLT` and the identity NFT family (`MinSimpleBOLT`,
`AuthBOLT`, `SerialBOLT`). It uses the Lean verifier of BSV consensus,
[bsv-script-lean](https://github.com/Calhooon/bsv-script-lean) (v1.2.0), to run the shipped
covenant bytes on real transactions inside Lean.

Read this file for **exactly** what is machine-checked and what is still trusted. The short
version: the theorems of the hand proof are proved from the covenant *interface* (Lemmas 1–7 as
the definition of "the covenant accepts a spend"); that interface is then confronted with the
real bytecode twice. On 74 real transactions their verdicts are registered with the Lean kernel;
and for each of the four shipped covenants a symbolic run of the compiled suffix proves, for
*every* input, what the bytes enforce, and that a spend the consensus rules judge valid satisfies
the interface once read into the model, under residual assumptions each refinement states once
(`BoltProof/Bridge/Glue/`, "What is still trusted" below). Everything at the bytecode level is judged under
the Chronicle consensus rules BSV runs (`Bridge/Params.lean`); nothing is claimed under the pre-Chronicle rules.
The run model admits only covenant-created tokens: the fabricated-hop attack is covered at the ledger level by
Theorem 5, and a recipient's off-chain lineage checks (`docs/verification-scaling.md`) are not formalized.
Composing the hops of a real chain into a model run, which lifts the per-input results to Theorems 1 and 5
for real tokens, is the open step.

## Layout

| Path | Layer | Depends on | What it is |
|---|---|---|---|
| `BoltProof/Model/*.lean` | 1 | core Lean only | The protocol model: tokens, spends, the covenant interface `Accepts`, runs. |
| `BoltProof/Theorems/*.lean` | 1 | core Lean only | Theorems 1–4, plus a concrete valid run (`Example.lean`) showing the interface is satisfiable. |
| `BoltProof/Bridge/Params.lean` | 2 | bsv-script-lean | Evaluate one input of a real transaction under post-Chronicle mainnet consensus parameters. |
| `BoltProof/Bridge/Generated/*.lean` | 2 | generated | The covenant suffixes (whole and chunked), 74 real transactions with prevouts and expectations, one theorem per transaction. **Do not hand-edit**: `npm run lean:vectors`. |
| `BoltProof/Bridge/Bytes.lean` | 2 | bsv-script-lean | The suffix fingerprints (`REGISTRY`) recomputed with bsv-script-lean's SHA-256. |
| `BoltProof/Bridge/VectorsMain.lean` | 2 | bsv-script-lean | `lake exe boltvectors`: runs every vector natively and prints a verdict table. |
| `BoltProof/Bridge/Gadgets/*.lean` | 2 | bsv-script-lean `Gadget` | Fragment-level proofs over the loop itself: per-instruction step lemmas (`Steps.lean`) and the covenant fragments proved from them. |
| `BoltProof/Bridge/Glue/Sym/`, `Sections.lean` | 2 (standard axioms) | bsv-script-lean | The glue's machinery: inversion lemmas, one per opcode, the `sym_all` driver that chains them over a chunked suffix, and the fragment literals at their offsets (`lean/GLUE-PLAN.md`). |
| `BoltProof/Bridge/Glue/{MinSimple,SimpleMulti,AuthBolt,SerialBolt}/` | 2 (standard axioms) | Model, bsv-script-lean | Per covenant: `Spec`/`Enforced` (what the suffix enforces), `Paths/` and `Sound.lean` (`*_sound` and the `reaches_*` theorems: every run reaches the proved fragments with the stack their lemmas assume), `Abs.lean` (a real spend read as a model `Spend`), `Refine*.lean` (`*_refines`: a valid spend satisfies `Accepts`), `Regress.lean` (the theorems applied to the real vectors, `native_decide`). |
| `BoltProof/Bridge/Glue/Refine/` | 2 (standard axioms) | Model, bsv-script-lean | Shared by the refinements: a valid verdict as a run of the lock, the node's serialisation round trip, the preimage fields, and `EndToEnd.lean` (Layer 1's per-input theorems of a real MinSimpleBOLT spend, Theorem 1's hop included). |
| `BoltProof/Bridge/Glue/SimpleMulti/EndToEnd.lean` | 2 (standard axioms) | Model, bsv-script-lean | The fungible family's end-to-end statement: the four refinement stages' hypotheses as `RealSpend`, `RealSettleGp`, `RealMergeCommit` and `RealMergeSettle`, and Layer 1's per-input theorems of a real SimpleMultiBOLT spend (Lemma 1, Theorems 2, 3 and 4 per step, Theorem 1 per hop). |
| `AxiomCheck.lean`, `AXIOMS-ALLOWED` | — | — | The axiom audit (`node scripts/lean-axiom-check.mjs`): three standard axioms for Layer 1 and the glue's theorems (listed in `AxiomCheck.lean`), plus `native_decide`'s per-theorem axiom for the rest of Layer 2 only; Layer 2's theorems are enumerated by Lean itself. |
| `vectors/export.test.ts`, `vectors/sections.ts` | — | vitest | The exporter: builds the test suite's honest and adversarial transactions and writes `Generated/`, including the suffixes cut into the chunks the glue names (`Generated/Chunks.lean`). |
| `scripts/*.py` | — | Python 3 | The generators of the glue's long, regular files (the path theorems, the rebuilds' arms, the guards); each names the files it writes. |

## Layer 1 — the protocol model and Theorems 1–4

`Accepts P fam s` (`Model/Covenant.lean`) is a `structure` of propositions whose fields are the
seven lemmas of `docs/formal-proof.md` §3, stated as the constraints the covenant of family
`fam` imposes on the transaction `s` that spends a token:

| Field(s) | Lemma |
|---|---|
| `l1_owner`, `l1_sig`, `l1_type` | L1 signature binding: `H160(pk) = owner`, `Verify(pk, sighash, sig)`, flag `0x41` |
| `l2_outs`, `l2_melt` | L2 output determinism: the outputs are exactly `expectedOuts` (the reconstructed token/proof outputs) plus non-token change; a melt is P2PKH-only |
| `l3_rebuild`, `l3_merge` | L3 ancestor integrity: a settle with a grandparent rebuilds it, matches its txid, co-spends its proof output, and (fungible) anchors the spent balance to the rebuilt ancestor's own transition (the §8.1 fabricated-hop defence) |
| `l4_null` | L4 null ancestor arguments when no rebuild runs |
| `l5_issuer`, `l5_no_merge_at_genesis` | L5 issuer enforcement, including the NFT family's `is2ndTx` guard |
| `l6_*` | L6 balance bounds: over-take and overflow guards at the commit and re-asserted at the settle |
| `commit_type`, `settle_type`, `commit_mode`, `settle_mode` and the type of every produced token | L7 the `txoType` state machine |

A **run** (`Model/Run.lean`) is a set of genesis tokens plus a sequence of spends; `Run.Valid`
adds the UTXO-model facts the chain enforces around the covenant (inputs are live and carry the
fields the spend claims; new transaction ids are fresh). The cryptographic assumptions are
hypotheses, never axioms (`Model/Assumptions.lean`): `CollisionFree P` (A1) and
`OwnerSecrecy P pk signed` (A2).

| Hand proof | Lean theorem | Hypotheses beyond `Valid` |
|---|---|---|
| T4 State-machine integrity | `t4_step`, `t4_defined_types`, `t4_no_skip`, `Fam.fungible_edge_iff`, `Fam.nft_edge_iff` (`Theorems/StateMachine.lean`) | none |
| T3 Balance conservation | `Run.t3_conservation`, `Run.t3_no_melt`, `Run.t3_single_genesis`, `Run.t3_nft_count` (`Theorems/Balance.lean`) | none |
| T2 Ownership | `t2_presented`, `t2_ownership`, `t2_no_keyless_spend` (`Theorems/Ownership.lean`) | A2 for `t2_ownership` |
| T1 Authenticity | `Run.t1_authenticity`, `Run.t1_issuer_invariant`, `Run.live_rooted`, `Run.t1_rebuild_sound`; per transition, `t1_step` (every produced token carries the spent token's issuer and names the spent outpoint as parent) and `t1_genesis_signer` (a genesis moves only under the issuer's key) (`Theorems/Authenticity.lean`) | A1 for `t1_rebuild_sound` only |
| T5 Proof gating (the fabricated-hop exclusion, §8.1) | `Run.t5_proof_gating`, `Run.t5_balance_anchor`, `Run.t5_fabricated_hop_excluded` (`Theorems/ProofGating.lean`) | the UTXO rule `NoDoubleSpend` for gating; A1 for the balance anchor |

Two statements are sharper than the prose:

* **T3 is over the set of genesis tokens a run starts from**, and counts value *in flight*: a
  merge-commit-typed token (`0x25`) carries the merged-in balance in `balanceCommit` until its
  settle adds it. `float + melted = Σ genesis` holds at every step; the hand proof's "per
  genesis" statement is the single-genesis, no-melt corollary. Two mints of one issuer can be
  merged, so "per genesis" is not well-defined under merges.
* **T1's "unique parentless root" is definitional**: `Run.root` is a function of the token and
  the run (the parent walk through the outputs the run created). What is proved is that the walk
  is well-founded, ends at a parentless genesis token of the run, that every token on it carries
  the run's issuer, and that every link is a real covenant-accepted transition whose types follow
  the machine (`Rooted`).

**T5** is the ledger-level reading of the §8.1 fabricated-hop defence, stated above the
single-spend interface: under the UTXO rule that no outpoint is consumed twice, two distinct
settles of tokens with grandparents consume two distinct proof outpoints, so a commit's proof
admits at most one settle, honest or forged; and under collision resistance the balance a settle
carries is exactly the settle result of the real commit its grandparent names. A fabrication
that runs no covenant can still exist on-chain (the run model admits only covenant-created
tokens; the off-chain verifier's lineage checks refuse such an anchor), but it can extract
nothing through a real proof beyond the real transition.

`Theorems/Example.lean` builds the five-transaction NFT lifecycle of the test harness as a
concrete run and proves it `Valid`, so the interface is not vacuous.

Every Layer-1 theorem depends on at most `propext`, `Classical.choice` and `Quot.sound`
(`lake env lean AxiomCheck.lean`, after `lake build`: the file also lists the glue's theorems, held to the
same rule).

## Layer 2 — the shipped bytes on real transactions

Layer 1 says nothing about whether the compiled covenant enforces `Accepts`. Layer 2 confronts
the two on concrete inputs with bsv-script-lean's consensus semantics
(`BsvScript.Eval.verifyScript`, which runs real SHA-256, RIPEMD-160 and secp256k1 ECDSA as Lean
functions):

* `Bytes.lean`: the static suffix of each shipped covenant hashes to the fingerprint the
  scanner's `REGISTRY` recognises it by — the bytes reasoned about are the bytes shipped.
* `Generated/VectorTheorems.lean`: for each of 74 real transactions (148 inputs judged), every
  input's verdict is the expected one: the honest lifecycles of both families (`buildChain`,
  `SimpleMultiBOLT` mint → transfer → split / merge → melt) verify; every adversarial
  transaction of the red-team suites (`test/lib/minSimpleAttack.test.ts` B1–B4, the fungible
  inflated balance, split over-take, merge overflow, cross-issuer merge, raw-byte extra output,
  wrong-key spend, melt by a non-owner) fails at exactly the input the hand proof names; and the
  historical fabricated-hop chain (`test/fixtures/fabricated-hop-chain.json`) is accepted by the
  pre-fix bytes it embeds, reproducing in Lean what a regtest Teranode accepted.

These theorems use `native_decide`: the kernel trusts Lean's compiled evaluator for them, which
Lean 4.34 records as one auxiliary axiom per theorem (`<theorem>._native.native_decide.ax_*`,
the successor of `Lean.ofReduceBool`).

**Fragment-level proofs (no evaluator trust).** `Gadgets/` proves covenant fragments over
bsv-script-lean's own instruction loop (`Gadget.run`, the semantics' `Machine.loop` without the
end test), with only the three standard axioms, in the style of their `Gadget/HashLock.lean`:

* `Gadgets/Steps.lean`: the effect of one instruction on the machine state for `OP_SIZE`,
  `OP_NIP`, `OP_0`, `OP_1`, `OP_2`, `OP_11`, a one-byte push, `OP_EQUALVERIFY` (the failing
  case), `OP_VERIFY` (both cases), `OP_GREATERTHANOREQUAL`, `OP_LESSTHANOREQUAL`, `OP_SUB`,
  `OP_ADD`, `OP_MOD`, `OP_1ADD`, `OP_DUP`, `OP_SWAP`, `OP_PICK`, the conditionals `OP_IF`
  (both outcomes), `OP_ELSE` and `OP_ENDIF`, and the instructions an inactive branch skips,
  each under the reference's preconditions (an executing branch, room under the op-count and
  memory limits, a post-Genesis UTXO, the block path's flag word).
* `Gadgets/NullAncestor.lean` — **Lemma 4 over the bytes.** The null-ancestor check's tail
  `OP_SIZE OP_NIP OP_0 OP_EQUALVERIFY` (`82 77 00 88`), which runs after the ancestor
  arguments are concatenated, reaches its end exactly when the concatenation is empty
  (`nullTail_accepts`, `nullTail_next_iff`) and fails with `SCRIPT_ERR_EQUALVERIFY` otherwise
  (`nullTail_refuses`). The hand proof's "any non-null field makes the size positive and fails
  the check" is a theorem about the instructions themselves, for every input, not only the
  exported vectors.
* `Gadgets/BalanceGuards.lean` — **Lemma 6's over-take guard over the bytes.** The split
  commit's guard `2d OP_PICK 34 OP_PICK OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY`
  (`01 2d 79 01 34 79 94 00 a2 69`, inside the split branch of the shipped `SimpleMultiBOLT`
  suffix) runs to its end, leaving the stack and the memory counter as it found them, exactly
  when `piece ≤ balance` (`splitGuard_accepts`, `splitGuard_next_iff`) and fails with
  `SCRIPT_ERR_VERIFY` otherwise (`splitGuard_refuses`): an inflating split is refused at its
  commit for every input. Likewise the merge commit's sum guard `2d OP_PICK 34 OP_PICK OP_ADD
  OP_11 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY` (`01 2d 79 01 34 79 93 5b 79 a1 69`) runs to its
  end exactly when `balance + other ≤ bound`, the bound being the value the covenant keeps ten
  deep (`mergeGuard_accepts`, `mergeGuard_refuses`, `mergeGuard_next_iff`): an overflowing
  merge is refused at its commit for every input.
* `Gadgets/BalanceBounds.lean` — **Lemma 6's bounds and settle-side re-checks over the bytes.**
  The bound check `d OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_5 OP_PICK
  OP_LESSTHANOREQUAL OP_VERIFY` (offsets 610 and 621, on the spent balance and the other
  balance) runs to its end exactly when `0 ≤ balance ≤ bound`, the bound being the sixteen bytes
  `ff…ff7f` (`2¹²⁷ − 1`) the covenant pushes at offset 566 (`boundCheck_next_iff`); the merge
  settle's `2f OP_PICK 2f OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_ADD OP_DUP
  OP_14 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY` (offset 781) exactly when `0 ≤ other` and
  `balance + other ≤ bound`, leaving the sum for the 16-byte field (`mergeSettle_next_iff`); the
  split settle's `2f OP_PICK 2f OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_SUB
  OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY` (offset 935) exactly when `0 ≤ piece ≤ balance`,
  leaving the remainder (`splitSettle_next_iff`); each fails with `SCRIPT_ERR_VERIFY` otherwise.
  With `BalanceGuards.lean` this closes Lemma 6 at the fragment level.
* `Gadgets/Parity.lean` — **Lemma 7 over the bytes.** The fungible covenant's parity check,
  the 29 bytes `01 1a 79 52 97 76 63 01 26 79 8b 01 1c 79 88 68 76 01 27 79 52 97 7c 63 00 67
  51 68 88` at offset 528 of the shipped `SimpleMultiBOLT` suffix (`1a OP_PICK OP_2 OP_MOD
  OP_DUP OP_IF 26 OP_PICK OP_1ADD 1c OP_PICK OP_EQUALVERIFY OP_ENDIF OP_DUP 27 OP_PICK OP_2
  OP_MOD OP_SWAP OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF OP_EQUALVERIFY`), runs to its end exactly
  when the hand proof's predicate holds — an odd (commit-typed) spent type forces the produced
  type to be one less, byte for byte, and an even (settle-typed) spent type forces an odd one
  (`parityCheck_next_iff`, with the state it leaves pinned down by `parityCheck_accepts_commit`
  and `parityCheck_accepts_settle`) — and fails with `SCRIPT_ERR_EQUALVERIFY` otherwise
  (`parityCheck_refuses_commit`, `parityCheck_refuses_settle`). On the six defined type bytes
  this is the model's own edge relation: `parityCheck_edge_iff` states that the fragment accepts
  iff `Fam.edge .fungible a b`, so the Layer-1 clauses `commit_type`/`settle_type` are, for this
  family, exactly what these bytes enforce. The proof composes the fragment from four
  sub-fragments (head, settle-side branch taken or skipped, produced-type parity, complement)
  with `run_append`, and walks both outcomes of every conditional.
* `Gadgets/NftType.lean` — **Lemma 7 for the NFT family, by construction.** The NFT covenants
  do not check the produced type: they *write* it. The selector `d OP_PICK OP_IF 0100 OP_ELSE
  0121 OP_ENDIF OP_CAT` (`01 d 79 63 02 01 00 67 02 01 21 68 7e`, depth `d = 0x17` at offset 534
  of `MinSimpleBOLT` and 543 of `AuthBOLT`, `d = 0x18` at offset 589 of `SerialBOLT`) picks the
  raw spent type byte and appends the type field `01 00` when it is true (`0x21`) and `01 21`
  otherwise (`0x00`) to the output being serialized, changing nothing else
  (`nftTypeSel_run_commit`, `nftTypeSel_run_settle`, stated for the canonical booleans at that
  depth; the glue's `reaches_nftTypeSel` shows the real stack carries the raw type byte there,
  and its path theorems run the selector on it). On the family's two type bytes the written type
  is a `Fam.edge .nft` successor of the spent one (`nftTypeSel_edge`); as the serialized outputs
  are bound by `hashOutputs` (Lemma 2), the NFT state machine holds with no spender input in the
  choice. *Correction:* this bullet used to describe the prologue's `OP_DUP OP_BIN2NUM
  OP_0NOTEQUAL` (`76 81 92`, `nftFlag_run`) as the type flag `txoType ≠ 0`; in the shipped
  suffixes it runs on the grandparent outpoint and computes `gp ≠ 0`.

`lake exe boltvectors` runs the same verdicts natively. Vectors are judged under the Chronicle rules BSV runs
(bsv-script-lean's `defaultSpendHeight`, block path).

## What is still trusted

| Item | Status |
|---|---|
| That the compiled covenant enforces `Accepts` on *every* input (A4 + L1–L7 fidelity) | **Proved for all four covenants, per input, under stated residuals.** `BoltProof/Bridge/Glue/` runs each shipped suffix symbolically over every input (`lean/GLUE-PLAN.md`): `minSimple_sound`, `simpleMulti_sound`, `authBolt_sound` and `serialBolt_sound` state what each suffix enforces whenever it does not fail, and the `reaches_*` theorems show the run reaches every proved fragment of `Gadgets/` with the stack its lemma assumes. The refinements `minSimple_refines`, `authBolt_refines`, `serialBolt_refines` and the fungible family's four stages (`simpleMulti_refines_basic`, `_settle_gp`, `_merge_commit`, `_merge_settle`) prove that a spend the consensus rules judge valid satisfies `Accepts` once read into the model, so Theorems 1–5 hold of what the bytes let through (`Glue/Refine/EndToEnd.lean` and `Glue/SimpleMulti/EndToEnd.lean` state the per-input consequences for MinSimpleBOLT and SimpleMultiBOLT, Theorem 1's hop included; reading a chain of real spends as a model `Run` is the open composition step). Their assumptions, stated in each `Residual`, are the cryptographic ones (OP_PUSH_TX soundness, second-preimage freedom of what the spend hashes), the lineage link (`GpReal`: the grandparent the token names is the real commit two steps back, which the composition step discharges), and the model's scope assumptions `HonestOutputs`/`HonestMelt` for three clauses the bytes do not enforce (melt outputs, the change blob, the melt's version: anyone can create a token-shaped output in any transaction, so these are not security properties; the lineage check at spend time, which is proved, carries the security, and the run model admits only covenant-built token outputs). The fungible family carries more, each recorded as an open question in `GLUE-PLAN.md` §7: the six protocol next types only (Q4), the widths of the rebuild's pieces (`HonestPiecesB`, Q7), the anchor index `i5` (Q6), and a merge's other token input presenting a preimage (Q8). Two are probed on the engine, and the vectors judged in Lean (`smb_probe_q8_*`, `smb_probe_q3_*`): a merge commit whose other token input takes the melt branch is accepted, and its carried balance is anchored only at the settle, whose second rebuild refuses an inflated one, so Q8 is an unsettleable commit, not a spendable token; a split settle with `pkh1` non-empty is accepted with its two tokens swapped, and both stay spendable with the committed balances, so Q3 is an output-order quirk the model's `l2_outs` does not admit. The `Regress.lean` files apply every refinement to the real honest spends with each decidable hypothesis discharged, so the residuals are what remains. Layer 2 still evidences all four families on 148 inputs. |
| A1 collision resistance, A2 EUF-CMA | Hypotheses of `t1_rebuild_sound` / `t2_ownership`; everything else is unconditional. |
| A3 chain finality | Not modelled (inherited, as in the hand proof). |
| bsv-script-lean's transcription of the node | Their `docs/HYPOTHESES.md`; pinned at v1.2.0, commit `6139161c`. |
| The consensus rules | **Chronicle only.** Layer 2 judges every vector, and the glue states every theorem, under the post-Chronicle mainnet parameters of `Bridge/Params.lean` (the block path: no `MINIMALIF`, FORKID signatures, the `codeSep ++ lock` scriptCode that b017's OP_PUSH_TX signs). Nothing is claimed under the pre-Chronicle rules; `paramsPreChronicle` is a negative control, printed beside the judged verdict by `lake exe boltvectors`. |
| The native evaluator (`native_decide`'s per-theorem axiom) | Layer 2 only. Layer 1 never uses it. |

## The issuer guards

Both families require the issuer's signature at the first settle as well as the first commit.
[`docs/issuer-guard.md`](../docs/issuer-guard.md) decodes both prologues and gives the history: `is2ndTx` is the
NFT family's flag, the fungible rule (the F3 fix) is broader, and porting `is2ndTx` would close nothing. The glue
proves both rules from the shipped bytes for every input, `Enforced.issuer` in each family's `*_sound`: NFT
`parent = 0 ∨ (gp = 0 ∧ txoType = 0x21) → issuer = pubKey`, fungible
`parent = 0 ∨ gp = 0 → issuer = pubKey ∧ nextTxoType ∉ {0x25, 0x27}` (suffix 0–29). The model's L5 clause for the
fungible family asks the issuer at genesis only, which is weaker than the bytes, so the refinement derives it; for
the NFT family it states the guard exactly as the bytes have it. *Correction:* an earlier version of this section
said the fungible family lacks the guard; it does not.

## Building

```
# toolchain: lean/lean-toolchain pins leanprover/lean4:v4.34.0 (the one bsv-script-lean v1.2.0 uses)
cd lean
lake exe cache get      # Mathlib's prebuilt .olean files (bsv-script-lean depends on Mathlib)
lake build              # BoltProofCore (seconds) + BoltProofBridge (the bsv-script-lean closure, the vectors, the glue)
lake exe boltvectors    # every vector natively, with the control columns
cd .. && node scripts/lean-axiom-check.mjs
```

`lake build BoltProofCore` needs neither Mathlib nor bsv-script-lean and builds in seconds.

Regenerate the vectors after any change to a covenant template, a test helper, or an expectation:

```
npm run lean:vectors    # rewrites lean/BoltProof/Bridge/Generated/ and lean/vectors/vectors.json
```

The output is deterministic (fixed keys, RFC6979 signatures); CI regenerates and fails on drift.
Exact bsv-script-lean error codes are pinned in `PINNED` in `vectors/export.test.ts` from a triage
run of `boltvectors`; an unpinned rejection is `anyInvalid`.

Never run `lake update` casually: `lake-manifest.json` pins bsv-script-lean and, through it,
Mathlib. To bump bsv-script-lean, change `rev` in `lakefile.toml`, copy its `lean-toolchain`, run
`lake update bsvscript`, rebuild, and re-triage the vectors.

## Credits and license

bsv-script-lean is consumed as a Lake dependency, not vendored. Its Lean sources are under the
Open BSV License v5 (the same license as this package); its tooling is Apache-2.0. See its
`NOTICE`.
