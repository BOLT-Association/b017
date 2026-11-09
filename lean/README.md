# BoltProof — the machine-checked companion to `docs/formal-proof.md`

A Lean 4 development that checks the security argument of the BOLT token protocol as shipped
in this package: the fungible `SimpleMultiBOLT` and the identity NFT family (`MinSimpleBOLT`,
`AuthBOLT`, `SerialBOLT`). It uses [bsv-script-lean](https://github.com/Calhooon/bsv-script-lean)
v1.2.0, a Lean specification of BSV consensus, to run the real covenant scripts on real
transactions inside Lean.

Three terms are used throughout. The **model** is the hand proof's seven rules (Lemmas 1–7)
written in Lean as `Accepts`, "the covenant accepts this spend". The **script** is each covenant's
compiled bytecode as shipped. A result holds **per input** when it is proved of one token spend at a
time, not yet of a token's whole history.

Read this file for **exactly** what is machine-checked and what is still trusted. In short:

* Theorems 1–5 of the hand proof are proved of the model (Layer 1).
* The script is run inside Lean on 101 real transactions and each verdict is registered with the
  kernel (Layer 2).
* For each of the four scripts, a symbolic execution proves what it enforces on every possible
  input, and that any spend the network accepts is one the model accepts, under assumptions listed
  once per script (`BoltProof/Bridge/Glue/`, "What is still trusted" below).

Scope. Everything about the script is under today's BSV rules (post-Chronicle, `Bridge/Params.lean`);
nothing is claimed for the old rules. The model contains only tokens the script created, so the
fabricated-hop attack is covered by Theorem 5 at the ledger level and the off-chain checks a recipient
runs (`docs/verification-scaling.md`) are not modelled. Chaining the per-input results along a real
token's history, which would give Theorems 1 and 5 for real tokens, is the open step.

## Layout

| Path | Layer | Depends on | What it is |
|---|---|---|---|
| `BoltProof/Model/*.lean` | 1 | core Lean only | The model: tokens, spends, `Accepts`, runs. |
| `BoltProof/Theorems/*.lean` | 1 | core Lean only | Theorems 1–5, and a concrete valid run (`Example.lean`) showing the model is satisfiable. |
| `BoltProof/Theorems/Chain.lean` | 1 | core Lean only | The Layer 1 half of the chaining step: in a valid run a settled token's grandparent is output 0 of an earlier commit step whose outputs are its token, the recipient's proof and, for a split, the second recipient's proof (`Run.grandparent_commit`). |
| `BoltProof/Bridge/Params.lean` | 2 | bsv-script-lean | Judges one input of a real transaction under today's BSV rules (post-Chronicle mainnet). |
| `BoltProof/Bridge/Generated/*.lean` | 2 | generated | The four scripts, whole and cut into named chunks; 101 real transactions with their prevouts and expected verdicts; one theorem per transaction. **Do not hand-edit**: `npm run lean:vectors`. |
| `BoltProof/Bridge/Bytes.lean` | 2 | bsv-script-lean | The scanner's fingerprints (`REGISTRY`) recomputed from the scripts with bsv-script-lean's SHA-256. |
| `BoltProof/Bridge/VectorsMain.lean` | 2 | bsv-script-lean | `lake exe boltvectors`: runs every vector natively and prints a verdict table. |
| `BoltProof/Bridge/Gadgets/*.lean` | 2 | bsv-script-lean `Gadget` | Proofs about fragments of the script over the interpreter's own instruction loop: one lemma per instruction (`Steps.lean`) and the fragments proved from them. |
| `BoltProof/Bridge/Glue/Sym/`, `Sections.lean` | 2 (standard axioms) | bsv-script-lean | The machinery of the symbolic execution: one inversion lemma per opcode, the `sym_all` driver that chains them over a chunked script, and each fragment located at its offset (`lean/GLUE-PLAN.md`). |
| `BoltProof/Bridge/Glue/{MinSimple,SimpleMulti,AuthBolt,SerialBolt}/` | 2 (standard axioms) | Model, bsv-script-lean | Per script: `Spec`/`Enforced` (what it enforces); `Paths/` and `Sound.lean` (`*_sound`, and `reaches_*`: every run reaches the proved fragments with the stack their lemmas assume); `Abs.lean` (a real spend read into the model); `Refine*.lean` (`*_refines`: any spend the network accepts is one the model accepts); `Regress.lean` (the theorems applied to the real vectors, `native_decide`). |
| `BoltProof/Bridge/Glue/Refine/` | 2 (standard axioms) | Model, bsv-script-lean | Shared by the `*_refines` proofs: a valid verdict as a run of the script, the node's serialisation round trip, the preimage fields; and `EndToEnd.lean`, Layer 1's per-input theorems of a real MinSimpleBOLT spend, Theorem 1's hop included. |
| `BoltProof/Bridge/Glue/SimpleMulti/EndToEnd.lean` | 2 (standard axioms) | Model, bsv-script-lean | The same for SimpleMultiBOLT: each proof stage's hypotheses as one structure (`RealSpend`, `RealSettleGp`, `RealMergeCommit`, `RealMergeSettle`), and Lemma 1, Theorems 2, 3 and 4 per step, Theorem 1 per hop. |
| `AxiomCheck.lean`, `AXIOMS-ALLOWED` | — | — | The axiom audit (`node scripts/lean-axiom-check.mjs`): the three standard axioms for Layer 1 and the symbolic proofs (listed in `AxiomCheck.lean`); `native_decide`'s per-theorem axiom allowed for the rest of Layer 2 only, whose theorems Lean enumerates itself. |
| `vectors/export.test.ts`, `vectors/sections.ts` | — | vitest | The exporter: builds the test suite's honest and adversarial transactions and writes `Generated/`, the scripts cut into the chunks the proofs name included (`Generated/Chunks.lean`). |
| `scripts/*.py` | — | Python 3 | Generators of the long, regular proof files (the path theorems, the rebuilds' arms, the guards); each names the files it writes. |

## Layer 1 — the model and Theorems 1–5

`Accepts P fam s` (`Model/Covenant.lean`) is the model: a `structure` of propositions, one field per
clause of the seven lemmas of `docs/formal-proof.md` §3, each a constraint the covenant of family `fam`
puts on the transaction `s` that spends a token:

| Field(s) | Lemma |
|---|---|
| `l1_owner`, `l1_sig`, `l1_type` | L1 signature binding: `H160(pk) = owner`, `Verify(pk, sighash, sig)`, flag `0x41` |
| `l2_outs`, `l2_melt` | L2 output determinism: the outputs are exactly `expectedOuts` (the rebuilt token and proof outputs), a split settle's two tokens in either order (`Spend.OutsOK`), plus non-token change; a melt is P2PKH-only |
| `l3_rebuild`, `l3_merge` | L3 ancestor integrity: a settle with a grandparent rebuilds it, matches its txid, co-spends one of its proof outputs, at index `j`, and (fungible) carries the settle result that proof selects, the one at `j − 1` (the §8.1 fabricated-hop defence) |
| `l4_null` | L4 null ancestor arguments when no rebuild runs |
| `l5_issuer`, `l5_no_merge_at_genesis` | L5 issuer enforcement, the NFT family's `is2ndTx` guard included |
| `l6_*` | L6 balance bounds: over-take and overflow guards at the commit, re-asserted at the settle |
| `commit_type`, `settle_type`, `commit_mode`, `settle_mode`, and the type of every produced token | L7 the `txoType` state machine |

A **run** (`Model/Run.lean`) is a set of genesis tokens plus a sequence of spends; `Run.Valid` adds
what the chain enforces around the covenant (inputs are live and carry the fields the spend claims;
new transaction ids are fresh). The cryptographic assumptions are hypotheses, never axioms
(`Model/Assumptions.lean`): `CollisionFree P` (A1) and `OwnerSecrecy P pk signed` (A2).

| Hand proof | Lean theorem | Hypotheses beyond `Valid` |
|---|---|---|
| T4 State-machine integrity | `t4_step`, `t4_defined_types`, `t4_no_skip`, `Fam.fungible_edge_iff`, `Fam.nft_edge_iff` (`Theorems/StateMachine.lean`) | none |
| T3 Balance conservation | `Run.t3_conservation`, `Run.t3_no_melt`, `Run.t3_single_genesis`, `Run.t3_nft_count` (`Theorems/Balance.lean`) | none |
| T2 Ownership | `t2_presented`, `t2_ownership`, `t2_no_keyless_spend` (`Theorems/Ownership.lean`) | A2 for `t2_ownership` |
| T1 Authenticity | `Run.t1_authenticity`, `Run.t1_issuer_invariant`, `Run.live_rooted`, `Run.t1_rebuild_sound`; per hop, `t1_step` (every token a spend produces carries the spent token's issuer and names it as parent) and `t1_genesis_signer` (a genesis moves only under the issuer's key) (`Theorems/Authenticity.lean`); `Run.grandparent_commit` (`Theorems/Chain.lean`), a settled token's grandparent is a real commit of the run with the honest output layout | A1 for `t1_rebuild_sound` only |
| T5 Proof gating (the §8.1 fabricated-hop defence) | `Run.t5_proof_gating`, `Run.t5_balance_anchor`, `Run.t5_fabricated_hop_excluded` (`Theorems/ProofGating.lean`) | the UTXO rule `NoDoubleSpend` for gating; A1 for the balance anchor |

Two statements are sharper than the prose:

* **T3 counts value in flight, over the set of genesis tokens a run starts from.** A merge-commit
  token (`0x25`) carries the merged-in balance in `balanceCommit` until its settle adds it.
  `float + melted = Σ genesis` holds at every step; the hand proof's "per genesis" form is the
  single-genesis, no-melt corollary. Two mints of one issuer can be merged, so "per genesis" is not
  well defined under merges.
* **T1's "unique parentless root" is definitional.** `Run.root` is a function of the token and the
  run: the parent walk through the outputs the run created. What is proved is that the walk is
  well-founded, ends at a parentless genesis of the run, that every token on it carries the run's
  issuer, and that every link is a real accepted spend whose types follow the state machine
  (`Rooted`).

**T5** is the §8.1 fabricated-hop defence at the ledger level, above the per-input model: under the
UTXO rule that no outpoint is consumed twice, two settles of tokens with grandparents consume two
distinct proof outpoints, so a commit's proof admits at most one settle, honest or forged; and under
collision resistance the balance a settle carries is exactly the settle result of the real commit its
grandparent names. A fabrication that runs no script can still exist on-chain (the model contains
only tokens the script created; the off-chain checks refuse such an anchor), but it can extract
nothing through a real proof beyond the real transition.

**L2 and L3 admit exactly what the script admits.** A split settle's two tokens may come out in either
order (`Spend.OutsOK`), and the anchor names the proof a settle co-spends rather than a position: the
balance carried must be the settle result at the index one below that proof. Both are safe. The order
changes neither recipient nor balance, a token's outpoint is wherever it sits, and no later check reads
the order. The anchor is selected by a proof output only its recipient can spend, the script forces that
proof to be the grandparent's first or, for a split, second (`AnchorOK`, `Bridge/Glue/SimpleMulti/Blocks.lean`),
and Theorem 5 lets each proof admit one settle, so every settle result of a real commit is claimed at
most once, by its recipient. The earlier position-based anchor agreed with this one in the honest order
and was wrong in the other, as the swapped-order vectors show (`smb_probe_idx_*`).

`Theorems/Example.lean` builds the test harness's five-transaction NFT lifecycle as a run and proves
it `Valid`, so the model is not vacuous.

Every Layer 1 theorem depends on at most `propext`, `Classical.choice` and `Quot.sound`
(`lake env lean AxiomCheck.lean` after `lake build`; the file also lists the symbolic proofs, held to
the same rule).

## Layer 2 — the script on real transactions

Layer 1 says nothing about whether the script enforces the model. Layer 2 runs the script, with
bsv-script-lean's consensus semantics (`BsvScript.Eval.verifyScript`: real SHA-256, RIPEMD-160 and
secp256k1 ECDSA as Lean functions):

* `Bytes.lean`: each script hashes to the fingerprint the scanner's `REGISTRY` recognises it by, so
  the script reasoned about is the script shipped.
* `Generated/VectorTheorems.lean`: for each of 101 real transactions (225 inputs), every input's
  verdict is the expected one. The honest lifecycles of both families verify (`buildChain`;
  `SimpleMultiBOLT` mint → transfer → split / merge → melt). Every red-team transaction
  (`test/lib/minSimpleAttack.test.ts` B1–B4; the fungible inflated balance, split over-take, merge
  overflow, cross-issuer merge, raw-byte extra output, wrong-key spend, melt by a non-owner) fails at
  exactly the input the hand proof names. The historical fabricated-hop chain
  (`test/fixtures/fabricated-hop-chain.json`) is accepted by the pre-fix script it embeds,
  reproducing in Lean what a regtest Teranode accepted.

These theorems use `native_decide`: the kernel trusts Lean's compiled evaluator for them, recorded
as one auxiliary axiom per theorem (`<theorem>._native.native_decide.ax_*`, the successor of
`Lean.ofReduceBool`).

**Fragment proofs, no evaluator trust.** `Gadgets/` proves pieces of the script over the
interpreter's own instruction loop (`Gadget.run`, the semantics' `Machine.loop` without the end
test), with the three standard axioms only, in the style of bsv-script-lean's `Gadget/HashLock.lean`.
Each fragment is proved for every possible input, not only the exported vectors:

* `Gadgets/Steps.lean`: what one instruction does to the machine state, for `OP_SIZE`, `OP_NIP`,
  `OP_0`, `OP_1`, `OP_2`, `OP_11`, a one-byte push, `OP_EQUALVERIFY` (failing), `OP_VERIFY` (both
  cases), `OP_GREATERTHANOREQUAL`, `OP_LESSTHANOREQUAL`, `OP_SUB`, `OP_ADD`, `OP_MOD`, `OP_1ADD`,
  `OP_DUP`, `OP_SWAP`, `OP_PICK`, `OP_IF` (both outcomes), `OP_ELSE`, `OP_ENDIF`, and the
  instructions an inactive branch skips; each under the interpreter's preconditions (an executing
  branch, room under the op-count and memory limits, a post-Genesis UTXO, the block path's flags).
* `Gadgets/NullAncestor.lean`, **Lemma 4.** The null-ancestor check's tail `OP_SIZE OP_NIP OP_0
  OP_EQUALVERIFY` (`82 77 00 88`), run after the ancestor arguments are concatenated, passes exactly
  when the concatenation is empty (`nullTail_accepts`, `nullTail_next_iff`) and fails with
  `SCRIPT_ERR_EQUALVERIFY` otherwise (`nullTail_refuses`).
* `Gadgets/BalanceGuards.lean`, **Lemma 6's commit guards.** The split commit's over-take guard
  `2d OP_PICK 34 OP_PICK OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY` (`01 2d 79 01 34 79 94 00 a2
  69`) passes, leaving stack and memory counter as it found them, exactly when `piece ≤ balance`
  (`splitGuard_accepts`, `splitGuard_next_iff`) and fails with `SCRIPT_ERR_VERIFY` otherwise
  (`splitGuard_refuses`). The merge commit's sum guard `2d OP_PICK 34 OP_PICK OP_ADD OP_11 OP_PICK
  OP_LESSTHANOREQUAL OP_VERIFY` (`01 2d 79 01 34 79 93 5b 79 a1 69`) passes exactly when
  `balance + other ≤ bound`, the bound being the value kept ten deep (`mergeGuard_accepts`,
  `mergeGuard_refuses`, `mergeGuard_next_iff`). An inflating split or an overflowing merge is refused
  at its commit.
* `Gadgets/BalanceBounds.lean`, **Lemma 6's bounds and settle re-checks.** The bound check `d OP_PICK
  OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_5 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY` (offsets 610
  and 621, on the spent and the other balance) passes exactly when `0 ≤ balance ≤ bound`, the bound
  being the sixteen bytes `ff…ff7f` (`2¹²⁷ − 1`) pushed at offset 566 (`boundCheck_next_iff`). The
  merge settle's `2f OP_PICK 2f OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_ADD OP_DUP
  OP_14 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY` (offset 781) passes exactly when `0 ≤ other` and
  `balance + other ≤ bound`, leaving the sum for the 16-byte field (`mergeSettle_next_iff`); the split
  settle's `2f OP_PICK 2f OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_SUB OP_DUP OP_0
  OP_GREATERTHANOREQUAL OP_VERIFY` (offset 935) exactly when `0 ≤ piece ≤ balance`, leaving the
  remainder (`splitSettle_next_iff`); each fails with `SCRIPT_ERR_VERIFY` otherwise. With
  `BalanceGuards.lean` this closes Lemma 6 at the fragment level.
* `Gadgets/Parity.lean`, **Lemma 7, fungible.** The 29-byte parity check at offset 528 of
  `SimpleMultiBOLT` (`1a OP_PICK OP_2 OP_MOD OP_DUP OP_IF 26 OP_PICK OP_1ADD 1c OP_PICK
  OP_EQUALVERIFY OP_ENDIF OP_DUP 27 OP_PICK OP_2 OP_MOD OP_SWAP OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF
  OP_EQUALVERIFY`) passes exactly when the hand proof's predicate holds: a commit-typed (odd) spent
  type forces the produced type to be one less, byte for byte, and a settle-typed (even) one forces an
  odd type (`parityCheck_next_iff`; the state it leaves, `parityCheck_accepts_commit` and
  `parityCheck_accepts_settle`). Otherwise `SCRIPT_ERR_EQUALVERIFY` (`parityCheck_refuses_commit`,
  `parityCheck_refuses_settle`). On the six defined type bytes this is the model's own edge relation:
  `parityCheck_edge_iff` says the fragment accepts iff `Fam.edge .fungible a b`, so the model's
  `commit_type` and `settle_type` are, for this family, exactly what the script enforces. The proof
  composes four sub-fragments with `run_append` and walks both outcomes of every conditional.
* `Gadgets/NftType.lean`, **Lemma 7, NFT, by construction.** The NFT scripts do not check the
  produced type: they write it. The selector `d OP_PICK OP_IF 0100 OP_ELSE 0121 OP_ENDIF OP_CAT`
  (`01 d 79 63 02 01 00 67 02 01 21 68 7e`; depth `d = 0x17` at offset 534 of `MinSimpleBOLT` and 543
  of `AuthBOLT`, `d = 0x18` at 589 of `SerialBOLT`) picks the raw spent type byte and appends the type
  field `01 00` when it is true (`0x21`) and `01 21` otherwise (`0x00`), changing nothing else
  (`nftTypeSel_run_commit`, `nftTypeSel_run_settle`, stated for the canonical booleans at that depth;
  `reaches_nftTypeSel` shows the real stack carries the raw type byte there, and the path theorems run
  the selector on it). On the family's two type bytes the written type is a `Fam.edge .nft` successor
  of the spent one (`nftTypeSel_edge`); since `hashOutputs` binds the outputs (Lemma 2), the NFT
  state machine holds with no spender input in the choice. *Correction:* this bullet once described
  the prologue's `OP_DUP OP_BIN2NUM OP_0NOTEQUAL` (`76 81 92`, `nftFlag_run`) as the type flag
  `txoType ≠ 0`; in the shipped scripts it runs on the grandparent outpoint and computes `gp ≠ 0`.

`lake exe boltvectors` runs the same verdicts natively, under today's BSV rules (bsv-script-lean's
`defaultSpendHeight`, block path).

## What is still trusted

| Item | Status |
|---|---|
| That the script enforces the model on *every* input (A4 + L1–L7 fidelity) | **Proved for all four scripts, per input, under listed assumptions** (`BoltProof/Bridge/Glue/`, `lean/GLUE-PLAN.md`). `*_sound` states what each script enforces whenever it does not fail; `reaches_*` shows each run reaches every proved fragment of `Gadgets/` with the stack its lemma assumes; `*_refines` (one per NFT script, four stages for the fungible one) shows that any spend the network accepts is one the model accepts. `Glue/Refine/EndToEnd.lean` and `Glue/SimpleMulti/EndToEnd.lean` state the consequences for MinSimpleBOLT and SimpleMultiBOLT, Theorem 1's hop included. Chaining real spends into a model `Run` is the open step; `Theorems/Chain.lean` has its Layer 1 half (the grandparent is a real commit of the run with the honest layout), and reading a real transaction's bytes as that step's `TxDesc` is what remains. The assumptions, one `Residual` per script: OP_PUSH_TX binds the preimage and nothing the spend hashes has a second preimage; `GpReal`, the grandparent a token names is the real commit two steps back (the chaining step would prove it); `HonestOutputs`/`HonestMelt` for three model rules the script does not check and that are not security properties (melt outputs, the change blob, the melt's version: anyone can create a token-shaped output anywhere; the lineage check at spend time, which is proved, carries the security). SimpleMultiBOLT adds three, each an open question in `GLUE-PLAN.md` §7: the six protocol types only (Q4), the rebuild's piece widths (`HonestPiecesB`, Q7) and the merge partner presenting a preimage (Q8). Two it once carried are gone: the model admits a split settle's two tokens in either order (`Spend.OutsOK`) and anchors a settle's balance at the co-spent proof's index (`l3_rebuild`), as the script does, so the refinement proves the swapped order from the script's own flag cases (`outs_settle_split`) and reads the anchor's index from the script's own check (`AnchorOK.index`), with no hypothesis on `pkh1`, `pkh2` or `i5`. Two are probed on the engine and judged in Lean (`smb_probe_q8_*`, `smb_probe_q3_*`): a merge whose partner input takes the melt branch is accepted, but its carried balance is checked at the settle, which refuses an inflated one (Q8: an unsettleable commit, not a spendable token); a split settle with `pkh1` set comes out with its two tokens swapped (Q3), and a token whose index byte disagrees with its position, by `pkh1`, `i2` or `inputIndexN`, is accepted by every later operation, transfer, split, merge at either input and melt (`smb_probe_idx_*`, 20 vectors): no spend reads the byte, so it is informational, and Q3 is an output-order quirk the model admits (`Spend.OutsOK`). The same shapes run under the fast TypeScript suite (`test/lib/indexByte.test.ts`, builders shared with the exporter). `Regress.lean` applies every `*_refines` to the real honest spends with each decidable hypothesis discharged. Layer 2 still evidences all four on 225 inputs. |
| A1 collision resistance, A2 EUF-CMA | Hypotheses of `t1_rebuild_sound` / `t2_ownership`; everything else is unconditional. |
| A3 chain finality | Not modelled (inherited, as in the hand proof). |
| bsv-script-lean's transcription of the node | Their `docs/HYPOTHESES.md`; pinned at v1.2.0, commit `6139161c`. |
| The judging rules | **Today's BSV rules only** (post-Chronicle, `Bridge/Params.lean`: the block path, no `MINIMALIF`, FORKID signatures, the `codeSep ++ lock` scriptCode b017's OP_PUSH_TX signs). Nothing is claimed for the old rules; `paramsPreChronicle` is a control, printed beside each verdict by `lake exe boltvectors`. |
| The native evaluator (`native_decide`'s per-theorem axiom) | Layer 2 only. Layer 1 never uses it. |

## The issuer guards

Both families require the issuer's signature at the first settle as well as the first commit.
[`docs/issuer-guard.md`](../docs/issuer-guard.md) decodes both prologues and gives the history:
`is2ndTx` is the NFT family's flag, the fungible rule (the F3 fix) is broader, and porting `is2ndTx`
would close nothing. The symbolic execution proves both rules from the script for every input
(`Enforced.issuer` in each `*_sound`): NFT, `parent = 0 ∨ (gp = 0 ∧ txoType = 0x21) → issuer = pubKey`;
fungible, `parent = 0 ∨ gp = 0 → issuer = pubKey ∧ nextTxoType ∉ {0x25, 0x27}` (script offsets 0–29).
The model's L5 clause asks the issuer at genesis only for the fungible family, weaker than the script,
so the proof derives it; for the NFT family it states the guard exactly as the script has it.
*Correction:* an earlier version of this section said the fungible family lacks the guard; it does not.

## Building

```
# toolchain: lean/lean-toolchain pins leanprover/lean4:v4.34.0 (the one bsv-script-lean v1.2.0 uses)
cd lean
lake exe cache get      # Mathlib's prebuilt .olean files (bsv-script-lean depends on Mathlib)
lake build              # BoltProofCore (seconds) + BoltProofBridge (bsv-script-lean, the vectors, the fragment and symbolic proofs)
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
