# BoltProof — the machine-checked companion to `docs/formal-proof.md`

A Lean 4 development that checks the security argument of the BOLT token protocol as shipped
in this package: the fungible `SimpleMultiBOLT` and the identity NFT family (`MinSimpleBOLT`,
`AuthBOLT`, `SerialBOLT`). It uses the Lean verifier of BSV consensus,
[bsv-script-lean](https://github.com/Calhooon/bsv-script-lean) (v1.2.0), to run the shipped
covenant bytes on real transactions inside Lean.

Read this file for **exactly** what is machine-checked and what is still trusted. The short
version: the four theorems of the hand proof are proved from the covenant *interface*
(Lemmas 1–7 as the definition of "the covenant accepts a spend"); that interface is then
confronted with the real bytecode on 69 real transactions whose verdicts are registered
with the Lean kernel. A symbolic proof that the 5 KB compiled covenant enforces the interface
on *every* input is not claimed.

## Layout

| Path | Layer | Depends on | What it is |
|---|---|---|---|
| `BoltProof/Model/*.lean` | 1 | core Lean only | The protocol model: tokens, spends, the covenant interface `Accepts`, runs. |
| `BoltProof/Theorems/*.lean` | 1 | core Lean only | Theorems 1–4, plus a concrete valid run (`Example.lean`) showing the interface is satisfiable. |
| `BoltProof/Bridge/Params.lean` | 2 | bsv-script-lean | Evaluate one input of a real transaction under post-Chronicle mainnet consensus parameters. |
| `BoltProof/Bridge/Generated/*.lean` | 2 | generated | The covenant suffixes, 69 real transactions with prevouts and expectations, one theorem per transaction. **Do not hand-edit**: `npm run lean:vectors`. |
| `BoltProof/Bridge/Bytes.lean` | 2 | bsv-script-lean | The suffix fingerprints (`REGISTRY`) recomputed with bsv-script-lean's SHA-256. |
| `BoltProof/Bridge/VectorsMain.lean` | 2 | bsv-script-lean | `lake exe boltvectors`: runs every vector natively and prints a verdict table. |
| `BoltProof/Bridge/Gadgets/*.lean` | 2 | bsv-script-lean `Gadget` | Fragment-level proofs over the loop itself: per-instruction step lemmas (`Steps.lean`) and the covenant fragments proved from them. |
| `AxiomCheck.lean`, `AXIOMS-ALLOWED` | — | — | The axiom audit (`node scripts/lean-axiom-check.mjs`): three standard axioms for Layer 1, plus `native_decide`'s per-theorem axiom for Layer 2 only. |
| `vectors/export.test.ts` | — | vitest | The exporter: builds the test suite's honest and adversarial transactions and writes `Generated/`. |

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
| T1 Authenticity | `Run.t1_authenticity`, `Run.t1_issuer_invariant`, `Run.live_rooted`, `Run.t1_rebuild_sound` (`Theorems/Authenticity.lean`) | A1 for `t1_rebuild_sound` only |

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

`Theorems/Example.lean` builds the five-transaction NFT lifecycle of the test harness as a
concrete run and proves it `Valid`, so the interface is not vacuous.

Every Layer-1 theorem depends on at most `propext`, `Classical.choice` and `Quot.sound`
(`lake env lean AxiomCheck.lean`).

## Layer 2 — the shipped bytes on real transactions

Layer 1 says nothing about whether the compiled covenant enforces `Accepts`. Layer 2 confronts
the two on concrete inputs with bsv-script-lean's consensus semantics
(`BsvScript.Eval.verifyScript`, which runs real SHA-256, RIPEMD-160 and secp256k1 ECDSA as Lean
functions):

* `Bytes.lean`: the static suffix of each shipped covenant hashes to the fingerprint the
  scanner's `REGISTRY` recognises it by — the bytes reasoned about are the bytes shipped.
* `Generated/VectorTheorems.lean`: for each of 69 real transactions (138 inputs judged), every
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
  `OP_NIP`, `OP_0`, a one-byte push, `OP_EQUALVERIFY` (the failing case), `OP_VERIFY` (both
  cases), `OP_GREATERTHANOREQUAL`, `OP_SUB` and `OP_PICK`, each under the reference's
  preconditions (an executing branch, room under the op-count and memory limits, a post-Genesis
  UTXO, the block path's flag word).
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
  commit for every input. The merge sum guard (`… OP_ADD OP_11 OP_PICK OP_LESSTHANOREQUAL
  OP_VERIFY`), the settle-side re-checks and the L7 parity check are the next follow-ups. `lake exe boltvectors` runs the same verdicts natively and prints a
table, with the pre-Chronicle verdict as an informative control.

**Judging height, and a finding.** Every vector is judged at bsv-script-lean's
`defaultSpendHeight` (post-Chronicle, block path). Under post-Genesis but **pre-Chronicle**
rules (`paramsPreChronicle`, the control column of `boltvectors`) *every* covenant input of
every vector — honest or not — fails with `SCRIPT_ERR_SIG_PUSHONLY`: b017's unlocking scripts
carry the OP_PUSH_TX computation after an `OP_CODESEPARATOR`, i.e. non-push opcodes, which the
Genesis-era `SIGPUSHONLY` rule forbids and the Chronicle rules admit (they also make the
scriptCode inside the unlocking script `codeSep ++ lockingScript`, which is what b017's
`splitCtx(ctx, 2)` signs). The covenant is therefore a Chronicle-era protocol; its security
claims are stated for Chronicle consensus and would not hold on a pre-Chronicle node, where the
transactions are simply invalid. The P2PKH and proof inputs are valid in both eras.

## What is still trusted

| Item | Status |
|---|---|
| That the compiled covenant enforces `Accepts` on *every* input (A4 + L1–L7 fidelity) | **Not proved in full.** Evidenced on 138 inputs by Layer 2; the Lemma 4 tail and the Lemma 6 split over-take guard are proved for every input at the fragment level (`Gadgets/`); the merge guard, the settle re-checks and the L7 parity check are the next follow-ups. |
| A1 collision resistance, A2 EUF-CMA | Hypotheses of `t1_rebuild_sound` / `t2_ownership`; everything else is unconditional. |
| A3 chain finality | Not modelled (inherited, as in the hand proof). |
| bsv-script-lean's transcription of the node | Their `docs/HYPOTHESES.md`; pinned at v1.2.0, commit `6139161c`. |
| The native evaluator (`native_decide`'s per-theorem axiom) | Layer 2 only. Layer 1 never uses it. |

## An observation on the NFT `is2ndTx` guard (recorded, no action taken)

Every covenant hard-codes that a commit's token output stays owned by the current holder
(`owner := spent.owner`, the recipient is only *named*), so Lemma 1 already forces the holder to
sign the settle. On a chain built from a real genesis the first commit's output is owned by the
issuer, so the issuer signs the first settle whether or not `is2ndTx` exists: on honest chains
the flag is redundant. It only bites on a *fabricated* first-commit shape whose owner field an
attacker chose (then L1 asks for the attacker's key and `is2ndTx` for the issuer's). It is
therefore either superfluous or security hardening; if hardening, the fungible family, which
lacks it, would need it. The model states the NFT clause exactly as the bytes have it and takes
no position; the vectors do not exercise the fungible analogue.

## Building

```
# toolchain: lean/lean-toolchain pins leanprover/lean4:v4.34.0 (the one bsv-script-lean v1.2.0 uses)
cd lean
lake exe cache get      # Mathlib's prebuilt .olean files (bsv-script-lean depends on Mathlib)
lake build              # BoltProofCore (seconds) + BoltProofBridge (the bsv-script-lean closure, then the vectors)
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
