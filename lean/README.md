# BoltProof — the machine-checked companion to `docs/formal-proof.md`

A Lean 4 development that checks the security argument of the BOLT token protocol as shipped in this
package: the fungible `SimpleMultiBOLT` and the identity NFT family (`MinSimpleBOLT`, `AuthBOLT`,
`SerialBOLT`). It uses [bsv-script-lean](https://github.com/Calhooon/bsv-script-lean) v1.2.0, a Lean
specification of BSV consensus, to run and to reason about the real covenant scripts.

**In one line:** BOLT's shipped covenants are proved counterfeit-proof — the real bytecode enforces the
protocol for *every* input and over a token's whole history, machine-checked with no `sorry`, no `admit`,
and an axiom audit that pins exactly what each theorem rests on.

Three terms are used throughout. The **model** is the hand proof's seven rules (Lemmas 1–7) written in
Lean as `Accepts`, "the covenant accepts this spend". The **script** is each covenant's compiled bytecode
as shipped. A result holds **per input** when it is proved of one token spend at a time, and **over a
chain** when it is proved of a token's whole history.

What is proved:

* **Theorems 1–5 of the hand proof hold of the model** (Layer 1, Lean's three standard axioms only).
* **The script is run inside Lean** on 107 real transactions, 245 inputs, and each verdict is registered
  with the kernel (Layer 2).
* **The script enforces the model, per input.** For each of the four scripts a symbolic execution proves
  what it enforces on every possible input, and that any spend the network accepts is one the model
  accepts, under assumptions listed once per script ("The glue" below).
* **A chain of real spends is a valid run**, for all four scripts, so Theorems 1, 3, 4
  and 5 hold of real tokens. The grandparent a settle names is read off the run, not assumed.

Scope. Everything about the script is under today's BSV rules (post-Chronicle, `Bridge/Params.lean`);
nothing is claimed for the old rules. The model contains only tokens the script created, so the
fabricated-hop attack is covered by Theorem 5 at the ledger level and the off-chain checks a recipient
runs (`docs/verification-scaling.md`) are not modelled. "What is still trusted" below is the exact
boundary.

## Layout

| Path | Layer | Depends on | What it is |
|---|---|---|---|
| `BoltProof/Model/*.lean` | 1 | core Lean only | The model: tokens, spends, `Accepts`, runs. |
| `BoltProof/Theorems/*.lean` | 1 | core Lean only | Theorems 1–5; `Chain.lean`, validity step by step and the grandparent's layout in a valid run; `Example.lean`, a concrete valid run, so the model is satisfiable. |
| `BoltProof/Bridge/Params.lean`, `Bytes.lean`, `VectorsMain.lean` | 2 | bsv-script-lean | Today's BSV rules; the scanner's fingerprints recomputed from the scripts; `lake exe boltvectors`. |
| `BoltProof/Bridge/Generated/*.lean` | 2 | generated | The four scripts, whole and cut into named chunks; the real transactions with prevouts and expected verdicts; one theorem per transaction. **Do not hand-edit**: `npm run lean:vectors`. |
| `BoltProof/Bridge/Gadgets/*.lean` | 2 (standard axioms) | bsv-script-lean `Gadget` | Fragments of the script proved over the interpreter's own instruction loop, for every input. |
| `BoltProof/Bridge/Glue/Sym/`, `Sections.lean` | 2 (standard axioms) | bsv-script-lean | The symbolic execution: one inversion lemma per opcode, the `sym_all` driver, each fragment at its offset. |
| `BoltProof/Bridge/Glue/{MinSimple,AuthBolt,SerialBolt,SimpleMulti}/` | 2 (standard axioms) | Model, bsv-script-lean | Per script: `Spec`/`Enforced` (what it enforces), `Paths/` and `Sound.lean` (`*_sound`, `reaches_*`), `Abs.lean` (a real spend read into the model), `Refine*.lean` (`*_refines`), `Regress.lean` (applied to the real vectors). The fungible directory also holds the two rebuilds' parses and welds (`Rebuilt*.lean`, `Anchor*.lean`, `GpWeld*.lean`, `L3.lean`). |
| `BoltProof/Bridge/Glue/Refine/` | 2 (standard axioms) | Model, bsv-script-lean | Shared by the refinements: a valid verdict as a run of the script, the node's serialisation round trip, the preimage fields. `EndToEnd.lean` and `Chain.lean`: the per-input theorems and the chain for MinSimpleBOLT (AuthBOLT's and SerialBOLT's chains are `AuthBolt/Chain.lean` and `SerialBolt/Chain.lean`, this file over their abstractions). |
| `BoltProof/Bridge/Glue/SimpleMulti/EndToEnd.lean`, `Chain.lean` | 2 (standard axioms) | Model, bsv-script-lean | The same for SimpleMultiBOLT, each refinement stage's hypotheses as one structure. |
| `AxiomCheck.lean`, `AXIOMS-ALLOWED` | — | — | The axiom audit (`node scripts/lean-axiom-check.mjs`): three standard axioms for Layer 1 and the symbolic proofs; `native_decide`'s per-theorem axiom for the rest of Layer 2 only. |
| `vectors/export.test.ts`, `vectors/sections.ts` | — | vitest | The exporter: builds the suite's honest and adversarial transactions and writes `Generated/`. |
| `scripts/*.py` | — | Python 3 | Generators of the long, regular proof files (`scripts/README.md`). |

## Layer 1 — the model and Theorems 1–5

`Accepts P fam s` (`Model/Covenant.lean`) is a structure of propositions, one field per clause of the seven
lemmas of `docs/formal-proof.md` §3, each a constraint the covenant of family `fam` puts on the
transaction `s` that spends a token:

| Field(s) | Lemma |
|---|---|
| `l1_owner`, `l1_sig`, `l1_type` | L1 signature binding: `H160(pk) = owner`, `Verify(pk, sighash, sig)`, flag `0x41` |
| `l2_outs`, `l2_melt` | L2 output determinism: the outputs are exactly `expectedOuts`, a split settle's two tokens in either order (`Spend.OutsOK`), then non-token change; a melt is P2PKH-only |
| `l3_rebuild`, `l3_merge` | L3 ancestor integrity: a settle with a grandparent rebuilds it, matches its txid, co-spends one of its proof outputs, at index `j`, and (fungible) carries the settle result that proof selects, the one at `j − 1` |
| `l4_null` | L4 null ancestor arguments when no rebuild runs |
| `l5_issuer`, `l5_no_merge_at_genesis` | L5 issuer enforcement, the NFT family's `is2ndTx` guard included |
| `l6_*` | L6 balance bounds: over-take and overflow guards at the commit, re-asserted at the settle |
| `commit_type`, `settle_type`, `commit_mode`, `settle_mode` | L7 the `txoType` state machine |

A **run** (`Model/Run.lean`) is a set of genesis tokens plus a sequence of spends; `Run.Valid` adds what
the chain enforces around the covenant: inputs are live and carry the fields the spend claims, new
transaction ids are fresh. The cryptographic assumptions are hypotheses, never axioms
(`Model/Assumptions.lean`): `CollisionFree P` (A1) and `OwnerSecrecy P pk signed` (A2).

| Hand proof | Lean theorem | Beyond `Valid` |
|---|---|---|
| T4 State machine | `t4_step`, `t4_defined_types`, `t4_no_skip` (`Theorems/StateMachine.lean`) | none |
| T3 Balance conservation | `Run.t3_conservation`, `Run.t3_no_melt`, `Run.t3_single_genesis`, `Run.t3_nft_count` (`Theorems/Balance.lean`) | none |
| T2 Ownership | `t2_presented`, `t2_ownership`, `t2_no_keyless_spend` (`Theorems/Ownership.lean`) | A2 for `t2_ownership` |
| T1 Authenticity | `Run.t1_authenticity`, `Run.t1_issuer_invariant`, `Run.t1_rebuild_sound`; per hop `t1_step`, `t1_genesis_signer` (`Theorems/Authenticity.lean`); `Run.grandparent_commit` (`Theorems/Chain.lean`) | A1 for `t1_rebuild_sound` |
| T5 Proof gating | `Run.t5_proof_gating`, `Run.t5_balance_anchor`, `Run.t5_fabricated_hop_excluded` (`Theorems/ProofGating.lean`) | the UTXO rule `NoDoubleSpend`; A1 for the balance anchor |

Three points where the Lean is sharper than the prose:

* **T3 counts value in flight, over the set of genesis tokens a run starts from.** A merge-commit token
  (`0x25`) carries the merged-in balance in `balanceCommit` until its settle adds it. `float + melted = Σ
  genesis` holds at every step; the hand proof's "per genesis" form is the single-genesis, no-melt
  corollary.
* **T1's "unique parentless root" is definitional.** `Run.root` is the parent walk through the outputs
  the run created; what is proved is that the walk is well-founded, ends at a genesis of the run, keeps
  the issuer, and that every link is an accepted spend whose types follow the machine (`Rooted`).
* **L2 and L3 admit exactly what the script admits.** A split settle's two tokens may come out in either
  order, and the anchor names the proof a settle co-spends rather than a position: the balance carried
  is the settle result at the index one below that proof. Both are safe: the order changes neither
  recipient nor balance, only a proof's recipient can spend it, the script forces the proof to the
  grandparent's first or, for a split, second output (`AnchorOK`), and T5 lets each proof admit one
  settle, so every settle result of a real commit is claimed at most once. The earlier position-based
  anchor was wrong in the swapped order (`smb_probe_idx_*`).

**T5** is the §8.1 fabricated-hop defence at the ledger level: under the UTXO rule two settles with
grandparents consume two distinct proof outpoints, so a commit's proof admits at most one settle, and
under A1 the balance a settle carries is the settle result of the real commit its grandparent names. A
fabrication that runs no script can exist on-chain, but it can extract nothing through a real proof
beyond the real transition.

## Layer 2 — the script on real transactions

Layer 2 runs the script with bsv-script-lean's consensus semantics (`BsvScript.Eval.verifyScript`: real
SHA-256, RIPEMD-160 and secp256k1 as Lean functions):

* `Bytes.lean`: each script hashes to the fingerprint the scanner's `REGISTRY` recognises it by, so the
  script reasoned about is the script shipped.
* `Generated/VectorTheorems.lean`: for each of 107 real transactions (245 inputs), every input's verdict
  is the expected one. The honest lifecycles of both families verify; every red-team transaction
  (`test/lib/minSimpleAttack.test.ts` B1–B4; the fungible inflated balance, split over-take, merge overflow,
  cross-issuer merge, raw-byte extra output, wrong-key spend, melt by a non-owner) fails at exactly the
  input the hand proof names; the probes of the questions register below are judged; the historical
  fabricated-hop chain (`test/fixtures/fabricated-hop-chain.json`) is accepted by the pre-fix script it
  embeds, reproducing what a regtest Teranode accepted.

These theorems use `native_decide`: the kernel trusts Lean's compiled evaluator for them, recorded as one
auxiliary axiom per theorem.

**Fragment proofs** (`Gadgets/`, no evaluator trust) prove pieces of the script over the interpreter's own
instruction loop for every input: one lemma per instruction (`Steps.lean`); Lemma 4's null-ancestor tail
(`NullAncestor.lean`); Lemma 6's commit guards and settle re-checks (`BalanceGuards.lean`,
`BalanceBounds.lean`), which refuse an inflating split or an overflowing merge at the commit; Lemma 7's
fungible parity check (`Parity.lean`: on the six type bytes it accepts iff `Fam.edge .fungible a b`) and
the NFT type selector (`NftType.lean`: the NFT scripts write the next type rather than check it, and the
written type is a `Fam.edge .nft` successor).

## The glue — the script enforces the model

**How.** Every step lemma is an inversion lemma on the remaining program: `run env (op :: g) t st = r →
r.IsOk → ⟨the fact the op checks⟩ ∧ ∃ m' k', run env g t st' = r` (`Glue/Sym/`). The `sym_all` driver
chains them over the script cut into named chunks (`Generated/Chunks.lean`; `Sections.lean` locates each
proved fragment at its offset), so a run of a whole suffix is a conjunction of facts about the stack it
started from. Limits need no hypotheses: a violation returns `.err`, which `IsOk` refutes. The unlocking
script is attacker-controlled and proves nothing (its own OP_PUSH_TX included): the proofs quantify over
whatever stack phase 1 leaves and never run it; the binding check is the lock's own OP_PUSH_TX block on
the preimage item.

**Per script.** `*_sound` says what the suffix enforces whenever it does not fail, path by path (the NFT
scripts' ten paths; the fungible script's commit, settle and melt paths by mode, with the twenty-four
refused type pairs in `SimpleMulti/Refute.lean`). `reaches_*` shows each proved fragment of `Gadgets/` is
reached with the stack its lemma assumes. `Abs.lean` reads a real spend into the model (`spendOf`: the
lock's fields become a `Token`, outputs become `Out`s by their scripts, the transaction a `TxDesc`).
`*_refines` proves `Accepts P fam (spendOf …)` from a valid verdict under the residual assumptions; the
fungible refinement has four stages (a commit, a settle without a grandparent or a melt; a transfer or
split settle with a grandparent; a merge commit with the partner input's run; a merge settle with both
rebuilds). `Regress.lean` applies every refinement to the real honest spends with each decidable
hypothesis discharged by `native_decide`. `EndToEnd.lean` states Lemma 1 and Theorems 1–4 per input of
the shipped bytes.

**The rebuilds.** A settle with a grandparent rebuilds it from pieces the unlocking script supplies, hashes
the bytes against the token's grandparent txid and anchors the spent balance to the rebuilt token's.
Under no second preimage of the real grandparent's serialisation, the bytes are that serialisation, so the
proof parses them (`Rebuilt.lean`, `decode_rebuiltA`), identifies the parsed transaction with the real one
(`GpWeld.lean`, `gp_eq_gpTxA`), reads its first output as the pieces' token (`Anchor.lean`) and turns the
anchor into the model's `settledBalance` (`anchorOK_settled`); the anchor also fixes the co-spent index to
1, or to 2 for a split-commit grandparent (`AnchorOK.index`). A merge settle's second rebuild, of the
other lineage's grandparent, is welded the same way (`RebuiltBParse.lean`, `AnchorB.lean`,
`GpWeldB.lean`; `anchorB_index` for its index argument `i4`).

**The chain** (`Refine/Chain.lean`, `AuthBolt/Chain.lean`, `SerialBolt/Chain.lean`, `SimpleMulti/Chain.lean`). A run whose steps are real spends, each read
by its refinement, with the UTXO model's bookkeeping (a well-formed genesis set, each step spending live
tokens, each transaction id new: `RealChain`), is valid (`valid_of_chain`). The induction is
`Run.valid_of_stepwise`; at each step the grandparent a settle names is read off the valid prefix: it is
output 0 of an earlier commit step with the honest layout (`Run.grandparent_layout_upto`), which
discharges `GpReal` outright for the three NFT scripts and, under A1 to identify the ancestor the settle
supplies with that step, `GpRealF` and `GpRealB` for the fungible one; the grandparent token output's balance
signs `GpRealF` needs are read off that creating commit's own bound check (`chainStep_commit_bals`), not assumed,
after the grandparent is identified with the commit's transaction byte for byte (`tx_eq_of_txid`). Theorems 1, 3, 4 and 5 then hold
of real tokens: `chain_authenticity`, `chain_count` / `chain_conservation`, `chain_defined_types`,
`chain_proof_gating`, `chain_fabricated_hop_excluded`.

**What each refinement assumes** (`Residual`, one per script; the fungible one adds `ResidualGp` and
`GpRealB` on the settle stages):

* `PushTxSound`: a preimage the lock's own OP_PUSH_TX block accepts hashes to this spend's digest (the
  ECDSA algebra of the fixed-key signature, with the negligible root cases excluded).
* `NoSecondPreimage` of what the spend hashes: the preimage, the serialised outputs and outpoints, the
  grandparents' serialisations (A1 stated on the spend's own data).
* `Agrees`: the primitives `P` compute `hash160` and this spend's `OP_CHECKSIG`, and the primitives' txid of
  an ancestor's abstraction is its real txid.
* `HonestOutputs`, `HonestMelt`: three model rules the script does not check and that are not security
  properties (Finding 1 below): the change blob carries no token, a melt pays P2PKH only in a version-2
  transaction. Anyone can create a token-shaped output anywhere; the lineage check at spend time, which is
  proved, carries the security.
* `GpReal`, `GpRealF`, `GpRealB`: the grandparent a settle names is real, well-formed, with the token at the
  named index and the proof outputs of a commit. Per input an assumption; over a chain, proved.
* SimpleMultiBOLT only: the six protocol types (Q4, the restriction the probes back; see the questions register below), the rebuilds' pieces named at their fields' widths
  (`HonestPiecesB`, both piece sets; Q7, a representation choice, not an enforcement gap: the covenant
  concatenates the pieces and hashes the result, so the binding is the hash, not the split), and the merge
  partner presenting a preimage (Q8).
* Lock-data conditions every covenant-built token meets, asked of the spent token: a genesis token is settled-typed,
  a non-merge token names no other lineage, the balance is in range, a split's second recipient is not the zero hash
  (fungible); the recipient hash and the signing key at their widths, which the bytes copy into the new lock
  unchecked (`ArgsWF`, all four). `Regress.lean` checks them on the vectors.
* Over the fungible chain, also A1, and each step's txid agreement (that the primitives compute the step
  transaction's real txid, `hptxid`, the A1-style fact the NFT chain's `ChainSpend` also carries). No byte-level
  balance fact is assumed: the grandparent token output's balance signs are read off the commit step that wrote
  them (`chainStep_commit_bals`, `ChainBals.lean`), from the covenant's own bound check.

**Findings.** What the glue found that the prose did not say, each pinned by a vector where one applies:

1. Two model clauses are not enforced by the script: the melt branch constrains no output, and the change
   blob is concatenated unparsed into `hashOutputs`, so it can carry several outputs, token-shaped ones
   included (`nft_probe_melt_token_output`, `nft_probe_change_*`). The refinements take them as
   `HonestMelt` and `HonestOutputs`; the model keeps the clauses.
2. The NFT prologue fragment `76 81 92` tests the grandparent outpoint, not the type, and the type
   selector reads the raw type byte.
3. Both families require the issuer at the first settle as well as the first commit
   (`docs/issuer-guard.md`); the fungible guard also refuses `0x25` and `0x27` as next types there, and
   the written type comes from the mode flags, not the byte (`smb_probe_type27_commit`).
4. `smb_wrong_key_commit#0` is refused by the issuer guard, `smb_extra_output_settle#0` by the unlocking
   script's own OP_PUSH_TX, not the covenant.
5. A merge's carried balance is checked at the settle, not the commit (Q8, `smb_probe_q8_*`): a merge
   commit whose partner input takes the melt branch is accepted whatever balance it claims; the settle
   claiming 1,000,000 for a token of balance 1 is refused. An inflated merge commit can exist but never
   settles.
6. A token's index byte is informational and no token dies of it (Q3, `smb_probe_idx_*`, 20 vectors;
   `test/lib/indexByte.test.ts`): with `pkh1` set a split settle's tokens come out swapped, with `i2` or
   `inputIndexN` set a token carries a byte that is not its position, and every later operation accepts
   it. No spend reads the byte. Dropping it is recorded in `docs/ROADMAP.md`.
7. A merge settle's other-lineage index is pinned to a proof output (Q9, `smb_probe_q9_*`): naming the
   other grandparent's change output and spending it in the proof input's place is refused; the second
   rebuild's anchor pins `i4` to 1 or, under the split type, to 2 (`anchorB_index`).
8. Smaller byte-level facts. No script checks the `fd` of the preimage's scriptCode varint (the NFT scripts drop
   the byte at 104, the fungible parse accepts any width), so the proofs take it from the preimage the lock's
   OP_PUSH_TX block weighed (`preimage_varint`). Only the txid half of the grandparent outpoint is bound by the
   rebuild; the index half comes from `GpReal`, over a chain from the run's layout. A settle at genesis takes the
   signing key as the new token's issuer, like a commit. A `0x25` token's `balanceCommit` is unanchored until its
   settle (Finding 5).
9. **BENIGN — not an attack vector, SimpleMultiBOLT only.** An undefined next type cannot be committed (Q4,
   `smb_probe_type_oor_*`, `smb_probe_type27_commit`): the parity check fixes only the next type's parity, and
   the issuer guard refuses `0x27` only when it fires, but a mid-lineage commit to an undefined type (the guard
   silent) is refused at the covenant's own output `OP_EQUALVERIFY`: the token the covenant rebuilds carries the
   mode-flag-derived type, one of the six (Finding 3), so an output claiming an undefined type cannot match
   `hashOutputs`. The written type is thus pinned to the six. This is a spender malforming the successor of their
   own token — refused by the script, counterfeiting nothing. It is SimpleMultiBOLT only: the NFT scripts
   (MinSimpleBOLT, AuthBOLT, SerialBOLT) write the next type rather than check a claimed one (`NftType.lean`), so
   they carry no such seam. The `SmbType a.nty` restriction in the proofs is the modelling boundary, not a gap
   the bytes leave open (see the questions register below).

**Questions raised, and how each was resolved.** Q4 (**RESOLVED, BENIGN — SimpleMultiBOLT only; a spender malforming their own token's successor,
refused by the script and counterfeiting nothing; the NFT family writes the type and has no such seam**): off
genesis, the parity check only fixes the next type's parity, so a settled token's spend may name any odd byte. Whether an undefined next type can be committed is resolved by probe: the issuer
guard refuses `0x25` and `0x27` only when it fires (genesis or no grandparent), but a mid-lineage commit whose
spent token has a grandparent (the guard silent) and an undefined next type is refused at the covenant's own
`OP_EQUALVERIFY` too (`smb_probe_type_oor_27_commit`, `smb_probe_type_oor_29_commit`, and the honest-shaped
`smb_probe_type27_commit`), so no undefined-typed token can be committed. The covenant's own check pins the
written type to the six. `simpleMulti_sound` and the refinement still carry the restriction `SmbType a.nty`
rather than deriving that refusal. The output-hash injectivity such a derivation would use is already assumed
(`NoSecondPreimage` of the serialised outputs, `Residual.outputs`); what is missing is the symbolic execution,
not a lemma — driving a symbolic undefined next type through the whole output builder to read off that the
rebuilt type is one of the six and so cannot be the claimed byte. The driver reaches that `OP_EQUALVERIFY` only
after the full reconstruction and does not refute a symbolic undefined type at bounded cost, so this
path-family proof is deferred, with the probes as the standing evidence. Q7 is not an open enforcement
question: the covenant concatenates the rebuild's pieces and hashes the result against the grandparent's
txid, and never parses the concatenation back into fields, so no contract operation splits the bytes at the
field boundaries and there is nothing for the bytes to force. `HonestPiecesB` names the pieces at their
fields' widths as the honest spender supplies them; the binding is carried by the hash, which under no
second preimage makes the concatenation the real grandparent's serialisation whatever the split. It is
discharged on every real spend in `Regress.lean`. Q1 (Finding 1) was decided for the hypothesis route; Q2 (the token at
input 0) is derived from the bytes; Q3, Q6 and Q9 are closed by model and lemma; Q5 was retracted (a probe
had recorded a false literal fact; every probe is now scanned for them); Q8 is settled at the vector level
and kept as the hypothesis `hpre'`.

**Follow-ups.** If the `SmbType a.nty` restriction is to be dropped formally, the path-family proof that the
output builder refuses an undefined next type (Q4, already resolved by probe): the output-hash injectivity it
needs is already assumed (`Residual.outputs`), so the work is the symbolic drive of a symbolic next type
through the builder, which does not refute at bounded cost today. `BalsNonneg` is shed: the
grandparent's balance signs are now derived from its creating commit (`chainStep_commit_bals`).

**Generators.** The long, regular files (the path theorems, the rebuilds' arms and parses, the gate items,
the guards) are written by `scripts/*.py` (`scripts/README.md`); a generated file says so in its header.
The audit holds every theorem outside `BoltProof.Bridge.*` to the three standard axioms, so the symbolic
glue lives under `BoltProof.Glue`, the `native_decide` guards under `BoltProof.Bridge.Glue`.

## What is still trusted

**BY DESIGN — this is the proof's trust base, not a defect list, and it is compressed to its irreducible core.**
You cannot prove a hash collision-free (A1/A2), you must judge against some consensus ruleset, and you need the
kernel's axioms and bsv-script-lean's transcription of the node. The development has actively shed assumptions
into derivations rather than parking them (the grandparent's balance signs, its reality over a chain, the split
order and the proof and merge indices), leaving only what no proof of this kind can remove.

| Item | Status |
|---|---|
| That the script enforces the model on *every* input (A4 + L1–L7 fidelity) | **Proved for all four scripts, per input, under the assumptions listed above; proved over a chain for all four scripts.** Layer 2 still evidences all four on 245 inputs. |
| A1 collision resistance, A2 EUF-CMA | Hypotheses of `t1_rebuild_sound`, the fungible chain and `t2_ownership`; everything else is unconditional. |
| A3 chain finality | Not modelled (inherited, as in the hand proof). |
| bsv-script-lean's transcription of the node | Their `docs/HYPOTHESES.md`; pinned at v1.2.0, commit `6139161c`. |
| The judging rules | **Today's BSV rules only** (post-Chronicle, `Bridge/Params.lean`: the block path, no `MINIMALIF`, FORKID signatures, the `codeSep ++ lock` scriptCode b017's OP_PUSH_TX signs). `paramsPreChronicle` is a control, printed beside each verdict by `lake exe boltvectors`. |
| The native evaluator (`native_decide`'s per-theorem axiom) | The vector checks and the regression guards only. Layer 1 and the glue never use it. |

## The issuer guards

Both families require the issuer's signature at the first settle as well as the first commit.
[`docs/issuer-guard.md`](../docs/issuer-guard.md) decodes both prologues and gives the history: `is2ndTx`
is the NFT family's flag, the fungible rule (the F3 fix) is broader, and porting `is2ndTx` would close
nothing. The symbolic execution proves both rules from the script for every input (`Enforced.issuer` in
each `*_sound`): NFT, `parent = 0 ∨ (gp = 0 ∧ txoType = 0x21) → issuer = pubKey`; fungible,
`parent = 0 ∨ gp = 0 → issuer = pubKey ∧ nextTxoType ∉ {0x25, 0x27}`. The model's L5 clause asks the issuer
at genesis only for the fungible family, weaker than the script, so the proof derives it; for the NFT
family it states the guard as the script has it.

## Building

```
# toolchain: lean/lean-toolchain pins leanprover/lean4:v4.34.0 (the one bsv-script-lean v1.2.0 uses)
cd lean
lake exe cache get      # Mathlib's prebuilt .olean files (bsv-script-lean depends on Mathlib)
lake build              # BoltProofCore (seconds) + BoltProofBridge (bsv-script-lean, the vectors, the fragment and symbolic proofs)
lake exe boltvectors    # every vector natively, with the control columns
cd .. && node scripts/lean-axiom-check.mjs
```

`lake build BoltProofCore` needs neither Mathlib nor bsv-script-lean and builds in seconds. The glue takes about
30 minutes of wall time on four cores and 15 GB; `SimpleMulti/Settle/Split.lean` peaks near 8 GB and the fungible
`Refute.lean` needs several gigabytes, so on a smaller machine build it alone first
(`lake build BoltProof.Bridge.Glue.SimpleMulti.Refute`). CI's `lean-proof` job restores the previous build from
its cache and rebuilds only what depends on a change; a change to the model or a spec rebuilds the glue, 50 to 70
minutes against the 90-minute limit.

Regenerate the vectors after any change to a covenant template, a test helper, or an expectation:

```
npm run lean:vectors    # rewrites lean/BoltProof/Bridge/Generated/ and lean/vectors/vectors.json
```

The output is deterministic (fixed keys, RFC6979 signatures); CI regenerates and fails on drift. Exact
bsv-script-lean error codes are pinned in `PINNED` in `vectors/export.test.ts` from a triage run of
`boltvectors`; an unpinned rejection is `anyInvalid`.

Never run `lake update` casually: `lake-manifest.json` pins bsv-script-lean and, through it, Mathlib. To
bump bsv-script-lean, change `rev` in `lakefile.toml`, copy its `lean-toolchain`, run `lake update
bsvscript`, rebuild, and re-triage the vectors.

## Credits and license

bsv-script-lean is consumed as a Lake dependency, not vendored. Its Lean sources are under the Open BSV
License v5 (the same license as this package); its tooling is Apache-2.0. See its `NOTICE`.
