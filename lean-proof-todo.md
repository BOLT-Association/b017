# Lean Proof TODO

- [x] Use the Lean verifier (here: https://t.co/u1q9ojZBPO, i.e. https://github.com/Calhooon/bsv-script-lean)
      to prove protocol security — see `lean/README.md`; CI job `lean-proof`.
      Done: Theorems 1–4 proved in Lean from the covenant interface (Lemmas 1–7) for both families; the shipped
      covenant bytes run on the test suite's real transactions inside Lean with bsv-script-lean v1.2.0.

Follow-ups (the residual trust boundary, in order of value):
- [ ] Fragment-level proofs that the compiled covenant enforces the interface clauses, with bsv-script-lean's
      `Gadget` API. Each closes part of the bytecode-to-interface gap that Layer 2 only samples.
  - [x] L4, the null-ancestor size check's tail `OP_SIZE OP_NIP OP_0 OP_EQUALVERIFY`
        (`lean/BoltProof/Bridge/Gadgets/NullAncestor.lean`), plus the per-instruction step lemmas it rests on
        (`Steps.lean`: SIZE, NIP, OP_0, a one-byte push, EQUALVERIFY, VERIFY, GREATERTHANOREQUAL, SUB, PICK).
  - [x] L6, the split over-take guard `2d OP_PICK 34 OP_PICK OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY`
        (`lean/BoltProof/Bridge/Gadgets/BalanceGuards.lean`).
  - [x] L6, the merge sum guard `2d OP_PICK 34 OP_PICK OP_ADD OP_11 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY`
        (`BalanceGuards.lean`; step lemmas for OP_ADD, OP_LESSTHANOREQUAL and OP_11 added).
  - [x] L6, the balance bounds and the settle-side re-checks (`lean/BoltProof/Bridge/Gadgets/BalanceBounds.lean`:
        `boundCheck` at offsets 610/621, the merge settle's `mergeSettle` at 781, the split settle's `splitSettle`
        at 935; step lemmas for OP_5 and OP_14 added).
  - [x] The glue between fragments: that the covenant reaches each fragment with the fields at the depths the
        lemmas name, and that it enforces `Accepts` on every input (`lean/GLUE-PLAN.md`, M1–M7). A symbolic,
        inversion-style run of each shipped suffix from the stack the unlocking script leaves
        (`lean/BoltProof/Bridge/Glue/`): `minSimple_sound`, `simpleMulti_sound`, `authBolt_sound`,
        `serialBolt_sound` with the `reaches_*` theorems for every proved fragment, and the refinements
        `minSimple_refines`, `simpleMulti_refines_{basic,settle_gp,merge_commit,merge_settle}`,
        `authBolt_refines`, `serialBolt_refines` to `Accepts`, each with its residual assumptions stated and
        applied to the real vectors (`Regress.lean` per family). Still open, recorded in `GLUE-PLAN.md` §7: the
        composition of real spends into a model `Run`, and the fungible family's four residual questions (next
        types beyond the six, the rebuild's piece widths, the anchor index, a merge's other input).
  - [x] L7, the fungible `txoType` parity check (`lean/BoltProof/Bridge/Gadgets/Parity.lean`: accepts iff the
        hand proof's predicate holds, and iff `Fam.edge .fungible a b` on the defined type bytes; step lemmas for
        OP_1, OP_2, OP_MOD, OP_1ADD, OP_DUP, OP_SWAP, OP_IF/OP_ELSE/OP_ENDIF and skipped instructions added).
  - [x] L7, the NFT family's type selector (`lean/BoltProof/Bridge/Gadgets/NftType.lean`: the
        `d OP_PICK OP_IF 0100 OP_ELSE 0121 OP_ENDIF OP_CAT` selector of all three NFT covenants writes a
        `Fam.edge .nft` successor type; step lemmas for a two-byte push, OP_CAT, OP_BIN2NUM and OP_0NOTEQUAL
        added. The prologue's `OP_DUP OP_BIN2NUM OP_0NOTEQUAL`, once read as the type flag, runs on the
        grandparent outpoint: the glue found it and the file now says so).
- [x] Pin the exact `ScriptError` of every rejected vector (`PINNED` in `lean/vectors/export.test.ts`). Done: all
      27 rejected inputs in `lean/vectors/vectors.json` carry a pinned code; none is `anyInvalid`.
- [x] A ledger-level theorem (T5) that every settle with a grandparent consumes the proof of a unique real
      commit — the fabricated-hop exclusion stated above the single-spend interface
      (`lean/BoltProof/Theorems/ProofGating.lean`: `t5_proof_gating`, `t5_balance_anchor`,
      `t5_fabricated_hop_excluded`; hypotheses: the UTXO no-double-spend rule and collision-freeness).
- [x] Compose real spends into a model `Run` (`lean/GLUE-PLAN.md` M4's Option A): discharges `GpReal` and lifts the
      per-input results of the two `EndToEnd.lean` files to Theorems 1 and 5 for real tokens. Done:
      `Bridge/Glue/Refine/Chain.lean` and `Glue/SimpleMulti/Chain.lean` (`RealChain`, `valid_of_chain`, the
      `chain_*` theorems) over `Run.valid_of_stepwise` and the `*_upto` lemmas of `Theorems/Chain.lean`. `GpReal` is
      discharged outright for the NFT script, and for the fungible one under A1 plus two facts read off the
      ancestors' bytes (`BalsNonneg`, and Q9's `i4` naming a proof output).
- [ ] Shed the two byte-level facts the fungible chain still reads off the ancestors: the balance signs from the
      commit paths' output bytes (`BalsNonneg`), and the second rebuild's index `i4` from `rebuildB_k` (Q9), as
      `AnchorOK.index` did for `i5`.
- [ ] State the chain for AuthBOLT and SerialBOLT: their `Residual.gp` is already settle-only, and the file is
      MinSimple's over their abstraction.
- [x] Decide the model's reading of the two probed quirks (`GLUE-PLAN.md` §7). Done for Q3 and Q6: the model admits
      either split order (`Spend.OutsOK`) and anchors by the co-spent proof's index (`l3_rebuild`), safely (the
      Lean README says why). Q8 stays the hypothesis `hpre'`.
- [x] Shed the coverage hypotheses the model no longer needs: `splitFlags` (the swapped order from
      `settleOuts_22`'s other flag cases in `outs_settle_split`) and `i5` (read the index from `AnchorOK`, state
      `GpRealF.proof` at it). Done: `Residual` and `ResidualGp` no longer name them (`AnchorOK.index`,
      `GpRealF.proof1`/`proof2`); the fungible residuals are Q4, Q7 and Q8.
- [x] Decide the issuer-guard question: decided in `docs/issuer-guard.md`. Both families have the second-spend
      guard (the glue proves it from the bytes); `is2ndTx` is not to be ported; aligning the NFT rule with the
      fungible one is deferred to the next NFT bytecode rebuild (`docs/ROADMAP.md`).
