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
  - [ ] L6, the settle-side re-checks (`… OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_ADD OP_DUP OP_14 OP_PICK
        OP_LESSTHANOREQUAL OP_VERIFY …`, needs OP_DUP and OP_14).
  - [ ] L7, the `txoType` parity check.
- [ ] Pin the exact `ScriptError` of every rejected vector (`PINNED` in `lean/vectors/export.test.ts`).
- [x] A ledger-level theorem (T5) that every settle with a grandparent consumes the proof of a unique real
      commit — the fabricated-hop exclusion stated above the single-spend interface
      (`lean/BoltProof/Theorems/ProofGating.lean`: `t5_proof_gating`, `t5_balance_anchor`,
      `t5_fabricated_hop_excluded`; hypotheses: the UTXO no-double-spend rule and collision-freeness).
- [ ] Decide the `is2ndTx` question recorded in `lean/README.md` (redundant on honest chains vs hardening the
      fungible family lacks).
