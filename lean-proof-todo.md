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
  - [ ] L6, the split over-take and merge sum guards (`… OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY`,
        `… OP_ADD … OP_LESSTHANOREQUAL OP_VERIFY`).
  - [ ] L7, the `txoType` parity check.
- [ ] Pin the exact `ScriptError` of every rejected vector (`PINNED` in `lean/vectors/export.test.ts`).
- [ ] A ledger-level theorem (T5) that every settle with a grandparent consumes the proof of a unique real
      commit — the fabricated-hop exclusion stated above the single-spend interface.
- [ ] Decide the `is2ndTx` question recorded in `lean/README.md` (redundant on honest chains vs hardening the
      fungible family lacks).
