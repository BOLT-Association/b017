# Lean Proof TODO

- [x] Use the Lean verifier (here: https://t.co/u1q9ojZBPO, i.e. https://github.com/Calhooon/bsv-script-lean)
      to prove protocol security — see `lean/README.md`; CI job `lean-proof`.
      Done: Theorems 1–4 proved in Lean from the covenant interface (Lemmas 1–7) for both families; the shipped
      covenant bytes run on the test suite's real transactions inside Lean with bsv-script-lean v1.2.0.

Follow-ups (the residual trust boundary, in order of value):
- [ ] Fragment-level proofs that the compiled covenant enforces the interface clauses, with bsv-script-lean's
      `Gadget` triples: the `txoType` parity check (L7), the null-ancestor size check (L4), the split/merge
      guards (L6). Each closes part of the bytecode-to-interface gap that Layer 2 only samples.
- [ ] Pin the exact `ScriptError` of every rejected vector (`PINNED` in `lean/vectors/export.test.ts`).
- [ ] A ledger-level theorem (T5) that every settle with a grandparent consumes the proof of a unique real
      commit — the fabricated-hop exclusion stated above the single-spend interface.
- [ ] Decide the `is2ndTx` question recorded in `lean/README.md` (redundant on honest chains vs hardening the
      fungible family lacks).
