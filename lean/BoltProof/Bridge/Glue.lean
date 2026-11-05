import BoltProof.Bridge.Glue.Sections
import BoltProof.Bridge.Glue.Sym.Basic
import BoltProof.Bridge.Glue.Sym.Steps

/-!
# BoltProof.Bridge.Glue

The glue between the fragment proofs of `Gadgets/` and the shipped covenant bytes
(`lean/GLUE-PLAN.md`). Everything under `BoltProof.Glue` is symbolic and held to Layer 1's axiom
rules; the few evaluator-trusted identities live in `BoltProof.Bridge` (`Bridge/Bytes.lean`).
-/
