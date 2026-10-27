import BoltProof.Model.Prelude
import BoltProof.Model.Family
import BoltProof.Model.Token
import BoltProof.Model.Spend
import BoltProof.Model.Assumptions
import BoltProof.Model.Covenant
import BoltProof.Model.Run
import BoltProof.Theorems.RunLemmas
import BoltProof.Theorems.StateMachine
import BoltProof.Theorems.Balance
import BoltProof.Theorems.Ownership
import BoltProof.Theorems.Authenticity

/-!
# BoltProof.Core

Layer 1 of the BOLT machine-checked security argument: the protocol model (the covenant
*interface*, L1-L7 of `docs/formal-proof.md`) and Theorems 1-4 proved against it.

This library depends on core Lean only. `#print axioms` on every theorem reports at most
`propext`, `Classical.choice` and `Quot.sound` (see `AxiomCheck.lean`).
-/
