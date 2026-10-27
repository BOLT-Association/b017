import BoltProof.Bridge.Params
import BoltProof.Bridge.Generated.Bytes
import BoltProof.Bridge.Generated.Vectors
import BoltProof.Bridge.Bytes
import BoltProof.Bridge.Generated.VectorTheorems

/-!
# BoltProof.Bridge

Layer 2: the shipped covenant bytes and real transactions, evaluated inside Lean by the
bsv-script-lean consensus semantics. Theorems in this library use `native_decide`
(`Lean.ofReduceBool`) in addition to Lean's three standard axioms.
-/
