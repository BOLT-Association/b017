import BoltProof.Bridge.Params
import BoltProof.Bridge.Generated.Bytes
import BoltProof.Bridge.Generated.Vectors
import BoltProof.Bridge.Bytes
import BoltProof.Bridge.Generated.VectorTheorems
import BoltProof.Bridge.Gadgets.Steps
import BoltProof.Bridge.Gadgets.NullAncestor
import BoltProof.Bridge.Gadgets.BalanceGuards
import BoltProof.Bridge.Gadgets.Parity
import BoltProof.Bridge.Gadgets.NftType
import BoltProof.Bridge.Gadgets.BalanceBounds

/-!
# BoltProof.Bridge

Layer 2: the shipped covenant bytes and real transactions, evaluated inside Lean by the
bsv-script-lean consensus semantics. The vector and fingerprint theorems use `native_decide`
(one auxiliary axiom per theorem) in addition to Lean's three standard axioms; the fragment
proofs under `Gadgets/` use the three standard axioms only.
-/
