import BoltProof.Model.Prelude

/-!
# BoltProof.Model.Family

The two covenant families covered by `docs/formal-proof.md`:

* `fungible` — `SimpleMultiBOLT`: 16-byte balance; transfer, split and merge; `txoType`
  machine `0x20..0x25` (Lemma 7).
* `nft` — the `MinSimpleBOLT` identity family (`MinSimpleBOLT`, `AuthBOLT`, `SerialBOLT`):
  no balance, transfer only, `txoType` machine `0x00 ↔ 0x21`, and the `is2ndTx` issuer guard.

Everything that differs between the families is a function of `Fam`, so one model and one
set of theorems serve both.
-/

namespace BoltProof

/-- The covenant family. -/
inductive Fam
  | fungible
  | nft
deriving DecidableEq, Repr

/-- A commit's mode. The NFT family only transfers. -/
inductive Mode
  | transfer
  | split
  | merge
deriving DecidableEq, Repr

namespace Mode

/-- The commit-typed `txoType` byte a commit of this mode produces (odd, Lemma 7). -/
def commitType : Mode → Nat
  | .transfer => 0x21
  | .split => 0x23
  | .merge => 0x25

end Mode

namespace Fam

/-- The commit-typed (odd) `txoType` bytes a family uses. -/
def commitTypes : Fam → List Nat
  | .fungible => [0x21, 0x23, 0x25]
  | .nft => [0x21]

/-- The settle-typed (even) `txoType` bytes a family uses; the genesis carries one of these. -/
def settleTypes : Fam → List Nat
  | .fungible => [0x20, 0x22, 0x24]
  | .nft => [0x00]

/-- The settle type forced by spending a commit-typed token of type `a` (Lemma 7:
`nextTxoType == txoType − 1` for the fungible covenant; the NFT settle type is `0x00`). -/
def settleOf : Fam → Nat → Nat
  | .fungible, a => a - 1
  | .nft, _ => 0x00

/-- The mode a commit-typed byte encodes, if the family admits it. -/
def modeOfCommitType : Fam → Nat → Option Mode
  | .fungible, 0x21 => some .transfer
  | .fungible, 0x23 => some .split
  | .fungible, 0x25 => some .merge
  | .nft, 0x21 => some .transfer
  | _, _ => none

/-- **Lemma 7 (state machine)** as an edge relation on `txoType` bytes: spending a settle-typed
token may produce any of the family's commit types; spending a commit-typed token produces
exactly its matching settle type. -/
def edge (fam : Fam) (a b : Nat) : Prop :=
  (a ∈ fam.settleTypes ∧ b ∈ fam.commitTypes) ∨ (a ∈ fam.commitTypes ∧ b = fam.settleOf a)

instance (fam : Fam) (a b : Nat) : Decidable (fam.edge a b) := by
  unfold edge; exact inferInstance

/-- Every balance the fungible covenant accepts is bounded by `2^127 − 1` (Lemma 6). -/
def maxBalance : Nat := 2 ^ 127 - 1

end Fam

end BoltProof
