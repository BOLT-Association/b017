import BoltProof.Model.Family

/-!
# BoltProof.Model.Token

A token state `T(n)` (`docs/formal-proof.md` §1.3): the data pushes of a BOLT locking script,
abstracted. The fungible covenant carries every field below; the NFT family carries no
balance (`balance = balanceCommit = 0`), no second commitment and no `otherGrandparent`.
-/

namespace BoltProof

/-- A token state: the fields of one BOLT UTXO's locking script. -/
structure Token (Txid : Type) where
  /-- `pubKeyHash`: the current owner, `hash160 pk`. -/
  owner : PKH
  /-- `pubKeyHashCommit`: the recipient named by a commit (zeros on a settle-typed token). -/
  commitment : PKH
  /-- `pubKeyHashCommit2`: the second recipient of a split commit (fungible only). -/
  commitment2 : PKH
  /-- `txoType`: the state-machine byte (Lemma 7). -/
  txoType : Nat
  /-- `parentOutpoint`: `T(n−1)`, or `none` at a genesis. -/
  parent : Option (Outpoint Txid)
  /-- `grandparentOutpoint`: `T(n−2)`, or `none` when `n < 2`. -/
  grandparent : Option (Outpoint Txid)
  /-- `otherGrandparentOutpoint`: the second input's lineage on a merge (fungible only). -/
  otherGrandparent : Option (Outpoint Txid)
  /-- `issuerPubKey`: immutable along a lineage (Theorem 1). -/
  issuer : PubKey
  /-- `balance` (fungible). -/
  balance : Nat
  /-- `balanceCommit`: the split piece or the merged-in balance carried on a commit (fungible). -/
  balanceCommit : Nat
deriving DecidableEq, Repr

namespace Token

variable {Txid : Type}

/-- A token is a **genesis** iff it is parentless (§1.3: genesis is derived, not stored). -/
def isGenesis (t : Token Txid) : Prop := t.parent = none

/-- The NFT family's `is2ndTx` flag: the token being spent is commit-typed and has no
grandparent, i.e. it is the output of the first commit of its lineage. -/
def is2ndTx (t : Token Txid) : Prop := t.txoType ≠ 0x00 ∧ t.grandparent = none

/-- **Lemma 5 trigger.** The issuer must sign the spend of a parentless token (both families)
and, in the NFT family only, the spend of a first-commit output (`is2ndTx`). -/
def issuerMustSign (fam : Fam) (t : Token Txid) : Prop :=
  t.isGenesis ∨ (fam = .nft ∧ t.is2ndTx)

instance (t : Token Txid) : Decidable t.isGenesis := by unfold Token.isGenesis; exact inferInstance

instance (t : Token Txid) : Decidable t.is2ndTx := by unfold Token.is2ndTx; exact inferInstance

instance (fam : Fam) (t : Token Txid) : Decidable (t.issuerMustSign fam) := by
  unfold Token.issuerMustSign; exact inferInstance

/-- The value a token holds, counting value in flight: a merge-commit-typed token (`0x25`)
has consumed a second token whose balance it carries in `balanceCommit` until the settle
adds it in. Theorem 3 conserves this quantity at every step. -/
def value (t : Token Txid) : Nat :=
  if t.txoType = 0x25 then t.balance + t.balanceCommit else t.balance

/-- **Lemma 6.** The balance of the settle output at index `i` when the commit-typed token
`t` is settled: transfer copies, split yields `balance − piece` then `piece`, merge sums. -/
def settledBalance (fam : Fam) (t : Token Txid) (i : Nat) : Nat :=
  match fam.modeOfCommitType t.txoType with
  | some .transfer => t.balance
  | some .split => if i = 0 then t.balance - t.balanceCommit else t.balanceCommit
  | some .merge => t.balance + t.balanceCommit
  | none => t.balance

end Token

end BoltProof
