import BoltProof.Theorems.RunLemmas

/-!
# Theorem 2 — Ownership

`docs/formal-proof.md` §5: given `T(n)`, no adversary lacking the secret key behind
`owner(T(n))` can produce a valid transition. The first theorem is unconditional (what the
covenant demands: Lemma 1); the second adds Assumption 2 as the hypothesis `OwnerSecrecy`.
Melt is covered: `Accepts` demands Lemma 1 for every kind.
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

/-- **Lemma 1 as a theorem.** An accepted spend presents a public key hashing to the owner,
a signature that verifies over *this* transaction's `SIGHASH_ALL | FORKID` digest, and the
`0x41` flag byte. -/
theorem t2_presented {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s) :
    P.h160 s.signer = s.spent.owner ∧
    P.verify s.signer (P.sighash s.tx s.inputIndex) s.sig = true ∧
    s.sigHashType = 0x41 :=
  ⟨h.l1_owner, h.l1_sig, h.l1_type⟩

/-- **Theorem 2 (Ownership).** If `pkO` is the owner's key and Assumption 2 holds for it, an
accepted spend of the token means the holder of `pkO`'s secret key signed this very
transaction (`SIGHASH_ALL` commits the signature to all of its outputs). -/
theorem t2_ownership {P : Prims Txid} {fam : Fam} {s : Spend Txid} {pkO : PubKey}
    {signed : Msg → Prop} (hO : P.h160 pkO = s.spent.owner) (hS : OwnerSecrecy P pkO signed)
    (h : Accepts P fam s) : signed (P.sighash s.tx s.inputIndex) := by
  have e : s.signer = pkO := hS.h160_unique _ (h.l1_owner.trans hO.symm)
  exact hS.euf _ _ (e ▸ h.l1_sig)

/-- **Theorem 2, contrapositive.** An adversary who never obtained the owner's signature on
this transaction cannot make the covenant accept the spend. -/
theorem t2_no_keyless_spend {P : Prims Txid} {fam : Fam} {s : Spend Txid} {pkO : PubKey}
    {signed : Msg → Prop} (hO : P.h160 pkO = s.spent.owner) (hS : OwnerSecrecy P pkO signed)
    (hn : ¬ signed (P.sighash s.tx s.inputIndex)) : ¬ Accepts P fam s :=
  fun h => hn (t2_ownership hO hS h)

end BoltProof
