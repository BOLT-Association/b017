import BoltProof.Theorems.RunLemmas

/-!
# Theorem 4 — State-Machine Integrity

`docs/formal-proof.md` §7: every valid chain alternates commit and settle transitions; no
transition can skip a step or produce an undefined `txoType`. The theorems here are
**unconditional**: they use no cryptographic hypothesis, only the covenant interface.
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

/-- The fungible machine, enumerated: exactly the twelve edges of §7. -/
theorem Fam.fungible_edge_iff (a b : Nat) :
    Fam.edge .fungible a b ↔
      ((a = 0x20 ∨ a = 0x22 ∨ a = 0x24) ∧ (b = 0x21 ∨ b = 0x23 ∨ b = 0x25)) ∨
      (a = 0x21 ∧ b = 0x20) ∨ (a = 0x23 ∧ b = 0x22) ∨ (a = 0x25 ∧ b = 0x24) := by
  simp only [Fam.edge, Fam.settleTypes, Fam.commitTypes, Fam.settleOf, List.mem_cons,
    List.mem_nil_iff, or_false]
  omega

/-- The NFT machine: `0x00 → 0x21 → 0x00`. -/
theorem Fam.nft_edge_iff (a b : Nat) :
    Fam.edge .nft a b ↔ (a = 0x00 ∧ b = 0x21) ∨ (a = 0x21 ∧ b = 0x00) := by
  simp only [Fam.edge, Fam.settleTypes, Fam.commitTypes, Fam.settleOf, List.mem_cons,
    List.mem_nil_iff, or_false]

/-- An edge never leads to an undefined type byte. -/
theorem Fam.edge_defined {fam : Fam} {a b : Nat} (h : fam.edge a b) :
    b ∈ fam.settleTypes ++ fam.commitTypes := by
  cases fam <;>
    simp only [Fam.edge, Fam.settleTypes, Fam.commitTypes, Fam.settleOf, List.mem_cons,
      List.mem_nil_iff, List.mem_append, or_false] at h ⊢ <;>
    omega

/-- Edges alternate parity: a settle-typed source yields a commit-typed target and back. -/
theorem Fam.edge_alternates {fam : Fam} {a b : Nat} (h : fam.edge a b) :
    (a ∈ fam.settleTypes ∧ b ∈ fam.commitTypes) ∨ (a ∈ fam.commitTypes ∧ b ∈ fam.settleTypes) := by
  cases fam <;>
    simp only [Fam.edge, Fam.settleTypes, Fam.commitTypes, Fam.settleOf, List.mem_cons,
      List.mem_nil_iff, or_false] at h ⊢ <;>
    omega

/-- **Theorem 4, per transition (Lemma 7).** Every token an accepted spend produces is typed
by an edge of the family's machine from the spent token's type. -/
theorem t4_step {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s) :
    ∀ t ∈ s.tx.tokens, fam.edge s.spent.txoType t.txoType := by
  intro t ht
  rcases Spend.mem_tokens_cases h ht with ⟨hk, rfl⟩ | ⟨hk, rfl | ⟨_, rfl⟩⟩
  · exact Or.inl ⟨h.commit_type hk, h.commit_mode hk⟩
  · exact Or.inr ⟨h.settle_type hk, rfl⟩
  · exact Or.inr ⟨h.settle_type hk, rfl⟩

/-- **Theorem 4 (no undefined type).** In a valid run every token ever created carries one of
the family's type bytes; nothing outside `0x20..0x25` (fungible) or `{0x00, 0x21}` (NFT) exists. -/
theorem t4_defined_types {P : Prims Txid} {fam : Fam} {r : Run Txid} (hv : r.Valid P fam) (k : Nat) :
    ∀ x ∈ r.everAfter P k, x.2.txoType ∈ fam.settleTypes ++ fam.commitTypes := by
  induction k with
  | zero =>
    intro x hx
    exact List.mem_append_left _ (hv.1.settleTyped x hx)
  | succ k ih =>
    intro x hx
    cases hk : r.steps[k]? with
    | none => rw [Run.everAfter_succ_none hk] at hx; exact ih x hx
    | some s =>
      rw [Run.everAfter_succ_some hk] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih x hx
      · exact Fam.edge_defined (t4_step (hv.2 k s hk).accepts x.2 (Spend.mem_tokens_of_mem_produced hx))

/-- **Theorem 4 (no skipped step).** A commit-typed token is only ever spent by a settle and a
settle-typed token only by a commit (or either by a melt): two commits or two settles in a
row are impossible. -/
theorem t4_no_skip {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s) :
    (s.kind = .commit → s.spent.txoType ∈ fam.settleTypes) ∧
    (s.kind = .settle → s.spent.txoType ∈ fam.commitTypes) :=
  ⟨h.commit_type, h.settle_type⟩

end BoltProof
