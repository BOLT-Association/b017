import BoltProof.Theorems.StateMachine

/-!
# Theorem 3 — Balance Conservation

`docs/formal-proof.md` §6, generalised to the split/merge DAG: the value held by the live
token set, plus everything melted so far, equals the value of the genesis set at every step.
The theorem is **unconditional** arithmetic over the covenant interface (Lemmas 2 and 6).

Two notes the hand proof does not make explicit:

* Value is counted *in flight*: a merge-commit-typed token (`0x25`) has already consumed its
  second input and carries that balance in `balanceCommit` until its settle adds it in
  (`Token.value`). On every settle-typed token `value = balance`.
* The statement is over the **set of genesis tokens** a run starts from. Two mints of one
  issuer can be merged, so "per genesis" is only meaningful without merges
  (`t3_single_genesis`).
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

/-! ## Value facts about one spend -/

theorem Token.value_of_settleTyped {fam : Fam} {t : Token Txid} (h : t.txoType ∈ fam.settleTypes) :
    t.value = t.balance := by
  have hne : t.txoType ≠ 0x25 := by
    cases fam <;> simp only [Fam.settleTypes, List.mem_cons, List.mem_nil_iff, or_false] at h <;>
      omega
  simp [Token.value, hne]

/-- What a commit-type byte says about the mode and family. -/
theorem Fam.modeOfCommitType_cases {fam : Fam} {a : Nat} {m : Mode}
    (h : fam.modeOfCommitType a = some m) :
    (m = .transfer ∧ a = 0x21) ∨ (m = .split ∧ a = 0x23 ∧ fam = .fungible) ∨
      (m = .merge ∧ a = 0x25 ∧ fam = .fungible) := by
  unfold Fam.modeOfCommitType at h
  split at h <;> simp_all

theorem Fam.settleOf_ne_merge {fam : Fam} {a : Nat} (h : a ∈ fam.commitTypes) :
    fam.settleOf a ≠ 0x25 := by
  cases fam <;> simp only [Fam.commitTypes, List.mem_cons, List.mem_nil_iff, or_false] at h <;>
    simp only [Fam.settleOf] <;> omega

theorem Spend.other_none_of_not_merge {P : Prims Txid} {fam : Fam} {s : Spend Txid}
    (h : Accepts P fam s) (hn : ¬ (s.kind = .commit ∧ s.mode = .merge)) : s.other = none := by
  cases ho : s.other with
  | none => rfl
  | some o => exact absurd (h.other_iff_merge.mp (by simp [ho])) hn

/-- The value a spend's token outputs carry, plus what a melt destroys, equals the value of
the token(s) it consumed. -/
theorem Spend.value_conserved {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s) :
    (s.tx.tokens.map Token.value).sum + (if s.kind = .melt then s.spent.value else 0) =
      s.spent.value + (match s.other with | some (ot, _) => ot.value | none => 0) := by
  cases hk : s.kind with
  | melt =>
    have ho : s.other = none := Spend.other_none_of_not_merge h (by simp [hk])
    rw [Spend.tokens_of_melt h hk, ho]
    simp
  | commit =>
    rw [Spend.tokens_of_accepts h (by simp [hk]), Spend.expectedOuts_tokens_commit hk]
    have hsv := Token.value_of_settleTyped (h.commit_type hk)
    rw [hsv]
    cases hm : s.mode with
    | transfer =>
      have ho : s.other = none := Spend.other_none_of_not_merge h (by simp [hm])
      rw [ho]
      simp [Spend.commitToken, Token.value, Mode.commitType, hm]
    | split =>
      have ho : s.other = none := Spend.other_none_of_not_merge h (by simp [hm])
      rw [ho]
      simp [Spend.commitToken, Token.value, Mode.commitType, hm]
    | merge =>
      obtain ⟨o, ho, _⟩ := h.l6_merge hk hm
      obtain ⟨ot, oo⟩ := o
      have hov := Token.value_of_settleTyped (h.other_settle_typed _ ho)
      rw [ho]
      simp only [hov]
      simp [Spend.commitToken, Token.value, Mode.commitType, hm, ho]
  | settle =>
    have ho : s.other = none := Spend.other_none_of_not_merge h (by simp [hk])
    have hmode := h.settle_mode hk
    rw [Spend.tokens_of_accepts h (by simp [hk]), Spend.expectedOuts_tokens_settle hk, ho]
    rcases Fam.modeOfCommitType_cases hmode with ⟨hm, ha⟩ | ⟨hm, ha, _⟩ | ⟨hm, ha, _⟩
    · -- transfer
      have hsplit : fam.modeOfCommitType s.spent.txoType ≠ some .split := by rw [hmode, hm]; simp
      have hspv : s.spent.value = s.spent.balance := by simp [Token.value, ha]
      rw [hspv]
      simp [Spend.settleToken, Token.value, Token.settledBalance, hmode, hm]
    · -- split
      have hsplit : fam.modeOfCommitType s.spent.txoType = some .split := by rw [hmode, hm]
      have hle := h.l6_settle_split hk hm
      have hspv : s.spent.value = s.spent.balance := by simp [Token.value, ha]
      rw [hspv]
      simp [hsplit, Spend.settleToken, Token.value, Token.settledBalance]
      omega
    · -- merge
      have hsplit : fam.modeOfCommitType s.spent.txoType ≠ some .split := by rw [hmode, hm]; simp
      have hspv : s.spent.value = s.spent.balance + s.spent.balanceCommit := by
        simp [Token.value, ha]
      rw [hspv]
      simp [Spend.settleToken, Token.value, Token.settledBalance, hmode, hm]

/-! ## Conservation along a run -/

namespace Run

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

/-- One step moves value from the consumed tokens to the produced ones, or to `melted`. -/
theorem float_step (hv : r.Valid P fam) {k : Nat} {s : Spend Txid} (hk : r.steps[k]? = some s) :
    r.float P (k + 1) + (if s.kind = .melt then s.spent.value else 0) = r.float P k := by
  have hs := hv.2 k s hk
  have hnd := nodup_keys_liveAfter hv k
  have hprod : vsum (s.produced P) = (s.tx.tokens.map Token.value).sum := by
    rw [vsum_eq_sum_map_snd, Spend.produced_map_snd]
  have hcons := Spend.value_conserved hs.accepts
  simp only [float] at *
  change vsum (r.liveAfter P (k + 1)) + _ = vsum (r.liveAfter P k)
  rw [liveAfter_succ_some hk, vsum_append, hprod]
  cases ho : s.other with
  | none =>
    rw [Spend.consumed_none ho, removeKeys_cons, removeKeys_nil]
    have := vsum_removeKey hnd hs.spent_live
    rw [ho] at hcons
    simp only at hcons
    omega
  | some o =>
    obtain ⟨ot, oo⟩ := o
    rw [Spend.consumed_some ho, removeKeys_cons, removeKeys_cons, removeKeys_nil]
    have h1 := vsum_removeKey hnd hs.spent_live
    have hne : oo ≠ s.spentOutpoint := (hs.accepts.other_input _ ho).2
    have hmem : (oo, ot) ∈ removeKey s.spentOutpoint (r.liveAfter P k) :=
      mem_removeKey.mpr ⟨hs.other_live _ ho, hne⟩
    have hnd2 := nodup_keys_of_sublist (removeKey_sublist s.spentOutpoint _) hnd
    have h2 := vsum_removeKey hnd2 hmem
    rw [ho] at hcons
    simp only at hcons
    omega

theorem float_step_none {k : Nat} (hk : r.steps[k]? = none) : r.float P (k + 1) = r.float P k := by
  simp [float, liveAfter_succ_none hk]

/-- **Theorem 3 (Balance Conservation).** At every step of a valid run, the value held by
the live token set plus the value melted so far equals the value of the genesis set. -/
theorem t3_conservation (hv : r.Valid P fam) (k : Nat) :
    r.float P k + r.melted P k = r.genesisValue := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases hk : r.steps[k]? with
    | none =>
      simp only [melted, hk, float_step_none hk]
      omega
    | some s =>
      have := float_step hv hk
      simp only [melted, hk]
      omega

/-- **Theorem 3, no melts:** the float is exactly the genesis value. -/
theorem t3_no_melt (hv : r.Valid P fam) (hm : ∀ s ∈ r.steps, s.kind ≠ .melt) (k : Nat) :
    r.float P k = r.genesisValue := by
  have hz : ∀ k, r.melted P k = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [melted, ih]
      cases hk : r.steps[k]? with
      | none => rfl
      | some s =>
        have := hm s (List.mem_of_getElem? hk)
        simp [this]
  have := t3_conservation hv k
  rw [hz] at this
  omega

/-- **Theorem 3 as stated in §6:** a run from a single genesis token of balance `B` with no
melt holds exactly `B` at every step. -/
theorem t3_single_genesis (hv : r.Valid P fam) (hm : ∀ s ∈ r.steps, s.kind ≠ .melt)
    {o : Outpoint Txid} {g : Token Txid} (hg : r.genesis = [(o, g)]) (k : Nat) :
    r.float P k = g.balance := by
  rw [t3_no_melt hv hm k, genesisValue, hg]
  have := Token.value_of_settleTyped (hv.1.settleTyped (o, g) (by rw [hg]; simp))
  simp [this]

/-- Every live token's value is its balance once nothing is in flight (no live merge commit). -/
theorem float_eq_sum_balance (hq : ∀ x ∈ r.liveAfter P k, x.2.txoType ≠ 0x25) :
    r.float P k = ((r.liveAfter P k).map fun x => x.2.balance).sum := by
  simp only [float]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [Token.value, hq x hx]

end Run

/-! ## The NFT family: token count conservation -/

namespace Run

variable {P : Prims Txid} {r : Run Txid}

/-- Melts performed in the first `k` steps. -/
def meltCount (r : Run Txid) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    r.meltCount k + match r.steps[k]? with
      | some s => if s.kind = .melt then 1 else 0
      | none => 0

theorem nft_other_none {s : Spend Txid} (h : Accepts P .nft s) : s.other = none := by
  cases ho : s.other with
  | none => rfl
  | some o =>
    have ⟨hk, hm⟩ := h.other_iff_merge.mp (by simp [ho])
    have := h.commit_mode hk
    simp [hm, Mode.commitType, Fam.commitTypes] at this

theorem nft_tokens_length {s : Spend Txid} (h : Accepts P .nft s) :
    s.tx.tokens.length = if s.kind = .melt then 0 else 1 := by
  cases hk : s.kind with
  | melt => simp [Spend.tokens_of_melt h hk]
  | commit => simp [Spend.tokens_of_accepts h (by simp [hk]), Spend.expectedOuts_tokens_commit hk]
  | settle =>
    rw [Spend.tokens_of_accepts h (by simp [hk]), Spend.expectedOuts_tokens_settle hk]
    have hmode := h.settle_mode hk
    rcases Fam.modeOfCommitType_cases hmode with ⟨hm, _⟩ | ⟨_, _, hf⟩ | ⟨_, _, hf⟩
    · simp [hmode, hm]
    · cases hf
    · cases hf

/-- **Theorem 3 for the NFT family:** tokens are neither created nor duplicated — the number
of live tokens plus the number melted is the number minted. -/
theorem t3_nft_count (hv : r.Valid P .nft) (k : Nat) :
    (r.liveAfter P k).length + r.meltCount k = r.genesis.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases hk : r.steps[k]? with
    | none => simp only [meltCount, hk, liveAfter_succ_none hk]; omega
    | some s =>
      have hs := hv.2 k s hk
      have hnd := nodup_keys_liveAfter hv k
      have hlen := length_removeKey hnd hs.spent_live
      have hp : (s.produced P).length = s.tx.tokens.length := by
        rw [← Spend.produced_map_snd P s, List.length_map]
      have ht := nft_tokens_length hs.accepts
      rw [liveAfter_succ_some hk, Spend.consumed_none (nft_other_none hs.accepts), removeKeys_cons,
        removeKeys_nil, List.length_append, hp, ht]
      simp only [meltCount, hk]
      split <;> omega

end Run

end BoltProof
