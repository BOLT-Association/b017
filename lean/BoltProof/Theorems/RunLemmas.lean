import BoltProof.Model.Run

/-!
# BoltProof.Theorems.RunLemmas

Bookkeeping lemmas about runs: keyed lists, the live and ever-created UTXO sets, and what
`Accepts` says about a spend's token outputs. Nothing here is protocol-specific beyond the
shape of `expectedOuts`.
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

/-! ## Keyed lists -/

/-- The outpoints of a keyed list. -/
abbrev keys (l : List (Outpoint Txid × Token Txid)) : List (Outpoint Txid) := l.map Prod.fst

theorem mem_keys {l : List (Outpoint Txid × Token Txid)} {o : Outpoint Txid} :
    o ∈ keys l ↔ ∃ t, (o, t) ∈ l := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact ⟨x.2, hx⟩
  · rintro ⟨t, ht⟩
    exact List.mem_map.mpr ⟨(o, t), ht, rfl⟩

theorem mem_removeKey {o : Outpoint Txid} {l : List (Outpoint Txid × Token Txid)} {x} :
    x ∈ removeKey o l ↔ x ∈ l ∧ x.1 ≠ o := by
  simp [removeKey, List.mem_filter]

theorem removeKey_sublist (o : Outpoint Txid) (l : List (Outpoint Txid × Token Txid)) :
    (removeKey o l).Sublist l :=
  List.filter_sublist

theorem removeKey_cons_self (o : Outpoint Txid) (t : Token Txid) (xs) :
    removeKey o ((o, t) :: xs) = removeKey o xs := by
  simp [removeKey]

theorem removeKey_cons_ne {o : Outpoint Txid} {x : Outpoint Txid × Token Txid} (h : x.1 ≠ o)
    (xs) : removeKey o (x :: xs) = x :: removeKey o xs := by
  simp [removeKey, h]

theorem removeKey_of_not_mem {o : Outpoint Txid} {l : List (Outpoint Txid × Token Txid)}
    (h : o ∉ keys l) : removeKey o l = l := by
  rw [removeKey, List.filter_eq_self]
  intro a ha
  simp only [ne_eq, decide_eq_true_eq]
  intro e
  exact h (mem_keys.mpr ⟨a.2, e ▸ ha⟩)

theorem removeKeys_cons (o : Outpoint Txid) (os : List (Outpoint Txid)) (l) :
    removeKeys (o :: os) l = removeKeys os (removeKey o l) := by
  simp [removeKeys]

theorem removeKeys_nil (l : List (Outpoint Txid × Token Txid)) : removeKeys [] l = l := rfl

theorem mem_removeKeys {os : List (Outpoint Txid)} {l : List (Outpoint Txid × Token Txid)} {x} :
    x ∈ removeKeys os l ↔ x ∈ l ∧ x.1 ∉ os := by
  induction os generalizing l with
  | nil => simp [removeKeys]
  | cons o os ih =>
    rw [removeKeys_cons, ih, mem_removeKey]
    simp only [List.mem_cons, not_or]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem removeKeys_sublist (os : List (Outpoint Txid)) (l : List (Outpoint Txid × Token Txid)) :
    (removeKeys os l).Sublist l := by
  induction os generalizing l with
  | nil => simp [removeKeys]
  | cons o os ih => rw [removeKeys_cons]; exact (ih _).trans (removeKey_sublist o l)

theorem nodup_keys_of_sublist {a b : List (Outpoint Txid × Token Txid)} (h : a.Sublist b)
    (hb : (keys b).Nodup) : (keys a).Nodup :=
  (h.map Prod.fst).nodup hb

/-! ## Lookups -/

theorem lookupKey_of_mem {o : Outpoint Txid} {t : Token Txid} {l} (hn : (keys l).Nodup)
    (hm : (o, t) ∈ l) : lookupKey o l = some t := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    rw [keys, List.map_cons, List.nodup_cons] at hn
    obtain ⟨hx, hxs⟩ := hn
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp [lookupKey]
    · have hx1 : x.1 ≠ o := fun e => hx (e ▸ mem_keys.mpr ⟨t, hm'⟩)
      simp [lookupKey, hx1, ih hxs hm']

theorem mem_of_lookupKey {o : Outpoint Txid} {t : Token Txid} {l} (h : lookupKey o l = some t) :
    (o, t) ∈ l := by
  induction l with
  | nil => simp [lookupKey] at h
  | cons x xs ih =>
    by_cases hx : x.1 = o
    · simp [lookupKey, hx] at h
      subst h
      rw [← hx]
      exact List.mem_cons_self
    · simp [lookupKey, hx] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ## Value sums -/

/-- The value held by a keyed token list. -/
def vsum (l : List (Outpoint Txid × Token Txid)) : Nat := (l.map fun x => x.2.value).sum

theorem vsum_nil : vsum ([] : List (Outpoint Txid × Token Txid)) = 0 := rfl

theorem vsum_cons (x : Outpoint Txid × Token Txid) (l) : vsum (x :: l) = x.2.value + vsum l := by
  simp [vsum]

theorem vsum_append (a b : List (Outpoint Txid × Token Txid)) :
    vsum (a ++ b) = vsum a + vsum b := by
  simp [vsum]

theorem vsum_removeKey {o : Outpoint Txid} {t : Token Txid} {l} (hn : (keys l).Nodup)
    (hm : (o, t) ∈ l) : vsum (removeKey o l) + t.value = vsum l := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    rw [keys, List.map_cons, List.nodup_cons] at hn
    obtain ⟨hx, hxs⟩ := hn
    rcases List.mem_cons.mp hm with rfl | hm'
    · rw [removeKey_cons_self, removeKey_of_not_mem hx, vsum_cons]
      show vsum xs + t.value = t.value + vsum xs
      omega
    · have hx1 : x.1 ≠ o := fun e => hx (e ▸ mem_keys.mpr ⟨t, hm'⟩)
      rw [removeKey_cons_ne hx1, vsum_cons, vsum_cons]
      have := ih hxs hm'
      omega

theorem length_removeKey {o : Outpoint Txid} {t : Token Txid} {l} (hn : (keys l).Nodup)
    (hm : (o, t) ∈ l) : (removeKey o l).length + 1 = l.length := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    rw [keys, List.map_cons, List.nodup_cons] at hn
    obtain ⟨hx, hxs⟩ := hn
    rcases List.mem_cons.mp hm with rfl | hm'
    · rw [removeKey_cons_self, removeKey_of_not_mem hx]
      simp
    · have hx1 : x.1 ≠ o := fun e => hx (e ▸ mem_keys.mpr ⟨t, hm'⟩)
      rw [removeKey_cons_ne hx1]
      have := ih hxs hm'
      simp only [List.length_cons]
      omega

/-! ## Produced outputs -/

theorem mem_producedFrom_txid {txid : Txid} {os : List (Out Txid)} {j} {x}
    (h : x ∈ producedFrom txid os j) : x.1.txid = txid := by
  induction os generalizing j with
  | nil => simp [producedFrom] at h
  | cons o os ih =>
    cases o with
    | token t =>
      simp only [producedFrom, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact ih h
    | proof pkh => exact ih (by simpa [producedFrom] using h)
    | p2pkh pkh => exact ih (by simpa [producedFrom] using h)
    | other => exact ih (by simpa [producedFrom] using h)

theorem vout_ge_of_mem_producedFrom {txid : Txid} {os : List (Out Txid)} {j} {x}
    (h : x ∈ producedFrom txid os j) : j ≤ x.1.vout := by
  induction os generalizing j with
  | nil => simp [producedFrom] at h
  | cons o os ih =>
    cases o with
    | token t =>
      simp only [producedFrom, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih h)
    | proof pkh => exact Nat.le_of_succ_le (ih (by simpa [producedFrom] using h))
    | p2pkh pkh => exact Nat.le_of_succ_le (ih (by simpa [producedFrom] using h))
    | other => exact Nat.le_of_succ_le (ih (by simpa [producedFrom] using h))

theorem nodup_keys_producedFrom (txid : Txid) (os : List (Out Txid)) (j) :
    (keys (producedFrom txid os j)).Nodup := by
  induction os generalizing j with
  | nil => simp [producedFrom, keys]
  | cons o os ih =>
    cases o with
    | token t =>
      simp only [producedFrom, keys, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (j + 1)⟩
      intro hmem
      obtain ⟨y, hy, hyk⟩ := List.mem_map.mp hmem
      have := vout_ge_of_mem_producedFrom hy
      rw [hyk] at this
      exact absurd (by simpa using this : j + 1 ≤ j) (by omega)
    | proof pkh => simpa [producedFrom] using ih (j + 1)
    | p2pkh pkh => simpa [producedFrom] using ih (j + 1)
    | other => simpa [producedFrom] using ih (j + 1)

theorem map_snd_producedFrom (txid : Txid) (os : List (Out Txid)) (j) :
    (producedFrom txid os j).map Prod.snd = os.filterMap Out.token? := by
  induction os generalizing j with
  | nil => simp [producedFrom]
  | cons o os ih =>
    cases o <;> simp [producedFrom, Out.token?, ih, List.filterMap_cons]

theorem vsum_eq_sum_map_snd (l : List (Outpoint Txid × Token Txid)) :
    vsum l = ((l.map Prod.snd).map Token.value).sum := by
  simp [vsum, List.map_map, Function.comp_def]

/-! ## Tokens of an accepted spend -/

theorem Out.token?_eq_none_of_not_token {o : Out Txid} (h : o.isToken = false) :
    o.token? = none := by
  cases o <;> simp_all [Out.isToken, Out.token?]

/-- An accepted non-melt spend's token outputs are the reconstructed ones (Lemma 2): in the covenant's
order or, for a split settle, the two settled tokens in the other order. -/
theorem Spend.tokens_of_accepts {P : Prims Txid} {fam : Fam} {s : Spend Txid}
    (h : Accepts P fam s) (hk : s.kind ≠ .melt) :
    s.tx.tokens = (s.expectedOuts fam).filterMap Out.token? ∨
      (s.kind = .settle ∧ fam.modeOfCommitType s.spent.txoType = some .split ∧
        s.tx.tokens = [s.settleToken fam 1, s.settleToken fam 0]) := by
  obtain ⟨outs, change, hok, hc, hout⟩ := h.l2_outs hk
  have hch : change.filterMap Out.token? = [] :=
    List.filterMap_eq_nil_iff.mpr fun o ho => Out.token?_eq_none_of_not_token (hc o ho)
  rcases hok with rfl | ⟨hs, hm, rfl⟩
  · left
    rw [TxDesc.tokens, hout, List.filterMap_append, hch, List.append_nil]
  · right
    refine ⟨hs, hm, ?_⟩
    rw [TxDesc.tokens, hout, List.filterMap_append, hch, List.append_nil]
    simp [Out.token?]

/-- An accepted melt has no token output (Lemma 2, melt). -/
theorem Spend.tokens_of_melt {P : Prims Txid} {fam : Fam} {s : Spend Txid}
    (h : Accepts P fam s) (hk : s.kind = .melt) : s.tx.tokens = [] := by
  have hp := h.l2_melt hk
  rw [TxDesc.tokens]
  apply List.filterMap_eq_nil_iff.mpr
  intro o ho
  have := hp o ho
  cases o <;> simp_all [Out.isP2pkh, Out.token?]

theorem Spend.expectedOuts_tokens_commit {fam : Fam} {s : Spend Txid} (hk : s.kind = .commit) :
    (s.expectedOuts fam).filterMap Out.token? = [s.commitToken] := by
  simp only [Spend.expectedOuts, hk]
  split <;> simp [Out.token?]

theorem Spend.expectedOuts_tokens_settle {fam : Fam} {s : Spend Txid} (hk : s.kind = .settle) :
    (s.expectedOuts fam).filterMap Out.token? =
      if fam.modeOfCommitType s.spent.txoType = some .split then
        [s.settleToken fam 0, s.settleToken fam 1]
      else [s.settleToken fam 0] := by
  simp only [Spend.expectedOuts, hk]
  split <;> simp [Out.token?]

/-- The value an accepted non-melt spend's token outputs carry, whatever their order. -/
theorem Spend.tokens_value_sum {P : Prims Txid} {fam : Fam} {s : Spend Txid}
    (h : Accepts P fam s) (hk : s.kind ≠ .melt) :
    (s.tx.tokens.map Token.value).sum =
      (((s.expectedOuts fam).filterMap Out.token?).map Token.value).sum := by
  rcases Spend.tokens_of_accepts h hk with heq | ⟨hs, hm, heq⟩
  · rw [heq]
  · rw [heq, Spend.expectedOuts_tokens_settle hs, ite_eq_left hm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- The number of token outputs of an accepted non-melt spend, whatever their order. -/
theorem Spend.tokens_length {P : Prims Txid} {fam : Fam} {s : Spend Txid}
    (h : Accepts P fam s) (hk : s.kind ≠ .melt) :
    s.tx.tokens.length = ((s.expectedOuts fam).filterMap Out.token?).length := by
  rcases Spend.tokens_of_accepts h hk with heq | ⟨hs, hm, heq⟩
  · rw [heq]
  · rw [heq, Spend.expectedOuts_tokens_settle hs, ite_eq_left hm]; rfl

theorem Spend.produced_map_snd (P : Prims Txid) (s : Spend Txid) :
    (s.produced P).map Prod.snd = s.tx.tokens := by
  rw [Spend.produced, map_snd_producedFrom, TxDesc.tokens]

theorem Spend.mem_produced_txid {P : Prims Txid} {s : Spend Txid} {x} (h : x ∈ s.produced P) :
    x.1.txid = P.txid s.tx :=
  mem_producedFrom_txid h

theorem Spend.nodup_keys_produced (P : Prims Txid) (s : Spend Txid) :
    (keys (s.produced P)).Nodup :=
  nodup_keys_producedFrom _ _ _

theorem Spend.mem_tokens_of_mem_produced {P : Prims Txid} {s : Spend Txid} {x}
    (h : x ∈ s.produced P) : x.2 ∈ s.tx.tokens := by
  rw [← Spend.produced_map_snd P s]
  exact List.mem_map.mpr ⟨x, h, rfl⟩

theorem Spend.consumed_none {s : Spend Txid} (h : s.other = none) :
    s.consumed = [s.spentOutpoint] := by
  simp [Spend.consumed, h]

theorem Spend.consumed_some {s : Spend Txid} {t : Token Txid} {o : Outpoint Txid}
    (h : s.other = some (t, o)) : s.consumed = [s.spentOutpoint, o] := by
  simp [Spend.consumed, h]

/-- Every token output of an accepted spend is the reconstructed commit token or one of the
reconstructed settle tokens (Lemma 2). -/
theorem Spend.mem_tokens_cases {P : Prims Txid} {fam : Fam} {s : Spend Txid} {t : Token Txid}
    (h : Accepts P fam s) (ht : t ∈ s.tx.tokens) :
    (s.kind = .commit ∧ t = s.commitToken) ∨
    (s.kind = .settle ∧ (t = s.settleToken fam 0 ∨
      (fam.modeOfCommitType s.spent.txoType = some .split ∧ t = s.settleToken fam 1))) := by
  cases hk : s.kind with
  | melt => rw [Spend.tokens_of_melt h hk] at ht; simp at ht
  | commit =>
    rcases Spend.tokens_of_accepts h (by simp [hk]) with heq | ⟨hks, -, -⟩
    · rw [heq, Spend.expectedOuts_tokens_commit hk] at ht
      simp at ht
      exact Or.inl ⟨rfl, ht⟩
    · rw [hk] at hks; cases hks
  | settle =>
    refine Or.inr ⟨rfl, ?_⟩
    rcases Spend.tokens_of_accepts h (by simp [hk]) with heq | ⟨-, hsplit, heq⟩
    · rw [heq, Spend.expectedOuts_tokens_settle hk] at ht
      split at ht
      · rename_i hsplit
        simp at ht
        rcases ht with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨hsplit, rfl⟩
      · simp at ht
        exact Or.inl ht
    · rw [heq] at ht
      simp at ht
      rcases ht with rfl | rfl
      · exact Or.inr ⟨hsplit, rfl⟩
      · exact Or.inl rfl

/-- The lineage fields every produced token carries (Lemma 2): parent, grandparent, issuer. -/
theorem Spend.token_fields {P : Prims Txid} {fam : Fam} {s : Spend Txid} {t : Token Txid}
    (h : Accepts P fam s) (ht : t ∈ s.tx.tokens) :
    t.parent = some s.spentOutpoint ∧ t.grandparent = s.spent.parent ∧
      t.issuer = s.spent.issuer := by
  rcases Spend.mem_tokens_cases h ht with ⟨_, rfl⟩ | ⟨_, rfl | ⟨_, rfl⟩⟩ <;>
    exact ⟨rfl, rfl, rfl⟩

/-! ## Live and ever-created sets -/

namespace Run

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

theorem liveAfter_succ_some {k} {s} (hk : r.steps[k]? = some s) :
    r.liveAfter P (k + 1) = removeKeys s.consumed (r.liveAfter P k) ++ s.produced P := by
  simp [liveAfter, hk]

theorem liveAfter_succ_none {k} (hk : r.steps[k]? = none) :
    r.liveAfter P (k + 1) = r.liveAfter P k := by
  simp [liveAfter, hk]

theorem everAfter_succ_some {k} {s} (hk : r.steps[k]? = some s) :
    r.everAfter P (k + 1) = r.everAfter P k ++ s.produced P := by
  simp [everAfter, hk]

theorem everAfter_succ_none {k} (hk : r.steps[k]? = none) :
    r.everAfter P (k + 1) = r.everAfter P k := by
  simp [everAfter, hk]

theorem liveAfter_sublist_everAfter (k) : (r.liveAfter P k).Sublist (r.everAfter P k) := by
  induction k with
  | zero => simp [liveAfter, everAfter]
  | succ k ih =>
    cases hk : r.steps[k]? with
    | none => rw [liveAfter_succ_none hk, everAfter_succ_none hk]; exact ih
    | some s =>
      rw [liveAfter_succ_some hk, everAfter_succ_some hk]
      exact ((removeKeys_sublist _ _).trans ih).append (List.Sublist.refl _)

theorem mem_everAfter_of_mem_liveAfter {k} {x} (h : x ∈ r.liveAfter P k) :
    x ∈ r.everAfter P k :=
  (liveAfter_sublist_everAfter k).subset h

theorem everAfter_subset_succ (k) : ∀ x ∈ r.everAfter P k, x ∈ r.everAfter P (k + 1) := by
  intro x hx
  cases hk : r.steps[k]? with
  | none => rw [everAfter_succ_none hk]; exact hx
  | some s => rw [everAfter_succ_some hk]; exact List.mem_append_left _ hx

theorem everAfter_mono {i j} (h : i ≤ j) : ∀ x ∈ r.everAfter P i, x ∈ r.everAfter P j := by
  induction j with
  | zero =>
    intro x hx
    have : i = 0 := by omega
    subst this
    exact hx
  | succ j ih =>
    intro x hx
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact hx
    · exact everAfter_subset_succ j x (ih (Nat.le_of_lt_succ hlt) x hx)

theorem everAfter_of_ge {k} (h : r.steps.length ≤ k) :
    r.everAfter P k = r.everAfter P r.steps.length := by
  induction k with
  | zero =>
    have : r.steps.length = 0 := by omega
    rw [this]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with e | hlt
    · rw [e]
    · have hk : r.steps[k]? = none := List.getElem?_eq_none (by omega)
      rw [everAfter_succ_none hk]
      exact ih (by omega)

theorem nodup_keys_everAfter (hv : r.Valid P fam) (k) : (keys (r.everAfter P k)).Nodup := by
  induction k with
  | zero => exact hv.1.nodup
  | succ k ih =>
    cases hk : r.steps[k]? with
    | none => rw [everAfter_succ_none hk]; exact ih
    | some s =>
      rw [everAfter_succ_some hk]
      have hs := hv.2 k s hk
      rw [keys, List.map_append, List.nodup_append]
      refine ⟨ih, Spend.nodup_keys_produced P s, ?_⟩
      intro a ha b hb e
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      have h1 := hs.fresh x hx
      have h2 := Spend.mem_produced_txid hy
      apply h1
      rw [e, h2]

theorem nodup_keys_liveAfter (hv : r.Valid P fam) (k) : (keys (r.liveAfter P k)).Nodup :=
  nodup_keys_of_sublist (liveAfter_sublist_everAfter k) (nodup_keys_everAfter hv k)

/-- The token created at an outpoint is the one any step saw there. -/
theorem tokenAt_of_mem (hv : r.Valid P fam) {k} {o : Outpoint Txid} {t : Token Txid}
    (hm : (o, t) ∈ r.everAfter P k) : r.tokenAt P o = some t := by
  rw [tokenAt]
  apply lookupKey_of_mem (nodup_keys_everAfter hv _)
  rcases Nat.le_total k r.steps.length with h | h
  · exact everAfter_mono h _ hm
  · rw [everAfter_of_ge h] at hm
    exact hm

end Run

end BoltProof
