import BoltProof.Theorems.Authenticity

/-!
# The chain, one hop at a time: what a run says about a settle's grandparent

The refinements (`Bridge/Glue/`) prove that a spend the script accepts is one the model accepts, per
input, under `GpReal`: that the grandparent a token names is a real commit transaction with the token at
the named index and a proof output at the co-spent index. Composing real spends into a model `Run` would
discharge it. This file is the Layer 1 half of that composition. In a valid run the grandparent a settled
token names is output 0 of the transaction of an earlier commit step, whose outputs begin with that token,
the recipient's proof output and, for a split, the second recipient's proof output
(`Run.grandparent_commit`). The script forces the co-spent index to 1, or to 2 for a split (`AnchorOK`,
`Bridge/Glue/SimpleMulti/Blocks.lean`), so the output a settle co-spends is a proof output of the real
grandparent, and the anchor of `Accepts.l3_rebuild` names a settle result the grandparent assigned to a
recipient. What remains for the Bridge is to read a real transaction's bytes as that step's `TxDesc`
(`lean/GLUE-PLAN.md`, Option A).
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

/-! ## Type bytes -/

/-- A commit-typed byte is not settle-typed. -/
theorem Fam.not_settle_of_commit {fam : Fam} {a : Nat} (h : a ∈ fam.commitTypes) :
    a ∉ fam.settleTypes := by
  cases fam <;>
    simp only [Fam.commitTypes, Fam.settleTypes, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢ <;>
    omega

/-- The settle type of a commit-typed byte is settle-typed. -/
theorem Fam.settleOf_mem {fam : Fam} {a : Nat} (h : a ∈ fam.commitTypes) :
    fam.settleOf a ∈ fam.settleTypes := by
  cases fam <;>
    simp only [Fam.commitTypes, Fam.settleTypes, Fam.settleOf, List.mem_cons, List.mem_nil_iff,
      or_false] at h ⊢ <;>
    omega

/-! ## Produced outputs, by index -/

/-- A key of `producedFrom` names the output, counted from `j`, that holds its token. -/
theorem getElem?_of_mem_producedFrom {txid : Txid} {os : List (Out Txid)} {j : Nat}
    {o : Outpoint Txid} {t : Token Txid} (h : (o, t) ∈ producedFrom txid os j) :
    os[o.vout - j]? = some (.token t) := by
  induction os generalizing j with
  | nil => simp [producedFrom] at h
  | cons x os ih =>
    cases x with
    | token u =>
      simp only [producedFrom, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · have hge : j + 1 ≤ o.vout := vout_ge_of_mem_producedFrom h
        have : o.vout - j = (o.vout - (j + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
        exact ih h
    | proof pkh =>
      have h' : (o, t) ∈ producedFrom txid os (j + 1) := by simpa [producedFrom] using h
      have hge : j + 1 ≤ o.vout := vout_ge_of_mem_producedFrom h'
      have : o.vout - j = (o.vout - (j + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact ih h'
    | p2pkh pkh =>
      have h' : (o, t) ∈ producedFrom txid os (j + 1) := by simpa [producedFrom] using h
      have hge : j + 1 ≤ o.vout := vout_ge_of_mem_producedFrom h'
      have : o.vout - j = (o.vout - (j + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact ih h'
    | other =>
      have h' : (o, t) ∈ producedFrom txid os (j + 1) := by simpa [producedFrom] using h
      have hge : j + 1 ≤ o.vout := vout_ge_of_mem_producedFrom h'
      have : o.vout - j = (o.vout - (j + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact ih h'

/-! ## A commit's outputs -/

/-- **A commit's outputs** (Lemma 2): its token at 0, the recipient's proof output at 1, for a split the
second recipient's proof output at 2, and no token after index 0. -/
theorem Spend.commit_outputs {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s)
    (hk : s.kind = .commit) :
    s.tx.outputs[0]? = some (.token s.commitToken) ∧
      s.tx.outputs[1]? = some (.proof s.recipient) ∧
      (s.mode = .split → s.tx.outputs[2]? = some (.proof s.recipient2)) ∧
      ∀ v t, s.tx.outputs[v]? = some (.token t) → v = 0 := by
  obtain ⟨outs, change, hok, hc, hout⟩ := h.l2_outs (by rw [hk]; decide)
  have houts : outs = s.expectedOuts fam := by
    rcases hok with h' | ⟨hks, -, -⟩
    · exact h'
    · rw [hk] at hks; cases hks
  subst houts
  rw [hout]
  simp only [Spend.expectedOuts, hk]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro hm; rw [ite_eq_left hm]; rfl
  · intro v t hv
    rcases v with _ | _ | v
    · rfl
    · exfalso; simp at hv
    · exfalso
      simp only [List.cons_append, List.getElem?_cons_succ] at hv
      have hmem := List.mem_of_getElem? hv
      rcases List.mem_append.mp hmem with hm | hm
      · split at hm <;> simp at hm
      · have := hc _ hm
        simp [Out.isToken] at this

namespace Run

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

/-- Every token output the run created in its first `k` steps is a genesis token or was produced by an
earlier step. -/
theorem mem_everAfter_cases {k : Nat} {x : Outpoint Txid × Token Txid} (h : x ∈ r.everAfter P k) :
    x ∈ r.genesis ∨ ∃ j < k, ∃ s : Spend Txid, r.steps[j]? = some s ∧ x ∈ s.produced P := by
  induction k with
  | zero => exact Or.inl h
  | succ k ih =>
    cases hk : r.steps[k]? with
    | none =>
      rw [everAfter_succ_none hk] at h
      rcases ih h with hg | ⟨j, hj, s, hs, hx⟩
      · exact Or.inl hg
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, s, hs, hx⟩
    | some s =>
      rw [everAfter_succ_some hk] at h
      rcases List.mem_append.mp h with h | h
      · rcases ih h with hg | ⟨j, hj, s', hs', hx⟩
        · exact Or.inl hg
        · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, s', hs', hx⟩
      · exact Or.inr ⟨k, Nat.lt_succ_self k, s, hk, h⟩

/-- The token a step spends is a genesis token or a token output of an earlier step. -/
theorem spent_cases (hv : r.Valid P fam) {k : Nat} {s : Spend Txid} (hk : r.steps[k]? = some s) :
    (s.spentOutpoint, s.spent) ∈ r.genesis ∨
      ∃ j < k, ∃ sj : Spend Txid, r.steps[j]? = some sj ∧ (s.spentOutpoint, s.spent) ∈ sj.produced P :=
  mem_everAfter_cases (mem_everAfter_of_mem_liveAfter (hv.2 k s hk).spent_live)

/-- A commit-typed token output of a step is the commit token of a commit step. -/
theorem produced_commit_typed (hv : r.Valid P fam) {j : Nat} {sj : Spend Txid}
    (hj : r.steps[j]? = some sj) {o : Outpoint Txid} {t : Token Txid} (hx : (o, t) ∈ sj.produced P)
    (hty : t.txoType ∈ fam.commitTypes) : sj.kind = .commit ∧ t = sj.commitToken := by
  have hsj := hv.2 j sj hj
  have ht : t ∈ sj.tx.tokens := Spend.mem_tokens_of_mem_produced hx
  rcases Spend.mem_tokens_cases hsj.accepts ht with ⟨hc, he⟩ | ⟨hs, he⟩
  · exact ⟨hc, he⟩
  · exfalso
    have hst : sj.spent.txoType ∈ fam.commitTypes := hsj.accepts.settle_type hs
    have : t.txoType ∈ fam.settleTypes := by
      rcases he with he | ⟨_, he⟩ <;> rw [he] <;> exact Fam.settleOf_mem hst
    exact Fam.not_settle_of_commit hty this

/-- A settle-typed token output of a step is a settle token of a settle step, so its parent is the
outpoint that step spent. -/
theorem produced_settle_typed (hv : r.Valid P fam) {j : Nat} {sj : Spend Txid}
    (hj : r.steps[j]? = some sj) {o : Outpoint Txid} {t : Token Txid} (hx : (o, t) ∈ sj.produced P)
    (hty : t.txoType ∈ fam.settleTypes) : sj.kind = .settle ∧ t.parent = some sj.spentOutpoint := by
  have hsj := hv.2 j sj hj
  have ht : t ∈ sj.tx.tokens := Spend.mem_tokens_of_mem_produced hx
  rcases Spend.mem_tokens_cases hsj.accepts ht with ⟨hc, he⟩ | ⟨hs, he⟩
  · exfalso
    have : t.txoType ∈ fam.commitTypes := by rw [he]; exact hsj.accepts.commit_mode hc
    exact Fam.not_settle_of_commit this hty
  · refine ⟨hs, ?_⟩
    rcases he with he | ⟨_, he⟩ <;> rw [he] <;> rfl

/-- **The grandparent is a real commit of the run, with the honest layout.** In a valid run, the
grandparent a settled token names is output 0 of the transaction of an earlier commit step, whose
outputs are that token, the recipient's proof output and, for a split, the second recipient's proof
output, before any change. With the script forcing the co-spent index to 1 or, for a split, 2
(`AnchorOK`), the output a settle co-spends is a proof output of its real grandparent: the Layer 1 half
of discharging the refinements' `GpReal`. -/
theorem grandparent_commit (hv : r.Valid P fam) {k : Nat} {s : Spend Txid} (hk : r.steps[k]? = some s)
    (hs : s.kind = .settle) {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) :
    ∃ c < k, ∃ sc : Spend Txid, r.steps[c]? = some sc ∧ sc.kind = .commit ∧
      P.txid sc.tx = gp.txid ∧ gp.vout = 0 ∧
      sc.tx.outputs[0]? = some (.token sc.commitToken) ∧
      sc.tx.outputs[1]? = some (.proof sc.recipient) ∧
      (sc.mode = .split → sc.tx.outputs[2]? = some (.proof sc.recipient2)) := by
  have hsk := hv.2 k s hk
  -- the settled token is commit-typed, so it is the commit token of an earlier commit step j
  have hXty : s.spent.txoType ∈ fam.commitTypes := hsk.accepts.settle_type hs
  rcases spent_cases hv hk with hg | ⟨j, hjk, sj, hj, hXj⟩
  · exact absurd (hv.1.settleTyped _ hg) (Fam.not_settle_of_commit hXty)
  obtain ⟨hjc, hXeq⟩ := produced_commit_typed hv hj hXj hXty
  -- its grandparent is the parent of the token that commit spent
  have hBp : sj.spent.parent = some gp := by
    have := hgp; rw [hXeq] at this; exact this
  have hsj := hv.2 j sj hj
  have hBty : sj.spent.txoType ∈ fam.settleTypes := hsj.accepts.commit_type hjc
  -- that token has a parent, so it is a settle token of an earlier settle step i, and the grandparent
  -- is the outpoint i spent
  rcases spent_cases hv hj with hgB | ⟨i, hij, si, hi, hBi⟩
  · have hpl := (hv.1.parentless _ hgB).1
    simp only at hpl
    rw [hpl] at hBp; cases hBp
  obtain ⟨his, hBpar⟩ := produced_settle_typed hv hi hBi hBty
  have hgpY : gp = si.spentOutpoint := by
    rw [hBpar] at hBp
    exact (Option.some.inj hBp).symm
  -- the token at the grandparent outpoint is commit-typed, so it is the commit token of a commit step c
  have hsi := hv.2 i si hi
  have hYty : si.spent.txoType ∈ fam.commitTypes := hsi.accepts.settle_type his
  rcases spent_cases hv hi with hgY | ⟨c, hci, sc, hc, hYc⟩
  · exact absurd (hv.1.settleTyped _ hgY) (Fam.not_settle_of_commit hYty)
  obtain ⟨hcc, -⟩ := produced_commit_typed hv hc hYc hYty
  have hsc := hv.2 c sc hc
  obtain ⟨h0, h1, h2, hidx⟩ := Spend.commit_outputs hsc.accepts hcc
  -- the grandparent outpoint is keyed by c's transaction id, and its index holds the token
  have htxid : gp.txid = P.txid sc.tx := by
    rw [hgpY]; exact mem_producedFrom_txid hYc
  have hget : sc.tx.outputs[gp.vout]? = some (.token si.spent) := by
    have := getElem?_of_mem_producedFrom hYc
    rw [hgpY]; simpa using this
  exact ⟨c, by omega, sc, hc, hcc, htxid.symm, hidx _ _ hget, h0, h1, h2⟩

end Run

end BoltProof
