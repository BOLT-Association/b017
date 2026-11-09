import BoltProof.Theorems.Authenticity

/-!
# The chain, one hop at a time: what a run says about a settle's grandparent

The refinements (`Bridge/Glue/`) prove that a spend the script accepts is one the model accepts, per
input, under `GpReal`: that the grandparent a token names is a real commit transaction with the token at
the named index and a proof output at the co-spent index. Composing real spends into a model `Run`
discharges it. This file is the Layer 1 half of that composition, in two parts.

* **Validity, step by step.** `Run.ValidUpTo P fam r k` is validity of the first `k` steps, and
  `Run.valid_of_stepwise` builds a valid run from a proof that each step is valid once the steps before it
  are: the induction the Bridge runs when it reads a chain of real spends as a run
  (`Bridge/Glue/Refine/Chain.lean`, `Bridge/Glue/SimpleMulti/Chain.lean`).
* **The grandparent's layout.** In a valid prefix the grandparent a settled token names is output 0 of
  the transaction of an earlier commit step, whose outputs begin with that token, the recipient's proof
  output and, for a split, the second recipient's proof output (`Run.grandparent_commit_upto`, and
  `Run.grandparent_layout_upto` in the shape the Bridge's `GpReal` asks). The script forces the co-spent
  index to 1, or to 2 for a split (`AnchorOK`, `Bridge/Glue/SimpleMulti/Blocks.lean`), so the output a
  settle co-spends is a proof output of the real grandparent, and the anchor of `Accepts.l3_rebuild` names
  a settle result the grandparent assigned to a recipient. A merge settle's other grandparent is likewise
  output 0 of an earlier commit step (`Run.other_grandparent_layout_upto`).
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

/-- The split commit type names the split mode. -/
theorem Mode.eq_split_of_commitType {m : Mode} (h : m.commitType = 0x23) : m = .split := by
  cases m <;> simp [Mode.commitType] at h ⊢

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

/-! ## A commit's outputs and its token -/

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

/-- A commit token's type is its mode's commit type. -/
theorem Spend.commitToken_txoType (s : Spend Txid) : s.commitToken.txoType = s.mode.commitType := rfl

/-- A commit token with an other grandparent is a merge's, and the pointer is the other token's parent. -/
theorem Spend.commitToken_otherGrandparent {s : Spend Txid} {ogp : Outpoint Txid}
    (h : s.commitToken.otherGrandparent = some ogp) :
    s.mode = .merge ∧ ∃ o, s.other = some o ∧ o.1.parent = some ogp := by
  rcases hm : s.mode with _ | _ | _ <;> rcases ho : s.other with _ | ⟨o, op⟩ <;>
    simp [Spend.commitToken, hm, ho] at h
  exact ⟨rfl, (o, op), rfl, h⟩

namespace Run

/-- Validity of the first `k` steps of a run: a well-formed genesis set and valid steps below `k`. -/
def ValidUpTo (P : Prims Txid) (fam : Fam) (r : Run Txid) (k : Nat) : Prop :=
  r.GenesisOK fam ∧ ∀ j < k, ∀ s, r.steps[j]? = some s → r.StepOK P fam j s

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

theorem Valid.upto (hv : r.Valid P fam) (k : Nat) : r.ValidUpTo P fam k :=
  ⟨hv.1, fun j _ s hs => hv.2 j s hs⟩

theorem ValidUpTo.mono {j k : Nat} (hv : r.ValidUpTo P fam k) (h : j ≤ k) : r.ValidUpTo P fam j :=
  ⟨hv.1, fun i hi s hs => hv.2 i (Nat.lt_of_lt_of_le hi h) s hs⟩

/-- **Validity, step by step.** A run is valid once its genesis set is well-formed and each step is valid
whenever the steps before it are: the induction the Bridge runs to read a chain of real spends as a run. -/
theorem valid_of_stepwise (hg : r.GenesisOK fam)
    (hstep : ∀ k s, r.steps[k]? = some s → r.ValidUpTo P fam k → r.StepOK P fam k s) :
    r.Valid P fam := by
  have key : ∀ k, r.ValidUpTo P fam k := by
    intro k
    induction k with
    | zero => exact ⟨hg, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ k ih =>
      refine ⟨hg, fun j hj s hs => ?_⟩
      rcases Nat.lt_or_ge j k with hjk | hjk
      · exact ih.2 j hjk s hs
      · have hjk' : j = k := by omega
        subst hjk'
        exact hstep j s hs ih
  exact ⟨hg, fun k s hk => (key (k + 1)).2 k (Nat.lt_succ_self k) s hk⟩

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

/-- A token live after `k` steps is a genesis token or a token output of an earlier step. -/
theorem mem_cases_of_live {k : Nat} {x : Outpoint Txid × Token Txid} (h : x ∈ r.liveAfter P k) :
    x ∈ r.genesis ∨ ∃ j < k, ∃ s : Spend Txid, r.steps[j]? = some s ∧ x ∈ s.produced P :=
  mem_everAfter_cases (mem_everAfter_of_mem_liveAfter h)

/-- The token a step spends is a genesis token or a token output of an earlier step. -/
theorem spent_cases (hv : r.Valid P fam) {k : Nat} {s : Spend Txid} (hk : r.steps[k]? = some s) :
    (s.spentOutpoint, s.spent) ∈ r.genesis ∨
      ∃ j < k, ∃ sj : Spend Txid, r.steps[j]? = some sj ∧ (s.spentOutpoint, s.spent) ∈ sj.produced P :=
  mem_cases_of_live (hv.2 k s hk).spent_live

/-- A commit-typed token output of a step in a valid prefix is the commit token of a commit step. -/
theorem produced_commit_typed_upto {k : Nat} (hv : r.ValidUpTo P fam k) {j : Nat} (hjk : j < k)
    {sj : Spend Txid} (hj : r.steps[j]? = some sj) {o : Outpoint Txid} {t : Token Txid}
    (hx : (o, t) ∈ sj.produced P) (hty : t.txoType ∈ fam.commitTypes) :
    sj.kind = .commit ∧ t = sj.commitToken := by
  have hsj := hv.2 j hjk sj hj
  have ht : t ∈ sj.tx.tokens := Spend.mem_tokens_of_mem_produced hx
  rcases Spend.mem_tokens_cases hsj.accepts ht with ⟨hc, he⟩ | ⟨hs, he⟩
  · exact ⟨hc, he⟩
  · exfalso
    have hst : sj.spent.txoType ∈ fam.commitTypes := hsj.accepts.settle_type hs
    have : t.txoType ∈ fam.settleTypes := by
      rcases he with he | ⟨_, he⟩ <;> rw [he] <;> exact Fam.settleOf_mem hst
    exact Fam.not_settle_of_commit hty this

/-- A settle-typed token output of a step in a valid prefix is a settle token of a settle step, so its parent
is the outpoint that step spent. -/
theorem produced_settle_typed_upto {k : Nat} (hv : r.ValidUpTo P fam k) {j : Nat} (hjk : j < k)
    {sj : Spend Txid} (hj : r.steps[j]? = some sj) {o : Outpoint Txid} {t : Token Txid}
    (hx : (o, t) ∈ sj.produced P) (hty : t.txoType ∈ fam.settleTypes) :
    sj.kind = .settle ∧ t.parent = some sj.spentOutpoint := by
  have hsj := hv.2 j hjk sj hj
  have ht : t ∈ sj.tx.tokens := Spend.mem_tokens_of_mem_produced hx
  rcases Spend.mem_tokens_cases hsj.accepts ht with ⟨hc, he⟩ | ⟨hs, he⟩
  · exfalso
    have : t.txoType ∈ fam.commitTypes := by rw [he]; exact hsj.accepts.commit_mode hc
    exact Fam.not_settle_of_commit this hty
  · refine ⟨hs, ?_⟩
    rcases he with he | ⟨_, he⟩ <;> rw [he] <;> rfl

/-- A commit-typed token output of a step is the commit token of a commit step. -/
theorem produced_commit_typed (hv : r.Valid P fam) {j : Nat} {sj : Spend Txid}
    (hj : r.steps[j]? = some sj) {o : Outpoint Txid} {t : Token Txid} (hx : (o, t) ∈ sj.produced P)
    (hty : t.txoType ∈ fam.commitTypes) : sj.kind = .commit ∧ t = sj.commitToken :=
  produced_commit_typed_upto (hv.upto (j + 1)) (Nat.lt_succ_self j) hj hx hty

/-- A settle-typed token output of a step is a settle token of a settle step, so its parent is the
outpoint that step spent. -/
theorem produced_settle_typed (hv : r.Valid P fam) {j : Nat} {sj : Spend Txid}
    (hj : r.steps[j]? = some sj) {o : Outpoint Txid} {t : Token Txid} (hx : (o, t) ∈ sj.produced P)
    (hty : t.txoType ∈ fam.settleTypes) : sj.kind = .settle ∧ t.parent = some sj.spentOutpoint :=
  produced_settle_typed_upto (hv.upto (j + 1)) (Nat.lt_succ_self j) hj hx hty

/-- **The grandparent is a real commit of the run, with the honest layout** (valid prefix). A commit-typed
token live after `k` valid steps that names a grandparent names output 0 of the transaction of an earlier
commit step, whose outputs are that token, the recipient's proof output and, for a split, the second
recipient's proof output, before any change. Nothing is assumed of the step that spends the token: the
Bridge applies this while proving that step valid. -/
theorem grandparent_commit_upto {k : Nat} (hv : r.ValidUpTo P fam k) {s : Spend Txid}
    (hlive : (s.spentOutpoint, s.spent) ∈ r.liveAfter P k) (hXty : s.spent.txoType ∈ fam.commitTypes)
    {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) :
    ∃ c < k, ∃ sc : Spend Txid, r.steps[c]? = some sc ∧ sc.kind = .commit ∧
      P.txid sc.tx = gp.txid ∧ gp.vout = 0 ∧
      sc.tx.outputs[0]? = some (.token sc.commitToken) ∧
      sc.tx.outputs[1]? = some (.proof sc.recipient) ∧
      (sc.mode = .split → sc.tx.outputs[2]? = some (.proof sc.recipient2)) := by
  -- the token is commit-typed, so it is the commit token of an earlier commit step j
  rcases mem_cases_of_live hlive with hg | ⟨j, hjk, sj, hj, hXj⟩
  · exact absurd (hv.1.settleTyped _ hg) (Fam.not_settle_of_commit hXty)
  obtain ⟨hjc, hXeq⟩ := produced_commit_typed_upto hv hjk hj hXj hXty
  -- its grandparent is the parent of the token that commit spent
  have hBp : sj.spent.parent = some gp := by
    have := hgp; rw [hXeq] at this; exact this
  have hsj := hv.2 j hjk sj hj
  have hBty : sj.spent.txoType ∈ fam.settleTypes := hsj.accepts.commit_type hjc
  -- that token has a parent, so it is a settle token of an earlier settle step i, and the grandparent
  -- is the outpoint i spent
  rcases mem_cases_of_live hsj.spent_live with hgB | ⟨i, hij, si, hi, hBi⟩
  · have hpl := (hv.1.parentless _ hgB).1
    simp only at hpl
    rw [hpl] at hBp; cases hBp
  obtain ⟨his, hBpar⟩ := produced_settle_typed_upto hv (by omega) hi hBi hBty
  have hgpY : gp = si.spentOutpoint := by
    rw [hBpar] at hBp
    exact (Option.some.inj hBp).symm
  -- the token at the grandparent outpoint is commit-typed, so it is the commit token of a commit step c
  have hsi := hv.2 i (by omega) si hi
  have hYty : si.spent.txoType ∈ fam.commitTypes := hsi.accepts.settle_type his
  rcases mem_cases_of_live hsi.spent_live with hgY | ⟨c, hci, sc, hc, hYc⟩
  · exact absurd (hv.1.settleTyped _ hgY) (Fam.not_settle_of_commit hYty)
  obtain ⟨hcc, -⟩ := produced_commit_typed_upto hv (by omega) hc hYc hYty
  have hsc := hv.2 c (by omega) sc hc
  obtain ⟨h0, h1, h2, hidx⟩ := Spend.commit_outputs hsc.accepts hcc
  -- the grandparent outpoint is keyed by c's transaction id, and its index holds the token
  have htxid : gp.txid = P.txid sc.tx := by
    rw [hgpY]; exact mem_producedFrom_txid hYc
  have hget : sc.tx.outputs[gp.vout]? = some (.token si.spent) := by
    have := getElem?_of_mem_producedFrom hYc
    rw [hgpY]; simpa using this
  exact ⟨c, by omega, sc, hc, hcc, htxid.symm, hidx _ _ hget, h0, h1, h2⟩

/-- **The grandparent is a real commit of the run, with the honest layout.** In a valid run, the
grandparent a settled token names is output 0 of the transaction of an earlier commit step, whose
outputs are that token, the recipient's proof output and, for a split, the second recipient's proof
output, before any change. With the script forcing the co-spent index to 1 or, for a split, 2
(`AnchorOK`), the output a settle co-spends is a proof output of its real grandparent. -/
theorem grandparent_commit (hv : r.Valid P fam) {k : Nat} {s : Spend Txid} (hk : r.steps[k]? = some s)
    (hs : s.kind = .settle) {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) :
    ∃ c < k, ∃ sc : Spend Txid, r.steps[c]? = some sc ∧ sc.kind = .commit ∧
      P.txid sc.tx = gp.txid ∧ gp.vout = 0 ∧
      sc.tx.outputs[0]? = some (.token sc.commitToken) ∧
      sc.tx.outputs[1]? = some (.proof sc.recipient) ∧
      (sc.mode = .split → sc.tx.outputs[2]? = some (.proof sc.recipient2)) :=
  grandparent_commit_upto (hv.upto k) (hv.2 k s hk).spent_live ((hv.2 k s hk).accepts.settle_type hs) hgp

/-- The grandparent's layout in the shape the Bridge's `GpReal` asks: the step's transaction id is the
outpoint's, the index is 0 and holds a token, output 1 is a proof output, and output 2 is a proof output
whenever the token at 0 is a split commit. -/
theorem grandparent_layout_upto {k : Nat} (hv : r.ValidUpTo P fam k) {s : Spend Txid}
    (hlive : (s.spentOutpoint, s.spent) ∈ r.liveAfter P k) (hXty : s.spent.txoType ∈ fam.commitTypes)
    {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) :
    ∃ c < k, ∃ sc : Spend Txid, r.steps[c]? = some sc ∧ P.txid sc.tx = gp.txid ∧ gp.vout = 0 ∧
      (∃ t, sc.tx.outputs[0]? = some (.token t)) ∧ (∃ pkh, sc.tx.outputs[1]? = some (.proof pkh)) ∧
      (∀ t, sc.tx.outputs[0]? = some (.token t) → t.txoType = 0x23 →
        ∃ pkh, sc.tx.outputs[2]? = some (.proof pkh)) := by
  obtain ⟨c, hck, sc, hc, -, hid, hvout, h0, h1, h2⟩ := grandparent_commit_upto hv hlive hXty hgp
  refine ⟨c, hck, sc, hc, hid, hvout, ⟨_, h0⟩, ⟨_, h1⟩, fun t ht hty => ⟨_, h2 ?_⟩⟩
  have hteq : t = sc.commitToken := by
    rw [h0] at ht
    exact (Out.token.inj (Option.some.inj ht)).symm
  rw [hteq, Spend.commitToken_txoType] at hty
  exact Mode.eq_split_of_commitType hty

/-- **The other grandparent is a real commit of the run.** A commit-typed token live after `k` valid steps
that names an other grandparent (a merge commit's token) names output 0 of the transaction of an earlier
commit step, the other lineage's, and that output holds a token: the shape the Bridge's `GpRealB` asks. -/
theorem other_grandparent_layout_upto {k : Nat} (hv : r.ValidUpTo P fam k) {s : Spend Txid}
    (hlive : (s.spentOutpoint, s.spent) ∈ r.liveAfter P k) (hXty : s.spent.txoType ∈ fam.commitTypes)
    {ogp : Outpoint Txid} (hogp : s.spent.otherGrandparent = some ogp) :
    ∃ c < k, ∃ sc : Spend Txid, r.steps[c]? = some sc ∧ P.txid sc.tx = ogp.txid ∧ ogp.vout = 0 ∧
      ∃ t, sc.tx.outputs[0]? = some (.token t) := by
  -- the token is the commit token of an earlier commit step j, a merge
  rcases mem_cases_of_live hlive with hg | ⟨j, hjk, sj, hj, hXj⟩
  · exact absurd (hv.1.settleTyped _ hg) (Fam.not_settle_of_commit hXty)
  obtain ⟨hjc, hXeq⟩ := produced_commit_typed_upto hv hjk hj hXj hXty
  have hsj := hv.2 j hjk sj hj
  obtain ⟨-, ⟨o, op⟩, ho, hop⟩ := Spend.commitToken_otherGrandparent (by rw [← hXeq]; exact hogp)
  simp only at hop
  -- the other token was live at j and is settle-typed, so it is a settle token of an earlier settle step
  -- i, and the other grandparent is the outpoint i spent
  have holive : (op, o) ∈ r.liveAfter P j := hsj.other_live _ ho
  have hoty : o.txoType ∈ fam.settleTypes := hsj.accepts.other_settle_typed _ ho
  rcases mem_cases_of_live holive with hgo | ⟨i, hij, si, hi, hoi⟩
  · have hpl := (hv.1.parentless _ hgo).1
    simp only at hpl
    rw [hpl] at hop; cases hop
  obtain ⟨his, hopar⟩ := produced_settle_typed_upto hv (by omega) hi hoi hoty
  have hogpY : ogp = si.spentOutpoint := by
    rw [hopar] at hop
    exact (Option.some.inj hop).symm
  -- the token at that outpoint is commit-typed, so it is the commit token of a commit step c
  have hsi := hv.2 i (by omega) si hi
  have hYty : si.spent.txoType ∈ fam.commitTypes := hsi.accepts.settle_type his
  rcases mem_cases_of_live hsi.spent_live with hgY | ⟨c, hci, sc, hc, hYc⟩
  · exact absurd (hv.1.settleTyped _ hgY) (Fam.not_settle_of_commit hYty)
  obtain ⟨hcc, -⟩ := produced_commit_typed_upto hv (by omega) hc hYc hYty
  have hsc := hv.2 c (by omega) sc hc
  obtain ⟨h0, -, -, hidx⟩ := Spend.commit_outputs hsc.accepts hcc
  have htxid : ogp.txid = P.txid sc.tx := by
    rw [hogpY]; exact mem_producedFrom_txid hYc
  have hget : sc.tx.outputs[ogp.vout]? = some (.token si.spent) := by
    have := getElem?_of_mem_producedFrom hYc
    rw [hogpY]; simpa using this
  exact ⟨c, by omega, sc, hc, htxid.symm, hidx _ _ hget, sc.commitToken, h0⟩

end Run

end BoltProof
