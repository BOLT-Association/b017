import BoltProof.Theorems.StateMachine

/-!
# Theorem 1 — Authenticity

`docs/formal-proof.md` §4: every token in a valid chain has a `parent`-chain that terminates
at a unique parentless root — its genesis — with the same issuer, and the deep ancestors a
settle rebuilds are the real ones.

The lineage of a token is a *function* of the run (`Run.lineage`, `Run.root`): it walks
`parent` through the outputs the run created. Uniqueness of the root is therefore
definitional; what has to be proved is that the walk is well-founded, reaches a genesis
token, and that every link is a real, covenant-accepted transition (`Rooted`).

Only `t1_rebuild_sound` uses a cryptographic hypothesis (Assumption 1, `CollisionFree`);
everything else is unconditional.
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

namespace Run

variable (P : Prims Txid) (r : Run Txid)

/-- The parent walk from `t`, at most `n` hops. -/
def lineageFuel : Nat → Token Txid → List (Token Txid)
  | 0, t => [t]
  | n + 1, t =>
    t :: (match t.parent.bind (r.tokenAt P) with
      | some u => lineageFuel n u
      | none => [])

/-- The end of the parent walk from `t`, at most `n` hops. -/
def rootFuel : Nat → Token Txid → Token Txid
  | 0, t => t
  | n + 1, t =>
    match t.parent.bind (r.tokenAt P) with
    | some u => rootFuel n u
    | none => t

/-- The lineage of a token: itself, its parent, its grandparent, … back to the root. -/
def lineage (t : Token Txid) : List (Token Txid) := r.lineageFuel P r.steps.length t

/-- The root (genesis) of a token's lineage. -/
def root (t : Token Txid) : Token Txid := r.rootFuel P r.steps.length t

variable {P r}

theorem lineageFuel_genesis {t : Token Txid} (h : t.parent = none) (n : Nat) :
    r.lineageFuel P n t = [t] := by
  cases n <;> simp [lineageFuel, h]

theorem rootFuel_genesis {t : Token Txid} (h : t.parent = none) (n : Nat) :
    r.rootFuel P n t = t := by
  cases n <;> simp [rootFuel, h]

theorem lineageFuel_link {t u : Token Txid} {o : Outpoint Txid} (hp : t.parent = some o)
    (hu : r.tokenAt P o = some u) (n : Nat) :
    r.lineageFuel P (n + 1) t = t :: r.lineageFuel P n u := by
  simp [lineageFuel, hp, hu]

theorem rootFuel_link {t u : Token Txid} {o : Outpoint Txid} (hp : t.parent = some o)
    (hu : r.tokenAt P o = some u) (n : Nat) :
    r.rootFuel P (n + 1) t = r.rootFuel P n u := by
  simp [rootFuel, hp, hu]

theorem lineageFuel_head (n : Nat) (t : Token Txid) : (r.lineageFuel P n t)[0]? = some t := by
  cases n <;> simp [lineageFuel]

theorem rootFuel_mem (n : Nat) (t : Token Txid) : r.rootFuel P n t ∈ r.lineageFuel P n t := by
  induction n generalizing t with
  | zero => simp [rootFuel, lineageFuel]
  | succ n ih =>
    cases hp : t.parent with
    | none => simp [rootFuel_genesis hp, lineageFuel_genesis hp]
    | some o =>
      cases hu : r.tokenAt P o with
      | none => simp [rootFuel, lineageFuel, hp, hu]
      | some u =>
        rw [rootFuel_link hp hu, lineageFuel_link hp hu]
        exact List.mem_cons_of_mem _ (ih u)

end Run

/-- `Rooted P fam r d t`: `t` reaches a genesis token of `r` in `d` real hops. Each hop is a
covenant-accepted transition: the parent outpoint was created by the run (`tokenAt`), the
issuer is inherited, the grandparent pointer is the parent's parent, and the types follow
an edge of the machine. -/
inductive Rooted (P : Prims Txid) (fam : Fam) (r : Run Txid) : Nat → Token Txid → Prop
  | genesis {o : Outpoint Txid} {t : Token Txid} : (o, t) ∈ r.genesis → Rooted P fam r 0 t
  | link {d : Nat} {t u : Token Txid} {o : Outpoint Txid} :
      t.parent = some o → r.tokenAt P o = some u → Rooted P fam r d u →
      t.issuer = u.issuer → t.grandparent = u.parent → fam.edge u.txoType t.txoType →
      Rooted P fam r (d + 1) t

namespace Rooted

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

/-- Along a rooted lineage the issuer is the run's issuer. -/
theorem issuer (hv : r.Valid P fam) {d : Nat} {t : Token Txid} (h : Rooted P fam r d t) :
    t.issuer = r.issuer := by
  induction h with
  | genesis hg => exact hv.1.issuer _ hg
  | link _ _ _ hi _ _ ih => exact hi.trans ih

/-- The walk of at least `d` hops ends at a parentless genesis token. -/
theorem root (hv : r.Valid P fam) {d : Nat} {t : Token Txid} (h : Rooted P fam r d t) :
    ∀ n, d ≤ n → (r.rootFuel P n t).parent = none ∧ ∃ o, (o, r.rootFuel P n t) ∈ r.genesis := by
  induction h with
  | genesis hg =>
    intro n _
    have hp := (hv.1.parentless _ hg).1
    rw [Run.rootFuel_genesis hp]
    exact ⟨hp, _, hg⟩
  | link hp hu _ _ _ _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Run.rootFuel_link hp hu]
    exact ih n (by omega)

/-- Every token on the walk carries the run's issuer. -/
theorem lineage_issuer (hv : r.Valid P fam) {d : Nat} {t : Token Txid} (h : Rooted P fam r d t) :
    ∀ n, ∀ u ∈ r.lineageFuel P n t, u.issuer = r.issuer := by
  induction h with
  | genesis hg =>
    intro n u hu
    rw [Run.lineageFuel_genesis (hv.1.parentless _ hg).1] at hu
    simp at hu
    subst hu
    exact hv.1.issuer _ hg
  | link hp hu hr hi _ _ ih =>
    intro n v hv'
    cases n with
    | zero =>
      simp [Run.lineageFuel] at hv'
      subst hv'
      exact hi.trans (Rooted.issuer hv hr)
    | succ n =>
      rw [Run.lineageFuel_link hp hu] at hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hi.trans (Rooted.issuer hv hr)
      · exact ih n v hv'

/-- Consecutive tokens on the walk are joined by a real link: the later one's `parent` is an
outpoint the run created for the earlier one, and their types follow an edge. -/
theorem lineage_links (hv : r.Valid P fam) {d : Nat} {t : Token Txid} (h : Rooted P fam r d t) :
    ∀ n i a b, (r.lineageFuel P n t)[i]? = some a → (r.lineageFuel P n t)[i + 1]? = some b →
      (∃ o, a.parent = some o ∧ r.tokenAt P o = some b) ∧ a.grandparent = b.parent ∧
        fam.edge b.txoType a.txoType := by
  induction h with
  | genesis hg =>
    intro n i a b _ hb
    rw [Run.lineageFuel_genesis (hv.1.parentless _ hg).1] at hb
    simp at hb
  | link hp hu hr hi hg he ih =>
    intro n i a b ha hb
    cases n with
    | zero => simp [Run.lineageFuel] at hb
    | succ n =>
      rw [Run.lineageFuel_link hp hu] at ha hb
      cases i with
      | zero =>
        simp at ha
        subst ha
        rw [List.getElem?_cons_succ, Run.lineageFuel_head] at hb
        simp at hb
        subst hb
        exact ⟨⟨_, hp, hu⟩, hg, he⟩
      | succ i =>
        rw [List.getElem?_cons_succ] at ha hb
        exact ih n i a b ha hb

end Rooted

/-! ## Every token the run creates is rooted -/

namespace Run

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

theorem everAfter_rooted (hv : r.Valid P fam) (k : Nat) :
    ∀ x ∈ r.everAfter P k, ∃ d, Rooted P fam r d x.2 := by
  induction k with
  | zero =>
    intro x hx
    exact ⟨0, Rooted.genesis hx⟩
  | succ k ih =>
    intro x hx
    cases hk : r.steps[k]? with
    | none => rw [everAfter_succ_none hk] at hx; exact ih x hx
    | some s =>
      rw [everAfter_succ_some hk] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih x hx
      · have hs := hv.2 k s hk
        have ht := Spend.mem_tokens_of_mem_produced hx
        obtain ⟨hp, hg, hi⟩ := Spend.token_fields hs.accepts ht
        have hu : r.tokenAt P s.spentOutpoint = some s.spent :=
          tokenAt_of_mem hv (mem_everAfter_of_mem_liveAfter hs.spent_live)
        obtain ⟨d, hd⟩ := ih _ (mem_everAfter_of_mem_liveAfter hs.spent_live)
        exact ⟨d + 1, Rooted.link hp hu hd hi hg (t4_step hs.accepts _ ht)⟩

/-- The walk from a token created at step `k` needs at most `k` hops. -/
theorem everAfter_rooted_depth (hv : r.Valid P fam) (k : Nat) :
    ∀ x ∈ r.everAfter P k, ∃ d ≤ k, Rooted P fam r d x.2 := by
  induction k with
  | zero =>
    intro x hx
    exact ⟨0, Nat.le_refl _, Rooted.genesis hx⟩
  | succ k ih =>
    intro x hx
    cases hk : r.steps[k]? with
    | none =>
      rw [everAfter_succ_none hk] at hx
      obtain ⟨d, hd, hr⟩ := ih x hx
      exact ⟨d, Nat.le_succ_of_le hd, hr⟩
    | some s =>
      rw [everAfter_succ_some hk] at hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨d, hd, hr⟩ := ih x hx
        exact ⟨d, Nat.le_succ_of_le hd, hr⟩
      · have hs := hv.2 k s hk
        have ht := Spend.mem_tokens_of_mem_produced hx
        obtain ⟨hp, hg, hi⟩ := Spend.token_fields hs.accepts ht
        have hu : r.tokenAt P s.spentOutpoint = some s.spent :=
          tokenAt_of_mem hv (mem_everAfter_of_mem_liveAfter hs.spent_live)
        obtain ⟨d, hd, hr⟩ := ih _ (mem_everAfter_of_mem_liveAfter hs.spent_live)
        exact ⟨d + 1, Nat.succ_le_succ hd, Rooted.link hp hu hr hi hg (t4_step hs.accepts _ ht)⟩

theorem live_rooted (hv : r.Valid P fam) :
    ∀ x ∈ r.live P, ∃ d ≤ r.steps.length, Rooted P fam r d x.2 := fun x hx =>
  everAfter_rooted_depth hv _ x (mem_everAfter_of_mem_liveAfter hx)

/-- **Theorem 1 (Authenticity).** Every live token of a valid run:
1. has a lineage whose root is a parentless genesis token of the run (the unique root, since
   `root` is a function of the token and the run);
2. carries the run's issuer, as does every token on its lineage;
3. is joined to its root by real links: each token's `parent` is an outpoint the run created
   for the previous one, grandparent pointers agree, and the types follow the machine. -/
theorem t1_authenticity (hv : r.Valid P fam) :
    ∀ x ∈ r.live P,
      ((r.root P x.2).parent = none ∧ ∃ o, (o, r.root P x.2) ∈ r.genesis) ∧
      (∀ u ∈ r.lineage P x.2, u.issuer = r.issuer) ∧
      (∀ i a b, (r.lineage P x.2)[i]? = some a → (r.lineage P x.2)[i + 1]? = some b →
        (∃ o, a.parent = some o ∧ r.tokenAt P o = some b) ∧ a.grandparent = b.parent ∧
          fam.edge b.txoType a.txoType) := by
  intro x hx
  obtain ⟨d, hd, hr⟩ := live_rooted hv x hx
  exact ⟨hr.root hv _ hd, hr.lineage_issuer hv _, hr.lineage_links hv _⟩

/-- The root lies on the lineage, and every live token's issuer is the run's. -/
theorem t1_issuer_invariant (hv : r.Valid P fam) : ∀ x ∈ r.live P, x.2.issuer = r.issuer := by
  intro x hx
  obtain ⟨d, _, hr⟩ := live_rooted hv x hx
  exact hr.issuer hv

theorem root_mem_lineage (t : Token Txid) : r.root P t ∈ r.lineage P t :=
  rootFuel_mem _ _

/-- **Theorem 1 (ancestor integrity, Lemma 3 + Assumption 1).** Under collision resistance,
the ancestor transaction a settle rebuilds *is* the transaction of the step that created the
grandparent outpoint: a spliced ancestor would be a collision. -/
theorem t1_rebuild_sound (hc : CollisionFree P) (hv : r.Valid P fam) {k j : Nat}
    {s sj : Spend Txid} (hk : r.steps[k]? = some s) (hs : s.kind = .settle)
    {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) (_hj : r.steps[j]? = some sj)
    (hprod : P.txid sj.tx = gp.txid) : s.anc = some sj.tx := by
  obtain ⟨A, _, hA, hid, _⟩ := (hv.2 k s hk).accepts.l3_rebuild hs gp hgp
  rw [hA, hc A sj.tx (hid.trans hprod.symm)]

end Run

/-! ## Theorem 1, one transition at a time

The per-hop form of authenticity, stated of a single accepted spend so that the bytecode refinements
(`Bridge/Glue/*/EndToEnd.lean`) can state it of the shipped bytes: what a lineage verifier checks at each hop
is that the token it holds was written by the covenant from the token it spent. -/

/-- **Theorem 1, per transition.** Every token an accepted spend produces carries the spent token's issuer and
names the spent outpoint as its parent: one hop of a lineage is what the covenant wrote from the token it spent. -/
theorem t1_step {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s) :
    ∀ t ∈ s.tx.tokens, t.issuer = s.spent.issuer ∧ t.parent = some s.spentOutpoint := by
  intro t ht
  rcases Spend.mem_tokens_cases h ht with ⟨_, rfl⟩ | ⟨_, rfl | ⟨_, rfl⟩⟩ <;> exact ⟨rfl, rfl⟩

/-- **Lemma 5, per transition.** A parentless token, the genesis, moves only under the issuer's key. -/
theorem t1_genesis_signer {P : Prims Txid} {fam : Fam} {s : Spend Txid} (h : Accepts P fam s)
    (hg : s.spent.isGenesis) : s.signer = s.spent.issuer :=
  h.l5_issuer (Or.inl hg)

end BoltProof
