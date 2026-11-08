import BoltProof.Theorems.Authenticity

/-!
# Theorem 5 — Proof gating (the fabricated-hop exclusion at the ledger level)

`docs/formal-proof.md` §8.1, last row: the historical **fabricated hop**. A past recipient, who
legitimately owns a real commit's proof output, funds a sibling settle-typed token carrying an
arbitrary balance, commits it, and settles it while co-spending that real proof. The pre-fix
covenant accepted the chain; the fix anchors the settle to the rebuilt ancestor's own balance
transition (`Accepts.l3_rebuild`, last conjunct).

Two facts make the attack zero-sum once the anchor is in place, and both are stated here above
the single-spend interface:

* **Proof outputs are single-use gates.** A settle with a grandparent co-spends a proof output
  of the transaction its grandparent id names (Lemma 3). Under the UTXO rule that no outpoint is
  consumed twice (`NoDoubleSpend`), two distinct settles consume two distinct proof outpoints —
  so a commit's proof can admit at most one settle, honest or not, and a forged settle that
  consumes it has displaced the honest one (`t5_proof_gating`).
* **The settled balance is the ancestor's.** Under collision resistance, the transaction a
  settle rebuilds is the transaction of the step that created the grandparent outpoint, so the
  spent balance equals the settle result of *that* commit's token: a cloned settle cannot carry
  a balance the real lineage did not (`t5_balance_anchor`).

What these do **not** say: that a transaction which creates a token-shaped output without
spending a token (a fabrication, which runs no covenant) cannot exist on-chain. It can; the
run model admits only covenant-created tokens, and the off-chain verifier's lineage checks
(`docs/verification-scaling.md`) are what refuse such an anchor. The theorems bound what a
fabrication can *extract* through a real proof: nothing beyond the real transition.
-/

set_option linter.unusedSectionVars false

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

namespace Run

variable {P : Prims Txid} {fam : Fam} {r : Run Txid}

/-- The UTXO rule for the transactions of a run: no outpoint is consumed by two steps. -/
abbrev NoDoubleSpend (r : Run Txid) : Prop :=
  ∀ (i j : Nat) (si sj : Spend Txid), r.steps[i]? = some si → r.steps[j]? = some sj → i ≠ j →
    ∀ o : Outpoint Txid, o ∈ si.tx.inputs → o ∉ sj.tx.inputs

/-- **Lemma 3, extracted.** A settle of a token with a grandparent co-spends a proof output of
the transaction the grandparent's id names. -/
theorem settle_consumes_proof (hv : r.Valid P fam) {k : Nat} {s : Spend Txid}
    (hk : r.steps[k]? = some s) (hs : s.kind = .settle) {gp : Outpoint Txid}
    (hgp : s.spent.grandparent = some gp) :
    ∃ (A : TxDesc Txid) (j : Nat) (pkh : PKH), s.anc = some A ∧ P.txid A = gp.txid ∧
      A.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Txid) ∈ s.tx.inputs := by
  obtain ⟨A, _, hA, hid, _, ⟨j, pkh, hj, hin⟩, _⟩ := (hv.2 k s hk).accepts.l3_rebuild hs gp hgp
  exact ⟨A, j, pkh, hA, hid, hj, hin⟩

/-- **Theorem 5 (proof gating).** Two distinct settles of tokens with grandparents consume two
distinct proof outpoints: a commit's proof output admits at most one settle. -/
theorem t5_proof_gating (hv : r.Valid P fam) (hnd : r.NoDoubleSpend) {i j : Nat}
    {si sj : Spend Txid} (hi : r.steps[i]? = some si) (hj : r.steps[j]? = some sj) (hne : i ≠ j)
    (hsi : si.kind = .settle) (hsj : sj.kind = .settle) {gpi gpj : Outpoint Txid}
    (hgi : si.spent.grandparent = some gpi) (hgj : sj.spent.grandparent = some gpj) :
    ∃ pi pj : Outpoint Txid,
      pi.txid = gpi.txid ∧ pi ∈ si.tx.inputs ∧ pj.txid = gpj.txid ∧ pj ∈ sj.tx.inputs ∧ pi ≠ pj := by
  obtain ⟨_, ki, _, _, _, _, hin_i⟩ := settle_consumes_proof hv hi hsi hgi
  obtain ⟨_, kj, _, _, _, _, hin_j⟩ := settle_consumes_proof hv hj hsj hgj
  refine ⟨⟨gpi.txid, ki⟩, ⟨gpj.txid, kj⟩, rfl, hin_i, rfl, hin_j, ?_⟩
  intro heq
  exact hnd i j si sj hi hj hne _ hin_i (heq ▸ hin_j)

/-- **Theorem 5 (balance anchor).** Under collision resistance, when the grandparent outpoint of
a settled token was created by step `c`, the rebuilt ancestor is `c`'s transaction, its token
output at that outpoint is a commit token, and (fungible) the spent balance is exactly that
token's settle result at the parent's index: a cloned settle carries the real lineage's balance.
The producing step is a hypothesis (`_hcs`, `hprod`), not derived. -/
theorem t5_balance_anchor (hc : CollisionFree P) (hv : r.Valid P fam) {k c : Nat}
    {s sc : Spend Txid} (hk : r.steps[k]? = some s) (hs : s.kind = .settle)
    {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) (_hcs : r.steps[c]? = some sc)
    (hprod : P.txid sc.tx = gp.txid) :
    s.anc = some sc.tx ∧
    ∃ t : Token Txid, sc.tx.outputs[gp.vout]? = some (.token t) ∧
      (fam = .fungible → ∀ p, s.spent.parent = some p → s.spent.balance = t.settledBalance fam p.vout) := by
  obtain ⟨A, t, hA, hid, ht, _, hbal⟩ := (hv.2 k s hk).accepts.l3_rebuild hs gp hgp
  have hAeq : A = sc.tx := hc A sc.tx (hid.trans hprod.symm)
  subst hAeq
  exact ⟨hA, t, ht, hbal⟩

/-- **Theorem 5, combined.** In a valid, double-spend-free run under collision resistance, every
settle with a grandparent (i) consumes a proof outpoint of the grandparent's transaction that
no other settle consumes, and (ii) carries the balance the grandparent's own transition dictates. -/
theorem t5_fabricated_hop_excluded (hc : CollisionFree P) (hv : r.Valid P fam) (hnd : r.NoDoubleSpend)
    {k c : Nat} {s sc : Spend Txid} (hk : r.steps[k]? = some s) (hs : s.kind = .settle)
    {gp : Outpoint Txid} (hgp : s.spent.grandparent = some gp) (hcs : r.steps[c]? = some sc)
    (hprod : P.txid sc.tx = gp.txid) :
    (∃ j, (⟨gp.txid, j⟩ : Outpoint Txid) ∈ s.tx.inputs ∧
      ∀ k' s', r.steps[k']? = some s' → k' ≠ k → (⟨gp.txid, j⟩ : Outpoint Txid) ∉ s'.tx.inputs) ∧
    (∃ t : Token Txid, sc.tx.outputs[gp.vout]? = some (.token t) ∧
      (fam = .fungible → ∀ p, s.spent.parent = some p → s.spent.balance = t.settledBalance fam p.vout)) := by
  obtain ⟨_, j, _, _, _, _, hin⟩ := settle_consumes_proof hv hk hs hgp
  obtain ⟨_, t, ht, hbal⟩ := t5_balance_anchor hc hv hk hs hgp hcs hprod
  refine ⟨⟨j, hin, fun k' s' hk' hne' hin' => hnd k k' s s' hk hk' (Ne.symm hne') _ hin hin'⟩, t, ht, hbal⟩

end Run

end BoltProof
