import BoltProof.Bridge.Glue.AuthBolt.Refine
import BoltProof.Bridge.Glue.AuthBolt.Regress
import BoltProof.Theorems.Ownership
import BoltProof.Theorems.StateMachine
import BoltProof.Theorems.Balance
import BoltProof.Theorems.Authenticity
import BoltProof.Theorems.Chain
import BoltProof.Theorems.ProofGating

/-!
# `AuthBOLT`: a chain of real spends is a valid run

The chaining step, Bridge half (`lean/README.md`, "The chain"). `AuthBolt/Refine.lean` states what
holds of one real spend; this file reads a whole chain of real spends as a model `Run` and proves the
run valid, so Layer 1's run-level theorems hold of real tokens: Theorem 1 over a history (every live
token is rooted at a genesis token of the run and carries the issuer along its lineage), Theorem 3's
count, Theorem 4 over every token ever created, and Theorem 5 (proof gating, the fabricated-hop
exclusion).

What is assumed of each spend is `ChainSpend`: everything `authBolt_refines` asks, with one thing left out and
two added. Left out is `GpReal`, the reality of the grandparent a settle names; the chain supplies it. In
a valid prefix of the run the grandparent is output 0 of an earlier commit step whose transaction the
chain already holds as a real spend (`Run.grandparent_layout_upto`, `Theorems/Chain.lean`), and that
transaction is well-formed, has the token at index 0 and a proof output at index 1, so `GpReal` is proved
rather than assumed (`gpReal_of_chain`). Added are two facts about the spend's own transaction, used when
a later settle names it: nothing else serialises to its hash, and the primitives' id of its abstraction
is its real id (the same two facts `GpReal` asked of the grandparent). The chain's own hypotheses are the
UTXO model's: a well-formed genesis set, each step spending a live token, and each step's id new
(`RealChain`); none is the covenant's to check.

The induction is `Run.valid_of_stepwise`: step `k` is read as a real spend, its grandparent is read off
the valid prefix, and the refinement (`authBolt_refines`) gives `Accepts`.
-/

set_option autoImplicit false

namespace BoltProof.Glue.AuthBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Bridge (params)

/-- One spend of a real `AuthBOLT` chain: what `authBolt_refines` asks of a spend, with the grandparent's
reality (`GpReal`) left out, since the chain supplies it, and two facts about this transaction itself that
the chain uses when a later settle names it as a grandparent: nothing else serialises to its hash, and the
primitives' id of its abstraction is its real id. -/
structure ChainSpend (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) : Prop where
  hwf : WF f
  hargs : castToBool a.pre = true → ArgsWF a
  hty : f.ty = [0x00] ∨ f.ty = [0x21]
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  pushTx : PushTxSound tx i amt (lockOf f)
  preimage : NoSecondPreimage (preimageBIP143 (lockOf f) tx i ⟨0x41⟩ amt)
  outputs : NoSecondPreimage ((tx.outputs.map serTxOut).flatten)
  prevouts : NoSecondPreimage ((tx.inputs.map serOutPoint).flatten)
  agrees : Agrees P tx i amt (lockOf f)
  honest : castToBool a.pre = true → HonestOutputs tx (if f.ty = [0] then 2 else 1)
  melt : castToBool a.pre = false → HonestMelt tx
  nsp : NoSecondPreimage (serTx tx)
  ptxid : P.txid (absTx tx) = Sighash.txid tx
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust (some (lockOf f)))
    scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockOf f) = .valid

/-- A real `AuthBOLT` chain: a run whose genesis set is well-formed, whose every step is the
abstraction of a real spend (`ChainSpend`), and whose ledger bookkeeping holds: each step spends a token
live at that point and each step's transaction id is new. The first is the UTXO model's rule and the
others the ledger's; none is the covenant's to check. -/
structure RealChain (P : Prims Bytes) (r : Run Bytes) : Prop where
  genesis : r.GenesisOK .nft
  steps : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s →
    ∃ (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes) (scriptSig : Bytes),
      s = spendOf tx i f a ∧ ChainSpend P tx i amt f a S scriptSig
  spent_live : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s → (s.spentOutpoint, s.spent) ∈ r.liveAfter P k
  fresh : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s → ∀ x ∈ r.everAfter P k, x.1.txid ≠ P.txid s.tx

variable {P : Prims Bytes} {r : Run Bytes}

/-- **The grandparent a settle of the chain names is real.** Read off the valid prefix: it is output 0 of
the transaction of an earlier commit step, which the chain holds as a real spend, so it is well-formed,
its id is the one the token names, nothing else serialises to its hash, the primitives agree on its id,
the token sits at index 0 and a proof output at index 1. -/
theorem gpReal_of_chain (h : RealChain P r) {k : Nat} (hv : r.ValidUpTo P .nft k) {tx : Tx} {i : Nat}
    {f : Fields} {a : Args}
    (hlive : ((spendOf tx i f a).spentOutpoint, (spendOf tx i f a).spent) ∈ r.liveAfter P k)
    (hty : f.ty = [0x21]) : GpReal P f := by
  intro hgp0
  have hXty : (spendOf tx i f a).spent.txoType ∈ Fam.commitTypes .nft := by
    simp [spendOf, tokenOf, hty, Fam.commitTypes]
  have hgp : (spendOf tx i f a).spent.grandparent =
      some ⟨List.take 32 f.gp, leNat (List.drop 32 f.gp)⟩ := by
    simp [spendOf, tokenOf, outpointOf, hgp0]
  obtain ⟨c, -, sc, hc, hid, hvout, ⟨t, ht⟩, ⟨pkh, hpk⟩, -⟩ := Run.grandparent_layout_upto hv hlive hXty hgp
  obtain ⟨txc, ic, amtc, fc, ac, Sc, sigc, rfl, hcs⟩ := h.steps c sc hc
  have hvout' : leNat (List.drop 32 f.gp) = 0 := hvout
  refine ⟨txc, hcs.htx, ?_, hcs.nsp, hcs.ptxid, ⟨t, ?_⟩, ⟨pkh, hpk⟩⟩
  · rw [← hcs.ptxid]; exact hid
  · rw [hvout']; exact ht

/-- **A chain of real spends is a valid run.** Every step is accepted by the model (`authBolt_refines`,
with the grandparent's reality read off the steps before it) and the ledger facts are the chain's. -/
theorem valid_of_chain (h : RealChain P r) : r.Valid P .nft := by
  refine Run.valid_of_stepwise h.genesis ?_
  intro k s hk hv
  obtain ⟨tx, i, amt, f, a, S, scriptSig, rfl, hcs⟩ := h.steps k s hk
  have hlive := h.spent_live k _ hk
  have hres : Residual P tx i amt f a :=
    ⟨hcs.pushTx, hcs.preimage, hcs.outputs, hcs.prevouts, fun _ hty => gpReal_of_chain h hv hlive hty,
      hcs.agrees, hcs.honest, hcs.melt⟩
  exact ⟨authBolt_refines P tx i amt f a S scriptSig hcs.hwf hcs.hargs hcs.hty hcs.htx hcs.hamt hcs.hi hcs.hnz
      hres hcs.hstack hcs.hvalid,
    hlive, fun o ho => by simp [spendOf] at ho, h.fresh k _ hk⟩

/-! ## What holds of real tokens

Each theorem is Layer 1's run-level statement applied to the run a real chain is, so it speaks of
`AuthBOLT` tokens the consensus rules have accepted. -/

/-- **Theorem 1 of the shipped bytes, over a history.** Every live token of a real chain has a lineage whose
root is a parentless genesis token of the run, carries the run's issuer along that lineage, and is joined
to its root by real links: each token's parent is an outpoint the run created for the previous one, the
grandparent pointers agree, and the types follow the NFT machine. -/
theorem chain_authenticity (h : RealChain P r) :
    ∀ x ∈ r.live P,
      ((r.root P x.2).parent = none ∧ ∃ o, (o, r.root P x.2) ∈ r.genesis) ∧
      (∀ u ∈ r.lineage P x.2, u.issuer = r.issuer) ∧
      (∀ i a b, (r.lineage P x.2)[i]? = some a → (r.lineage P x.2)[i + 1]? = some b →
        (∃ o, a.parent = some o ∧ r.tokenAt P o = some b) ∧ a.grandparent = b.parent ∧
          Fam.edge .nft b.txoType a.txoType) :=
  Run.t1_authenticity (valid_of_chain h)

/-- **Theorem 1, the invariant.** Every live token of a real chain carries the run's issuer. -/
theorem chain_issuer_invariant (h : RealChain P r) : ∀ x ∈ r.live P, x.2.issuer = r.issuer :=
  Run.t1_issuer_invariant (valid_of_chain h)

/-- **Theorem 3 of the shipped bytes, over a history.** Tokens are neither created nor duplicated: the live
count plus the melts is the number minted. -/
theorem chain_count (h : RealChain P r) (k : Nat) :
    (r.liveAfter P k).length + r.meltCount k = r.genesis.length :=
  Run.t3_nft_count (valid_of_chain h) k

/-- **Theorem 4 of the shipped bytes, over a history.** Every token a real chain ever created carries one of
the NFT machine's two type bytes. -/
theorem chain_defined_types (h : RealChain P r) (k : Nat) :
    ∀ x ∈ r.everAfter P k, x.2.txoType ∈ Fam.settleTypes .nft ++ Fam.commitTypes .nft :=
  t4_defined_types (valid_of_chain h) k

/-- **Theorem 5 of the shipped bytes (proof gating).** Under the UTXO rule, two distinct settles of a real
chain consume two distinct proof outpoints: a commit's proof output admits at most one settle. -/
theorem chain_proof_gating (h : RealChain P r) (hnd : r.NoDoubleSpend) {i j : Nat} {si sj : Spend Bytes}
    (hi : r.steps[i]? = some si) (hj : r.steps[j]? = some sj) (hne : i ≠ j)
    (hsi : si.kind = .settle) (hsj : sj.kind = .settle) {gpi gpj : Outpoint Bytes}
    (hgi : si.spent.grandparent = some gpi) (hgj : sj.spent.grandparent = some gpj) :
    ∃ pi pj : Outpoint Bytes,
      pi.txid = gpi.txid ∧ pi ∈ si.tx.inputs ∧ pj.txid = gpj.txid ∧ pj ∈ sj.tx.inputs ∧ pi ≠ pj :=
  Run.t5_proof_gating (valid_of_chain h) hnd hi hj hne hsi hsj hgi hgj

/-- **Theorem 1, ancestor integrity, of the shipped bytes.** Under A1, the ancestor a settle of a real chain
rebuilds is the transaction of the step that created the grandparent outpoint. -/
theorem chain_rebuild_sound (hc : CollisionFree P) (h : RealChain P r) {k j : Nat} {s sj : Spend Bytes}
    (hk : r.steps[k]? = some s) (hs : s.kind = .settle) {gp : Outpoint Bytes}
    (hgp : s.spent.grandparent = some gp) (hj : r.steps[j]? = some sj) (hprod : P.txid sj.tx = gp.txid) :
    s.anc = some sj.tx :=
  Run.t1_rebuild_sound hc (valid_of_chain h) hk hs hgp hj hprod

/-- **Theorem 5 of the shipped bytes, combined.** In a real chain under the UTXO rule and A1, every settle
with a grandparent consumes a proof outpoint of the grandparent's transaction that no other step consumes. -/
theorem chain_fabricated_hop_excluded (hc : CollisionFree P) (h : RealChain P r) (hnd : r.NoDoubleSpend)
    {k c : Nat} {s sc : Spend Bytes} (hk : r.steps[k]? = some s) (hs : s.kind = .settle)
    {gp : Outpoint Bytes} (hgp : s.spent.grandparent = some gp) (hcs : r.steps[c]? = some sc)
    (hprod : P.txid sc.tx = gp.txid) :
    ∃ (t : Token Bytes) (j : Nat) (pkh : PKH), sc.tx.outputs[gp.vout]? = some (.token t) ∧
      sc.tx.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Bytes) ∈ s.tx.inputs ∧
      (∀ k' s', r.steps[k']? = some s' → k' ≠ k → (⟨gp.txid, j⟩ : Outpoint Bytes) ∉ s'.tx.inputs) ∧
      (Fam.nft = .fungible → s.spent.balance = t.settledBalance .nft (j - 1)) :=
  Run.t5_fabricated_hop_excluded hc (valid_of_chain h) hnd hk hs hgp hcs hprod

end BoltProof.Glue.AuthBolt
