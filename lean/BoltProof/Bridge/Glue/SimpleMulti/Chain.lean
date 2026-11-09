import BoltProof.Bridge.Glue.SimpleMulti.EndToEnd
import BoltProof.Theorems.Chain
import BoltProof.Theorems.ProofGating

/-!
# `SimpleMultiBOLT`: a chain of real spends is a valid run

The chaining step, Bridge half, for the fungible family, as `Refine/Chain.lean` does it for
`MinSimpleBOLT`. A chain of real `SimpleMultiBOLT` spends, each read by the refinement stage that fits it
(`ChainStep`), is a model `Run`; this file proves the run valid, so Layer 1's run-level theorems hold of
real fungible tokens: Theorem 1 over a history, Theorem 3's conservation of value, Theorem 4 over every
token ever created, and Theorem 5 (proof gating, the fabricated-hop exclusion).

The grandparents' reality is read off the run instead of assumed. For a settle with a grandparent the
refinement wants `GpRealF` of the ancestor `G` it is given; the chain asserts of `G` only that it is a
well-formed transaction whose id the token names, with no second preimage of its serialisation and the
primitives' id (`ChainTx`), and that its token outputs' balance fields are non-negative script numbers
(`BalsNonneg`). In a valid prefix the grandparent outpoint is output 0 of an earlier commit step whose
outputs are its token and the recipients' proof outputs (`Run.grandparent_layout_upto`,
`Theorems/Chain.lean`), and A1 (`CollisionFree`) identifies `G`'s abstraction with that step's transaction,
as the hand proof's Lemma 3 does, so `GpRealF` follows (`gpRealF_of_chain`). A merge settle's other
grandparent is read the same way (`Run.other_grandparent_layout_upto`, `gpRealB_of_chain`).

What stays assumed, per step: the fungible `Residual` (the cryptographic assumptions and the clauses the
bytes do not check), the rebuild's piece widths (`HonestPiecesB`, §7 Q7), the index arguments' widths, Q8's
preimage at a merge's partner input, and two facts about ancestors that the bytes write but the proof
reads off the chain: `BalsNonneg`, and that a merge settle's other-lineage index argument `i4` names a proof
output of the other grandparent (`proofB`; the first rebuild's anchor fixes its index, `AnchorOK.index`, and the
vectors `smb_probe_q9_*` show the second rebuild pins `i4` the same way, a settle naming the change output being
refused and the proof control accepted, so `proofB` is a proof debt until a lemma reads that pin off the bytes). The chain's own hypotheses
are the UTXO model's (`RealChain`): a well-formed genesis set, each step spending live tokens, each step's
id new.
-/

set_option autoImplicit false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (outpointOf NoSecondPreimage)
open BoltProof.Bridge (params)

/-! ## What a step asserts of the transactions it names -/

/-- A transaction of the chain as a settle's rebuild names it: well-formed, nothing else serialises to its
hash, and the primitives' id of its abstraction is its real id. -/
structure ChainTx (P : Prims Bytes) (G : Tx) : Prop where
  wf : TxWF G
  nsp : NoSecondPreimage (serTx G)
  ptxid : P.txid (absTx G) = Sighash.txid G

/-- The balance fields of every token-shaped output are non-negative script numbers: what the covenant
writes (a sixteen-byte pad of a value below `2^127`), decidable on the bytes, and the one fact about an
ancestor the composition reads off its bytes rather than derives from the run. -/
def BalsNonneg (G : Tx) : Prop :=
  ∀ o ∈ G.outputs, ∀ g, decodeLock o.scriptPubKey = some g → 0 ≤ decode g.bal ∧ 0 ≤ decode g.balCommit

/-- A transfer or split settle with a grandparent, as `RealSettleGp` takes it, with the grandparent's reality
(`GpRealF`) left out: the chain supplies it. Of `ResidualGp` the rebuild's piece widths (§7 Q7) and the index
argument's width stay; of the ancestor `G` the step asserts that it is a transaction of the chain whose id the
token names, with non-negative balance fields. -/
structure ChainSettleGp (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (G : Tx) : Prop where
  hwf : WF f
  hA : ArgsWF a
  hty : SmbType f.ty
  hnty : SmbType a.nty
  hpre : castToBool a.pre = true
  hset : ¬ settledTy f.ty
  hnm : f.ty ≠ [0x25]
  hgp : decode f.gp ≠ 0
  hgen : decode f.parent = 0 → settledTy f.ty
  hogp : decode f.ogp = 0
  hcom2 : f.ty = [0x23] → f.com2 ≠ zeroPKH
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hres : Residual P tx i amt f a
  pieces : HonestPiecesB a.psB
  i5len : a.i5.length = 4
  hG : ChainTx P G
  hGtxid : Sighash.txid G = List.take 32 f.gp
  hGbals : BalsNonneg G
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
    (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid

/-- A merge settle, as `RealMergeSettle` takes it, with both grandparents' reality (`GpRealF`, `GpRealB`) left
out: the chain supplies it. Of the other grandparent `GB` the step asserts its id and the primitives'
agreement on it, the width of the index argument `i4`, and that `i4` names one of its proof outputs. -/
structure ChainMergeSettle (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (G GB : Tx) : Prop where
  hwf : WF f
  hA : ArgsWF a
  hty : SmbType f.ty
  hnty : SmbType a.nty
  hpre : castToBool a.pre = true
  hmrg : f.ty = [0x25]
  hgp : decode f.gp ≠ 0
  hgen : decode f.parent = 0 → settledTy f.ty
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hres : Residual P tx i amt f a
  pieces : HonestPiecesB a.psB
  i5len : a.i5.length = 4
  hG : ChainTx P G
  hGtxid : Sighash.txid G = List.take 32 f.gp
  hGbals : BalsNonneg G
  hogp : decode f.ogp ≠ 0
  hGBtxid : Sighash.txid GB = List.take 32 f.ogp
  hGBptxid : P.txid (absTx GB) = Sighash.txid GB
  i4len : a.i4.length = 4
  proofB : ∃ pkh, (absTx GB).outputs[leNat a.i4]? = some (.proof pkh)
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
    (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid

/-- One step of a real `SimpleMultiBOLT` chain, by the refinement stage that reads it: a commit, a settle
without a grandparent or a melt (`RealSpend`); a transfer or split settle with a grandparent
(`ChainSettleGp`); a merge commit with its second token input's run (`RealMergeCommit`); a merge settle
(`ChainMergeSettle`). -/
inductive ChainStep (P : Prims Bytes) : Spend Bytes → Prop
  | basic {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} {S : List Bytes} {scriptSig : Bytes}
      (h : RealSpend P tx i amt f a S scriptSig) : ChainStep P (spendOf tx i f a none none none)
  | settleGp {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} {S : List Bytes} {scriptSig : Bytes} {G : Tx}
      (h : ChainSettleGp P tx i amt f a S scriptSig G) : ChainStep P (spendOf tx i f a none (some G) none)
  | mergeCommit {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} {S : List Bytes} {scriptSig : Bytes}
      {i' amt' : Nat} {f' : Fields} {a' : Args} {S' : List Bytes} {scriptSig' : Bytes}
      (h : RealMergeCommit P tx i amt f a S scriptSig i' amt' f' a' S' scriptSig') :
      ChainStep P (spendOf tx i f a (some (f', ⟨(inputAt tx i').prevHash, (inputAt tx i').prevIndex⟩)) none none)
  | mergeSettle {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} {S : List Bytes} {scriptSig : Bytes} {G GB : Tx}
      (h : ChainMergeSettle P tx i amt f a S scriptSig G GB) :
      ChainStep P (spendOf tx i f a none (some G) (some GB))

/-- A real `SimpleMultiBOLT` chain: a run whose genesis set is well-formed, whose every step is a real spend
read by its stage (`ChainStep`), and whose ledger bookkeeping holds: each step spends tokens live at that
point and each step's transaction id is new. -/
structure RealChain (P : Prims Bytes) (r : Run Bytes) : Prop where
  genesis : r.GenesisOK .fungible
  steps : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s → ChainStep P s
  spent_live : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s → (s.spentOutpoint, s.spent) ∈ r.liveAfter P k
  other_live : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s →
    ∀ o, s.other = some o → (o.2, o.1) ∈ r.liveAfter P k
  fresh : ∀ (k : Nat) (s : Spend Bytes), r.steps[k]? = some s → ∀ x ∈ r.everAfter P k, x.1.txid ≠ P.txid s.tx

/-! ## The grandparents, read off the run -/

/-- The type of a transfer or split settle's token. -/
theorem commitTy_of_settleGp {f : Fields} (hty : SmbType f.ty) (hset : ¬ settledTy f.ty) (hnm : f.ty ≠ [0x25]) :
    f.ty = [0x21] ∨ f.ty = [0x23] := by
  rcases hty with h | h | h | h | h | h
  · exact absurd (by simp [settledTy, h] : settledTy f.ty) hset
  · exact Or.inl h
  · exact absurd (by simp [settledTy, h] : settledTy f.ty) hset
  · exact Or.inr h
  · exact absurd (by simp [settledTy, h] : settledTy f.ty) hset
  · exact absurd h hnm

/-- A commit-typed lock reads as a commit-typed token. -/
theorem spent_commitTyped {tx : Tx} {i : Nat} {f : Fields} {a : Args} {other : Option (Fields × Outpoint Bytes)}
    {ancA ancB : Option Tx} (h : f.ty = [0x21] ∨ f.ty = [0x23] ∨ f.ty = [0x25]) :
    (spendOf tx i f a other ancA ancB).spent.txoType ∈ Fam.commitTypes .fungible := by
  rcases h with h | h | h <;> simp [spendOf, tokenOf, h, Fam.commitTypes]

/-- A non-zero grandparent field reads as the grandparent outpoint. -/
theorem spent_grandparent {tx : Tx} {i : Nat} {f : Fields} {a : Args} {other : Option (Fields × Outpoint Bytes)}
    {ancA ancB : Option Tx} (hgp0 : decode f.gp ≠ 0) :
    (spendOf tx i f a other ancA ancB).spent.grandparent =
      some ⟨List.take 32 f.gp, leNat (List.drop 32 f.gp)⟩ := by
  simp [spendOf, tokenOf, outpointOf, hgp0]

/-- A non-zero other-grandparent field reads as the other grandparent outpoint. -/
theorem spent_otherGrandparent {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx} (hogp0 : decode f.ogp ≠ 0) :
    (spendOf tx i f a other ancA ancB).spent.otherGrandparent =
      some ⟨List.take 32 f.ogp, leNat (List.drop 32 f.ogp)⟩ := by
  simp [spendOf, tokenOf, outpointOf, hogp0]

variable {P : Prims Bytes} {r : Run Bytes}

/-- **The grandparent a settle names is real** (`GpRealF`), read off the valid prefix. The grandparent
outpoint is output 0 of an earlier commit step whose outputs are its token and the recipients' proof
outputs; A1 identifies the ancestor's abstraction with that step's transaction. -/
theorem gpRealF_of_chain (hc : CollisionFree P) {k : Nat} (hv : r.ValidUpTo P .fungible k) {tx : Tx} {i : Nat}
    {f : Fields} {a : Args} {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx}
    (hlive : ((spendOf tx i f a other ancA ancB).spentOutpoint, (spendOf tx i f a other ancA ancB).spent) ∈
      r.liveAfter P k)
    (hty : f.ty = [0x21] ∨ f.ty = [0x23] ∨ f.ty = [0x25]) (hgp0 : decode f.gp ≠ 0) {G : Tx} (hG : ChainTx P G)
    (hGtxid : Sighash.txid G = List.take 32 f.gp) (hGbals : BalsNonneg G) : GpRealF P f G := by
  obtain ⟨c, -, sc, -, hid, hvout, ⟨t, ht⟩, ⟨pkh, hpk⟩, h2⟩ :=
    Run.grandparent_layout_upto hv hlive (spent_commitTyped hty) (spent_grandparent hgp0)
  have hvout' : leNat (List.drop 32 f.gp) = 0 := hvout
  have hA : absTx G = sc.tx := hc _ _ (by rw [hG.ptxid, hGtxid]; exact hid.symm)
  refine ⟨hG.wf, hGtxid, hG.nsp, hG.ptxid, ⟨t, ?_⟩, ⟨pkh, ?_⟩, ?_, hGbals⟩
  · rw [hA, hvout']; exact ht
  · rw [hA]; exact hpk
  · intro t' ht' hty'
    rw [hA, hvout'] at ht'
    rw [hA]
    exact h2 t' ht' hty'

/-- **The other grandparent a merge settle names is real** (`GpRealB`), read off the valid prefix: its
outpoint is output 0 of an earlier commit step, the other lineage's, and A1 identifies the ancestor's
abstraction with that step's transaction. Which of its outputs the index argument names is the step's
own assertion (`proofB`). -/
theorem gpRealB_of_chain (hc : CollisionFree P) {k : Nat} (hv : r.ValidUpTo P .fungible k) {tx : Tx} {i : Nat}
    {f : Fields} {a : Args} {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx}
    (hlive : ((spendOf tx i f a other ancA ancB).spentOutpoint, (spendOf tx i f a other ancA ancB).spent) ∈
      r.liveAfter P k)
    (hmrg : f.ty = [0x25]) (hogp0 : decode f.ogp ≠ 0) {GB : Tx}
    (hGBtxid : Sighash.txid GB = List.take 32 f.ogp) (hGBptxid : P.txid (absTx GB) = Sighash.txid GB)
    (i4len : a.i4.length = 4) (proofB : ∃ pkh, (absTx GB).outputs[leNat a.i4]? = some (.proof pkh)) :
    GpRealB P f a GB := by
  obtain ⟨c, -, sc, -, hid, hvout, t, ht⟩ :=
    Run.other_grandparent_layout_upto hv hlive (spent_commitTyped (Or.inr (Or.inr hmrg)))
      (spent_otherGrandparent hogp0)
  have hvout' : leNat (List.drop 32 f.ogp) = 0 := hvout
  have hB : absTx GB = sc.tx := hc _ _ (by rw [hGBptxid, hGBtxid]; exact hid.symm)
  exact ⟨hGBtxid, hGBptxid, ⟨t, by rw [hB, hvout']; exact ht⟩, i4len, proofB⟩

/-! ## The chain is a valid run -/

/-- **A chain of real spends is a valid run.** Each step is accepted by the model through its refinement
stage, with the grandparents' reality read off the steps before it, and the ledger facts are the chain's.
A1 enters where the hand proof's Lemma 3 uses it: to identify a rebuilt ancestor with the step that created
the grandparent outpoint. -/
theorem valid_of_chain (hc : CollisionFree P) (h : RealChain P r) : r.Valid P .fungible := by
  refine Run.valid_of_stepwise h.genesis ?_
  intro k s hk hv
  have hlive := h.spent_live k s hk
  refine ⟨?_, hlive, h.other_live k s hk, h.fresh k s hk⟩
  cases h.steps k s hk with
  | basic hs => exact accepts_of_real hs
  | @settleGp tx i amt f a S scriptSig G hs =>
    exact @accepts_of_real_settle_gp P tx i amt f a S scriptSig G
      { hwf := hs.hwf, hA := hs.hA, hty := hs.hty, hnty := hs.hnty, hpre := hs.hpre, hset := hs.hset,
        hnm := hs.hnm, hgp := hs.hgp, hgen := hs.hgen, hogp := hs.hogp, hcom2 := hs.hcom2, htx := hs.htx,
        hamt := hs.hamt, hi := hs.hi, hnz := hs.hnz, hres := hs.hres,
        hgr := ⟨gpRealF_of_chain hc hv hlive ((commitTy_of_settleGp hs.hty hs.hset hs.hnm).imp_right Or.inl)
          hs.hgp hs.hG hs.hGtxid hs.hGbals, hs.pieces, hs.i5len⟩,
        hstack := hs.hstack, hvalid := hs.hvalid }
  | mergeCommit hs => exact accepts_of_real_merge_commit hs
  | @mergeSettle tx i amt f a S scriptSig G GB hs =>
    exact @accepts_of_real_merge_settle P tx i amt f a S scriptSig G GB
      { hwf := hs.hwf, hA := hs.hA, hty := hs.hty, hnty := hs.hnty, hpre := hs.hpre, hmrg := hs.hmrg,
        hgp := hs.hgp, hgen := hs.hgen, htx := hs.htx, hamt := hs.hamt, hi := hs.hi, hnz := hs.hnz,
        hres := hs.hres,
        hgr := ⟨gpRealF_of_chain hc hv hlive (Or.inr (Or.inr hs.hmrg)) hs.hgp hs.hG hs.hGtxid hs.hGbals,
          hs.pieces, hs.i5len⟩,
        hgb := gpRealB_of_chain hc hv hlive hs.hmrg hs.hogp hs.hGBtxid hs.hGBptxid hs.i4len hs.proofB,
        hstack := hs.hstack, hvalid := hs.hvalid }

/-! ## What holds of real tokens

Each theorem is Layer 1's run-level statement applied to the run a real chain is, so it speaks of
`SimpleMultiBOLT` tokens the consensus rules have accepted. -/

/-- **Theorem 1 of the shipped bytes, over a history.** Every live token of a real chain has a lineage whose
root is a parentless genesis token of the run, carries the run's issuer along that lineage, and is joined
to its root by real links: each token's parent is an outpoint the run created for the previous one, the
grandparent pointers agree, and the types follow the fungible machine. -/
theorem chain_authenticity (hc : CollisionFree P) (h : RealChain P r) :
    ∀ x ∈ r.live P,
      ((r.root P x.2).parent = none ∧ ∃ o, (o, r.root P x.2) ∈ r.genesis) ∧
      (∀ u ∈ r.lineage P x.2, u.issuer = r.issuer) ∧
      (∀ i a b, (r.lineage P x.2)[i]? = some a → (r.lineage P x.2)[i + 1]? = some b →
        (∃ o, a.parent = some o ∧ r.tokenAt P o = some b) ∧ a.grandparent = b.parent ∧
          Fam.edge .fungible b.txoType a.txoType) :=
  Run.t1_authenticity (valid_of_chain hc h)

/-- **Theorem 1, the invariant.** Every live token of a real chain carries the run's issuer. -/
theorem chain_issuer_invariant (hc : CollisionFree P) (h : RealChain P r) :
    ∀ x ∈ r.live P, x.2.issuer = r.issuer :=
  Run.t1_issuer_invariant (valid_of_chain hc h)

/-- **Theorem 3 of the shipped bytes, over a history.** The value the live tokens hold plus the value melted
is the value minted, at every step. -/
theorem chain_conservation (hc : CollisionFree P) (h : RealChain P r) (k : Nat) :
    r.float P k + r.melted P k = r.genesisValue :=
  Run.t3_conservation (valid_of_chain hc h) k

/-- **Theorem 4 of the shipped bytes, over a history.** Every token a real chain ever created carries one of
the fungible machine's six type bytes. -/
theorem chain_defined_types (hc : CollisionFree P) (h : RealChain P r) (k : Nat) :
    ∀ x ∈ r.everAfter P k, x.2.txoType ∈ Fam.settleTypes .fungible ++ Fam.commitTypes .fungible :=
  t4_defined_types (valid_of_chain hc h) k

/-- **Theorem 5 of the shipped bytes (proof gating).** Under the UTXO rule, two distinct settles of a real
chain consume two distinct proof outpoints: a commit's proof output admits at most one settle. -/
theorem chain_proof_gating (hc : CollisionFree P) (h : RealChain P r) (hnd : r.NoDoubleSpend) {i j : Nat}
    {si sj : Spend Bytes} (hi : r.steps[i]? = some si) (hj : r.steps[j]? = some sj) (hne : i ≠ j)
    (hsi : si.kind = .settle) (hsj : sj.kind = .settle) {gpi gpj : Outpoint Bytes}
    (hgi : si.spent.grandparent = some gpi) (hgj : sj.spent.grandparent = some gpj) :
    ∃ pi pj : Outpoint Bytes,
      pi.txid = gpi.txid ∧ pi ∈ si.tx.inputs ∧ pj.txid = gpj.txid ∧ pj ∈ sj.tx.inputs ∧ pi ≠ pj :=
  Run.t5_proof_gating (valid_of_chain hc h) hnd hi hj hne hsi hsj hgi hgj

/-- **Theorem 5 of the shipped bytes, combined.** In a real chain under the UTXO rule, every settle with a
grandparent consumes a proof outpoint of the grandparent's transaction that no other step consumes, and
carries exactly the settle result the grandparent's own transition assigned to that proof. -/
theorem chain_fabricated_hop_excluded (hc : CollisionFree P) (h : RealChain P r) (hnd : r.NoDoubleSpend)
    {k c : Nat} {s sc : Spend Bytes} (hk : r.steps[k]? = some s) (hs : s.kind = .settle)
    {gp : Outpoint Bytes} (hgp : s.spent.grandparent = some gp) (hcs : r.steps[c]? = some sc)
    (hprod : P.txid sc.tx = gp.txid) :
    ∃ (t : Token Bytes) (j : Nat) (pkh : PKH), sc.tx.outputs[gp.vout]? = some (.token t) ∧
      sc.tx.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Bytes) ∈ s.tx.inputs ∧
      (∀ k' s', r.steps[k']? = some s' → k' ≠ k → (⟨gp.txid, j⟩ : Outpoint Bytes) ∉ s'.tx.inputs) ∧
      (Fam.fungible = .fungible → s.spent.balance = t.settledBalance .fungible (j - 1)) :=
  Run.t5_fabricated_hop_excluded hc (valid_of_chain hc h) hnd hk hs hgp hcs hprod

end BoltProof.Glue.SimpleMulti
