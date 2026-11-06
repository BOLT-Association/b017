import BoltProof.Bridge.Glue.SimpleMulti.GpWeld
import BoltProof.Bridge.Glue.SimpleMulti.Residual
import BoltProof.Bridge.Glue.Refine.Weld

/-!
# `Accepts.l3_rebuild` for the transfer and split settles

A settle of a token with a grandparent rebuilds the grandparent, hashes it against the grandparent's txid,
anchors the spent balance to the grandparent token's, and names the co-spent proof output in `hashPrevouts`.
Under the fungible `GpRealF` (the grandparent is a real, well-formed transaction whose serialisation has no
second preimage, whose token output the token names, with a proof output after the parent's index and
non-negative balances), the honest piece widths and the index assumption on `i5`, those facts are the model's
`l3_rebuild` (`l3_settle`), for each of the rebuild's optional arms (a merge-commit grandparent's second token
input, a split-commit grandparent's second proof output).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (sc scLen preOutpoint preHashPrevouts outpointOf NoSecondPreimage)

/-- The grandparent is real (fungible): a well-formed transaction whose txid the token names and whose
serialisation has no second preimage, with the primitives' id; its output at the named index is a token, it has a
proof output just after the parent's index, and its tokens' balances are non-negative script numbers. What the
accepted commit two steps back guarantees; the run-level argument discharges it. -/
structure GpRealF (P : Prims Bytes) (f : Fields) (G : Tx) : Prop where
  wf : TxWF G
  txid : Sighash.txid G = List.take 32 f.gp
  nsp : NoSecondPreimage (serTx G)
  ptxid : P.txid (absTx G) = Sighash.txid G
  token : ∃ t, (absTx G).outputs[leNat (List.drop 32 f.gp)]? = some (.token t)
  proof : ∀ p, outpointOf f.parent = some p → ∃ pkh, (absTx G).outputs[p.vout + 1]? = some (.proof pkh)
  bal : ∀ o ∈ G.outputs, ∀ g, decodeLock o.scriptPubKey = some g → 0 ≤ decode g.bal ∧ 0 ≤ decode g.balCommit

/-- A 32-bit word that reads as a positive script number reads as its value. -/
theorem decode_le32_of_pos {n : Nat} (hn : n < 2 ^ 32) (h : 0 < decode (le32 n)) : decode (le32 n) = n := by
  simp only [le32, decode, decodeRev, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    beNat, List.foldl] at h ⊢
  split_ifs at h ⊢ with hs
  · omega
  · simp only [decide_eq_true_eq] at hs
    omega

theorem gpOutA_eq (t0 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes) :
    gpOutA t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 =
      Hash.hash256 (rebuiltA t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) ++ item T 61 := rfl

theorem rebuildA_fact0_eq (t0 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes) :
    rebuildA_fact0 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 =
      AnchorOK (if item T 145 = [37] then [1] else []) (item T 145) (encode (decode (item T 150)))
        (encode (decode (item T 151))) (encode (decode (item T 46))) (item T 61) := rfl

/-- **`l3_rebuild`, a transfer or split settle.** -/
theorem l3_settle {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args} {S : List Bytes} {G : Tx}
    {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes}
    (other : Option (Fields × Outpoint Bytes)) (ancB : Option Tx)
    (hwf : WF f) (hsc : sc a.pre = lockScript f) (hop : 104 ≤ a.pre.length)
    (hval : (List.take 8 (List.drop (107 + (decode (List.take 2 (List.drop 105 a.pre))).toNat) a.pre)).length = 8)
    (hnty : a.nty = [0x20] ∨ a.nty = [0x22])
    (hlen : a.nty = [0x22] → (padN 16 (encode (decode f.bal - decode f.balCommit))).length = 16)
    (hp : HonestPiecesB a.psB)
    (h0 : rebuildA_fact0 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h1 : rebuildA_fact1 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h2 : rebuildA_fact2 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h3 : rebuildA_fact3 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h5 : rebuildA_fact5 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h6 : rebuildA_fact6 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h7 : rebuildA_fact7 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h8 : rebuildA_fact8 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h9 : rebuildA_fact9 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h11 : rebuildA_fact11 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h12 : rebuildA_fact12 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (hprevs : Hash.hash256 (preOutpoint a.pre ++
      gpOutA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 ++ a.fund) =
        preHashPrevouts a.pre)
    (hprev : preHashPrevouts a.pre = hashPrevouts tx) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (htx : TxWF tx) (h32 : (inputAt tx i).prevHash.length = 32)
    (hnspP : NoSecondPreimage ((tx.inputs.map serOutPoint).flatten))
    (hG : GpRealF P f G) (hi5len : a.i5.length = 4)
    (hi5 : ∀ p, outpointOf f.parent = some p → decode a.i5 = (p.vout : Int) + 1)
    (hbal : 0 ≤ decode f.bal) (hpar : decode f.parent ≠ 0) :
    ∀ gp, outpointOf f.gp = some gp →
      ∃ (A : TxDesc Bytes) (t : Token Bytes), (spendOf tx i f a other (some G) ancB).anc = some A ∧
        P.txid A = gp.txid ∧ A.outputs[gp.vout]? = some (.token t) ∧
        (∃ j pkh, A.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Bytes) ∈ (absTx tx).inputs) ∧
        ∀ p, outpointOf f.parent = some p → balOf f.bal = t.settledBalance .fungible p.vout := by
  intro gp hgp
  have hgp0 : decode f.gp ≠ 0 := by intro h; simp [outpointOf, h] at hgp
  have hgpeq : gp = ⟨List.take 32 f.gp, leNat (List.drop 32 f.gp)⟩ := by
    simp [outpointOf, hgp0] at hgp; exact hgp.symm
  subst hgpeq
  -- the grandparent is the parsed transaction
  have hw := widthsA_gate hwf hsc hop hval hnty hlen hp h2 h3 h5 h6 h7 h8 h9 h11 h12
  have hGeq := gp_eq_gpTxA h1 hw hG.wf hG.nsp hG.txid
  have h15 : item (gateT f a S) 15 = 33 :: f.issuer := by rw [gateT_item15]; exact scPush_issuer hwf hsc
  have h14 : item (gateT f a S) 14 = SimpleMulti.suffix := by rw [gateT_item14]; exact scSuffix_of_sc hwf hsc
  have hl := lockWidthsA_gate (f := f) S hp
  obtain ⟨t, ht⟩ := hG.token
  have ht' := ht
  rw [hGeq] at ht'
  obtain ⟨hv0, htt⟩ := gpTxA_token hw hl hwf.issuer h15 h14 _ t ht'
  -- the anchor: the grandparent token's balances are non-negative
  have hlk : (gpTxA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46).outputs[0]? =
      some (outOfBytes (item (gateT f a S) 30) (lkA (gateT f a S))) := rfl
  have hmem0 : outOfBytes (item (gateT f a S) 30) (lkA (gateT f a S)) ∈ G.outputs := by
    rw [hGeq]; exact List.mem_of_getElem? hlk
  have hdec : decodeLock (outOfBytes (item (gateT f a S) 30) (lkA (gateT f a S))).scriptPubKey =
      some (gpFieldsA (gateT f a S) f.issuer) := by
    simp only [outOfBytes, lkA_eq hl h15 h14, decodeLock_lockScript (gpFieldsA_wf hl hwf.issuer)]
  obtain ⟨hn2, hn3⟩ := hG.bal _ hmem0 _ hdec
  -- the co-spent proof output: the second outpoint `hashPrevouts` names
  have hflat : serOutPoint (inputAt tx i) ++
      ((Hash.hash256 (rebuiltA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) ++ a.i5) ++
        a.fund) = (tx.inputs.map serOutPoint).flatten := by
    rw [← hout]
    have := hnspP (preOutpoint a.pre ++ (Hash.hash256 (rebuiltA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14
      w17 w18 w19 w20 w23 w46) ++ a.i5) ++ a.fund) (by
        rw [← gateT_item61 f a S, ← gpOutA_eq, hprevs, hprev]; rfl)
    simpa only [List.append_assoc] using this
  obtain ⟨i0, is1, his1, -, hf1⟩ := flatten_serOutPoint_cons
    (fun j hj => (htx.inputs j hj).1) (by rw [serOutPoint_length, h32]) hflat.symm
  obtain ⟨i1, is2, his2, hi1, -⟩ := flatten_serOutPoint_cons
    (fun j hj => (htx.inputs j (by rw [his1]; exact List.mem_cons_of_mem _ hj)).1)
    (by rw [List.length_append, BoltProof.Glue.MinSimple.hash256_length, hi5len]) hf1
  have hi1mem : i1 ∈ tx.inputs := by rw [his1, his2]; simp
  have h32' : i1.prevHash.length = 32 := (htx.inputs i1 hi1mem).1
  have hidx1 : i1.prevIndex < 2 ^ 32 := (htx.inputs i1 hi1mem).2.1
  have hsplit := List.append_inj (by simpa [serOutPoint] using hi1 : i1.prevHash ++ le32 i1.prevIndex =
    Hash.hash256 (rebuiltA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) ++ a.i5)
    (by rw [h32', BoltProof.Glue.MinSimple.hash256_length])
  rw [rebuildA_fact1_eq, gateT_item36] at h1
  have hprev1 : i1.prevHash = List.take 32 f.gp := by rw [hsplit.1, h1]
  refine ⟨absTx G, t, by simp [spendOf], by rw [hG.ptxid, hG.txid], ht, ?_, ?_⟩
  · -- the proof output after the parent's index is the one co-spent
    have hpp : outpointOf f.parent = some ⟨List.take 32 f.parent, leNat (List.drop 32 f.parent)⟩ := by
      simp [outpointOf, hpar]
    obtain ⟨pkh, hproof⟩ := hG.proof _ hpp
    have hx := hi5 _ hpp
    have hle : decode (le32 i1.prevIndex) = i1.prevIndex :=
      decode_le32_of_pos hidx1 (by rw [hsplit.2, hx]; omega)
    have hidx' : i1.prevIndex = leNat (List.drop 32 f.parent) + 1 := by
      rw [hsplit.2, hx] at hle; dsimp only at hle; omega
    refine ⟨_, pkh, hproof, ?_⟩
    simp only [absTx, List.mem_map]
    exact ⟨i1, hi1mem, by rw [hprev1, hidx']⟩
  · intro p hpp
    have hx := hi5 p hpp
    rw [rebuildA_fact0_eq, gateT_item61, gateT_item145, gateT_item150, gateT_item151, gateT_item46] at h0
    rw [htt]
    exact anchorOK_settled (g := gpFieldsA (gateT f a S) f.issuer) (ty := a.psB.p8) (n3 := a.psB.p13)
      (n2 := a.psB.p14) (by simp [gpFieldsA, gateT_item145]) (by rw [← gateT_item145 f a S]; exact hl.ty)
      (by simp [gpFieldsA, gateT_item151]) (by simp [gpFieldsA, gateT_item150]) h0 hx
      (by rw [← gateT_item151 f a S]; exact hn2) (by rw [← gateT_item150 f a S]; exact hn3) hbal

end BoltProof.Glue.SimpleMulti
