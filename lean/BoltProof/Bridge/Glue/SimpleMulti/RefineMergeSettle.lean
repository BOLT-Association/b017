import BoltProof.Bridge.Glue.SimpleMulti.RefineMerge
import BoltProof.Bridge.Glue.SimpleMulti.RebuiltB

/-!
# `SimpleMultiBOLT`: the bytes refine `Accepts` (third stage, the merge settle)

A merge settle spends the merged commit token (`0x25`) into a settled token (`0x24`) carrying the sum. With a
grandparent both rebuilds run: the first lineage's as for the other settles (`l3_settle`, the anchor of the
spent balance), and the second's, which hashes the other lineage's grandparent against the token's
`otherGrandparent` and names its co-spent outpoint in `hashPrevouts`, the other lineage's before this one's when
the spent lock's index is not zero. The model's `l3_merge` asks of the second lineage only the ancestor's id, its
token output and a co-spent proof output, so beyond `ResidualGp` for the first lineage the theorem assumes
`GpRealB` for the second (a real transaction with the primitives' id, whose txid the token names, with a token at
the named index, a proof output at index 1 and, when the piece the settle supplies as its token's type is the
split commit type, at index 2). Which of those the fourth interop slot `i4` names is not assumed: the second
rebuild's anchor pins it to 1, or to 2 under the split type, as the first rebuild's anchor pins `i5`
(`anchorB_index`, `lean/GLUE-PLAN.md` §7 Q9). Every merged token a covenant builds has a grandparent (a merge
commit is refused at genesis), so the merge settle without one is not a case.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (sc preOutpoint preValue preVersion preHashOutputs preHashPrevouts outpointOf
  getLast_eq_of_drop cleanupScriptCode_forkid two_le_of_decode_serVersion)
open BoltProof.Bridge (params)
open BoltProof.Bridge.Generated

/-- The eighth piece of the first set, as the gate stack holds it: the type the settle supplies for the other
grandparent's token, which the second rebuild hashes and anchors on. -/
theorem gateT_item70 (f : Fields) (a : Args) (S : List Bytes) : item (gateT f a S) 70 = a.psA.p8 := by
  unfold gateT; split_ifs <;> rfl

/-- The second rebuild's anchor, first case on the spent lock's index: `AnchorOK` on the other grandparent's
token type and balances (the first piece set's items 70, 75 and 76), the spent token's carried balance (item 45)
and the index argument `i4` (item 60), as `rebuildA_fact0_eq` reads the first rebuild's. -/
theorem rebuildB_1_fact0_eq (t1 t0 a1 a2 : Bytes) (T : List Bytes)
    (w10c1 w11c1 w12c1 w13c1 w14c1 w17c1 w18c1 w19c1 w20c1 w23c1 : Bytes) :
    rebuildB_1_fact0 t1 t0 a1 a2 T w10c1 w11c1 w12c1 w13c1 w14c1 w17c1 w18c1 w19c1 w20c1 w23c1 =
      AnchorOK (if item T 70 = [37] then [1] else []) (item T 70) (encode (decode (item T 75)))
        (encode (decode (item T 76))) (encode (decode (item T 45))) (item T 60) := rfl

/-- The second rebuild's anchor, second case. -/
theorem rebuildB_2_fact0_eq (t1 t0 a1 a2 : Bytes) (T : List Bytes)
    (w10c2 w11c2 w12c2 w13c2 w14c2 w17c2 w18c2 w19c2 w20c2 w23c2 : Bytes) :
    rebuildB_2_fact0 t1 t0 a1 a2 T w10c2 w11c2 w12c2 w13c2 w14c2 w17c2 w18c2 w19c2 w20c2 w23c2 =
      AnchorOK (if item T 70 = [37] then [1] else []) (item T 70) (encode (decode (item T 75)))
        (encode (decode (item T 76))) (encode (decode (item T 45))) (item T 60) := rfl

/-- **The second rebuild pins `i4`** (`lean/GLUE-PLAN.md` §7 Q9). In either case on the spent lock's index, the
anchor of the carried balance fixes the other lineage's index argument: it reads as 1, or as 2 when the piece the
settle supplies as the other grandparent's type is the split commit type. The analogue of `AnchorOK.index` for
`i5`; the vectors `smb_probe_q9_*` show the refusal on the bytes. -/
theorem anchorB_index {f : Fields} {a : Args} {S : List Bytes} {t1 t0 a1 a2 : Bytes}
    {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 : Bytes}
    (h : rebuildB_1_fact0 t1 t0 a1 a2 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 ∨
      rebuildB_2_fact0 t1 t0 a1 a2 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23) :
    decode a.i4 = 1 ∨ (a.psA.p8 = [0x23] ∧ decode a.i4 = 2) := by
  rcases h with h | h
  · rw [rebuildB_1_fact0_eq, gateT_item60, gateT_item70] at h; exact AnchorOK.index h
  · rw [rebuildB_2_fact0_eq, gateT_item60, gateT_item70] at h; exact AnchorOK.index h

/-- The other lineage's grandparent is real: a transaction whose txid the token's `otherGrandparent` names, with
the primitives' id, a token at the named index, a proof output at index 1 and, when the piece the settle supplies
as its token's type is the split commit type, at index 2; the fourth interop slot is a 32-bit word. Which output
that slot names is read off the bytes (`anchorB_index`), not assumed. -/
structure GpRealB (P : Prims Bytes) (f : Fields) (a : Args) (G : Tx) : Prop where
  txid : Sighash.txid G = List.take 32 f.ogp
  ptxid : P.txid (absTx G) = Sighash.txid G
  token : ∃ t, (absTx G).outputs[leNat (List.drop 32 f.ogp)]? = some (.token t)
  i4len : a.i4.length = 4
  proof1 : ∃ pkh, (absTx G).outputs[1]? = some (.proof pkh)
  proof2 : a.psA.p8 = [0x23] → ∃ pkh, (absTx G).outputs[2]? = some (.proof pkh)

/-- A merge settle's outputs, read by the model: the settled token carrying the sum, then non-token change. -/
theorem outs_settle_merge {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (other : Option (Fields × Outpoint Bytes))
    (ancA ancB : Option Tx) (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx) (hamt : amt < 2 ^ 64)
    (hpre : castToBool a.pre = true) (hty : f.ty = [0x25]) (hnty : a.nty = [0x24])
    (hb : 0 ≤ decode f.bal) (hbc : 0 ≤ decode f.balCommit) (hsum : decode f.bal + decode f.balCommit ≤ maxBalance)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : MinSimple.sc a.pre = lockScript f)
    (hflat : settleOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 1) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a other ancA ancB).expectedOuts .fungible ++ change := by
  have hlen : (padN 16 (encode (decode f.bal + decode f.balCommit))).length = 16 :=
    padN16_length_of_range (by omega) hsum
  have hswf := mergeFieldsS_wf hwf ha hlen
  have h20 : a.nty ≠ [0x20] := by rw [hnty]; decide
  have h22 : a.nty ≠ [0x22] := by rw [hnty]; decide
  rw [settleOuts, ite_eq_right h20, ite_eq_right h22, settleOuts_24_eq hwf hsc, tokenOut_eq hswf hval] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hswf hamt) hflat.symm
  refine ⟨os1.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1]; simpa using ho')
  · have hset : ¬ settledTy f.ty := by simp [settledTy, hty]
    have hk : (spendOf tx i f a other ancA ancB).kind = .settle := kindOf_settle hpre hset
    simp only [absTx, hos1, List.map_cons, Spend.expectedOuts, hk, outOf_lock hswf,
      tokenOf_settle_merge tx i other ancA ancB hty hb hbc hout hnz h32 hidx]
    simp [spendOf, tokenOf, hty, Fam.modeOfCommitType]

/-- **`SimpleMultiBOLT` refines `Accepts`, third stage**: a merge settle of a token with a grandparent. -/
theorem simpleMulti_refines_merge_settle (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args)
    (S : List Bytes) (scriptSig : Bytes) (G GB : Tx) (hwf : WF f) (hA : ArgsWF a)
    (hty : SmbType f.ty) (hnty : SmbType a.nty) (hpre : castToBool a.pre = true)
    (hmrg : f.ty = [0x25]) (hgp : decode f.gp ≠ 0)
    (hgen : decode f.parent = 0 → settledTy f.ty)
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hres : Residual P tx i amt f a) (hgr : ResidualGp P f a G) (hgb : GpRealB P f a GB)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid) :
    Accepts P .fungible (spendOf tx i f a none (some G) (some GB)) := by
  obtain ⟨hse, hsig0, hpreimg, htypes⟩ := refine_run P tx i amt f a S scriptSig hwf hty (fun _ => hnty) htx hi hres hS1 hv
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  have hpe := hpreimg hpre
  obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
    preimage_fields (lockScript f) (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  rw [← hpe] at hsc hver' hprev hout hval hhout
  obtain ⟨-, hpar2⟩ := htypes hpre
  have hhon := hres.honest hpre
  have hset : ¬ settledTy f.ty := by simp [settledTy, hmrg]
  have hset' : ¬ (f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) := hset
  have h24 : a.nty = [0x24] := by
    have hrel := hpar2 hset'
    rcases hnty with g | g | g | g | g | g <;> simp_all
  have henf : EnforcedSettle (phase2Env (txContext tx i amt)) f a S (lockScript f) := by
    have h := hse; simp only [SpendEnforced, hpre, ↓reduceIte] at h
    rw [ite_eq_right hset', ite_eq_right hgp] at h; exact h
  have hlast := getLast_eq_of_drop henf.sigType
  have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
    rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockScript f) a.sig hlast]; exact hsig0
  have hk : kindOf f a = .settle := kindOf_settle hpre hset
  have hflat : settleOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
    hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
  have hver : 2 ≤ tx.version := two_le_of_decode_serVersion _ htx.version (by rw [← hver']; exact henf.version)
  have hmode : modeOf f a = .merge := by
    have hkc : kindOf f a ≠ .commit := by rw [hk]; decide
    simp [modeOf, hkc, hmrg, Fam.modeOfCommitType]
  have hpar : decode f.parent ≠ 0 := fun h => hset (hgen h)
  have hop : 104 ≤ a.pre.length := by
    have := congrArg List.length hout
    simp only [preOutpoint, List.length_take, List.length_drop, serOutPoint_length, h32] at this
    omega
  have hval8 : (List.take 8 (List.drop (107 + (decode (List.take 2 (List.drop 105 a.pre))).toNat) a.pre)).length = 8 := by
    show (preValue a.pre).length = 8
    rw [hval]; exact le64_length _
  have hbc := henf.balCommitLo (by rw [h24]; decide)
  have hsum := henf.mergeSum h24
  have hlen24 : a.nty = [0x24] → (padN 16 (encode (decode f.bal + decode f.balCommit))).length = 16 := fun _ =>
    padN16_length_of_range (by have := henf.balLo; omega) hsum
  obtain ⟨w10, w11, w12, w13, w14, w17, w18, w19, w20, w23, w46, w10c1, w11c1, w12c1, w13c1, w14c1, w17c1, w18c1,
    w19c1, w20c1, w23c1, w10c2, w11c2, w12c2, w13c2, w14c2, w17c2, w18c2, w19c2, w20c2, w23c2,
    ⟨h0, h1, h2, h3, -, h5, h6, h7, h8, h9, -, h11, h12⟩, hB1, hB2, hprevs⟩ := henf.rebuild
  have hflag : castToBool (item (gateT f a S) 2) = true := by rw [gateT_item2_24 f a S h24]; decide
  simp only [hflag, ↓reduceIte] at hprevs
  -- the co-spent outpoints, in either order
  have hlenA : (gpOutA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46).length = 36 := by
    rw [gpOutA_eq, List.length_append, BoltProof.Glue.MinSimple.hash256_length, gateT_item61, hgr.i5len]
  have hnspP := hres.prevouts
  have hflatP : ∀ y, Hash.hash256 (preOutpoint a.pre ++ y ++ a.fund) = preHashPrevouts a.pre →
      serOutPoint (inputAt tx i) ++ (y ++ a.fund) = (tx.inputs.map serOutPoint).flatten := by
    intro y hy
    rw [← hout]
    have := hnspP (preOutpoint a.pre ++ y ++ a.fund) (by rw [hy, hprev]; rfl)
    simpa only [List.append_assoc] using this
  have hcoA_of : ∀ i1 : TxIn, serOutPoint i1 = (gpOutA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) →
      serOutPoint i1 = Hash.hash256 (rebuiltA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) ++ a.i5 := by
    intro i1 h; rw [h, gpOutA_eq, gateT_item61]
  have hcoB_of : ∀ (iB : TxIn) (XB : Bytes), iB ∈ tx.inputs → Hash.hash256 XB = List.take 32 f.ogp →
      serOutPoint iB = Hash.hash256 XB ++ a.i4 → iB.prevHash = List.take 32 f.ogp ∧ le32 iB.prevIndex = a.i4 := by
    intro iB XB hiB hXB h
    have h32B : iB.prevHash.length = 32 := (htx.inputs iB hiB).1
    have hsp := List.append_inj (by simpa [serOutPoint] using h : iB.prevHash ++ le32 iB.prevIndex =
      Hash.hash256 XB ++ a.i4) (by rw [h32B, BoltProof.Glue.MinSimple.hash256_length])
    exact ⟨hsp.1.trans hXB, hsp.2⟩
  obtain ⟨hcoA, hcoB, hpin⟩ : (∃ i1 ∈ tx.inputs, serOutPoint i1 =
      Hash.hash256 (rebuiltA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) ++ a.i5) ∧
      (∃ iB ∈ tx.inputs, iB.prevHash = List.take 32 f.ogp ∧ le32 iB.prevIndex = a.i4) ∧
      (decode a.i4 = 1 ∨ (a.psA.p8 = [0x23] ∧ decode a.i4 = 2)) := by
    by_cases h39 : decode (item (gateT f a S) 39) = 0
    · rw [ite_eq_left h39] at hprevs
      have hb1 := (hB1 hflag h39).2.1
      rw [rebuildB_1_fact1_eq, gateT_item41] at hb1
      have hlenB : (gpOutB_1 (gpOutA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (preOutpoint a.pre) (altA1 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (altA2 w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (gateT f a S) w10c1 w11c1 w12c1 w13c1 w14c1 w17c1 w18c1 w19c1 w20c1 w23c1).length = 36 := by
        rw [gpOutB_1_eq, List.length_append, BoltProof.Glue.MinSimple.hash256_length, gateT_item60, hgb.i4len]
      obtain ⟨⟨i1, hi1, hs1⟩, ⟨iB, hiB, hsB⟩⟩ := coSpent_third htx h32 hlenA hlenB
        (by have := hflatP _ hprevs; simpa only [List.append_assoc] using this)
      refine ⟨⟨i1, hi1, hcoA_of i1 hs1⟩, ⟨iB, hiB, hcoB_of iB _ hiB hb1 ?_⟩, anchorB_index (Or.inl (hB1 hflag h39).1)⟩
      rw [hsB, gpOutB_1_eq, gateT_item60]
    · rw [ite_eq_right h39] at hprevs
      have hb2 := (hB2 hflag h39).2.1
      rw [rebuildB_2_fact1_eq, gateT_item41] at hb2
      have hlenB : (gpOutB_2 (gpOutA (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (preOutpoint a.pre) (altA1 (preOutpoint a.pre) (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (altA2 w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (gateT f a S) w10c2 w11c2 w12c2 w13c2 w14c2 w17c2 w18c2 w19c2 w20c2 w23c2).length = 36 := by
        rw [gpOutB_2_eq, List.length_append, BoltProof.Glue.MinSimple.hash256_length, gateT_item60, hgb.i4len]
      obtain ⟨⟨iB, hiB, hsB⟩, ⟨i1, hi1, hs1⟩⟩ := coSpent_third htx h32 hlenB hlenA
        (by have := hflatP _ hprevs; simpa only [List.append_assoc] using this)
      refine ⟨⟨i1, hi1, hcoA_of i1 hs1⟩, ⟨iB, hiB, hcoB_of iB _ hiB hb2 ?_⟩, anchorB_index (Or.inr (hB2 hflag h39).1)⟩
      rw [hsB, gpOutB_2_eq, gateT_item60]
  have hreb := l3_settle (P := P) (tx := tx) (i := i) (G := G) none (some GB) hwf hsc hop hval8 (Or.inr (Or.inr h24))
    (fun h => absurd h (by rw [h24]; decide)) hlen24 hgr.pieces
    h0 h1 h2 h3 h5 h6 h7 h8 h9 h11 h12 hcoA htx hgr.gp henf.balLo hpar
  have hhon1 : HonestOutputs tx 1 := by
    have hcount : expectedCount f a = 1 := by
      rw [expectedCount, ite_eq_right hset, ite_eq_right (by rw [hmrg]; decide)]
    rw [hcount] at hhon; exact hhon
  refine accepts_of_facts P tx i f a none (some G) (some GB) hty (fun _ => hnty) (fun _ h => absurd h hset) hgen hi hver
    (by rw [hres.agrees.h160]; exact henf.owner) hsig (by simp [hlast]) henf.issuer ?_
    (fun h => absurd h (by rw [hk]; decide)) (balOf_le henf.balHi) (fun h => by rw [hk] at h; cases h)
    (fun h => by rw [hk] at h; cases h) (fun _ hm => by rw [hmode] at hm; cases hm) ?_ ?_ (fun _ h => by cases h)
    (fun _ h => by cases h) (fun _ h => by cases h) (fun _ gp h => hreb gp h) ?_
    (fun h => absurd h (by
      rintro (h | h)
      · rw [hk] at h; cases h
      · simp [outpointOf, hgp] at h))
  · intro _
    exact Spend.outsOK_of_canonical (outs_settle_merge none (some G) (some GB) hwf hA htx hamt hpre hmrg h24
      henf.balLo hbc hsum h32 hidx hnz hval hout hsc hflat hhon1)
  · intro _ _
    have hm := maxBalance_eq
    have hb0 := henf.balLo
    unfold balOf Fam.maxBalance
    omega
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro h; rw [hk] at h; cases h
  · intro _ ogp hogp
    have hogp0 : decode f.ogp ≠ 0 := by intro h; simp [outpointOf, h] at hogp
    have hogpeq : ogp = ⟨List.take 32 f.ogp, leNat (List.drop 32 f.ogp)⟩ := by
      simp [outpointOf, hogp0] at hogp; exact hogp.symm
    subst hogpeq
    obtain ⟨t, ht⟩ := hgb.token
    obtain ⟨iB, hiB, htB, hlB⟩ := hcoB
    have hidxB : iB.prevIndex < 2 ^ 32 := (htx.inputs iB hiB).2.1
    have h32B : iB.prevHash.length = 32 := (htx.inputs iB hiB).1
    -- the pin: `i4` is the co-spent index, 1 or (under the split type) 2, and names a proof output
    have hpos : 0 < decode a.i4 := by rcases hpin with h | ⟨-, h⟩ <;> omega
    have hdec : decode a.i4 = (iB.prevIndex : Int) := by
      rw [← hlB]; exact decode_le32_of_pos hidxB (by rw [hlB]; exact hpos)
    have hle : leNat a.i4 = iB.prevIndex := by rw [← hlB]; exact leNat_le32 _ hidxB
    obtain ⟨pkh, hpr⟩ : ∃ pkh, (absTx GB).outputs[leNat a.i4]? = some (.proof pkh) := by
      rcases hpin with h1 | ⟨h8, h2⟩
      · have h1' : leNat a.i4 = 1 := by omega
        rw [h1']; exact hgb.proof1
      · have h2' : leNat a.i4 = 2 := by omega
        rw [h2']; exact hgb.proof2 h8
    refine ⟨absTx GB, t, by simp [spendOf], by rw [hgb.ptxid, hgb.txid], ht, leNat a.i4, pkh, hpr, ?_⟩
    simp only [absTx, List.mem_map]
    exact ⟨iB, hiB, by rw [htB, ← hlB, leNat_le32 _ hidxB]⟩

end BoltProof.Glue.SimpleMulti
