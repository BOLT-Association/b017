import BoltProof.Bridge.Glue.SimpleMulti.Refine
import BoltProof.Bridge.Glue.SimpleMulti.L3

/-!
# `SimpleMultiBOLT`: the bytes refine `Accepts` (second stage, the settles with a grandparent)

The second stage of the refinement (`lean/GLUE-PLAN.md`, M5): a transfer or split settle of a token with a
grandparent that the shipped lock accepts is a spend `Accepts .fungible` admits, read through `spendOf` with the
real grandparent as the first ancestor, for the rebuild with neither optional arm (the grandparent has one
token input and no second proof output: the second piece set's flags at depths 3 and 45 are zero). Beyond the
first stage's `Residual` it assumes `ResidualGp`: the grandparent is real (`GpRealF`), the second piece set has
the widths of the fields it stands for (`HonestPiecesB`), and the fifth interop slot is the parent's output
index plus one as a 32-bit word (the anchor's index, §7's sixth question). `refine_run` is the run prefix both
stages share.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (sc preOutpoint preValue preVersion preHashOutputs preHashPrevouts outpointOf
  getLast_eq_of_drop cleanupScriptCode_forkid two_le_of_decode_serVersion)
open BoltProof.Bridge (params)
open BoltProof.Bridge.Generated

/-- What the second stage assumes beyond `Residual`, of a settle with a grandparent `G`. -/
structure ResidualGp (P : Prims Bytes) (f : Fields) (a : Args) (G : Tx) : Prop where
  gp : GpRealF P f G
  pieces : HonestPiecesB a.psB
  i5len : a.i5.length = 4
  i5 : ∀ p, outpointOf f.parent = some p → decode a.i5 = (p.vout : Int) + 1

/-- The run prefix of the refinement: a valid verdict runs the suffix to `SpendEnforced` with the owner's
signature verified, and with a preimage the preimage is the real one and the types are related. -/
theorem refine_run (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (hwf : WF f) (hty : SmbType f.ty) (hnty : SmbType a.nty) (htx : TxWF tx)
    (hi : i < tx.inputs.length) (hres : Residual P tx i amt f a)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid) :
    SpendEnforced (phase2Env (txContext tx i amt)) f a S (lockScript f) ∧
    Ops.Crypto.txCheckSig tx i amt a.sig a.pk (cleanupScriptCode (lockScript f) a.sig true) true = true ∧
    (castToBool a.pre = true → a.pre = preimageBIP143 (lockScript f) tx i ⟨0x41⟩ amt) ∧
    (castToBool a.pre = true →
      ((f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) → ¬ (a.nty = [0x20] ∨ a.nty = [0x22] ∨ a.nty = [0x24])) ∧
      (¬ (f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) → f.ty.headD 0 = a.nty.headD 0 + 1)) := by
  obtain ⟨st1, h1, st2, top, rest, hrun, hs2, htop⟩ := run_of_valid hv
  have hS : st1.stack = a.stack ++ S := by rw [h1] at hS1; exact hS1
  have he : EnvOK (phase2Env (txContext tx i amt)) := envOK_phase2 _
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, -, -, -⟩ := htx.inputs _ hmem
  rw [hS] at hrun
  obtain ⟨r0, hr0, hok0, hend0⟩ : ∃ r0, run Eval.opExec (phase2Env (txContext tx i amt)) (lockScript f) []
      (St (a.stack ++ S) [] st1.memUsed {} 0 (lockScript f)) = r0 ∧ r0.IsOk ∧ (r0 = .next st2 ∨ r0 = .stop st2) := by
    rcases hrun with hrun | hrun
    · exact ⟨_, hrun, trivial, Or.inl rfl⟩
    · exact ⟨_, hrun, trivial, Or.inr rfl⟩
  obtain ⟨m', k', hsuf⟩ := lock_pushes he (by decide) hwf hr0 hok0
  rw [← List.append_nil SimpleMulti.suffix] at hsuf
  have hpreimg : castToBool a.pre = true → a.pre = preimageBIP143 (lockScript f) tx i ⟨0x41⟩ amt := by
    intro hpre
    obtain ⟨tail, X, A, mm, C, kk, r', hC, hpt, hok'⟩ := pushTxReached he (by decide) hpre hsuf hok0
    have hh := hres.pushTx a.pre tail X A mm C kk r' hC hpt hok'
    exact hres.preimage _ (by rw [hh]; rfl)
  have hvar : castToBool a.pre = true → List.take 1 (List.drop 104 a.pre) = [0xfd] := by
    intro hpre
    rw [hpreimg hpre]
    exact preimage_varint _ (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  obtain ⟨hse, rest2, alt2, m2, k2, hend⟩ := simpleMulti_sound he (by decide) hty hnty hvar hsuf hok0
  rw [run.eq_1] at hend
  have hst2 : st2 = St (ownerCheck (phase2Env (txContext tx i amt)) a (lockScript f) :: rest2) alt2 m2 {} k2
      (lockScript f) := by
    rcases hend0 with h0 | h0 <;> rw [h0] at hend <;> simp_all
  have htop' : top = ownerCheck (phase2Env (txContext tx i amt)) a (lockScript f) := by
    rw [hst2] at hs2; simp only [List.cons.injEq] at hs2; exact hs2.1.symm
  have hsig0 : Ops.Crypto.txCheckSig tx i amt a.sig a.pk (cleanupScriptCode (lockScript f) a.sig true) true = true := by
    rw [htop'] at htop
    unfold ownerCheck at htop
    split_ifs at htop with hc
    · exact hc
    · simp at htop
  exact ⟨hse, hsig0, hpreimg, fun hpre => types_of_run he (by decide) hty hnty hpre (hvar hpre) hsuf hok0⟩

/-- **`SimpleMultiBOLT` refines `Accepts`, second stage**: a transfer or split settle of a token with a
grandparent, the rebuild with neither optional arm. -/
theorem simpleMulti_refines_settle_gp (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args)
    (S : List Bytes) (scriptSig : Bytes) (G : Tx) (hwf : WF f) (hA : ArgsWF a)
    (hty : SmbType f.ty) (hnty : SmbType a.nty) (hpre : castToBool a.pre = true)
    (hset : ¬ settledTy f.ty) (hnm : f.ty ≠ [0x25]) (hgp : decode f.gp ≠ 0)
    (hgen : decode f.parent = 0 → settledTy f.ty) (hogp : decode f.ogp = 0)
    (hcom2 : f.ty = [0x23] → f.com2 ≠ zeroPKH)
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hres : Residual P tx i amt f a) (hgr : ResidualGp P f a G)
    (h140 : decode a.psB.p3 = 0) (h182 : decode a.psB.p45 = 0)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid) :
    Accepts P .fungible (spendOf tx i f a none (some G) none) := by
  obtain ⟨hse, hsig0, hpreimg, htypes⟩ := refine_run P tx i amt f a S scriptSig hwf hty hnty htx hi hres hS1 hv
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  have hpe := hpreimg hpre
  obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
    preimage_fields (lockScript f) (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  rw [← hpe] at hsc hver' hprev hout hval hhout
  obtain ⟨-, hpar2⟩ := htypes hpre
  have hhon := hres.honest hpre
  have henf : EnforcedSettle (phase2Env (txContext tx i amt)) f a S (lockScript f) := by
    have hset' : ¬ (f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) := hset
    have h := hse; simp only [SpendEnforced, hpre, ↓reduceIte] at h
    rw [ite_eq_right hset', ite_eq_right hgp] at h; exact h
  have hlast := getLast_eq_of_drop henf.sigType
  have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
    rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockScript f) a.sig hlast]; exact hsig0
  have hk : kindOf f a = .settle := kindOf_settle hpre hset
  have hflat : settleOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
    hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
  have hver : 2 ≤ tx.version := two_le_of_decode_serVersion _ htx.version (by rw [← hver']; exact henf.version)
  have hrel := hpar2 hset
  have htn : (f.ty = [0x21] ∧ a.nty = [0x20]) ∨ (f.ty = [0x23] ∧ a.nty = [0x22]) := by
    rcases hty with h | h | h | h | h | h <;> rcases hnty with g | g | g | g | g | g <;> simp_all [settledTy]
  have hnty' : a.nty = [0x20] ∨ a.nty = [0x22] := by rcases htn with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have hmode : modeOf f a = (if f.ty = [0x23] then .split else .transfer) := by
    have hkc : kindOf f a ≠ .commit := by rw [hk]; decide
    simp only [modeOf, hkc, ↓reduceIte]
    rcases htn with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Fam.modeOfCommitType]
  have hogpn : outpointOf f.ogp = none := by simp [outpointOf, hogp]
  have hpar : decode f.parent ≠ 0 := fun h => hset (hgen h)
  have hop : 104 ≤ a.pre.length := by
    have := congrArg List.length hout
    simp only [preOutpoint, List.length_take, List.length_drop, serOutPoint_length, h32] at this
    omega
  have hval8 : (List.take 8 (List.drop (107 + (decode (List.take 2 (List.drop 105 a.pre))).toNat) a.pre)).length = 8 := by
    show (preValue a.pre).length = 8
    rw [hval]; exact le64_length _
  have hlen : a.nty = [0x22] → (padN 16 (encode (decode f.bal - decode f.balCommit))).length = 16 := fun g =>
    padN16_length_of_range (henf.splitRem g) (by have := henf.balCommitLo (by rw [g]; decide); have := henf.balHi; omega)
  obtain ⟨w10, w11, w12, w13, w14, w17, w18, w19, w20, w23, w46, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨h0, h1, -, h3, -, h5, h6, h7, h8, h9, -, h11, h12⟩, -, -, hprevs⟩ := henf.rebuild
  rw [gateT_item2 f a S hnty', castToBool_nil] at hprevs
  simp only [Bool.false_eq_true, ↓reduceIte] at hprevs
  have hreb := l3_settle_00 (P := P) (tx := tx) (i := i) (G := G) none none hwf hsc hop hval8 hnty' hlen hgr.pieces
    h140 h182 h0 h1 h3 h5 h6 h7 h8 h9 h11 h12 hprevs hprev hout htx h32 hres.prevouts hgr.gp hgr.i5len hgr.i5
    henf.balLo hpar
  refine accepts_of_facts P tx i f a none (some G) none hty hnty (fun _ h => absurd h hset) hgen hi hver
    (by rw [hres.agrees.h160]; exact henf.owner) hsig (by simp [hlast]) henf.issuer ?_
    (fun h => absurd h (by rw [hk]; decide)) (balOf_le henf.balHi) (fun h => by rw [hk] at h; cases h)
    (fun h => by rw [hk] at h; cases h) ?_ ?_ ?_ (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ h => by cases h) (fun _ gp h => hreb gp h) (fun _ og h => by rw [hogpn] at h; cases h)
    (fun h => absurd h (by
      rintro (h | h)
      · rw [hk] at h; cases h
      · simp [outpointOf, hgp] at h))
  · intro _
    have hcount : expectedCount f a = (if f.ty = [0x23] then 2 else 1) := by
      simp [expectedCount, hset]
    rw [hcount] at hhon
    rcases htn with ⟨h, g⟩ | ⟨h, g⟩
    · rw [ite_eq_right (by rw [h]; decide)] at hhon
      exact outs_settle_transfer none (some G) none hwf hA htx hamt hpre h g h32 hidx hnz hval hout hsc hflat hhon
    · rw [ite_eq_left h] at hhon
      obtain ⟨hpk, -⟩ := hres.splitFlags hpre h
      exact outs_settle_split none (some G) none hwf hA htx hamt hpre h g hpk (henf.balCommitLo (by rw [g]; decide))
        (henf.splitRem g) henf.balHi (hcom2 h) h32 hidx hnz hval hout hsc hflat hhon
  · intro _ hm
    rw [hmode] at hm
    split_ifs at hm with h
    rcases htn with ⟨h', g⟩ | ⟨h', g⟩
    · rw [h'] at h; cases h
    · have h1 := henf.balCommitLo (by rw [g]; decide)
      have h2 := henf.splitRem g
      simp only [balOf]; omega
  · intro _ hm
    rw [hmode] at hm; split_ifs at hm
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro h; rw [hk] at h; cases h

end BoltProof.Glue.SimpleMulti
