import BoltProof.Bridge.Glue.SimpleMulti.Outs

/-!
# `SimpleMultiBOLT`: the bytes refine `Accepts` (first stage)

**The refinement theorem, first stage** (`lean/GLUE-PLAN.md`, M5): a spend the shipped `SimpleMultiBOLT` lock
accepts under the post-Chronicle consensus rules is a spend `Accepts` admits for the fungible family, once read
into the model's vocabulary (`spendOf`, `Abs.lean`), for the spends this stage covers: the transfer and split
commits, the transfer and split settles of a token without a grandparent, and the melt. The merges and the settles
with a grandparent (the rebuilds and their balance anchors) are the next stages; `hnm` and `hgp0` exclude them.

Beyond the bytes it assumes `Residual` (`Residual.lean`) and the lock-data conditions a token a covenant produced
meets: a genesis token is settled-typed, a non-merge token carries no other lineage, the balance is in range, and
a split's second recipient is not the zero hash.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (preOutpoint preValue preVersion preHashOutputs preHashPrevouts outpointOf
  getLast_eq_of_drop cleanupScriptCode_forkid two_le_of_decode_serVersion)
open BoltProof.Bridge (params)
open BoltProof.Bridge.Generated

theorem maxBalance_eq : maxBalance = 2 ^ 127 - 1 := by decide

theorem balOf_le {b : Bytes} (h : decode b ≤ maxBalance) : balOf b ≤ Fam.maxBalance := by
  have := maxBalance_eq
  simp only [balOf, Fam.maxBalance]; omega

/-- **`SimpleMultiBOLT` refines `Accepts`, first stage.** -/
theorem simpleMulti_refines_basic (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args)
    (S : List Bytes) (scriptSig : Bytes) (hwf : WF f) (ha : castToBool a.pre = true → ArgsWF a)
    (hty : SmbType f.ty) (hnty : SmbType a.nty)
    (hnm : f.ty ≠ [0x25] ∧ a.nty ≠ [0x25]) (hgp0 : ¬ settledTy f.ty → decode f.gp = 0)
    (hgen : decode f.parent = 0 → settledTy f.ty) (hogp : decode f.ogp = 0)
    (hbal : 0 ≤ decode f.bal ∧ decode f.bal ≤ maxBalance)
    (hcom2 : f.ty = [0x23] → f.com2 ≠ zeroPKH) (hpkh2 : a.nty = [0x23] → a.pkh2 ≠ zeroPKH)
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hres : Residual P tx i amt f a)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid) :
    Accepts P .fungible (spendOf tx i f a none none none) := by
  obtain ⟨st1, h1, st2, top, rest, hrun, hs2, htop⟩ := run_of_valid hv
  have hS : st1.stack = a.stack ++ S := by rw [h1] at hS1; exact hS1
  have he : EnvOK (phase2Env (txContext tx i amt)) := envOK_phase2 _
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  rw [hS] at hrun
  -- the run of the lock, and of the suffix from the fields
  obtain ⟨r0, hr0, hok0, hend0⟩ : ∃ r0, run Eval.opExec (phase2Env (txContext tx i amt)) (lockScript f) []
      (St (a.stack ++ S) [] st1.memUsed {} 0 (lockScript f)) = r0 ∧ r0.IsOk ∧ (r0 = .next st2 ∨ r0 = .stop st2) := by
    rcases hrun with hrun | hrun
    · exact ⟨_, hrun, trivial, Or.inl rfl⟩
    · exact ⟨_, hrun, trivial, Or.inr rfl⟩
  obtain ⟨m', k', hsuf⟩ := lock_pushes he (by decide) hwf hr0 hok0
  rw [← List.append_nil SimpleMulti.suffix] at hsuf
  -- with a preimage, the preimage is the real one
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
  -- the owner's signature verifies
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
  rcases hpre : castToBool a.pre with _ | _
  · -- a melt
    have hpre' : castToBool a.pre = false := hpre
    have hm : EnforcedMelt (phase2Env (txContext tx i amt)) f a := by
      have h := hse; simp only [SpendEnforced, hpre', Bool.false_eq_true, ↓reduceIte] at h; exact h
    have hlast := getLast_eq_of_drop hm.sigType
    have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
      rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockScript f) a.sig hlast]; exact hsig0
    have hk : kindOf f a = .melt := kindOf_melt_iff.mpr hpre'
    refine accepts_of_facts P tx i f a none none none hty hnty (fun h _ => by rw [hpre'] at h; cases h) hgen hi
      (hres.melt hpre').2 (by rw [hres.agrees.h160]; exact hm.owner) hsig (by simp [hlast]) hm.issuer
      (fun h => absurd hk h) ?_ (balOf_le hbal.2) (fun h => by rw [hk] at h; cases h) (fun h => by rw [hk] at h; cases h)
      (fun h => by rw [hk] at h; cases h) (fun h => by rw [hk] at h; cases h) ?_
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
      (fun h => by rw [hk] at h; cases h) (fun h => by rw [hk] at h; cases h) (fun _ => ⟨rfl, rfl⟩)
    · intro _ o ho
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp (by simpa [absTx] using ho)
      exact (hres.melt hpre').1 o' ho'
    · simp [hk]
  · -- a spend with a preimage
    have hpre' : castToBool a.pre = true := hpre
    have hpe := hpreimg hpre'
    obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
      preimage_fields (lockScript f) (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
    rw [← hpe] at hsc hver' hprev hout hval hhout
    obtain ⟨hpar1, hpar2⟩ := types_of_run he (by decide) hty hnty hpre' (hvar hpre') hsuf hok0
    have hA := ha hpre'
    have hhon := hres.honest hpre'
    by_cases hset : settledTy f.ty
    · -- a commit
      have henf : Enforced (phase2Env (txContext tx i amt)) f a (lockScript f) := by
        have hset' : f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24] := hset
        have h := hse; simp only [SpendEnforced, hpre', ↓reduceIte] at h; rw [ite_eq_left hset'] at h; exact h
      have hlast := getLast_eq_of_drop henf.sigType
      have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
        rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockScript f) a.sig hlast]; exact hsig0
      have hk : kindOf f a = .commit := kindOf_commit hpre' hset
      have hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
        hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
      have hver : 2 ≤ tx.version := two_le_of_decode_serVersion _ htx.version (by rw [← hver']; exact henf.version)
      have hnt : a.nty = [0x21] ∨ a.nty = [0x23] := by
        have := hpar1 hset
        rcases hnty with h | h | h | h | h | h <;> simp_all [settledTy]
      have hmode : modeOf f a = (if a.nty = [0x23] then .split else .transfer) := by
        simp only [modeOf, hk, ↓reduceIte, modeOfNext]
        rcases hnt with h | h <;> simp [h]
      refine accepts_of_facts P tx i f a none none none hty hnty (fun _ h => hpar1 h) hgen hi hver
        (by rw [hres.agrees.h160]; exact henf.owner) hsig (by simp [hlast]) henf.issuer ?_
        (fun h => absurd h (by rw [hk]; decide)) (balOf_le henf.balHi) ?_ ?_ (fun h => by rw [hk] at h; cases h)
        (fun h => by rw [hk] at h; cases h) ?_ (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun h => by rw [hk] at h; cases h) (fun h => by rw [hk] at h; cases h) (fun _ => ⟨rfl, rfl⟩)
      · intro _
        have hcount : expectedCount f a = (if a.nty = [0x23] then 3 else 2) := by
          simp [expectedCount, hset]
        rw [hcount] at hhon
        rcases hnt with h | h
        · rw [ite_eq_right (by rw [h]; decide)] at hhon
          exact outs_commit_transfer none none none hwf hA htx hamt hpre' hset h h32 hidx hnz hval hout hsc hflat hhon
        · rw [ite_eq_left h] at hhon
          exact outs_commit_split none none none hwf hA htx hamt hpre' hset h (hpkh2 h) h32 hidx hnz hval hout hsc
            hflat hhon
      · intro _ hm
        rw [hmode] at hm
        split_ifs at hm with h
        have := henf.splitGuard h
        have := henf.nbcLo
        simp only [balOf]; omega
      · intro _ hm
        rw [hmode] at hm; split_ifs at hm
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
        intro _ hm; rw [hmode] at hm; split_ifs at hm
    · -- a settle without a grandparent
      have hgp := hgp0 hset
      have henf : EnforcedSettle0 (phase2Env (txContext tx i amt)) f a (lockScript f) := by
        have hset' : ¬ (f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) := hset
        have h := hse; simp only [SpendEnforced, hpre', ↓reduceIte] at h
        rw [ite_eq_right hset', ite_eq_left hgp] at h; exact h
      have hlast := getLast_eq_of_drop henf.sigType
      have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
        rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockScript f) a.sig hlast]; exact hsig0
      have hk : kindOf f a = .settle := kindOf_settle hpre' hset
      have hflat : settleOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
        hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
      have hver : 2 ≤ tx.version := two_le_of_decode_serVersion _ htx.version (by rw [← hver']; exact henf.version)
      have hrel := hpar2 hset
      have htn : (f.ty = [0x21] ∧ a.nty = [0x20]) ∨ (f.ty = [0x23] ∧ a.nty = [0x22]) := by
        rcases hty with h | h | h | h | h | h <;> rcases hnty with g | g | g | g | g | g <;> simp_all [settledTy]
      have hmode : modeOf f a = (if f.ty = [0x23] then .split else .transfer) := by
        have hkc : kindOf f a ≠ .commit := by rw [hk]; decide
        simp only [modeOf, hkc, ↓reduceIte]
        rcases htn with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Fam.modeOfCommitType]
      have hgpn : outpointOf f.gp = none := by simp [outpointOf, hgp]
      have hogpn : outpointOf f.ogp = none := by simp [outpointOf, hogp]
      refine accepts_of_facts P tx i f a none none none hty hnty (fun _ h => absurd h hset) hgen hi hver
        (by rw [hres.agrees.h160]; exact henf.owner) hsig (by simp [hlast]) henf.issuer ?_
        (fun h => absurd h (by rw [hk]; decide)) (balOf_le henf.balHi) (fun h => by rw [hk] at h; cases h)
        (fun h => by rw [hk] at h; cases h) ?_ ?_ ?_ (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ gp h => by rw [hgpn] at h; cases h) (fun _ og h => by rw [hogpn] at h; cases h)
        (fun _ => ⟨rfl, rfl⟩)
      · intro _
        have hcount : expectedCount f a = (if f.ty = [0x23] then 2 else 1) := by
          simp [expectedCount, hset]
        rw [hcount] at hhon
        rcases htn with ⟨h, g⟩ | ⟨h, g⟩
        · rw [ite_eq_right (by rw [h]; decide)] at hhon
          exact outs_settle_transfer none none none hwf hA htx hamt hpre' h g h32 hidx hnz hval hout hsc hflat hhon
        · rw [ite_eq_left h] at hhon
          obtain ⟨hpk, -⟩ := hres.splitFlags hpre' h
          exact outs_settle_split none none none hwf hA htx hamt hpre' h g hpk (henf.balCommitLo (by rw [g]; decide))
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
