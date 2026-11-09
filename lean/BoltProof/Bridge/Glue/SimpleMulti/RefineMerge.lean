import BoltProof.Bridge.Glue.SimpleMulti.RefineGp
import BoltProof.Bridge.Glue.SimpleMulti.Merge

/-!
# `SimpleMultiBOLT`: the bytes refine `Accepts` (third stage, the merge commit)

A merge commit spends two settled tokens and the model reads it as one spend at the first token input that
consumes the other (`Spend.other`). The refinement takes both inputs' runs: at the first token input
(`inputIndexN` zero) `Accepts .fungible` holds of `spendOf` with the other token's fields and outpoint. The second
input's run supplies what the first input's covenant takes on trust: by `other_merge_path` its token is
settle-typed and it builds the merged token from its own fields, so by `merge_fields_eq` the first input's interop
arguments are the other token's balance and parent and the issuers are one. Beyond both inputs' `Residual`, it
assumes the two inputs spend distinct outpoints (the consensus rule against duplicate inputs) and that the second
input presents a preimage (§7's eighth question).
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

/-- **`SimpleMultiBOLT` refines `Accepts`, third stage**: a merge commit at its first token input, given the
second token input's run. -/
theorem simpleMulti_refines_merge_commit (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args)
    (S : List Bytes) (scriptSig : Bytes) (i' amt' : Nat) (f' : Fields) (a' : Args) (S' : List Bytes)
    (scriptSig' : Bytes) (hwf : WF f) (hA : ArgsWF a) (hwf' : WF f') (hA' : ArgsWF a')
    (hty : SmbType f.ty) (hnty : SmbType a.nty) (hty' : SmbType f'.ty) (hnty' : SmbType a'.nty)
    (hpre : castToBool a.pre = true) (hpre' : castToBool a'.pre = true)
    (hset : settledTy f.ty) (hmrg : a.nty = [0x25]) (hidx0 : decode a.inIdx = 0)
    (hgen : decode f.parent = 0 → settledTy f.ty)
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length) (hi' : i' < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hdis : serOutPoint (inputAt tx i) ≠ serOutPoint (inputAt tx i'))
    (hres : Residual P tx i amt f a) (hres' : Residual P tx i' amt' f' a')
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid)
    (hS1' : ((evalScript Eval.opExec (mkEnv params (txContext tx i' amt') params.flags.forkAdjust
      (some (lockScript f'))) scriptSig' [] 0).2).stack = a'.stack ++ S')
    (hv' : Eval.verifyScript params (txContext tx i' amt') scriptSig' (lockScript f') = .valid) :
    Accepts P .fungible (spendOf tx i f a
      (some (f', ⟨(inputAt tx i').prevHash, (inputAt tx i').prevIndex⟩)) none none) := by
  obtain ⟨hse, hsig0, hpreimg, htypes⟩ := refine_run P tx i amt f a S scriptSig hwf hty (fun _ => hnty) htx hi hres hS1 hv
  obtain ⟨hse', -, hpreimg', htypes'⟩ :=
    refine_run P tx i' amt' f' a' S' scriptSig' hwf' hty' (fun _ => hnty') htx hi' hres' hS1' hv'
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  have hmem' : inputAt tx i' ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi']
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  obtain ⟨h32', -, -, -⟩ := htx.inputs _ hmem'
  have hpe := hpreimg hpre
  obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
    preimage_fields (lockScript f) (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  rw [← hpe] at hsc hver' hprev hout hval hhout
  have hpe' := hpreimg' hpre'
  obtain ⟨-, hsc', -, -, hout', hval', hhout', -⟩ :=
    preimage_fields (lockScript f') (by rw [lockScript_length_eq hwf']; decide) tx i' amt' h32'
  rw [← hpe'] at hsc' hout' hval' hhout'
  obtain ⟨hpar1, -⟩ := htypes hpre
  obtain ⟨hpar1', hpar2'⟩ := htypes' hpre'
  have hset1 : f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24] := hset
  have henf : Enforced (phase2Env (txContext tx i amt)) f a (lockScript f) := by
    have h := hse; simp only [SpendEnforced, hpre, ↓reduceIte] at h; rw [ite_eq_left hset1] at h; exact h
  have hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
    hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
  -- the second token input took the merge path, and the two merged tokens are one
  obtain ⟨hset', h25', hi0', henf'⟩ := other_merge_path hwf hA hsc hval hmrg hidx0 hwf' hA' hsc' hval' hse' hpre'
    hty' hnty' hpar1' hpar2' (by rw [hout, hout']; exact hdis) hres.outputs hflat (by rw [hhout']; rfl)
  have hflat' : expectedOuts a' ++ a'.chg = (tx.outputs.map serTxOut).flatten :=
    hres.outputs _ (by rw [henf'.outputs, hhout']; rfl)
  have hfe := merge_fields_eq hwf hwf' hA hA' hsc hsc' hval hval' hmrg h25' hidx0 hi0' (hflat.trans hflat'.symm)
  have hnbc : a.nbc = f'.bal := congrArg Fields.balCommit hfe
  have hi1 : a.i1 = f'.parent := congrArg Fields.ogp hfe
  have hiss : f.issuer = f'.issuer := by
    have := congrArg Fields.issuer hfe; simpa only [commitFields, mergeFields1] using this
  -- the first input's spend
  have hlast := getLast_eq_of_drop henf.sigType
  have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
    rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockScript f) a.sig hlast]; exact hsig0
  have hk : kindOf f a = .commit := kindOf_commit hpre hset
  have hver : 2 ≤ tx.version := two_le_of_decode_serVersion _ htx.version (by rw [← hver']; exact henf.version)
  have hmode : modeOf f a = .merge := by simp [modeOf, hk, modeOfNext, hmrg]
  have hhon := hres.honest hpre
  have hcount : expectedCount f a = 2 := by simp [expectedCount, hset, hmrg]
  rw [hcount] at hhon
  refine accepts_of_facts P tx i f a _ none none hty (fun _ => hnty) (fun _ h => hpar1 h) hgen hi hver
    (by rw [hres.agrees.h160]; exact henf.owner) hsig (by simp [hlast]) henf.issuer ?_
    (fun h => absurd h (by rw [hk]; decide)) (balOf_le henf.balHi) ?_ ?_ (fun h => by rw [hk] at h; cases h)
    (fun h => by rw [hk] at h; cases h) ?_ ?_ ?_ ?_ (fun h => by rw [hk] at h; cases h)
    (fun h => by rw [hk] at h; cases h) (fun _ => ⟨rfl, rfl⟩)
  · intro _
    exact Spend.outsOK_of_canonical (outs_commit_merge _ none none hwf hA htx hamt hpre hset hmrg hidx0 hnbc hi1 h32
      hidx hnz hval hout hsc hflat hhon)
  · intro _ hm; rw [hmode] at hm; cases hm
  · intro _ _
    refine ⟨_, rfl, ?_⟩
    have hsum := henf.mergeGuard hmrg
    have hlo := henf.balLo
    have hlo' := henf.nbcLo
    have hm := maxBalance_eq
    simp only [tokenOf, balOf, ← hnbc, Fam.maxBalance]
    omega
  · simp [hk, hmode]
  · intro o ho
    simp only [Option.some.injEq] at ho
    subst ho
    refine ⟨?_, ?_⟩
    · simp only [absTx, List.mem_map]; exact ⟨_, hmem', rfl⟩
    · intro h
      apply hdis
      simp only [Outpoint.mk.injEq] at h
      simp [serOutPoint, h.1, h.2]
  · intro o ho
    simp only [Option.some.injEq] at ho
    subst ho
    exact hiss.symm
  · intro o ho
    simp only [Option.some.injEq] at ho
    subst ho
    rcases hset' with h | h | h <;> simp [tokenOf, h, Fam.settleTypes]

end BoltProof.Glue.SimpleMulti
