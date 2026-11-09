import BoltProof.Bridge.Glue.SimpleMulti.Refine

/-!
# Byte-level facts the fungible chain reads off a commit

Helpers for `Chain.lean` to derive `GpRealF.bal` (the grandparent token output's balance signs) from the
commit step that created the grandparent, instead of assuming it (`BalsNonneg`): a real commit's produced
token output carries non-negative balance bytes (`commit_out_bals_basic`, `commit_out_bals_merge`, from the
covenant's own bound check), and two well-formed transactions with the same txid are equal under no second
preimage (`tx_eq_of_txid`), which identifies the grandparent with its creating commit's transaction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (preOutpoint preValue preVersion preHashOutputs preHashPrevouts outpointOf
  getLast_eq_of_drop cleanupScriptCode_forkid two_le_of_decode_serVersion)
open BoltProof.Bridge (params)
open BoltProof.Bridge.Generated

/-- A real basic commit's produced token output (output 0) has non-negative balance bytes. -/
theorem commit_out_bals_basic (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args)
    (S : List Bytes) (scriptSig : Bytes) (hwf : WF f) (ha : castToBool a.pre = true → ArgsWF a)
    (hty : SmbType f.ty) (hnty : castToBool a.pre = true → SmbType a.nty)
    (hnm : f.ty ≠ [0x25] ∧ a.nty ≠ [0x25]) (hgp0 : ¬ settledTy f.ty → decode f.gp = 0)
    (hgen : decode f.parent = 0 → settledTy f.ty) (hogp : decode f.ogp = 0)
    (hbal : 0 ≤ decode f.bal ∧ decode f.bal ≤ maxBalance)
    (hcom2 : f.ty = [0x23] → f.com2 ≠ zeroPKH) (hpkh2 : a.nty = [0x23] → a.pkh2 ≠ zeroPKH)
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hres : Residual P tx i amt f a)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid)
    (hpre : castToBool a.pre = true) (hset : settledTy f.ty) :
    ∃ gout : Fields, tx.outputs[0]? = some ⟨amt, lockScript gout⟩ ∧ WF gout ∧
      0 ≤ decode gout.bal ∧ 0 ≤ decode gout.balCommit := by
  obtain ⟨st1, h1, st2, top, rest, hrun, hs2, htop⟩ := run_of_valid hv
  have hS : st1.stack = a.stack ++ S := by rw [h1] at hS1; exact hS1
  have he : EnvOK (phase2Env (txContext tx i amt)) := envOK_phase2 _
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  rw [hS] at hrun
  obtain ⟨r0, hr0, hok0, hend0⟩ : ∃ r0, run Eval.opExec (phase2Env (txContext tx i amt)) (lockScript f) []
      (St (a.stack ++ S) [] st1.memUsed {} 0 (lockScript f)) = r0 ∧ r0.IsOk ∧ (r0 = .next st2 ∨ r0 = .stop st2) := by
    rcases hrun with hrun | hrun
    · exact ⟨_, hrun, trivial, Or.inl rfl⟩
    · exact ⟨_, hrun, trivial, Or.inr rfl⟩
  obtain ⟨m', k', hsuf⟩ := lock_pushes he (by decide) hwf hr0 hok0
  rw [← List.append_nil SimpleMulti.suffix] at hsuf
  have hpreimg : a.pre = preimageBIP143 (lockScript f) tx i ⟨0x41⟩ amt := by
    obtain ⟨tail, X, A, mm, C, kk, r', hC, hpt, hok'⟩ := pushTxReached he (by decide) hpre hsuf hok0
    have hh := hres.pushTx a.pre tail X A mm C kk r' hC hpt hok'
    exact hres.preimage _ (by rw [hh]; rfl)
  have hvar : List.take 1 (List.drop 104 a.pre) = [0xfd] := by
    rw [hpreimg]; exact preimage_varint _ (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  obtain ⟨hse, rest2, alt2, m2, k2, hend⟩ := simpleMulti_sound he (by decide) hty (fun _ => hnty hpre) (fun _ => hvar) hsuf hok0
  obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
    preimage_fields (lockScript f) (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  rw [← hpreimg] at hsc hver' hprev hout hval hhout
  obtain ⟨hpar1, hpar2⟩ := types_of_run he (by decide) hty (hnty hpre) hpre hvar hsuf hok0
  have hA := ha hpre
  have hhon := hres.honest hpre
  have henf : Enforced (phase2Env (txContext tx i amt)) f a (lockScript f) := by
    have hset' : f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24] := hset
    have h := hse; simp only [SpendEnforced, hpre, ↓reduceIte] at h; rw [ite_eq_left hset'] at h; exact h
  have hnt : a.nty = [0x21] ∨ a.nty = [0x23] := by
    have := hpar1 hset
    rcases hnty hpre with h | h | h | h | h | h <;> simp_all [settledTy]
  have hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
    hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
  have hval2 : preValue a.pre = le64 amt := hval
  have hout2 : preOutpoint a.pre = serOutPoint (inputAt tx i) := hout
  -- parse output 0 by the next type
  rcases hnt with hnt | hnt
  · -- transfer commit: balCommit = zeros 16
    have hcwf := commitFields_wf hwf hA (Or.inl hnt) (zeros_length 16) (zeros_length 20) (zeros_length 36) (a := a)
    rw [commitOuts_transfer hwf hA hsc hval2 hnt, List.append_assoc] at hflat
    obtain ⟨os1, hos1, -⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hcwf hamt) hflat.symm
    refine ⟨commitFields f a (zeros 16) (zeros 20) (zeros 36), ?_, hcwf, ?_, ?_⟩
    · rw [hos1]; rfl
    · show 0 ≤ decode f.bal; exact hbal.1
    · show (0 : Int) ≤ decode (zeros 16); decide
  · -- split commit: balCommit = a.nbc
    have hcwf := commitFields_wf hwf hA (Or.inr (Or.inl hnt)) (hA.nbc (Or.inl hnt)) (hA.pkh2 hnt) (zeros_length 36) (a := a)
    rw [commitOuts_split hwf hA hsc hval2 hnt, List.append_assoc, List.append_assoc] at hflat
    obtain ⟨os1, hos1, -⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hcwf hamt) hflat.symm
    refine ⟨commitFields f a a.nbc a.pkh2 (zeros 36), ?_, hcwf, ?_, ?_⟩
    · rw [hos1]; rfl
    · show 0 ≤ decode f.bal; exact hbal.1
    · show 0 ≤ decode a.nbc; exact henf.nbcLo

/-- A real merge commit's first input produces the merged token (output 0) with non-negative balance bytes. -/
theorem commit_out_bals_merge (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args)
    (S : List Bytes) (scriptSig : Bytes) (hwf : WF f) (hA : ArgsWF a)
    (hty : SmbType f.ty) (hnty : SmbType a.nty)
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hres : Residual P tx i amt f a)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
      (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid)
    (hpre : castToBool a.pre = true) (hset : settledTy f.ty) (hmrg : a.nty = [0x25])
    (hidx0 : decode a.inIdx = 0) :
    ∃ gout : Fields, tx.outputs[0]? = some ⟨amt, lockScript gout⟩ ∧ WF gout ∧
      0 ≤ decode gout.bal ∧ 0 ≤ decode gout.balCommit := by
  obtain ⟨st1, h1, st2, top, rest, hrun, hs2, htop⟩ := run_of_valid hv
  have hS : st1.stack = a.stack ++ S := by rw [h1] at hS1; exact hS1
  have he : EnvOK (phase2Env (txContext tx i amt)) := envOK_phase2 _
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  rw [hS] at hrun
  obtain ⟨r0, hr0, hok0, hend0⟩ : ∃ r0, run Eval.opExec (phase2Env (txContext tx i amt)) (lockScript f) []
      (St (a.stack ++ S) [] st1.memUsed {} 0 (lockScript f)) = r0 ∧ r0.IsOk ∧ (r0 = .next st2 ∨ r0 = .stop st2) := by
    rcases hrun with hrun | hrun
    · exact ⟨_, hrun, trivial, Or.inl rfl⟩
    · exact ⟨_, hrun, trivial, Or.inr rfl⟩
  obtain ⟨m', k', hsuf⟩ := lock_pushes he (by decide) hwf hr0 hok0
  rw [← List.append_nil SimpleMulti.suffix] at hsuf
  have hpreimg : a.pre = preimageBIP143 (lockScript f) tx i ⟨0x41⟩ amt := by
    obtain ⟨tail, X, A, mm, C, kk, r', hC, hpt, hok'⟩ := pushTxReached he (by decide) hpre hsuf hok0
    have hh := hres.pushTx a.pre tail X A mm C kk r' hC hpt hok'
    exact hres.preimage _ (by rw [hh]; rfl)
  have hvar : List.take 1 (List.drop 104 a.pre) = [0xfd] := by
    rw [hpreimg]; exact preimage_varint _ (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  obtain ⟨hse, rest2, alt2, m2, k2, hend⟩ := simpleMulti_sound he (by decide) hty (fun _ => hnty) (fun _ => hvar) hsuf hok0
  obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
    preimage_fields (lockScript f) (by rw [lockScript_length_eq hwf]; decide) tx i amt h32
  rw [← hpreimg] at hsc hver' hprev hout hval hhout
  have henf : Enforced (phase2Env (txContext tx i amt)) f a (lockScript f) := by
    have hset' : f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24] := hset
    have h := hse; simp only [SpendEnforced, hpre, ↓reduceIte] at h; rw [ite_eq_left hset'] at h; exact h
  have hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
    hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
  have hval2 : preValue a.pre = le64 amt := hval
  have hcwf := commitFields_wf hwf hA (Or.inr (Or.inr hmrg)) (hA.nbc (Or.inr hmrg)) (zeros_length 20) (hA.i1 hmrg) (a := a)
  rw [commitOuts_merge0 hwf hA hsc hval2 hmrg hidx0, List.append_assoc] at hflat
  obtain ⟨os1, hos1, -⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hcwf hamt) hflat.symm
  refine ⟨commitFields f a a.nbc (zeros 20) a.i1, ?_, hcwf, ?_, ?_⟩
  · rw [hos1]; rfl
  · show 0 ≤ decode f.bal; exact henf.balLo
  · show 0 ≤ decode a.nbc; exact henf.nbcLo

/-- Two well-formed transactions with the same txid are equal, under no second preimage of one's serialisation. -/
theorem tx_eq_of_txid {G G' : Tx} (hwfG : TxWF G) (hwfG' : TxWF G')
    (hnsp : BoltProof.Glue.MinSimple.NoSecondPreimage (serTx G))
    (htxid : Sighash.txid G' = Sighash.txid G) : G' = G := by
  have hh : Hash.hash256 (serTx G') = Hash.hash256 (serTx G) := htxid
  have hser : serTx G' = serTx G := hnsp _ hh
  have h1 : decodeTx (serTx G') = some G' := decodeTx_serTx G' hwfG'
  rw [hser, decodeTx_serTx G hwfG] at h1
  exact (Option.some.inj h1).symm

end BoltProof.Glue.SimpleMulti
