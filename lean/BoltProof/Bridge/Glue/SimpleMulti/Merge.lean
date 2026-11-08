import BoltProof.Bridge.Glue.SimpleMulti.Outs
import BoltProof.Bridge.Glue.SimpleMulti.Sound

/-!
# The merge commit's two inputs agree

A merge commit spends two settled tokens, and each one's covenant runs on the same transaction. The first token
input (`inputIndexN` zero) builds the merged commit token from its own fields and the interop arguments (the
other token's balance `nbc` and parent `i1`); the second (`inputIndexN` non-zero) builds it from its own fields and
the interop arguments the other way round (`mergeLock1`: the first token's balance `nbc`, owner `i3`, outpoint
`i2` and parent `i1`). Both weld their outputs to one `hashOutputs`, so under second-preimage freedom of the
serialised outputs the two locks are one, and the interop arguments are the other token's real fields
(`merge_fields_eq`): the first input's `nbc` is the second token's balance, its `i1` the second token's parent,
and the two tokens have one issuer.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (sc preOutpoint preValue proofScript preHashOutputs outpointOf)

/-- The merged token's fields as the second token input builds them. -/
def mergeFields1 (f : Fields) (a : Args) : Fields :=
  { bal := a.nbc, balCommit := f.bal, pkh := a.i3, com := a.pkh1, com2 := zeros 20, ogp := f.parent, ty := a.nty,
    outIdx := [0], parent := a.i2, gp := a.i1, issuer := f.issuer }

theorem mergeFields1_wf {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) (hnty : a.nty = [0x25])
    (hidx : ¬ decode a.inIdx = 0) : WF (mergeFields1 f a) :=
  ⟨ha.nbc (Or.inr hnty), hwf.bal, ha.i3 hnty hidx, ha.pkh1 (Or.inr (Or.inr hnty)), zeros_length 20, hwf.parent, ha.nty, rfl,
    ha.i2 hnty, ha.i1 hnty, hwf.issuer⟩

/-- The lock the second token input builds is the fungible lock of `mergeFields1`. -/
theorem mergeLock1_eq {f : Fields} {a : Args} (hwf : WF f) (hsc : sc a.pre = lockScript f) :
    mergeLock1 a = lockScript (mergeFields1 f a) := by
  simp only [mergeLock1, lockOf, scBalPush_of_sc hwf hsc, scParentPush_of_sc hwf hsc, scIssuerPush_of_sc hwf hsc,
    scSuffix_of_sc hwf hsc, lockScript, mergeFields1, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append]

/-- The second token input's outputs: the merged token as it builds it, then the proof output. -/
theorem commitOuts_merge1 {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) (hsc : sc a.pre = lockScript f)
    {amt : Nat} (hval : preValue a.pre = le64 amt) (hnty : a.nty = [0x25]) (hidx : ¬ decode a.inIdx = 0) :
    expectedOuts a = serTxOut ⟨amt, lockScript (mergeFields1 f a)⟩ ++ serTxOut ⟨amt, proofScript a.pkh1⟩ := by
  rw [expectedOuts, ite_eq_right (by rw [hnty]; decide), ite_eq_right (by rw [hnty]; decide), ite_eq_left hnty,
    ite_eq_right hidx, mergeLock1_eq hwf hsc, tokenOut_eq (mergeFields1_wf hwf ha hnty hidx) hval,
    proofOut_eq (ha.pkh1 (Or.inr (Or.inr hnty))) hval]

/-- The fungible lock determines well-formed fields. -/
theorem lockScript_inj {g g' : Fields} (hg : WF g) (hg' : WF g') (h : lockScript g = lockScript g') : g = g' := by
  have := decodeLock_lockScript hg
  rw [h, decodeLock_lockScript hg'] at this
  exact (Option.some.inj this).symm

/-- A token output serialised in front of anything fixes the lock. -/
theorem lock_of_serTxOut_prefix {g g' : Fields} (hg : WF g) (hg' : WF g') {amt amt' : Nat} {r r' : Bytes}
    (h : serTxOut ⟨amt, lockScript g⟩ ++ r = serTxOut ⟨amt', lockScript g'⟩ ++ r') : g = g' := by
  have hl : (serTxOut ⟨amt, lockScript g⟩).length = (serTxOut ⟨amt', lockScript g'⟩).length := by
    simp [serTxOut, serScript, lockScript_length_eq hg, lockScript_length_eq hg', le64_length]
  have he := (List.append_inj h hl).1
  simp only [serTxOut, serScript, lockScript_length_eq hg, lockScript_length_eq hg'] at he
  have he' := (List.append_inj he (by simp [le64_length])).2
  exact lockScript_inj hg hg' (List.append_cancel_left he')

/-- **The two inputs of a merge commit agree**: the first input's merged token is the second's. -/
theorem merge_fields_eq {f f' : Fields} {a a' : Args} (hwf : WF f) (hwf' : WF f') (ha : ArgsWF a) (ha' : ArgsWF a')
    (hsc : sc a.pre = lockScript f) (hsc' : sc a'.pre = lockScript f') {amt amt' : Nat}
    (hval : preValue a.pre = le64 amt) (hval' : preValue a'.pre = le64 amt')
    (hnty : a.nty = [0x25]) (hnty' : a'.nty = [0x25]) (hidx : decode a.inIdx = 0) (hidx' : ¬ decode a'.inIdx = 0)
    (hout : expectedOuts a ++ a.chg = expectedOuts a' ++ a'.chg) :
    commitFields f a a.nbc (zeros 20) a.i1 = mergeFields1 f' a' := by
  rw [commitOuts_merge0 hwf ha hsc hval hnty hidx, commitOuts_merge1 hwf' ha' hsc' hval' hnty' hidx'] at hout
  simp only [List.append_assoc] at hout
  exact lock_of_serTxOut_prefix (commitFields_wf hwf ha (Or.inr (Or.inr hnty)) (ha.nbc (Or.inr hnty)) (zeros_length 20) (ha.i1 hnty))
    (mergeFields1_wf hwf' ha' hnty' hidx')
    hout

/-! ## The merge commit at the first token input, read by the model -/

/-- The merged token the first input builds is the model's `commitToken`, once the interop arguments are the
other token's balance and parent. -/
theorem tokenOf_commit_merge (tx : Tx) (i : Nat) {f f' : Fields} {a : Args} (op : Outpoint Bytes)
    (ancA ancB : Option Tx) (hpre : castToBool a.pre = true) (hset : settledTy f.ty) (hnty : a.nty = [0x25])
    (hnbc : a.nbc = f'.bal) (hi1 : a.i1 = f'.parent)
    (hout : preOutpoint a.pre = serOutPoint (inputAt tx i)) (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32) :
    tokenOf (commitFields f a a.nbc (zeros 20) a.i1) =
      (spendOf tx i f a (some (f', op)) ancA ancB).commitToken := by
  simp only [tokenOf, commitFields, spendOf, Spend.commitToken, modeOf, kindOf_commit hpre hset, modeOfNext, hnty,
    outpointOf_preOutpoint tx i hout hnz h32 hidx, com2Of_zeros, Mode.commitType, hnbc, hi1, Option.map_some]
  simp

/-- A merge commit's outputs at the first token input, read by the model: the merged token, the proof output,
then non-token change. -/
theorem outs_commit_merge {tx : Tx} {i amt : Nat} {f f' : Fields} {a : Args} (op : Outpoint Bytes)
    (ancA ancB : Option Tx) (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx) (hamt : amt < 2 ^ 64)
    (hpre : castToBool a.pre = true) (hset : settledTy f.ty) (hnty : a.nty = [0x25]) (hidx0 : decode a.inIdx = 0)
    (hnbc : a.nbc = f'.bal) (hi1 : a.i1 = f'.parent)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : MinSimple.sc a.pre = lockScript f)
    (hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 2) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a (some (f', op)) ancA ancB).expectedOuts .fungible ++ change := by
  have hcwf := commitFields_wf hwf ha (Or.inr (Or.inr hnty)) (ha.nbc (Or.inr hnty)) (zeros_length 20) (ha.i1 hnty) (a := a)
  have hp1 := ha.pkh1 (Or.inr (Or.inr hnty))
  rw [commitOuts_merge0 hwf ha hsc hval hnty hidx0, List.append_assoc] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hcwf hamt) hflat.symm
  obtain ⟨os2, hos2, hf2⟩ := flatten_serTxOut_cons
    (fun o ho => htx.outputs o (by rw [hos1]; exact List.mem_cons_of_mem _ ho)) (proofScript_value_ok hp1 hamt) hf1
  refine ⟨os2.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1, hos2]; simpa using ho')
  · have hk : (spendOf tx i f a (some (f', op)) ancA ancB).kind = .commit := kindOf_commit hpre hset
    have hm : (spendOf tx i f a (some (f', op)) ancA ancB).mode = .merge := by
      simp [spendOf, modeOf, kindOf_commit hpre hset, modeOfNext, hnty]
    simp only [absTx, hos1, hos2, List.map_cons, Spend.expectedOuts, hk, hm, outOf_lock hcwf, outOf_proof hp1,
      tokenOf_commit_merge tx i op ancA ancB hpre hset hnty hnbc hi1 hout hnz h32 hidx]
    simp [spendOf]

/-! ## The second token input took the merge path -/

theorem mergeFieldsS_wf {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a)
    (hlen : (padN 16 (encode (decode f.bal + decode f.balCommit))).length = 16) : WF (mergeFieldsS f a) := by
  constructor <;> simp only [mergeFieldsS, settleFieldsT, hlen, zeros_length, hwf.com, hwf.parent, hwf.issuer,
    ha.outpoint, List.length_singleton]

/-- A settle's outputs and ranges, whichever ancestor arm the run took. -/
theorem settle_outputs_of {env : Env} {f : Fields} {a : Args} {S : List Bytes} {cs : Bytes}
    (hse : SpendEnforced env f a S cs) (hpre : castToBool a.pre = true) (hset : ¬ settledTy f.ty) :
    Hash.hash256 (settleOuts f a ++ a.chg) = preHashOutputs a.pre ∧ 0 ≤ decode f.bal ∧
      decode f.bal ≤ maxBalance ∧ (a.nty ≠ [0x20] → 0 ≤ decode f.balCommit) ∧
      (a.nty = [0x22] → 0 ≤ decode f.bal - decode f.balCommit) ∧
      (a.nty = [0x24] → decode f.bal + decode f.balCommit ≤ maxBalance) := by
  have hset' : ¬ (f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) := hset
  simp only [SpendEnforced, hpre, ↓reduceIte] at hse
  rw [ite_eq_right hset'] at hse
  by_cases hgp : decode f.gp = 0
  · rw [ite_eq_left hgp] at hse
    exact ⟨hse.outputs, hse.balLo, hse.balHi, hse.balCommitLo, hse.splitRem, hse.mergeSum⟩
  · rw [ite_eq_right hgp] at hse
    exact ⟨hse.outputs, hse.balLo, hse.balHi, hse.balCommitLo, hse.splitRem, hse.mergeSum⟩

/-- No settle's first output is a merge commit token. -/
theorem settle_first_not_merge {f : Fields} {a : Args} {g : Fields} (hwf : WF f) (ha : ArgsWF a)
    (hsc : MinSimple.sc a.pre = lockScript f) {amt amt' : Nat} (hval : preValue a.pre = le64 amt')
    (hg : WF g) (hgty : g.ty = [0x25]) {r : Bytes}
    (hbal : 0 ≤ decode f.bal ∧ decode f.bal ≤ maxBalance) (hbc : a.nty ≠ [0x20] → 0 ≤ decode f.balCommit)
    (hrem : a.nty = [0x22] → 0 ≤ decode f.bal - decode f.balCommit)
    (hsum : a.nty = [0x24] → decode f.bal + decode f.balCommit ≤ maxBalance)
    (hnty3 : a.nty = [0x20] ∨ a.nty = [0x22] ∨ a.nty = [0x24])
    (h : settleOuts f a ++ a.chg = serTxOut ⟨amt, lockScript g⟩ ++ r) : False := by
  by_cases h20 : a.nty = [0x20]
  · rw [show settleOuts f a = settleOuts_20 f a from by unfold settleOuts; rw [ite_eq_left h20]] at h
    rw [settleOuts_20_eq hwf hsc, tokenOut_eq (settleFieldsT_wf hwf ha) hval] at h
    have := congrArg Fields.ty (lock_of_serTxOut_prefix (settleFieldsT_wf hwf ha) hg h)
    rw [hgty] at this; simp [settleFieldsT] at this
  by_cases h22 : a.nty = [0x22]
  · have hlenA : (padN 16 (encode (decode f.bal - decode f.balCommit))).length = 16 :=
      padN16_length_of_range (hrem h22) (by have := hbc (by rw [h22]; decide); omega)
    rw [show settleOuts f a = settleOuts_22 f a from by unfold settleOuts; rw [ite_eq_right h20, ite_eq_left h22]] at h
    unfold settleOuts_22 at h
    split_ifs at h
    · rw [splitOutA_eq hwf hsc, tokenOut_eq (splitFieldsA_wf hwf ha hlenA) hval, List.append_assoc] at h
      have := congrArg Fields.ty (lock_of_serTxOut_prefix (splitFieldsA_wf hwf ha hlenA) hg h)
      rw [hgty] at this; simp [splitFieldsA] at this
    · rw [splitOutB_eq hwf hsc hlenA, tokenOut_eq (splitFieldsB_wf hwf ha) hval, List.append_assoc] at h
      have := congrArg Fields.ty (lock_of_serTxOut_prefix (splitFieldsB_wf hwf ha) hg h)
      rw [hgty] at this; simp [splitFieldsB] at this
  · rw [show settleOuts f a = settleOuts_24 f a from by unfold settleOuts; rw [ite_eq_right h20, ite_eq_right h22]] at h
    have h24 : a.nty = [0x24] := by
      rcases hnty3 with h' | h' | h'
      · exact absurd h' h20
      · exact absurd h' h22
      · exact h'
    have hlenM : (padN 16 (encode (decode f.bal + decode f.balCommit))).length = 16 :=
      padN16_length_of_range (by have := hbc (by rw [h24]; decide); omega) (hsum h24)
    rw [settleOuts_24_eq hwf hsc, tokenOut_eq (mergeFieldsS_wf hwf ha hlenM) hval] at h
    have := congrArg Fields.ty (lock_of_serTxOut_prefix (mergeFieldsS_wf hwf ha hlenM) hg h)
    rw [hgty] at this; simp [mergeFieldsS] at this

/-- A commit's next type is a commit type. -/
theorem commit_nty_of {nty : Bytes} (hnty : SmbType nty) (h : ¬ (nty = [0x20] ∨ nty = [0x22] ∨ nty = [0x24])) :
    nty = [0x21] ∨ nty = [0x23] ∨ nty = [0x25] := by
  rcases hnty with g | g | g | g | g | g <;> simp_all

/-- A settle's next type is a settled type. -/
theorem settle_nty_of {fty nty : Bytes} (hty : SmbType fty) (hnty : SmbType nty)
    (hset : ¬ (fty = [0x20] ∨ fty = [0x22] ∨ fty = [0x24])) (hrel : fty.headD 0 = nty.headD 0 + 1) :
    nty = [0x20] ∨ nty = [0x22] ∨ nty = [0x24] := by
  rcases hty with h | h | h | h | h | h <;> rcases hnty with g | g | g | g | g | g <;> simp_all

/-- **The second token input took the merge path.** With a preimage, at an input whose outpoint is not the
first's, and with both runs welded to one `hashOutputs`, the second token input's spent token is settle-typed and
its run is the merge commit's second-input path (`inputIndexN` non-zero), which builds the merged token from the
interop arguments: any settle path's first output has a settled type, a transfer or split commit's has its own
type, and the merge's first-input path would name its own outpoint as the merged token's parent. -/
theorem other_merge_path {env : Env} {f f' : Fields} {a a' : Args} {S' : List Bytes} {cs' : Bytes}
    (hwf : WF f) (ha : ArgsWF a) (hsc : sc a.pre = lockScript f) {amt : Nat} (hval : preValue a.pre = le64 amt)
    (hnty : a.nty = [0x25]) (hidx : decode a.inIdx = 0)
    (hwf' : WF f') (ha' : ArgsWF a') (hsc' : sc a'.pre = lockScript f') {amt' : Nat}
    (hval' : preValue a'.pre = le64 amt')
    (hse' : SpendEnforced env f' a' S' cs') (hpre' : castToBool a'.pre = true)
    (hty' : SmbType f'.ty) (hnty' : SmbType a'.nty)
    (hpar1' : (f'.ty = [0x20] ∨ f'.ty = [0x22] ∨ f'.ty = [0x24]) → ¬ (a'.nty = [0x20] ∨ a'.nty = [0x22] ∨ a'.nty = [0x24]))
    (hpar2' : ¬ (f'.ty = [0x20] ∨ f'.ty = [0x22] ∨ f'.ty = [0x24]) → f'.ty.headD 0 = a'.nty.headD 0 + 1)
    (hdis : preOutpoint a.pre ≠ preOutpoint a'.pre)
    {X : Bytes} (hX : ∀ y, Hash.hash256 y = Hash.hash256 X → y = X)
    (hflat : expectedOuts a ++ a.chg = X) (hh' : preHashOutputs a'.pre = Hash.hash256 X) :
    settledTy f'.ty ∧ a'.nty = [0x25] ∧ ¬ decode a'.inIdx = 0 ∧ Enforced env f' a' cs' := by
  have hg := commitFields_wf hwf ha (Or.inr (Or.inr hnty)) (ha.nbc (Or.inr hnty)) (zeros_length 20) (ha.i1 hnty) (a := a)
  rw [commitOuts_merge0 hwf ha hsc hval hnty hidx, List.append_assoc] at hflat
  by_cases hset' : settledTy f'.ty
  · have hset'' : f'.ty = [0x20] ∨ f'.ty = [0x22] ∨ f'.ty = [0x24] := hset'
    have henf' : Enforced env f' a' cs' := by
      have h := hse'; simp only [SpendEnforced, hpre', ↓reduceIte] at h; rw [ite_eq_left hset''] at h; exact h
    have hflat' : expectedOuts a' ++ a'.chg = X := hX _ (by rw [henf'.outputs, hh'])
    rw [← hflat] at hflat'
    have hnt := commit_nty_of hnty' (hpar1' hset'')
    rcases hnt with h21 | h23 | h25
    · rw [commitOuts_transfer hwf' ha' hsc' hval' h21, List.append_assoc] at hflat'
      have := congrArg Fields.ty (lock_of_serTxOut_prefix
        (commitFields_wf hwf' ha' (Or.inl h21) (zeros_length 16) (zeros_length 20) (zeros_length 36)) hg hflat')
      simp [commitFields, h21, hnty] at this
    · rw [commitOuts_split hwf' ha' hsc' hval' h23, List.append_assoc, List.append_assoc] at hflat'
      have := congrArg Fields.ty (lock_of_serTxOut_prefix
        (commitFields_wf hwf' ha' (Or.inr (Or.inl h23)) (ha'.nbc (Or.inl h23)) (ha'.pkh2 h23) (zeros_length 36)) hg
        hflat')
      simp [commitFields, h23, hnty] at this
    · by_cases hi' : decode a'.inIdx = 0
      · rw [commitOuts_merge0 hwf' ha' hsc' hval' h25 hi', List.append_assoc] at hflat'
        have := congrArg Fields.parent (lock_of_serTxOut_prefix
          (commitFields_wf hwf' ha' (Or.inr (Or.inr h25)) (ha'.nbc (Or.inr h25)) (zeros_length 20) (ha'.i1 h25)) hg
          hflat')
        simp only [commitFields] at this
        exact absurd this.symm hdis
      · exact ⟨hset', h25, hi', henf'⟩
  · obtain ⟨hout', hbal', hbal2', hbc', hrem', hsum'⟩ := settle_outputs_of hse' hpre' hset'
    have hflat' : settleOuts f' a' ++ a'.chg = X := hX _ (by rw [hout', hh'])
    rw [← hflat] at hflat'
    have hset'' : ¬ (f'.ty = [0x20] ∨ f'.ty = [0x22] ∨ f'.ty = [0x24]) := hset'
    have hrel := hpar2' hset''
    have hnty3 := settle_nty_of hty' hnty' hset'' hrel
    exact (settle_first_not_merge hwf' ha' hsc' hval' hg (by simp [commitFields, hnty]) ⟨hbal', hbal2'⟩ hbc' hrem'
      hsum' hnty3 hflat').elim

end BoltProof.Glue.SimpleMulti
