import BoltProof.Bridge.Glue.SimpleMulti.Residual

/-!
# `SimpleMultiBOLT`: the outputs, per path

From `hashOutputs` and the outputs' second-preimage resistance the serialised outputs are the covenant's expected
outputs followed by the change; peeling the serialised outputs off gives the model's `l2_outs` for each path.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (preOutpoint preValue proofScript)

/-- A well-formed fungible lock output is a token output of the model. -/
theorem outOf_lock {g : Fields} (hwf : WF g) (v : Nat) : outOf ⟨v, lockScript g⟩ = .token (tokenOf g) := by
  simp [outOf, decodeLock_lockScript hwf]

/-- A pay-to-proof output is a proof output of the model. -/
theorem outOf_proof {pkh : Bytes} (h : pkh.length = 20) (v : Nat) : outOf ⟨v, proofScript pkh⟩ = .proof pkh := by
  have hd : decodeLock (proofScript pkh) = none := by
    unfold decodeLock
    rw [ite_eq_right_iff.mpr]
    intro hc
    have := hc.1
    simp [proofScript, h, suffix_length] at this
  simp only [outOf, hd]
  simp [proofScript, h]

theorem lockScript_value_ok {g : Fields} (hwf : WF g) {amt : Nat} (hamt : amt < 2 ^ 64) :
    amt < 2 ^ 64 ∧ (lockScript g).length < 2 ^ 64 := ⟨hamt, by rw [lockScript_length_eq hwf]; decide⟩

theorem proofScript_value_ok {pkh : Bytes} (h : pkh.length = 20) {amt : Nat} (hamt : amt < 2 ^ 64) :
    amt < 2 ^ 64 ∧ (proofScript pkh).length < 2 ^ 64 := ⟨hamt, by simp [proofScript, h]⟩

/-- An in-range balance fills at most sixteen bytes, so its padded push is sixteen bytes. -/
theorem padN16_length_of_range {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ maxBalance) : (padN 16 (encode x)).length = 16 := by
  apply padN16_length
  rw [encode_length_le_iff_pow x 16 (by decide)]
  have hm : maxBalance = 2 ^ 127 - 1 := by decide
  omega

/-- A transfer commit's outputs, read by the model: the commit token, the proof output, then non-token change. -/
theorem outs_commit_transfer {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (other : Option (Fields × Outpoint Bytes))
    (ancA ancB : Option Tx) (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx) (hamt : amt < 2 ^ 64)
    (hpre : castToBool a.pre = true) (hset : settledTy f.ty) (hnty : a.nty = [0x21])
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : MinSimple.sc a.pre = lockScript f)
    (hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 2) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a other ancA ancB).expectedOuts .fungible ++ change := by
  have hcwf := commitFields_wf hwf ha (Or.inl hnty) (zeros_length 16) (zeros_length 20) (zeros_length 36) (a := a)
  rw [commitOuts_transfer hwf ha hsc hval hnty, List.append_assoc] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hcwf hamt) hflat.symm
  obtain ⟨os2, hos2, hf2⟩ := flatten_serTxOut_cons
    (fun o ho => htx.outputs o (by rw [hos1]; exact List.mem_cons_of_mem _ ho)) (proofScript_value_ok (ha.pkh1 (Or.inl hnty)) hamt) hf1
  refine ⟨os2.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1, hos2]; simpa using ho')
  · have hk : (spendOf tx i f a other ancA ancB).kind = .commit := kindOf_commit hpre hset
    have hm : (spendOf tx i f a other ancA ancB).mode = .transfer := by
      simp [spendOf, modeOf, kindOf_commit hpre hset, modeOfNext, hnty]
    simp only [absTx, hos1, hos2, List.map_cons, Spend.expectedOuts, hk, hm, outOf_lock hcwf, outOf_proof (ha.pkh1 (Or.inl hnty)),
      tokenOf_commit_transfer tx i other ancA ancB hpre hset hnty hout hnz h32 hidx]
    simp [spendOf]

/-- A split commit's outputs, read by the model: the commit token, the two proof outputs, then non-token change. -/
theorem outs_commit_split {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (other : Option (Fields × Outpoint Bytes))
    (ancA ancB : Option Tx) (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx) (hamt : amt < 2 ^ 64)
    (hpre : castToBool a.pre = true) (hset : settledTy f.ty) (hnty : a.nty = [0x23]) (hpkh2 : a.pkh2 ≠ zeroPKH)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : MinSimple.sc a.pre = lockScript f)
    (hflat : expectedOuts a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 3) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a other ancA ancB).expectedOuts .fungible ++ change := by
  have hcwf := commitFields_wf hwf ha (Or.inr (Or.inl hnty)) (ha.nbc (Or.inl hnty)) (ha.pkh2 hnty) (zeros_length 36) (a := a)
  have hp1 := ha.pkh1 (Or.inr (Or.inl hnty))
  have hp2 := ha.pkh2 hnty
  rw [commitOuts_split hwf ha hsc hval hnty, List.append_assoc, List.append_assoc] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hcwf hamt) hflat.symm
  obtain ⟨os2, hos2, hf2⟩ := flatten_serTxOut_cons
    (fun o ho => htx.outputs o (by rw [hos1]; exact List.mem_cons_of_mem _ ho)) (proofScript_value_ok hp1 hamt) hf1
  obtain ⟨os3, hos3, hf3⟩ := flatten_serTxOut_cons
    (fun o ho => htx.outputs o (by rw [hos1, hos2]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)))
    (proofScript_value_ok hp2 hamt) hf2
  refine ⟨os3.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1, hos2, hos3]; simpa using ho')
  · have hk : (spendOf tx i f a other ancA ancB).kind = .commit := kindOf_commit hpre hset
    have hm : (spendOf tx i f a other ancA ancB).mode = .split := by
      simp [spendOf, modeOf, kindOf_commit hpre hset, modeOfNext, hnty]
    simp only [absTx, hos1, hos2, hos3, List.map_cons, Spend.expectedOuts, hk, hm, outOf_lock hcwf,
      outOf_proof hp1, outOf_proof hp2, tokenOf_commit_split tx i other ancA ancB hpre hset hnty hout hnz h32 hidx]
    simp [spendOf, com2Of, hpkh2]

theorem settleFieldsT_wf {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) : WF (settleFieldsT f a) :=
  ⟨hwf.bal, zeros_length 16, hwf.com, zeros_length 20, zeros_length 20, zeros_length 36, rfl, rfl, ha.outpoint,
    hwf.parent, hwf.issuer⟩

theorem splitFieldsA_wf {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a)
    (hlen : (padN 16 (encode (decode f.bal - decode f.balCommit))).length = 16) : WF (splitFieldsA f a) := by
  constructor <;> simp only [splitFieldsA, settleFieldsT, hlen, zeros_length, hwf.com, hwf.parent, hwf.issuer,
    ha.outpoint, List.length_singleton]

theorem splitFieldsB_wf {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) : WF (splitFieldsB f a) := by
  constructor <;> simp only [splitFieldsB, settleFieldsT, hwf.balCommit, zeros_length, hwf.com2, hwf.parent,
    hwf.issuer, ha.outpoint, List.length_singleton]

/-- A transfer settle's outputs, read by the model: the settled token, then non-token change. -/
theorem outs_settle_transfer {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (other : Option (Fields × Outpoint Bytes))
    (ancA ancB : Option Tx) (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx) (hamt : amt < 2 ^ 64)
    (hpre : castToBool a.pre = true) (hty : f.ty = [0x21]) (hnty : a.nty = [0x20])
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : MinSimple.sc a.pre = lockScript f)
    (hflat : settleOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 1) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a other ancA ancB).expectedOuts .fungible ++ change := by
  have hswf := settleFieldsT_wf hwf ha (a := a)
  rw [settleOuts, ite_eq_left hnty, settleOuts_20_eq hwf hsc, tokenOut_eq hswf hval] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hswf hamt) hflat.symm
  refine ⟨os1.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1]; simpa using ho')
  · have hset : ¬ settledTy f.ty := by simp [settledTy, hty]
    have hk : (spendOf tx i f a other ancA ancB).kind = .settle := kindOf_settle hpre hset
    simp only [absTx, hos1, List.map_cons, Spend.expectedOuts, hk, outOf_lock hswf,
      tokenOf_settle_transfer tx i other ancA ancB hty hout hnz h32 hidx]
    simp [spendOf, tokenOf, hty, Fam.modeOfCommitType]

/-- A split settle's outputs with the honest flags, read by the model: the two settled tokens, then non-token
change. -/
theorem outs_settle_split {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (other : Option (Fields × Outpoint Bytes))
    (ancA ancB : Option Tx) (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx) (hamt : amt < 2 ^ 64)
    (hpre : castToBool a.pre = true) (hty : f.ty = [0x23]) (hnty : a.nty = [0x22])
    (hpk : decode a.pkh1 = 0) (hbc : 0 ≤ decode f.balCommit) (hrem : 0 ≤ decode f.bal - decode f.balCommit)
    (hbal : decode f.bal ≤ maxBalance) (hcom2 : f.com2 ≠ zeroPKH)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : MinSimple.sc a.pre = lockScript f)
    (hflat : settleOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 2) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a other ancA ancB).expectedOuts .fungible ++ change := by
  have hlen := padN16_length_of_range hrem (by omega)
  have hawf := splitFieldsA_wf hwf ha hlen (a := a)
  have hbwf := splitFieldsB_wf hwf ha (a := a)
  rw [settleOuts, ite_eq_right (by rw [hnty]; decide), ite_eq_left hnty, settleOuts_22, ite_eq_left hpk,
    splitOutA_eq hwf hsc, splitOutB_eq hwf hsc hlen, tokenOut_eq hawf hval, tokenOut_eq hbwf hval,
    List.append_assoc] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs (lockScript_value_ok hawf hamt) hflat.symm
  obtain ⟨os2, hos2, hf2⟩ := flatten_serTxOut_cons
    (fun o ho => htx.outputs o (by rw [hos1]; exact List.mem_cons_of_mem _ ho)) (lockScript_value_ok hbwf hamt) hf1
  refine ⟨os2.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1, hos2]; simpa using ho')
  · have hset : ¬ settledTy f.ty := by simp [settledTy, hty]
    have hk : (spendOf tx i f a other ancA ancB).kind = .settle := kindOf_settle hpre hset
    obtain ⟨hA, hB⟩ := tokenOf_settle_split tx i other ancA ancB hty hbc hrem hcom2 hout hnz h32 hidx (a := a)
    simp only [absTx, hos1, hos2, List.map_cons, Spend.expectedOuts, hk, outOf_lock hawf, outOf_lock hbwf, hA, hB]
    simp [spendOf, tokenOf, hty, Fam.modeOfCommitType]

end BoltProof.Glue.SimpleMulti
