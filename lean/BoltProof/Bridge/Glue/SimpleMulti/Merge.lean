import BoltProof.Bridge.Glue.SimpleMulti.Outs

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

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (sc preOutpoint preValue proofScript)

/-- The merged token's fields as the second token input builds them. -/
def mergeFields1 (f : Fields) (a : Args) : Fields :=
  { bal := a.nbc, balCommit := f.bal, pkh := a.i3, com := a.pkh1, com2 := zeros 20, ogp := f.parent, ty := a.nty,
    outIdx := [0], parent := a.i2, gp := a.i1, issuer := f.issuer }

theorem mergeFields1_wf {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) : WF (mergeFields1 f a) :=
  ⟨ha.nbc, hwf.bal, ha.i3, ha.pkh1, zeros_length 20, hwf.parent, ha.nty, rfl, ha.i2, ha.i1, hwf.issuer⟩

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
    ite_eq_right hidx, mergeLock1_eq hwf hsc, tokenOut_eq (mergeFields1_wf hwf ha) hval, proofOut_eq ha.pkh1 hval]

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
  exact lock_of_serTxOut_prefix (commitFields_wf hwf ha ha.nbc (zeros_length 20) ha.i1) (mergeFields1_wf hwf' ha')
    hout

end BoltProof.Glue.SimpleMulti
