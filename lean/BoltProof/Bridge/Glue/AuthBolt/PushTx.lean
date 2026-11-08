import BoltProof.Bridge.Glue.AuthBolt.Spec
import BoltProof.Bridge.Glue.MinSimple.PushTx

/-!
# The `OP_PUSH_TX` block and the offsets the `AuthBOLT` path proofs stop at

`AuthBOLT`'s `OP_PUSH_TX` block (suffix 38–422) is byte for byte `MinSimpleBOLT`'s (`pushTxBlock_same`), so its
framing and its shape lemma are `MinSimple`'s. The two `suffix_drop_*` identities turn the program a path proof
holds at the type selector (543) or the null-ancestor tail (1094) into the `suffix.drop off ++ k` that `Reaches`
names.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.AuthBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (reached_of_append)

/-- The block is `MinSimpleBOLT`'s. -/
theorem pushTxBlock_same : pushTxBlock = MinSimple.pushTxBlock := by decide +kernel

theorem pushTxBlock_framed : framed pushTxBlock = true := by
  rw [pushTxBlock_same]; exact MinSimple.pushTxBlock_framed

/-- The block as the chunked suffix holds it. -/
theorem pushTxBlock_eq (R : Bytes) :
    AuthBolt.c38 ++ (AuthBolt.c159 ++ (AuthBolt.c280 ++ R)) = pushTxBlock ++ R := by
  simp only [pushTxBlock, List.append_assoc]

/-- The block leaves the stack as it found it (`MinSimple.pushTx_shape`). -/
theorem pushTx_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {pre : Bytes}
    {X A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (pushTxBlock ++ k) t (St (pre :: X) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (pre :: X) A m' C k' cs) = r := by
  rw [pushTxBlock_same] at h
  exact MinSimple.pushTx_shape he hact h hr

/-- The suffix from the NFT type selector on, as the path proofs hold it. -/
theorem suffix_drop_543_append (k : Bytes) :
    AuthBolt.suffix.drop 543 ++ k = AuthBolt.c543_nftTypeSel17 ++ (AuthBolt.c556 ++ (AuthBolt.c568_if ++ (AuthBolt.c569 ++ (AuthBolt.c575_else ++ (AuthBolt.c576 ++ (AuthBolt.c578_endif ++ (AuthBolt.c579 ++ (AuthBolt.c598_notif ++ (AuthBolt.c599 ++ (AuthBolt.c601_else ++ (AuthBolt.c602 ++ (AuthBolt.c603_endif ++ (AuthBolt.c604 ++ (AuthBolt.c622_if ++ (AuthBolt.c623 ++ (AuthBolt.c782 ++ (AuthBolt.c970 ++ (AuthBolt.c986_else ++ (AuthBolt.c987 ++ (AuthBolt.c1094_nullTail ++ (AuthBolt.c1098_endif ++ (AuthBolt.c1099 ++ (AuthBolt.c1125_else ++ (AuthBolt.c1126 ++ (AuthBolt.c1141_endif ++ (AuthBolt.c1142 ++ (k))))))))))))))))))))))))))) := by
  have : AuthBolt.suffix.drop 543 = AuthBolt.c543_nftTypeSel17 ++ (AuthBolt.c556 ++ (AuthBolt.c568_if ++ (AuthBolt.c569 ++ (AuthBolt.c575_else ++ (AuthBolt.c576 ++ (AuthBolt.c578_endif ++ (AuthBolt.c579 ++ (AuthBolt.c598_notif ++ (AuthBolt.c599 ++ (AuthBolt.c601_else ++ (AuthBolt.c602 ++ (AuthBolt.c603_endif ++ (AuthBolt.c604 ++ (AuthBolt.c622_if ++ (AuthBolt.c623 ++ (AuthBolt.c782 ++ (AuthBolt.c970 ++ (AuthBolt.c986_else ++ (AuthBolt.c987 ++ (AuthBolt.c1094_nullTail ++ (AuthBolt.c1098_endif ++ (AuthBolt.c1099 ++ (AuthBolt.c1125_else ++ (AuthBolt.c1126 ++ (AuthBolt.c1141_endif ++ (AuthBolt.c1142)))))))))))))))))))))))))) := by decide +kernel
  rw [this]; simp only [List.append_assoc]

/-- The suffix from the null-ancestor tail on. -/
theorem suffix_drop_1094_append (k : Bytes) :
    AuthBolt.suffix.drop 1094 ++ k = AuthBolt.c1094_nullTail ++ (AuthBolt.c1098_endif ++ (AuthBolt.c1099 ++ (AuthBolt.c1125_else ++ (AuthBolt.c1126 ++ (AuthBolt.c1141_endif ++ (AuthBolt.c1142 ++ (k))))))) := by
  have : AuthBolt.suffix.drop 1094 = AuthBolt.c1094_nullTail ++ (AuthBolt.c1098_endif ++ (AuthBolt.c1099 ++ (AuthBolt.c1125_else ++ (AuthBolt.c1126 ++ (AuthBolt.c1141_endif ++ (AuthBolt.c1142)))))) := by decide +kernel
  rw [this]; simp only [List.append_assoc]

end BoltProof.Glue.AuthBolt
