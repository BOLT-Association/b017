import BoltProof.Bridge.Glue.SerialBolt.Spec
import BoltProof.Bridge.Glue.MinSimple.PushTx

/-!
# The `OP_PUSH_TX` block and the offsets the `SerialBOLT` path proofs stop at

`SerialBOLT`'s `OP_PUSH_TX` block (suffix 62–446) is byte for byte `MinSimpleBOLT`'s (`pushTxBlock_same`), so its
framing and its shape lemma are `MinSimple`'s. The two `suffix_drop_*` identities turn the program a path proof
holds at the type selector (589) or the null-ancestor tail (1232) into the `suffix.drop off ++ k` that `Reaches`
names.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SerialBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (reached_of_append)

/-- The block is `MinSimpleBOLT`'s. -/
theorem pushTxBlock_same : pushTxBlock = MinSimple.pushTxBlock := by decide +kernel

theorem pushTxBlock_framed : framed pushTxBlock = true := by
  rw [pushTxBlock_same]; exact MinSimple.pushTxBlock_framed

/-- The block as the chunked suffix holds it. -/
theorem pushTxBlock_eq (R : Bytes) :
    SerialBolt.c62 ++ (SerialBolt.c183 ++ (SerialBolt.c304 ++ R)) = pushTxBlock ++ R := by
  simp only [pushTxBlock, List.append_assoc]

/-- The block leaves the stack as it found it (`MinSimple.pushTx_shape`). -/
theorem pushTx_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {pre : Bytes}
    {X A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (pushTxBlock ++ k) t (St (pre :: X) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (pre :: X) A m' C k' cs) = r := by
  rw [pushTxBlock_same] at h
  exact MinSimple.pushTx_shape he hact h hr

/-- The suffix from the NFT type selector on, as the path proofs hold it. -/
theorem suffix_drop_589_append (k : Bytes) :
    SerialBolt.suffix.drop 589 ++ k = SerialBolt.c589_nftTypeSel18 ++ (SerialBolt.c602 ++ (SerialBolt.c614_if ++ (SerialBolt.c615 ++ (SerialBolt.c621_else ++ (SerialBolt.c622 ++ (SerialBolt.c624_endif ++ (SerialBolt.c625 ++ (SerialBolt.c634_if ++ (SerialBolt.c635 ++ (SerialBolt.c641_endif ++ (SerialBolt.c642 ++ (SerialBolt.c662_notif ++ (SerialBolt.c663 ++ (SerialBolt.c665_else ++ (SerialBolt.c666 ++ (SerialBolt.c667_endif ++ (SerialBolt.c668 ++ (SerialBolt.c686_if ++ (SerialBolt.c687 ++ (SerialBolt.c806_notif ++ (SerialBolt.c807 ++ (SerialBolt.c815_endif ++ (SerialBolt.c816 ++ (SerialBolt.c822_if ++ (SerialBolt.c823 ++ (SerialBolt.c827_if ++ (SerialBolt.c828_else ++ (SerialBolt.c829 ++ (SerialBolt.c834_if ++ (SerialBolt.c835 ++ (SerialBolt.c839_else ++ (SerialBolt.c840 ++ (SerialBolt.c846_if ++ (SerialBolt.c847 ++ (SerialBolt.c851_else ++ (SerialBolt.c852 ++ (SerialBolt.c856_endif ++ (SerialBolt.c857_endif ++ (SerialBolt.c858 ++ (SerialBolt.c865_endif ++ (SerialBolt.c866 ++ (SerialBolt.c868_else ++ (SerialBolt.c869 ++ (SerialBolt.c872_endif ++ (SerialBolt.c873 ++ (SerialBolt.c1054 ++ (SerialBolt.c1124_else ++ (SerialBolt.c1125 ++ (SerialBolt.c1232_nullTail ++ (SerialBolt.c1236_endif ++ (SerialBolt.c1237 ++ (SerialBolt.c1263_else ++ (SerialBolt.c1264 ++ (SerialBolt.c1279_endif ++ (SerialBolt.c1280 ++ (k)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  have : SerialBolt.suffix.drop 589 = SerialBolt.c589_nftTypeSel18 ++ (SerialBolt.c602 ++ (SerialBolt.c614_if ++ (SerialBolt.c615 ++ (SerialBolt.c621_else ++ (SerialBolt.c622 ++ (SerialBolt.c624_endif ++ (SerialBolt.c625 ++ (SerialBolt.c634_if ++ (SerialBolt.c635 ++ (SerialBolt.c641_endif ++ (SerialBolt.c642 ++ (SerialBolt.c662_notif ++ (SerialBolt.c663 ++ (SerialBolt.c665_else ++ (SerialBolt.c666 ++ (SerialBolt.c667_endif ++ (SerialBolt.c668 ++ (SerialBolt.c686_if ++ (SerialBolt.c687 ++ (SerialBolt.c806_notif ++ (SerialBolt.c807 ++ (SerialBolt.c815_endif ++ (SerialBolt.c816 ++ (SerialBolt.c822_if ++ (SerialBolt.c823 ++ (SerialBolt.c827_if ++ (SerialBolt.c828_else ++ (SerialBolt.c829 ++ (SerialBolt.c834_if ++ (SerialBolt.c835 ++ (SerialBolt.c839_else ++ (SerialBolt.c840 ++ (SerialBolt.c846_if ++ (SerialBolt.c847 ++ (SerialBolt.c851_else ++ (SerialBolt.c852 ++ (SerialBolt.c856_endif ++ (SerialBolt.c857_endif ++ (SerialBolt.c858 ++ (SerialBolt.c865_endif ++ (SerialBolt.c866 ++ (SerialBolt.c868_else ++ (SerialBolt.c869 ++ (SerialBolt.c872_endif ++ (SerialBolt.c873 ++ (SerialBolt.c1054 ++ (SerialBolt.c1124_else ++ (SerialBolt.c1125 ++ (SerialBolt.c1232_nullTail ++ (SerialBolt.c1236_endif ++ (SerialBolt.c1237 ++ (SerialBolt.c1263_else ++ (SerialBolt.c1264 ++ (SerialBolt.c1279_endif ++ (SerialBolt.c1280))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by decide +kernel
  rw [this]; simp only [List.append_assoc]

/-- The suffix from the null-ancestor tail on. -/
theorem suffix_drop_1232_append (k : Bytes) :
    SerialBolt.suffix.drop 1232 ++ k = SerialBolt.c1232_nullTail ++ (SerialBolt.c1236_endif ++ (SerialBolt.c1237 ++ (SerialBolt.c1263_else ++ (SerialBolt.c1264 ++ (SerialBolt.c1279_endif ++ (SerialBolt.c1280 ++ (k))))))) := by
  have : SerialBolt.suffix.drop 1232 = SerialBolt.c1232_nullTail ++ (SerialBolt.c1236_endif ++ (SerialBolt.c1237 ++ (SerialBolt.c1263_else ++ (SerialBolt.c1264 ++ (SerialBolt.c1279_endif ++ (SerialBolt.c1280)))))) := by decide +kernel
  rw [this]; simp only [List.append_assoc]

end BoltProof.Glue.SerialBolt
