import BoltProof.Bridge.Glue.SimpleMulti.Spec
import BoltProof.Bridge.Glue.MinSimple.PushTx

/-!
# The fungible lock's `OP_PUSH_TX` block

As for the NFT family (`MinSimple/PushTx.lean`): the block is framed, the path proofs record that
it ran (`PushTxReached`, through `reached_of_append`), and `pushTx_shape` says it leaves the stack as
it found it.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

theorem pushTxBlock_framed : framed pushTxBlock = true := by decide +kernel

theorem pushTxBlock_eq (R : Bytes) :
    SimpleMulti.c38 ++ (SimpleMulti.c159 ++ (SimpleMulti.c280 ++ R)) = pushTxBlock ++ R := by
  simp only [pushTxBlock, List.append_assoc]

/-- The block works on a copy of the preimage and consumes what it builds. -/
theorem pushTx_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {pre : Bytes}
    {X A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (pushTxBlock ++ k) t (St (pre :: X) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (pre :: X) A m' C k' cs) = r := by
  simp only [pushTxBlock, SimpleMulti.c38, SimpleMulti.c159, SimpleMulti.c280, List.cons_append,
    List.append_assoc] at h
  sym_run h
  exact ⟨_, _, h⟩

end BoltProof.Glue.SimpleMulti
