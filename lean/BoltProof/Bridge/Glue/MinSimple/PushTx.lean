import BoltProof.Bridge.Glue.MinSimple.Spec

/-!
# The `OP_PUSH_TX` block and the offsets the path proofs stop at

The lock's own `OP_PUSH_TX` block (suffix 29–413) assembles a signature from the hash of the
preimage and checks it with `OP_CHECKSIGVERIFY`. Run symbolically, the signature is a term of
half a megabyte; the path proofs never carry it. Instead, when the symbolic run reaches the block,
they record that the block ran to its end from that stack (`PushTxReached`, via the library's
`run_append` and the block being framed) and continue with `pushTx_shape`, which says the block
leaves the stack, the alt stack, the tracker and the code separator as it found them. The
symbolic run inside `pushTx_shape` is the only place the block's facts exist, and they are
discarded there.

The two `suffix_drop_*` identities are how a path proof turns the program it holds at offset 534
or 1072 into the `suffix.drop off ++ k` that `Reaches` names.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.MinSimple

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- The block is framed: every push's data lies inside it (`decide` on the 385-byte literal). -/
theorem pushTxBlock_framed : framed pushTxBlock = true := by decide +kernel

/-- The block as the chunked suffix holds it. -/
theorem pushTxBlock_eq (R : Bytes) :
    MinSimple.c29 ++ (MinSimple.c150 ++ (MinSimple.c271 ++ R)) = pushTxBlock ++ R := by
  simp only [pushTxBlock, List.append_assoc]

/-- A framed prefix of a run that did not fail did not fail either (`run_append` read backwards). -/
theorem reached_of_append {env : Env} {g k t : Bytes} {st : State} {r : GOut} (hf : framed g = true)
    (h : run Eval.opExec env (g ++ k) t st = r) (hr : r.IsOk) :
    ∃ r', run Eval.opExec env g (k ++ t) st = r' ∧ r'.IsOk := by
  rw [run_append _ _ _ _ _ _ hf] at h
  rcases hg : run Eval.opExec env g (k ++ t) st with st' | st' | ⟨e, st'⟩ | ⟨f, st'⟩ | ⟨o, st'⟩
  · exact ⟨_, rfl, trivial⟩
  · exact ⟨_, rfl, trivial⟩
  all_goals (rw [hg] at h; simp only [GOut.andThen] at h; subst h; simp at hr)

/-- The block leaves the stack as it found it: it works on a copy of the preimage and the
`OP_CHECKSIGVERIFY` consumes the signature and key it built; the `0x41` it parks on the alt stack
comes back before the end. -/
theorem pushTx_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {pre : Bytes}
    {X A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (pushTxBlock ++ k) t (St (pre :: X) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (pre :: X) A m' C k' cs) = r := by
  simp only [pushTxBlock, MinSimple.c29, MinSimple.c150, MinSimple.c271, List.cons_append,
    List.append_assoc] at h
  sym_run h
  exact ⟨_, _, h⟩

/-- The suffix from the NFT type selector on, as the path proofs hold it. -/
theorem suffix_drop_534_append (k : Bytes) :
    MinSimple.suffix.drop 534 ++ k = MinSimple.c534_nftTypeSel17 ++ (MinSimple.c547 ++ (MinSimple.c559_if ++ (MinSimple.c560 ++ (MinSimple.c566_else ++ (MinSimple.c567 ++ (MinSimple.c569_endif ++ (MinSimple.c570 ++ (MinSimple.c589_notif ++ (MinSimple.c590 ++ (MinSimple.c592_else ++ (MinSimple.c593 ++ (MinSimple.c594_endif ++ (MinSimple.c595 ++ (MinSimple.c613_if ++ (MinSimple.c614 ++ (MinSimple.c774 ++ (MinSimple.c966 ++ (MinSimple.c968_else ++ (MinSimple.c969 ++ (MinSimple.c1072_nullTail ++ (MinSimple.c1076_endif ++ (MinSimple.c1077 ++ (MinSimple.c1103_else ++ (MinSimple.c1104 ++ (MinSimple.c1119_endif ++ (MinSimple.c1120 ++ (k))))))))))))))))))))))))))) := by
  have : MinSimple.suffix.drop 534 = MinSimple.c534_nftTypeSel17 ++ (MinSimple.c547 ++ (MinSimple.c559_if ++ (MinSimple.c560 ++ (MinSimple.c566_else ++ (MinSimple.c567 ++ (MinSimple.c569_endif ++ (MinSimple.c570 ++ (MinSimple.c589_notif ++ (MinSimple.c590 ++ (MinSimple.c592_else ++ (MinSimple.c593 ++ (MinSimple.c594_endif ++ (MinSimple.c595 ++ (MinSimple.c613_if ++ (MinSimple.c614 ++ (MinSimple.c774 ++ (MinSimple.c966 ++ (MinSimple.c968_else ++ (MinSimple.c969 ++ (MinSimple.c1072_nullTail ++ (MinSimple.c1076_endif ++ (MinSimple.c1077 ++ (MinSimple.c1103_else ++ (MinSimple.c1104 ++ (MinSimple.c1119_endif ++ (MinSimple.c1120)))))))))))))))))))))))))) := by decide +kernel
  rw [this]; simp only [List.append_assoc]

/-- The suffix from the null-ancestor tail on, as the path proofs hold it. -/
theorem suffix_drop_1072_append (k : Bytes) :
    MinSimple.suffix.drop 1072 ++ k = MinSimple.c1072_nullTail ++ (MinSimple.c1076_endif ++ (MinSimple.c1077 ++ (MinSimple.c1103_else ++ (MinSimple.c1104 ++ (MinSimple.c1119_endif ++ (MinSimple.c1120 ++ (k))))))) := by
  have : MinSimple.suffix.drop 1072 = MinSimple.c1072_nullTail ++ (MinSimple.c1076_endif ++ (MinSimple.c1077 ++ (MinSimple.c1103_else ++ (MinSimple.c1104 ++ (MinSimple.c1119_endif ++ (MinSimple.c1120)))))) := by decide +kernel
  rw [this]; simp only [List.append_assoc]

end BoltProof.Glue.MinSimple
