import BoltProof.Bridge.Glue.Sym.Basic

/-!
# Skipping an inactive branch

Inside a branch the conditional tracker marks inactive, the loop parses every instruction, counts
the opcodes, and executes nothing but the flow opcodes, which only move the tracker. The flow
opcodes' inactive readings are here; the non-flow opcodes' are generated (`Sym/SkipSteps.lean`).
`sym_skip` (`Sym/Tactic.lean`) walks a skipped arm with them, instruction by instruction, and the
tracker algebra of `Sym/Basic.lean` (`opEndif_opIf`, `opEndif_opElse_opIf`) folds the arm's
conditionals away, so a balanced arm leaves the stack, the alt stack, the memory counter and the
tracker exactly as they were.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoltProof.Glue

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-! ## One inactive instruction, read backwards -/

/-- An inactive `OP_IF`/`OP_NOTIF`: a false condition pushed, nothing popped. -/
theorem inv_skip_if {env : Env} (he : EnvOK env) {op : Nat} {rest t : Bytes} {r : GOut} {S A : List Bytes}
    {D : Cond} {cs : Bytes} {m k : Nat} (hop : op = Op.OP_IF ∨ op = Op.OP_NOTIF) (hin : D.isActive = false)
    (h : run Eval.opExec env (op :: rest) t (St S A m D k cs) = r) (hr : r.IsOk) :
    ∃ k', run Eval.opExec env rest t (St S A m (D.opIf false) k' cs) = r := by
  obtain ⟨hgen, hera, hmin, hminif, hfork, hcs⟩ := he
  rcases hop with rfl | rfl <;> rw [run.eq_2] at h <;> inv_simp at h <;> inv_split h <;>
    first | exact ⟨_, h⟩ | (subst h; simp at hr)

/-- `OP_ELSE` in an inactive branch: the innermost condition, which must not have seen an else,
flipped. -/
theorem inv_skip_else {env : Env} (he : EnvOK env) {rest t : Bytes} {r : GOut} {S A : List Bytes}
    {D : Cond} {cs : Bytes} {m k : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (Op.OP_ELSE :: rest) t (St S A m D k cs) = r) (hr : r.IsOk) :
    D.empty = false ∧ D.hasOpElse = false ∧ ∃ k', run Eval.opExec env rest t (St S A m D.opElse k' cs) = r := by
  obtain ⟨hgen, hera, hmin, hminif, hfork, hcs⟩ := he
  rw [run.eq_2] at h
  inv_simp at h
  inv_split h
  all_goals first
    | (subst h; simp at hr)
    | (refine ⟨?_, ?_, _, h⟩ <;> simp_all)

/-- `OP_ENDIF` in an inactive branch: the innermost condition, which must exist, closed. -/
theorem inv_skip_endif {env : Env} (he : EnvOK env) {rest t : Bytes} {r : GOut} {S A : List Bytes}
    {D : Cond} {cs : Bytes} {m k : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (Op.OP_ENDIF :: rest) t (St S A m D k cs) = r) (hr : r.IsOk) :
    D.empty = false ∧ ∃ k', run Eval.opExec env rest t (St S A m D.opEndif k' cs) = r := by
  obtain ⟨hgen, hera, hmin, hminif, hfork, hcs⟩ := he
  rw [run.eq_2] at h
  inv_simp at h
  inv_split h
  all_goals first
    | (subst h; simp at hr)
    | (refine ⟨?_, _, h⟩ <;> simp_all)

end BoltProof.Glue
