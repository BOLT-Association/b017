import BoltProof.Bridge.Glue.Sym.Basic
import BoltProof.Bridge.Params

/-!
# From a valid verdict to a run of the lock

`Eval.verifyScript` is the two-phase spend: the unlocking script on an empty stack, then the
locking script on the stack it left, and the top of the final stack must be true. `run_of_valid`
reads the second phase off a `.valid` verdict as a `Gadget.run` of the lock from some stack, in
the state `evalScript` starts from (`codeSep` the lock itself, the tracker empty), that ends in
`.next` or `.stop` with a true top. `envOK_phase2` says the environment that phase runs in, under
the post-Chronicle mainnet parameters Layer 2 judges every vector at (`Bridge/Params.lean`),
satisfies every fact the symbolic run relies on, whatever the transaction's version.
-/

set_option autoImplicit false

namespace BoltProof.Glue

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge

/-- The environment the locking script runs in under the judging parameters. -/
abbrev phase2Env (ctx : Context) : Env := mkEnv params ctx params.flags.forkAdjust none

/-- The judging parameters put the locking phase under `EnvOK`, for every transaction version:
the gate (`Flags.gate`) only ever clears flags, and the block word carries neither MINIMALDATA
nor MINIMALIF. -/
theorem envOK_phase2 (ctx : Context) : EnvOK (phase2Env ctx) := by
  have hmd : params.flags.forkAdjust.minimalData = false := by decide
  have hmi : params.flags.forkAdjust.minimalIf = false := by decide
  have hfk : params.flags.forkAdjust.enableSighashForkid = true := by decide
  have hera : params.flags.forkAdjust.utxoEra = Era.postChronicle := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phase2Env, mkEnv, Env.utxoAfterGenesis, hera]
  · simp only [phase2Env, mkEnv, hera]
  · simp only [phase2Env, mkEnv, Flags.gate]
    split_ifs <;> simp [hmd]
  · simp only [phase2Env, mkEnv, Flags.gate]
    split_ifs <;> simp [hmi]
  · simp only [phase2Env, mkEnv, Flags.gate]
    split_ifs <;> simp [hfk]
  · rfl

/-- A `.valid` verdict is a run of the locking script, from the stack and memory counter the
unlocking script left (`st1`, the state of the first phase), that does not fail and ends with a
true top. -/
theorem run_of_valid {ctx : Context} {scriptSig lock : Bytes}
    (hv : Eval.verifyScript params ctx scriptSig lock = .valid) :
    ∃ st1 : State, evalScript Eval.opExec (mkEnv params ctx params.flags.forkAdjust (some lock)) scriptSig [] 0 =
        (.ok, st1) ∧
      ∃ (st2 : State) (top : Bytes) (rest : List Bytes),
        (run Eval.opExec (phase2Env ctx) lock [] (St st1.stack [] st1.memUsed {} 0 lock) = .next st2 ∨
          run Eval.opExec (phase2Env ctx) lock [] (St st1.stack [] st1.memUsed {} 0 lock) = .stop st2) ∧
        st2.stack = top :: rest ∧ castToBool top = true := by
  unfold Eval.verifyScript Machine.verifyScript at hv
  simp only [] at hv
  split_ifs at hv
  rcases h1 : evalScript Eval.opExec (mkEnv params ctx params.flags.forkAdjust (some lock)) scriptSig [] 0
    with ⟨o1, st1⟩
  simp only [h1] at hv
  cases o1 <;> simp only at hv <;> try cases hv
  unfold phase2 at hv
  simp only [] at hv
  rcases h2 : evalScript Eval.opExec (mkEnv params ctx params.flags.forkAdjust none) lock st1.stack st1.memUsed
    with ⟨o2, st2⟩
  simp only [h2] at hv
  cases o2 <;> simp only at hv <;> try cases hv
  rcases hs : st2.stack with _ | ⟨top, rest⟩
  · simp only [hs] at hv; cases hv
  simp only [hs] at hv
  by_cases hc : castToBool top = true
  · refine ⟨st1, rfl, st2, top, rest, ?_, hs, hc⟩
    unfold evalScript at h2
    simp only [] at h2
    split_ifs at h2 with hlen
    · simp at h2
    rw [loop_eq_run] at h2
    rcases hr : run Eval.opExec (mkEnv params ctx params.flags.forkAdjust none) lock [] (St st1.stack [] st1.memUsed {} 0 lock)
      with st' | st' | ⟨e, st'⟩ | ⟨f, st'⟩ | ⟨o, st'⟩
    · rw [hr] at h2; simp only [GOut.toLoop] at h2
      split_ifs at h2 with hce
      · simp only [Prod.mk.injEq] at h2
        exact Or.inl (by rw [h2.2])
      · simp at h2
    · rw [hr] at h2; simp only [GOut.toLoop, Prod.mk.injEq] at h2
      exact Or.inr (by rw [h2.2])
    all_goals (rw [hr] at h2; simp [GOut.toLoop] at h2)
  · have hf : castToBool top = false := by simpa using hc
    simp only [hf, Bool.not_false, ↓reduceIte] at hv
    cases hv

end BoltProof.Glue
