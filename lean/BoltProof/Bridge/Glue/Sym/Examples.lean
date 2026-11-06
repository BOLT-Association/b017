import BoltProof.Bridge.Glue.Sym.Tactic
import BoltProof.Bridge.Generated.Chunks

/-!
# The drivers at work

Small runs that show the shape of a block proof: a straight-line fragment, a push read off the
program, a real chunk of the shipped `MinSimpleBOLT` suffix, and a conditional taken both ways.
They are checked on every build; a change to the step lemmas or the drivers that breaks the
pattern shows up here first.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace BoltProof.Glue

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- `OP_DUP OP_SWAP OP_CAT` doubles the top: `x :: y :: S` becomes `(x ++ x) :: y :: S`. -/
example {env : Env} {k t : Bytes} {r : GOut} {x y : Bytes} {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat}
    (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env ([Op.OP_DUP, Op.OP_SWAP, Op.OP_CAT] ++ k) t (St (x :: y :: S) A m C kk cs) = r)
    (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St ((x ++ x) :: y :: S) A m' C k' cs) = r := by
  simp only [List.cons_append, List.nil_append] at h
  sym_run h
  exact ⟨_, _, h⟩

/-- A two-byte push read off the program, then `OP_1 OP_PICK`. -/
example {env : Env} {k t : Bytes} {r : GOut} {y : Bytes} {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat}
    (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env ([2, 0xab, 0xcd, 0x51, Op.OP_PICK] ++ k) t (St (y :: S) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (y :: [0xab, 0xcd] :: y :: S) A m' C k' cs) = r := by
  simp only [List.cons_append, List.nil_append] at h
  sym_run h
  exact ⟨_, _, h⟩

/-- The first chunk of the `MinSimpleBOLT` suffix, `2 PICK BIN2NUM NOT SWAP 2SWAP`, from the six lock
pushes: `isGen := parent = 0` computed and the grandparent brought to the top. -/
example {env : Env} {k t : Bytes} {r : GOut} {issuer gp parent ty com pkh : Bytes} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat}
    (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env (MinSimple.c0 ++ k) t
      (St (issuer :: gp :: parent :: ty :: com :: pkh :: S) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t
      (St (gp :: parent :: issuer :: encode (if decode parent = 0 then 1 else 0) :: ty :: com :: pkh :: S)
        A m' C k' cs) = r := by
  simp only [MinSimple.c0, List.cons_append, List.nil_append] at h
  sym_run h
  exact ⟨_, _, h⟩

/-- The `MinSimpleBOLT` issuer guard `OP_IF 3 PICK 10 PICK OP_EQUALVERIFY OP_ENDIF` (chunks 3–5), from
the stack the prologue leaves it: taken, it forces the signing key to be the issuer; skipped, it
changes nothing; either way the stack below the condition is untouched. -/
example {env : Env} {k t : Bytes} {r : GOut} {c hasGp gp parent issuer isGen ty com pkh pre pk : Bytes}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat}
    (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env (MinSimple.c18_if ++ (MinSimple.c19 ++ (MinSimple.c24_endif ++ k))) t
      (St (c :: hasGp :: gp :: parent :: issuer :: isGen :: ty :: com :: pkh :: pre :: pk :: S) A m C kk cs) = r)
    (hr : r.IsOk) :
    (castToBool c = true → issuer = pk) ∧
      ∃ m' k', run Eval.opExec env k t
        (St (hasGp :: gp :: parent :: issuer :: isGen :: ty :: com :: pkh :: pre :: pk :: S) A m' C k' cs) = r := by
  simp only [MinSimple.c18_if, MinSimple.c19, MinSimple.c24_endif, List.cons_append,
    List.nil_append] at h
  sym_run h
  rcases hc : castToBool c with _ | _
  · simp only [hc] at h
    have hin : (C.opIf false).isActive = false := by simp
    sym_skip h
    sym_run h
    exact ⟨fun h1 => by simp at h1, _, _, h⟩
  · simp only [hc] at h
    have hact : (C.opIf true).isActive = true := by simp [hact]
    sym_run h
    exact ⟨fun _ => by assumption, _, _, h⟩

end BoltProof.Glue
