import Lean
import BoltProof.Bridge.Glue.Sym.Steps
import BoltProof.Bridge.Glue.Sym.Skip
import BoltProof.Bridge.Glue.Sym.SkipSteps

/-!
# The driver: `sym_step` and `sym_run`

`sym_step h` reads the hypothesis `h : run Eval.opExec env (op :: g) t st = r`, looks the head
opcode up in `stepTable`, and replaces `h` by the inversion lemma's conclusion for `g`: the facts
the opcode checked become anonymous hypotheses, the new memory counter and opcode count become
fresh variables (the old ones are cleared), and the stack is normalised (`sym_norm`: pushes read
off the literal program, `PICK`/`ROLL` depths resolved on the literal stack, small script numbers
decoded). The lemma's `EnvOK` and activity hypotheses are the ones named `he` and `hact` in the
context, and the outcome hypothesis is `hr`; a block proof names them so.

`sym_run h` repeats `sym_step h` until it stops: at the end of the program, at an opcode outside
the table, or at a conditional (`OP_IF`/`OP_NOTIF` leave the tracker as `C.opIf b` with `b`
symbolic; the block proof then cases on `b`, restates `hact` for the branch it takes, and goes
on, or skips the inactive arm with `inv_skip_balanced`).
-/

set_option autoImplicit false

namespace BoltProof.Glue

open Lean Elab Tactic Meta
open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- How many leading facts an inversion lemma's conclusion carries before its `∃ m' k'`, and
whether it takes `hact`. -/
structure StepInfo where
  lemma_ : Name
  facts : Nat := 0
  needsAct : Bool := true
  /-- the conclusion is `∃ y, _ ∧ ∃ m' k', _` (`OP_NUM2BIN`) -/
  exists1 : Bool := false

/-- The opcode table: every opcode and push width the locks use. -/
def stepTable : List (Nat × StepInfo) :=
  [(0x00, { lemma_ := ``inv_push0 }),
   (1, { lemma_ := ``inv_push_1, facts := 1 }), (2, { lemma_ := ``inv_push_2, facts := 1 }),
   (3, { lemma_ := ``inv_push_3, facts := 1 }), (4, { lemma_ := ``inv_push_4, facts := 1 }),
   (8, { lemma_ := ``inv_push_8, facts := 1 }), (16, { lemma_ := ``inv_push_16, facts := 1 }),
   (20, { lemma_ := ``inv_push_20, facts := 1 }), (30, { lemma_ := ``inv_push_30, facts := 1 }),
   (33, { lemma_ := ``inv_push_33, facts := 1 }), (35, { lemma_ := ``inv_push_35, facts := 1 }),
   (36, { lemma_ := ``inv_push_36, facts := 1 }),
   (0x51, { lemma_ := ``inv_op1 }), (0x52, { lemma_ := ``inv_op2 }), (0x53, { lemma_ := ``inv_op3 }),
   (0x54, { lemma_ := ``inv_op4 }), (0x55, { lemma_ := ``inv_op5 }), (0x56, { lemma_ := ``inv_op6 }),
   (0x57, { lemma_ := ``inv_op7 }), (0x58, { lemma_ := ``inv_op8 }), (0x59, { lemma_ := ``inv_op9 }),
   (0x5a, { lemma_ := ``inv_op10 }), (0x5b, { lemma_ := ``inv_op11 }), (0x5c, { lemma_ := ``inv_op12 }),
   (0x5d, { lemma_ := ``inv_op13 }), (0x5e, { lemma_ := ``inv_op14 }), (0x5f, { lemma_ := ``inv_op15 }),
   (0x60, { lemma_ := ``inv_op16 }),
   (0x63, { lemma_ := ``inv_if }), (0x64, { lemma_ := ``inv_notif }),
   (0x67, { lemma_ := ``inv_else, needsAct := false }), (0x68, { lemma_ := ``inv_endif, needsAct := false }),
   (0x69, { lemma_ := ``inv_verify, facts := 1 }),
   (0x6b, { lemma_ := ``inv_toalt }), (0x6c, { lemma_ := ``inv_fromalt }),
   (0x6d, { lemma_ := ``inv_2drop }), (0x72, { lemma_ := ``inv_2swap }), (0x73, { lemma_ := ``inv_ifdup }),
   (0x75, { lemma_ := ``inv_drop }), (0x76, { lemma_ := ``inv_dup }), (0x77, { lemma_ := ``inv_nip }),
   (0x78, { lemma_ := ``inv_over }),
   (0x79, { lemma_ := ``inv_pick, facts := 2 }), (0x7a, { lemma_ := ``inv_roll, facts := 2 }),
   (0x7b, { lemma_ := ``inv_rot }), (0x7c, { lemma_ := ``inv_swap }), (0x7d, { lemma_ := ``inv_tuck }),
   (0x7e, { lemma_ := ``inv_cat }), (0x7f, { lemma_ := ``inv_split, facts := 2 }),
   (0x80, { lemma_ := ``inv_num2bin, exists1 := true }), (0x81, { lemma_ := ``inv_bin2num }),
   (0x82, { lemma_ := ``inv_size }),
   (0x87, { lemma_ := ``inv_equal }), (0x88, { lemma_ := ``inv_equalverify, facts := 1 }),
   (0x8b, { lemma_ := ``inv_1add }), (0x8c, { lemma_ := ``inv_1sub }),
   (0x91, { lemma_ := ``inv_not }), (0x92, { lemma_ := ``inv_0notequal }),
   (0x93, { lemma_ := ``inv_add }), (0x94, { lemma_ := ``inv_sub }), (0x97, { lemma_ := ``inv_mod, facts := 1 }),
   (0x9a, { lemma_ := ``inv_booland }), (0x9b, { lemma_ := ``inv_boolor }),
   (0x9f, { lemma_ := ``inv_lessthan }), (0xa1, { lemma_ := ``inv_lte }), (0xa2, { lemma_ := ``inv_gte }),
   (0xa8, { lemma_ := ``inv_sha256 }), (0xa9, { lemma_ := ``inv_hash160 }), (0xaa, { lemma_ := ``inv_hash256 }),
   (0xac, { lemma_ := ``inv_checksig, facts := 2 }), (0xad, { lemma_ := ``inv_checksigverify, facts := 3 })]

/-- The normalisation after a step: pushes read off the literal program, list indexing on the
literal stack, small script numbers, the conditional tracker's algebra. -/
syntax "sym_norm" " at " ident : tactic
macro_rules
  | `(tactic| sym_norm at $h:ident) =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.take_nil,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, List.drop_one, List.tail_cons,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none,
      List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.length_cons, List.length_nil,
      decode_lit, decode_encode, Int.toNat_natCast, Int.reduceToNat, Nat.cast_ofNat,
      opEndif_opIf, opEndif_opElse_opIf, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte,
      castToBool_one, castToBool_nil] at $h:ident)

/-- The head opcode of the program in `h : run _ _ (op :: g) _ _ = _`, as a `Nat`. -/
private def headOp (hType : Expr) : MetaM (Option Nat) := do
  let hType ← instantiateMVars hType
  let some (_, lhs, _) := hType.eq? | return none
  let fn := lhs.getAppFn
  unless fn.isConstOf ``BsvScript.Gadget.run do return none
  let args := lhs.getAppArgs
  unless args.size == 5 do return none
  let prog ← whnfR args[2]!
  unless prog.getAppFn.isConstOf ``List.cons do return none
  let pargs := prog.getAppArgs
  unless pargs.size == 3 do return none
  let op ← whnfD pargs[1]!
  Meta.evalNat op

/-- The `memUsed` and `opCount` fields of the state in `h`, when they are local variables. -/
private def stateVars (hType : Expr) : MetaM (Array FVarId) := do
  let hType ← instantiateMVars hType
  let some (_, lhs, _) := hType.eq? | return #[]
  let args := lhs.getAppArgs
  unless args.size == 5 do return #[]
  let st ← whnfR args[4]!
  let stArgs := st.getAppArgs
  -- `State.mk stack alt memUsed cond opCount nonTopLevelReturn codeSep`
  unless st.getAppFn.isConstOf ``BsvScript.Machine.State.mk && stArgs.size == 7 do return #[]
  let mut out := #[]
  for i in [2, 4] do
    if let .fvar id := stArgs[i]! then out := out.push id
  return out

/-- One inversion step on `h` (the module header). Fails, without changing the goal, when the
program is empty, the head opcode is not in the table, or the lemma does not apply. -/
elab "sym_step" h:ident : tactic => withMainContext do
  let hDecl ← getLocalDeclFromUserName h.getId
  let some op ← headOp hDecl.type | throwError "sym_step: {h} is not a run of a non-empty program"
  let some (_, info) := stepTable.find? (·.1 == op)
    | throwError "sym_step: opcode {op} is not in the step table"
  let oldVars ← stateVars hDecl.type
  let lem := mkIdent info.lemma_
  let he := mkIdent (Name.mkSimple "he")
  let hact := mkIdent (Name.mkSimple "hact")
  let hr := mkIdent (Name.mkSimple "hr")
  let app ← if info.needsAct then `($lem $he $hact $h $hr) else `($lem $he $h $hr)
  let h' := mkIdent (← mkFreshUserName `h')
  withoutRecover do
    evalTactic (← `(tactic| have $h':ident := $app))
    evalTactic (← `(tactic| clear $h:ident))
    if info.exists1 then
      evalTactic (← `(tactic| obtain ⟨_, _, _, _, $h:ident⟩ := $h':ident))
    else
      match info.facts with
      | 0 => evalTactic (← `(tactic| obtain ⟨_, _, $h:ident⟩ := $h':ident))
      | 1 => evalTactic (← `(tactic| obtain ⟨_, _, _, $h:ident⟩ := $h':ident))
      | 2 => evalTactic (← `(tactic| obtain ⟨_, _, _, _, $h:ident⟩ := $h':ident))
      | _ => evalTactic (← `(tactic| obtain ⟨_, _, _, _, _, $h:ident⟩ := $h':ident))
    withMainContext do
      for v in oldVars do
        try evalTactic (← `(tactic| clear $(mkIdent (← v.getUserName)):ident)) catch _ => pure ()
    evalTactic (← `(tactic| sym_norm at $h:ident))

/-- Steps `h` as far as the table and the active branch allow. -/
elab "sym_run" h:ident : tactic => do
  let mut n : Nat := 0
  repeat
    let ok ← try
        evalTactic (← `(tactic| sym_step $h:ident)); pure true
      catch ex =>
        logInfo m!"sym_run stopped: {ex.toMessageData}"
        pure false
    unless ok do break
    n := n + 1
    if n > 5000 then throwError "sym_run: more than 5000 steps"
  logInfo m!"sym_run: {n} instructions"

/-! ## Skipping an inactive arm -/

/-- What one inactive instruction does to the nesting: stop (the arm's own `OP_ELSE`/`OP_ENDIF`,
or an opcode outside the table), or step with a given depth change. -/
private inductive SkipAction where
  | stop
  | step (delta : Int)

/-- One inactive step on `h`. The activity hypothesis of the current tracker is derived from the one
named `hin` in the context and the tracker algebra. -/
private def skipStep (h : Ident) (depth : Nat) : TacticM SkipAction := withMainContext do
  let he := mkIdent (Name.mkSimple "he")
  let hr := mkIdent (Name.mkSimple "hr")
  let hin := mkIdent (Name.mkSimple "hin")
  let hDecl ← getLocalDeclFromUserName h.getId
  let some op ← headOp hDecl.type | return .stop
  let hinTerm ← `((by simp only [isActive_opIf, isActive_opElse_opIf, Bool.and_false, Bool.and_true,
    Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]))
  let oldVars ← stateVars hDecl.type
  let h' := mkIdent (← mkFreshUserName `h')
  let mut lemName : Name := .anonymous
  let mut facts : Nat := 0
  let mut extra : Option (TSyntax `term) := none
  let mut delta : Int := 0
  if op == 0x63 then
    lemName := ``inv_skip_if; extra := some (← `(Or.inl rfl)); delta := 1
  else if op == 0x64 then
    lemName := ``inv_skip_if; extra := some (← `(Or.inr rfl)); delta := 1
  else if op == 0x67 then
    if depth == 0 then return .stop
    lemName := ``inv_skip_else; facts := 2
  else if op == 0x68 then
    if depth == 0 then return .stop
    lemName := ``inv_skip_endif; facts := 1; delta := -1
  else
    let some (_, info) := stepTable.find? (·.1 == op) | return .stop
    let s := info.lemma_.toString
    lemName := (s.replace "inv_" "inv_skip_").toName
    facts := if s.startsWith "BoltProof.Glue.inv_push_" then 1 else 0
  let lem := mkIdent lemName
  let app ← match extra with
    | some e => `($lem $he $e $hinTerm $h $hr)
    | none => `($lem $he $hinTerm $h $hr)
  try
    withoutRecover do
      evalTactic (← `(tactic| have $h':ident := $app))
      evalTactic (← `(tactic| clear $h:ident))
      match facts with
      | 0 => evalTactic (← `(tactic| obtain ⟨_, $h:ident⟩ := $h':ident))
      | 1 => evalTactic (← `(tactic| obtain ⟨_, _, $h:ident⟩ := $h':ident))
      | _ => evalTactic (← `(tactic| obtain ⟨_, _, _, $h:ident⟩ := $h':ident))
      withMainContext do
        for v in oldVars do
          try evalTactic (← `(tactic| clear $(mkIdent (← v.getUserName)):ident)) catch _ => pure ()
      evalTactic (← `(tactic| sym_norm at $h:ident))
    return .step delta
  catch ex =>
    logInfo m!"sym_skip stopped: {ex.toMessageData}"
    return .stop

/-- `sym_skip h`: `h` is the run of an inactive arm; step it with the inactive lemmas until the
`OP_ELSE` or `OP_ENDIF` that closes the arm (nested conditionals are walked through). The
activity hypothesis of the arm's tracker is derived from the one named `hin` in the context
(`hin : D.isActive = false` for the tracker the arm starts in) and the tracker algebra. -/
elab "sym_skip" h:ident : tactic => do
  let mut depth : Nat := 0
  let mut n : Nat := 0
  repeat
    match ← skipStep h depth with
    | .stop => break
    | .step d =>
      depth := (depth + d).toNat
      n := n + 1
      if n > 5000 then throwError "sym_skip: more than 5000 steps"
  logInfo m!"sym_skip: {n} instructions"

end BoltProof.Glue
