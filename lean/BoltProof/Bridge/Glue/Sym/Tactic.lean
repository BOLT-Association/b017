import Lean
import BoltProof.Bridge.Glue.Sym.Steps
import BoltProof.Bridge.Glue.Sym.Skip
import BoltProof.Bridge.Glue.Sym.SkipSteps

/-!
# The drivers: `sym_step`, `sym_run`, `sym_skip`, `sym_all`

`sym_step h` reads the hypothesis `h : run Eval.opExec env (op :: g) t st = r`, looks the head
opcode up in `stepTable`, and replaces `h` by the inversion lemma's conclusion for `g`: the facts
the opcode checked become anonymous hypotheses (the bound facts of pushes, `PICK`, `ROLL` and
`SPLIT` are dropped), the new memory counter and opcode count become fresh variables (the old
ones are cleared), and the stack is normalised (`sym_norm`: pushes read off the literal program,
`PICK`/`ROLL` depths resolved on the literal stack, small script numbers decoded, nested drops
folded, the tracker algebra applied). The lemma's `EnvOK` hypothesis is the one named `he` in
the context, the outcome hypothesis `hr`, and the activity hypothesis `hact` (`sym_run h hact'`
names another).

`sym_run h` repeats `sym_step h` until it stops: at the end of the program, at an opcode outside
the table, or at a conditional whose branch it cannot enter.

`sym_skip h` walks an inactive arm with the inactive lemmas (`Sym/SkipSteps.lean`,
`Sym/Skip.lean`), tracking the nesting, and stops at the arm's own `OP_ELSE` or `OP_ENDIF`.

`sym_all h hyps*` runs a whole program: straight-line code with `sym_run`, and at every
`OP_IF`/`OP_NOTIF` it evaluates the popped condition under the hypotheses named (and `decide`),
enters the arm it selects with a fresh activity hypothesis, skips the other arm with `sym_skip`,
and folds the tracker back at the `OP_ENDIF`. It stops at a condition it cannot decide: the block
proof then cases on it and calls `sym_all` again in each case.
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
literal stack, small script numbers, nested drops, numeral sums, the conditional tracker's
algebra, the computed flags. -/
syntax "sym_norm" " at " ident : tactic
macro_rules
  | `(tactic| sym_norm at $h:ident) =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero, List.take_nil,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, List.drop_one, List.tail_cons,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none,
      List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.length_cons, List.length_nil,
      decode_lit, decode_lit2, decode_nil, Nat.reduceLT, Nat.reduceMul, decode_encode, Int.toNat_natCast, Int.reduceToNat, Nat.cast_ofNat, List.drop_drop,
      Nat.reduceAdd, Int.reduceAdd, Int.reduceSub, Int.reduceMul, Int.reduceTMod, Int.reduceLT, Int.reduceLE,
      Int.reduceEq,
      opEndif_opIf, opEndif_opElse_opIf, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte,
      castToBool_one, castToBool_nil, ite_one_zero_eq_zero, ite_zero_one_eq_zero, not_not, encode_one, encode_zero,
      castToBool_encode_ite, decide_eq_true_eq, Bool.decide_and, Bool.decide_or] at $h:ident)

/-! ## Reading the hypothesis -/

/-- The head opcode of the program in `h : run _ _ (op :: g) _ _ = _`, as a `Nat`; `none` on an
empty program. -/
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

/-- Is the program in `h : run _ _ (c ++ k) _ _ = _` headed by a folded chunk, a constant `c`? Only
then is a block rule tried: unifying a block lemma's `c ++ k` against a bare variable makes the
unifier unfold `List.append`, which does not terminate in useful time. -/
private def headIsFoldedChunk (hType : Expr) : MetaM Bool := do
  let hType ← instantiateMVars hType
  let some (_, lhs, _) := hType.eq? | return false
  let fn := lhs.getAppFn
  unless fn.isConstOf ``BsvScript.Gadget.run do return false
  let args := lhs.getAppArgs
  unless args.size == 5 do return false
  let prog := args[2]!
  unless prog.getAppFn.isConstOf ``HAppend.hAppend do return false
  let pargs := prog.getAppArgs
  unless pargs.size == 6 do return false
  return pargs[4]!.isConst

/-- The kind of the folded chunk heading the program in `h`: the part of the chunk constant's name
after its last underscore (`SimpleMulti.c797_pad16` is a `pad16`), which names the block rule; for
a flow chunk or a plain run chunk, the whole name (`c1961_if`, `c3899`), the key of the lemma
reading the region it heads. -/
private def headChunkKind (hType : Expr) : MetaM (Option String) := do
  unless ← headIsFoldedChunk hType do return none
  let hType ← instantiateMVars hType
  let some (_, lhs, _) := hType.eq? | return none
  let prog := lhs.getAppArgs[2]!
  let .const c _ := prog.getAppArgs[4]! | return none
  let .str _ last := c | return none
  let parts := last.splitOn "_"
  -- a plain run chunk (`c3899`) heads a block read as one step too: its rule is keyed by its name
  if parts.length < 2 then return some last
  let kind := parts.getLast!
  -- a folded flow chunk heads a whole conditional arm read as one block (`secondInA`, …): the rule
  -- is keyed by the chunk's full name
  if kind == "if" || kind == "notif" || kind == "else" || kind == "endif" then return some last
  return some kind

/-- The state record of the run in `h`, as its seven fields. -/
private def stateFields (hType : Expr) : MetaM (Option (Array Expr)) := do
  let hType ← instantiateMVars hType
  let some (_, lhs, _) := hType.eq? | return none
  let args := lhs.getAppArgs
  unless args.size == 5 do return none
  let st ← whnfR args[4]!
  let stArgs := st.getAppArgs
  unless st.getAppFn.isConstOf ``BsvScript.Machine.State.mk && stArgs.size == 7 do return none
  return some stArgs

/-- The `memUsed` and `opCount` fields of the state in `h`, when they are local variables. -/
private def stateVars (hType : Expr) : MetaM (Array FVarId) := do
  let some f ← stateFields hType | return #[]
  let mut out := #[]
  for i in [2, 4] do
    if let .fvar id := f[i]! then out := out.push id
  return out

/-- The tracker (`cond` field) of the state in `h`. -/
private def stateCond (hType : Expr) : MetaM (Option Expr) := do
  let some f ← stateFields hType | return none
  return some f[3]!

/-! ## One step -/

/-- One inversion step on `h` with the activity hypothesis `hact`. Throws when the program is
empty, the head opcode is not in the table, or the lemma does not apply. -/
private def stepWith (h hact : Ident) : TacticM Unit := withMainContext do
  let hDecl ← getLocalDeclFromUserName h.getId
  let some op ← headOp hDecl.type | throwError "sym_step: {h} is not a run of a non-empty program"
  let some (_, info) := stepTable.find? (·.1 == op)
    | throwError "sym_step: opcode {op} is not in the step table"
  let oldVars ← stateVars hDecl.type
  let lem := mkIdent info.lemma_
  let he := mkIdent (Name.mkSimple "he")
  let hr := mkIdent (Name.mkSimple "hr")
  let app ← if info.needsAct then `($lem $he $hact $h $hr) else `($lem $he $h $hr)
  let h' := mkIdent (← mkFreshUserName `h')
  withoutRecover do
    evalTactic (← `(tactic| have $h':ident := $app))
    evalTactic (← `(tactic| clear $h:ident))
    -- the bound facts of pushes, PICK, ROLL and SPLIT are never needed downstream: cleared
    let bounds := info.lemma_.toString.startsWith "BoltProof.Glue.inv_push_" ||
      info.lemma_ == ``inv_pick || info.lemma_ == ``inv_roll || info.lemma_ == ``inv_split
    if info.exists1 then
      evalTactic (← `(tactic| obtain ⟨_, _, _, _, $h:ident⟩ := $h':ident))
    else if bounds then
      match info.facts with
      | 1 => evalTactic (← `(tactic| obtain ⟨-, _, _, $h:ident⟩ := $h':ident))
      | _ => evalTactic (← `(tactic| obtain ⟨-, -, _, _, $h:ident⟩ := $h':ident))
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

elab "sym_step" h:ident : tactic => stepWith h (mkIdent (Name.mkSimple "hact"))

/-- Steps `h` as far as the table and the active branch allow; returns the number of steps. With
`stopAtFlow`, stops before every `OP_IF`/`OP_NOTIF`/`OP_ELSE`/`OP_ENDIF` (for `sym_all`). -/
private def runWith (h hact : Ident) (stopAtFlow : Bool := false) : TacticM Nat := do
  let mut n : Nat := 0
  repeat
    -- the end of the literal program (empty, or a chunk constant not yet unfolded) ends the run quietly
    let hDecl ← withMainContext (getLocalDeclFromUserName h.getId)
    match ← withMainContext (headOp hDecl.type) with
    | some op => if stopAtFlow && (op == 0x63 || op == 0x64 || op == 0x67 || op == 0x68) then break
    | none => break
    let ok ← try stepWith h hact; pure true
      catch ex =>
        logInfo m!"sym_run: stopped after {n}: {ex.toMessageData}"
        pure false
    unless ok do break
    n := n + 1
    if n > 10000 then throwError "sym_run: more than 10000 steps"
  return n

elab "sym_run" h:ident hact:(colGt ident)? : tactic => do
  let hact := hact.getD (mkIdent (Name.mkSimple "hact"))
  let n ← runWith h hact
  logInfo m!"sym_run: {n} instructions"

/-! ## Skipping an inactive arm -/

/-- `sym_skipblock h hin` steps `h : run (c ++ k) …` over the folded chunk `c` inside an inactive
arm, by the chunk's skip lemma: the rule `sym_skipblockrule "<kind>" h hin` registered next to the
block lemmas (`SimpleMulti/Blocks.lean`), as for `sym_block`. `hin` is the activity hypothesis of
the arm. -/
syntax "sym_skipblockrule" str ident ident : tactic

elab "sym_skipblock" h:ident hin:ident : tactic => withMainContext do
  let hDecl ← getLocalDeclFromUserName h.getId
  let some kind ← headChunkKind hDecl.type | throwError "sym_skipblock: {h} is not at a folded chunk"
  evalTactic (← `(tactic| sym_skipblockrule $(Syntax.mkStrLit kind) $h:ident $hin:ident))

/-- What one inactive instruction does to the nesting: stop (the arm's own `OP_ELSE`/`OP_ENDIF`,
or an opcode outside the table), or step with a given depth change. -/
private inductive SkipAction where
  | stop
  | step (delta : Int)

/-- One inactive step on `h`. The activity hypothesis of the current tracker is derived from `hin`
(the inactivity of the tracker the arm starts in) and the tracker algebra. -/
private def skipStep (h hin : Ident) (depth : Nat) : TacticM SkipAction := withMainContext do
  let he := mkIdent (Name.mkSimple "he")
  let hr := mkIdent (Name.mkSimple "hr")
  let hDecl ← getLocalDeclFromUserName h.getId
  let some op ← headOp hDecl.type
    | -- a folded chunk: its skip lemma if one is registered (`sym_skipblock`), else the end of the arm
      unless ← headIsFoldedChunk hDecl.type do return .stop
      let s ← saveState
      try
        withoutRecover do evalTactic (← `(tactic| sym_skipblock $h:ident $hin:ident))
        return .step 0
      catch _ =>
        s.restore
        return .stop
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
      | 1 => evalTactic (← `(tactic| obtain ⟨-, _, $h:ident⟩ := $h':ident))
      | _ => evalTactic (← `(tactic| obtain ⟨-, -, _, $h:ident⟩ := $h':ident))
      withMainContext do
        for v in oldVars do
          try evalTactic (← `(tactic| clear $(mkIdent (← v.getUserName)):ident)) catch _ => pure ()
      evalTactic (← `(tactic| sym_norm at $h:ident))
    return .step delta
  catch ex =>
    logInfo m!"sym_skip stopped: {ex.toMessageData}"
    return .stop

/-- Walks the inactive arm in `h` to its own `OP_ELSE`/`OP_ENDIF`; returns the number of steps. -/
private def skipWith (h hin : Ident) : TacticM Nat := do
  let mut depth : Nat := 0
  let mut n : Nat := 0
  repeat
    match ← skipStep h hin depth with
    | .stop => break
    | .step d =>
      depth := (depth + d).toNat
      n := n + 1
      if n > 10000 then throwError "sym_skip: more than 10000 steps"
  return n

elab "sym_skip" h:ident hin:(colGt ident)? : tactic => do
  let hin := hin.getD (mkIdent (Name.mkSimple "hin"))
  let n ← skipWith h hin
  logInfo m!"sym_skip: {n} instructions"

/-! ## The whole program -/

/-- Is the tracker in `h` syntactically `D.opIf true` / `D.opIf false`? -/
private def condDecided (hType : Expr) : MetaM (Option Bool) := do
  let some c ← stateCond hType | return none
  let c ← instantiateMVars c
  unless c.getAppFn.isConstOf ``BsvScript.Machine.Cond.opIf do return none
  let args := c.getAppArgs
  unless args.size == 2 do return none
  let b ← whnfR args[1]!
  if b.isConstOf ``Bool.true then return some true
  if b.isConstOf ``Bool.false then return some false
  return none

/-- A fresh activity hypothesis for the tracker now in `h`, proved from the tracker algebra, the
hypotheses named, and `decide`. -/
private def mkActivity (h : Ident) (active : Bool) (extra : Array Ident) : TacticM Ident := withMainContext do
  let hDecl ← getLocalDeclFromUserName h.getId
  let some c ← stateCond hDecl.type | throwError "sym_all: no tracker in {h}"
  let name ← mkFreshUserName (if active then `hact else `hin)
  let id := mkIdent name
  let cStx ← Term.exprToSyntax c
  let val := if active then mkIdent ``Bool.true else mkIdent ``Bool.false
  let extras ← extra.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  withoutRecover do
    evalTactic (← `(tactic| have $id:ident : Cond.isActive $cStx = $val := by
      simp (config := { decide := true }) only [isActive_opIf, isActive_opElse_opIf, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, $extras,*]))
  return id

/-- Evaluate the popped condition in `h`'s tracker under the hypotheses named. -/
private def decideCond (h : Ident) (extra : Array Ident) : TacticM Unit := withMainContext do
  let extras ← extra.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  evalTactic (← `(tactic| simp (config := { decide := true, failIfUnchanged := false, maxDischargeDepth := 6 }) only
    [castToBool_single, castToBool_one, castToBool_nil, castToBool_encode_ite, castToBool_encode_decode, castToBool_append_of_right, castToBool_cons_of_ne, encode_zero, encode_one, decode_nil, decode_lit2, Nat.reduceLT, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, bne_iff_ne, ne_eq, decide_eq_true_eq, decide_true, decide_false, Int.reduceTMod, Int.reduceAdd, Int.reduceSub, Int.reduceEq, Int.reduceLT, Int.reduceLE, Bool.and_true, Bool.and_false,
     Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, Bool.not_true,
     Bool.not_false, ↓reduceIte, not_not, not_false_eq_true, not_true_eq_false, and_true, and_false, true_and,
     false_and, or_true, or_false, true_or, false_or, $extras,*] at $h:ident))

/-- Every identifier inside a piece of syntax. -/
private partial def collectIdents (stx : Syntax) : Array Ident :=
  match stx with
  | .ident .. => #[⟨stx⟩]
  | .node _ _ args => args.foldl (fun acc a => acc ++ collectIdents a) #[]
  | _ => #[]

/-! ## Blocks -/

/-- `sym_block h hact` replaces `h : run (c ++ k) …`, where `c` is a folded chunk, by the run of
`k` after a block lemma for `c`. The chunk's kind, the part of its name after the last underscore
(`c797_pad16` is a `pad16`), selects the rule `sym_blockrule "<kind>" h hact`, registered with
`macro_rules` where the block lemmas live (`SimpleMulti/Blocks.lean`); the rule applies its lemma
to `h` with the hypotheses `he` and `hr` of the context and the activity hypothesis given.
`sym_all` tries it whenever the program's head is a folded chunk, and stops there when no rule
applies. -/
syntax "sym_blockrule" str ident ident : tactic

elab "sym_block" h:ident hact:ident : tactic => withMainContext do
  let hDecl ← getLocalDeclFromUserName h.getId
  let some kind ← headChunkKind hDecl.type | throwError "sym_block: {h} is not at a folded chunk"
  evalTactic (← `(tactic| sym_blockrule $(Syntax.mkStrLit kind) $h:ident $hact:ident))

/-- `sym_all h hyps*` (the module header). -/
elab "sym_all" h:ident hs:(colGt ident)* : tactic => do
  let extras : Array Ident := hs.map fun s => ⟨s.raw⟩
  -- `hact : C.isActive = true` names the tracker the caller started from; the arm `h` is in now may
  -- be nested inside it (a second `sym_all` after a block lemma), so the activity hypothesis of the
  -- current tracker is derived from it, and derived again whenever the walk closes back down to it
  let baseHact := mkIdent (Name.mkSimple "hact")
  -- the activity hypotheses of the enclosing arms, innermost last; the current one on top
  let mut hacts : Array Ident := #[← mkActivity h true (extras.push baseHact)]
  let mut total : Nat := 0
  let mut blocks : Nat := 0
  repeat
    let hact := hacts.back!
    total := total + (← runWith h hact true)
    let hDecl ← withMainContext (getLocalDeclFromUserName h.getId)
    let op? ← withMainContext (headOp hDecl.type)
    let some op := op?
      | -- a folded chunk: a block lemma if one is registered for it, else the end of the walk
        unless ← withMainContext (headIsFoldedChunk hDecl.type) do break
        let s ← saveState
        let ok ← try
            withoutRecover do evalTactic (← `(tactic| sym_block $h:ident $hact:ident))
            pure true
          catch _ =>
            s.restore
            pure false
        if ok then
          blocks := blocks + 1
          continue
        else break
    if op == 0x63 || op == 0x64 then
      -- enter the conditional: evaluate what the hypotheses decide on the stack (an `OP_IFDUP`'s copy,
      -- a flag), pop the condition, decide it
      decideCond h extras
      stepWith h hact
      decideCond h extras
      let hType := (← withMainContext (getLocalDeclFromUserName h.getId)).type
      match ← withMainContext (condDecided hType) with
      | some true =>
        let hactNew ← mkActivity h true (extras.push hact)
        hacts := hacts.push hactNew
      | some false =>
        let hinNew ← mkActivity h false (extras.push hact)
        total := total + (← skipWith h hinNew)
        -- at the arm's OP_ELSE (then the else arm is active) or OP_ENDIF (then nothing was taken)
        let hDecl2 ← withMainContext (getLocalDeclFromUserName h.getId)
        let some op2 ← withMainContext (headOp hDecl2.type)
          | throwError "sym_all: the skipped arm has no end: {hDecl2.type}"
        if op2 == 0x67 then
          stepWith h hact
          let hactNew ← mkActivity h true (extras.push hact)
          hacts := hacts.push hactNew
        else if op2 == 0x68 then
          stepWith h hact
        else throwError "sym_all: the skipped arm stopped at opcode {op2}"
      | none =>
        let some c ← withMainContext (stateCond hType) | throwError "sym_all: no tracker"
        logInfo m!"sym_all: undecided condition after {total} instructions: {c}"
        break
    else if op == 0x67 then
      -- the end of an active arm: flip, skip the other arm, close
      stepWith h hact
      let hinNew ← mkActivity h false (extras.push hact)
      total := total + (← skipWith h hinNew)
      let hDecl2 ← withMainContext (getLocalDeclFromUserName h.getId)
      let some op2 ← withMainContext (headOp hDecl2.type)
        | throwError "sym_all: the else arm has no end: {hDecl2.type}"
      unless op2 == 0x68 do throwError "sym_all: the else arm stopped at opcode {op2}"
      stepWith h hact
      hacts := hacts.pop
      if hacts.isEmpty then hacts := #[← mkActivity h true (extras.push baseHact)]
    else if op == 0x68 then
      stepWith h hact
      hacts := hacts.pop
      if hacts.isEmpty then hacts := #[← mkActivity h true (extras.push baseHact)]
    else
      logInfo m!"sym_all: stopped at opcode {op} after {total} instructions"
      break
    total := total + 1
  logInfo m!"sym_all: {total} instructions, {blocks} blocks"

end BoltProof.Glue
