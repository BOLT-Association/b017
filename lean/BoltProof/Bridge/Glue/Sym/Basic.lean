import BoltProof.Bridge.Gadgets.Steps

/-!
# The symbolic run: outcomes and environments

The glue proof reads the covenant *backwards*: from "the whole suffix ran to `.next`" it recovers
what each instruction must have checked. Two notions carry that reading:

* `GOut.IsOk`: the outcomes a run can continue from (`next`, or the post-Genesis `stop`). `run`
  never recovers from an error, so `IsOk` of the final outcome forces every instruction on the
  way to have succeeded, limit checks included; the inversion lemmas of `Sym/Steps.lean` take it
  in place of the per-instruction limit hypotheses the forward lemmas of `Gadgets/Steps.lean` need.
* `EnvOK env`: the environment facts the covenant relies on, all true of the Chronicle block
  path the vectors are judged under (`Bridge/Params.lean`): a post-Chronicle UTXO (no disabled
  opcodes, no pre-Genesis limits), no MINIMALDATA (the raw `txoType` push is read by `OP_IF`),
  no MINIMALIF, FORKID signatures, and no `checksigData` (phase 2: the signed script is the
  locking script from the last separator, i.e. the whole lock).
-/

set_option autoImplicit false

namespace BsvScript.Gadget.GOut

/-- The outcomes a run can continue from. -/
def IsOk : GOut → Prop
  | .next _ => True
  | .stop _ => True
  | .err _ _ => False
  | .undefined _ _ => False
  | .unimpl _ _ => False

@[simp] theorem isOk_next (st : BsvScript.Machine.State) : (GOut.next st).IsOk := trivial
@[simp] theorem isOk_stop (st : BsvScript.Machine.State) : (GOut.stop st).IsOk := trivial
@[simp] theorem not_isOk_err (e : BsvScript.ScriptError) (st : BsvScript.Machine.State) :
    ¬ (GOut.err e st).IsOk := fun h => h
@[simp] theorem not_isOk_undefined (f : String) (st : BsvScript.Machine.State) :
    ¬ (GOut.undefined f st).IsOk := fun h => h
@[simp] theorem not_isOk_unimpl (o : Nat) (st : BsvScript.Machine.State) :
    ¬ (GOut.unimpl o st).IsOk := fun h => h

end BsvScript.Gadget.GOut

namespace BoltProof.Glue

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- The environment facts the symbolic run relies on (the module header). -/
structure EnvOK (env : Env) : Prop where
  gen : env.utxoAfterGenesis = true
  era : env.utxoEra = Era.postChronicle
  min : env.requireMinimal = false
  minIf : env.params.flags.minimalIf = false
  forkid : env.params.flags.enableSighashForkid = true
  cs : env.checksigData = none

/-- `throw` in the families' `do` blocks is `Except.error`. -/
@[simp] theorem throw_eq {α : Type} (e : ScriptError) : (throw e : Except ScriptError α) = Except.error e := rfl

/-- The simp set of one instruction, applied to a hypothesis: `Gadgets/Steps.lean`'s `step_simp`
list (the loop's step, the dispatcher, every family hook, the opcode constants), every hypothesis
in scope, and the extra lemmas named. -/
syntax "inv_simp" " at " ident (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| inv_simp at $h:ident) => `(tactic| inv_simp at $h [])
  | `(tactic| inv_simp at $h:ident [$hs,*]) =>
  `(tactic| simp (config := { failIfUnchanged := false }) [getOpTail, execStep, execFlow, isOpcodeDisabled, checkMinimalPush, Eval.opExec,
      Ops.Arith.exec, Ops.Arith.isUnary, Ops.Arith.isBinary, Ops.Arith.unary, Ops.Arith.binary,
      Ops.Arith.readOperand, Ops.Arith.pushResult, Ops.Arith.pushBool, Ops.Arith.binaryValue,
      Ops.Arith.binaryBounded, Ops.Arith.unaryValue, Ops.Arith.unaryBounded,
      Ops.Bitwise.exec, Ops.Bitwise.equal, Ops.Bitwise.vchTrue, Ops.Bitwise.vchFalse,
      Ops.Stack.exec, Ops.Stack.execStack, Ops.Stack.need, Ops.Stack.topAt, Ops.Stack.eraseTop,
      Ops.Stack.pushCount, Ops.Stack.swapTop, Ops.Stack.insertTop, Ops.Stack.toAlt, Ops.Stack.fromAlt,
      Ops.Splice.exec, Ops.Splice.cat, Ops.Splice.split, Ops.Splice.num2binOp, Ops.Splice.bin2num,
      Ops.Splice.invalidSplitPosition,
      Ops.Crypto.exec, Ops.Crypto.hashOp, Ops.Crypto.checkSigOp, Ops.Crypto.scriptCodeOf,
      Ops.Expansion.exec, execIf,
      popElem, pushElem, HookR.ofExcept, bind, Except.bind, pure, Except.pure, run.eq_1,
      Op.OP_0, Op.OP_PUSHDATA1, Op.OP_PUSHDATA2, Op.OP_PUSHDATA4, Op.OP_1NEGATE, Op.OP_1, Op.OP_16,
      Op.OP_11, Op.OP_2, Op.OP_NOP, Op.OP_VER, Op.OP_IF, Op.OP_NOTIF, Op.OP_VERIF, Op.OP_VERNOTIF, Op.OP_ELSE,
      Op.OP_ENDIF, Op.OP_VERIFY, Op.OP_RETURN, Op.OP_TOALTSTACK, Op.OP_FROMALTSTACK, Op.OP_2DROP,
      Op.OP_2DUP, Op.OP_3DUP, Op.OP_2OVER, Op.OP_2ROT, Op.OP_2SWAP, Op.OP_IFDUP, Op.OP_DEPTH,
      Op.OP_DROP, Op.OP_DUP, Op.OP_NIP, Op.OP_OVER, Op.OP_PICK, Op.OP_ROLL, Op.OP_ROT, Op.OP_SWAP,
      Op.OP_TUCK, Op.OP_CAT, Op.OP_SPLIT, Op.OP_NUM2BIN, Op.OP_BIN2NUM, Op.OP_SIZE, Op.OP_INVERT,
      Op.OP_AND, Op.OP_OR, Op.OP_XOR, Op.OP_EQUAL, Op.OP_EQUALVERIFY, Op.OP_1ADD, Op.OP_1SUB,
      Op.OP_2MUL, Op.OP_2DIV, Op.OP_NEGATE, Op.OP_ABS, Op.OP_NOT, Op.OP_0NOTEQUAL, Op.OP_ADD,
      Op.OP_SUB, Op.OP_MUL, Op.OP_DIV, Op.OP_MOD, Op.OP_LSHIFT, Op.OP_RSHIFT, Op.OP_BOOLAND,
      Op.OP_BOOLOR, Op.OP_NUMEQUAL, Op.OP_NUMEQUALVERIFY, Op.OP_NUMNOTEQUAL, Op.OP_LESSTHAN,
      Op.OP_GREATERTHAN, Op.OP_LESSTHANOREQUAL, Op.OP_GREATERTHANOREQUAL, Op.OP_MIN, Op.OP_MAX,
      Op.OP_WITHIN, Op.OP_RIPEMD160, Op.OP_SHA1, Op.OP_SHA256, Op.OP_HASH160, Op.OP_HASH256,
      Op.OP_CODESEPARATOR, Op.OP_CHECKSIG, Op.OP_CHECKSIGVERIFY, Op.OP_CHECKMULTISIG,
      Op.OP_CHECKMULTISIGVERIFY, Op.OP_NOP1, Op.OP_CHECKLOCKTIMEVERIFY, Op.OP_CHECKSEQUENCEVERIFY,
      Op.OP_NOP9, Op.OP_NOP10, Op.OP_SUBSTR, Op.OP_RSHIFTNUM, Op.hasCase, Env.utxoAfterChronicle, *, $hs,*] at $h:ident)

/-- Split every `if` the step left in the hypothesis and simplify again, until no `if` remains:
the limit checks surface one layer at a time as the family hook's `do` block unfolds. -/
syntax "inv_split" ident : tactic
macro_rules
  | `(tactic| inv_split $h:ident) => `(tactic| (repeat' (split_ifs at $h:ident <;> inv_simp at $h)))

/-- Close a branch of an inversion: the hypothesis is the surviving run (hand it back, after
rewriting the goal with the facts the splits produced), or it names an error outcome, which
`IsOk` refutes. -/
syntax "inv_close" ident ident : tactic
macro_rules
  | `(tactic| inv_close $h:ident $hr:ident) =>
  `(tactic| first
      | exact ⟨_, _, $h⟩
      | (subst $h; simp at $hr:ident)
      | (simp only [ne_eq, *]; exact ⟨_, _, $h⟩))

/-- The state literal every inversion lemma is stated on. -/
abbrev St (stack alt : List Bytes) (m : Nat) (C : Cond) (k : Nat) (cs : Bytes) : State :=
  { stack := stack, alt := alt, memUsed := m, cond := C, opCount := k, nonTopLevelReturn := false,
    codeSep := cs }

/-! ## The instruction parser on the shapes the suffixes use -/

/-- `OP_0` carries no data. -/
theorem getOpTail_push0 (g : Bytes) : getOpTail Op.OP_0 g = some ([], 0) := by
  simp [getOpTail, Op.OP_0, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1]

/-- A direct push of `n` bytes reads the next `n` bytes, or fails on a short program. -/
theorem getOpTail_push {n : Nat} (hn : 1 ≤ n ∧ n ≤ 75) (g : Bytes) :
    getOpTail n g = if g.length < n then none else some (g.take n, n) := by
  have h1 : n ≤ Op.OP_PUSHDATA4 := by simp only [Op.OP_PUSHDATA4]; omega
  have h2 : n < Op.OP_PUSHDATA1 := by simp only [Op.OP_PUSHDATA1]; omega
  simp [getOpTail, h1, h2]

/-- An opcode above `OP_PUSHDATA4` carries no data. -/
theorem getOpTail_op {op : Nat} (hop : Op.OP_PUSHDATA4 < op) (g : Bytes) : getOpTail op g = some ([], 0) := by
  simp [getOpTail, Nat.not_le.mpr hop]

/-! ## Small facts the driver normalises with -/

/-- A single byte below `0x80` is the script number it denotes. -/
theorem decode_lit (b : Nat) (hb : b < 128) : decode [b] = b := by
  simp [decode, decodeRev, beNat, Nat.mod_eq_of_lt hb, Nat.not_le.mpr hb]

/-- Two bytes, the low one first, with the high one below `0x80`: the number they denote (the
rebuilds' `PICK` depths past 127, such as `[0xd4, 0x00]`). -/
theorem decode_lit2 (a b : Nat) (ha : a < 256) (hb : b < 128) : decode [a, b] = ((a + 256 * b : Nat) : Int) := by
  simp [decode, decodeRev, beNat, Nat.mod_eq_of_lt hb, Nat.not_le.mpr hb]
  omega

/-- A byte string whose tail is true is true: `OP_IF` on a built output, whose last bytes are the
`OP_CHECKSIG` of its script. -/
theorem castToBool_append_of_right (x y : Bytes) (hy : castToBool y = true) : castToBool (x ++ y) = true := by
  induction x with
  | nil => simpa using hy
  | cons b x ih =>
    rw [List.cons_append]
    rcases hxy : x ++ y with _ | ⟨c, rest⟩
    · rw [hxy] at ih
      simp [castToBool] at ih
    · rw [hxy] at ih
      simp [castToBool, ih]

/-- A byte string headed by a non-zero byte other than `0x80` is true (a built output's script
length byte heads it). -/
theorem castToBool_cons_of_ne (b : Nat) (bs : Bytes) (hb : b ≠ 0) (hb' : b ≠ 128) : castToBool (b :: bs) = true := by
  cases bs <;> simp [castToBool, hb, hb']

@[simp] theorem castToBool_one : castToBool [1] = true := by decide
@[simp] theorem castToBool_nil : castToBool [] = false := rfl

/-- The boolean flags the covenants compute (`OP_NOT`, `OP_0NOTEQUAL`, `OP_BOOLAND`, …) as propositions. -/
@[simp] theorem ite_one_zero_eq_zero (c : Prop) [Decidable c] : ((if c then (1 : Int) else 0) = 0) ↔ ¬ c := by
  split_ifs <;> simp [*]
@[simp] theorem ite_zero_one_eq_zero (c : Prop) [Decidable c] : ((if c then (0 : Int) else 1) = 0) ↔ c := by
  split_ifs <;> simp [*]
@[simp] theorem encode_one : encode 1 = [1] := by decide
/-- `OP_IF` on a computed flag is the flag's proposition. -/
@[simp] theorem castToBool_encode_ite (c : Prop) [Decidable c] :
    castToBool (encode (if c then 1 else 0)) = decide c := by
  split_ifs <;> simp [*, encode_zero]

/-- A single byte is true unless it is `0x00` or the negative zero `0x80`. -/
theorem castToBool_single (b : Nat) : castToBool [b] = decide (b ≠ 0 ∧ b ≠ 128) := by
  unfold castToBool
  by_cases h0 : b = 0 <;> by_cases h1 : b = 128 <;> simp [h0, h1]

/-- The tracker after `OP_IF`: active iff the enclosing branch was and the condition holds. -/
@[simp] theorem isActive_opIf (C : Cond) (b : Bool) : (C.opIf b).isActive = (C.isActive && b) := by
  cases b <;> simp [Cond.isActive, Cond.opIf]

/-- The tracker after `OP_IF … OP_ELSE`: active iff the enclosing branch was and the condition fails. -/
@[simp] theorem isActive_opElse_opIf (C : Cond) (b : Bool) :
    ((C.opIf b).opElse).isActive = (C.isActive && !b) := by
  cases b <;> simp [Cond.isActive, Cond.opIf, Cond.opElse]

/-- `OP_ENDIF` closes an `OP_IF` without an `OP_ELSE`. -/
@[simp] theorem opEndif_opIf (C : Cond) (b : Bool) : (C.opIf b).opEndif = C := by
  cases C; cases b <;> simp [Cond.opIf, Cond.opEndif]

/-- `OP_ENDIF` closes an `OP_IF … OP_ELSE`. -/
@[simp] theorem opEndif_opElse_opIf (C : Cond) (b : Bool) : ((C.opIf b).opElse).opEndif = C := by
  cases C; cases b <;> simp [Cond.opIf, Cond.opElse, Cond.opEndif]

end BoltProof.Glue
