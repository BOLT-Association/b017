import BsvScript.Gadget
import BsvScript.Gadget.HashLock
import BsvScript.Eval

/-!
# Per-instruction step lemmas for the covenant fragments

The effect of one instruction on the machine state, through `Gadget.run` over the loop's own
step, in the style of `BsvScript.Gadget.HashLock` (`run_sha256`, …). Each lemma names the
reference's preconditions for the executing branch (an active conditional, no non-top-level
`OP_RETURN`, room under the op-count and memory limits, a post-Genesis UTXO) and, where the
opcode reads a script number, `requireMinimal = false` (the block path's flag word) and the
operand within the number width.

These are the bricks of `BoltProof.Bridge.Gadgets.*`, which compose them with `run_append`
into the covenant's own fragments.
-/

set_option autoImplicit false

namespace BoltProof.Gadgets

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- The simp set that evaluates one non-push instruction of `run`: the loop's step, the
dispatcher, every family hook, and the opcode constants their `if` chains compare against. -/
macro "step_simp" : tactic =>
  `(tactic| simp [getOpTail, execStep, execFlow, isOpcodeDisabled, checkMinimalPush, Eval.opExec,
      Ops.Arith.exec, Ops.Arith.isUnary, Ops.Arith.isBinary, Ops.Arith.unary, Ops.Arith.binary,
      Ops.Arith.readOperand, Ops.Arith.pushResult, Ops.Arith.pushBool, Ops.Arith.binaryValue,
      Ops.Arith.binaryBounded, Ops.Arith.unaryValue, Ops.Arith.unaryBounded,
      Ops.Bitwise.exec, Ops.Bitwise.equal, Ops.Bitwise.vchTrue, Ops.Bitwise.vchFalse,
      Ops.Stack.exec, Ops.Stack.execStack, Ops.Stack.need, Ops.Stack.topAt, Ops.Stack.eraseTop,
      Ops.Stack.pushCount, Ops.Splice.exec, Ops.Crypto.exec, Ops.Expansion.exec,
      popElem, pushElem, HookR.ofExcept, bind, Except.bind, pure, Except.pure, run.eq_1,
      Op.OP_0, Op.OP_PUSHDATA1, Op.OP_PUSHDATA2, Op.OP_PUSHDATA4, Op.OP_1NEGATE, Op.OP_1, Op.OP_16,
      Op.OP_11, Op.OP_NOP, Op.OP_VER, Op.OP_IF, Op.OP_NOTIF, Op.OP_VERIF, Op.OP_VERNOTIF, Op.OP_ELSE,
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
      Op.OP_NOP9, Op.OP_NOP10, *])

/-- The preconditions every executing instruction shares (the module header). -/
structure Exec (env : Env) (st : State) : Prop where
  act : st.cond.isActive = true
  ret : st.nonTopLevelReturn = false
  gen : env.utxoAfterGenesis = true

/-- **`OP_SIZE`** (`1057–1064`): the length of the top pushed as a script number above it. -/
theorem run_size (env : Env) (t : Bytes) (st : State) (x : Bytes) (rest : List Bytes)
    (hstk : st.stack = x :: rest) (he : Exec env st)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hnum : (encode (x.length : Int)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + (encode (x.length : Int)).length + elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_SIZE] t st =
      .next { st with opCount := st.opCount + 1, stack := encode (x.length : Int) :: x :: rest,
                      memUsed := st.memUsed + (encode (x.length : Int)).length + elementOverhead } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hnum' : ¬ (env.params.limits.maxScriptNumLength < (encode (x.length : Int)).length) := by omega
  have hmem' : ¬ (st.memUsed + (encode (x.length : Int)).length + elementOverhead >
      env.params.limits.maxStackMemoryUsage) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_NIP`** (`989–995`): the element below the top removed, its memory released. -/
theorem run_nip (env : Env) (t : Bytes) (st : State) (a b : Bytes) (rest : List Bytes)
    (hstk : st.stack = a :: b :: rest) (he : Exec env st)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript) :
    run Eval.opExec env [Op.OP_NIP] t st =
      .next { st with opCount := st.opCount + 1, stack := a :: rest,
                      memUsed := st.memUsed - (b.length + elementOverhead) } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_0`** (`473–481`): the empty vector pushed; no opcode counted. -/
theorem run_push0 (env : Env) (t : Bytes) (st : State) (he : Exec env st)
    (hmem : st.memUsed + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_0] t st =
      .next { st with stack := [] :: st.stack, memUsed := st.memUsed + elementOverhead } := by
  have hmem' : ¬ (env.params.limits.maxStackMemoryUsage < st.memUsed + elementOverhead) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **A one-byte push** (`0x01 b`, `473–481`) under a flag word without MINIMALDATA (the block
path): `[b]` pushed; no opcode counted. -/
theorem run_push1 (env : Env) (t : Bytes) (st : State) (b : Nat) (he : Exec env st)
    (hmin : env.requireMinimal = false)
    (hmem : st.memUsed + 1 + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [1, b] t st =
      .next { st with stack := [b] :: st.stack, memUsed := st.memUsed + 1 + elementOverhead } := by
  have hmem' : ¬ (st.memUsed + 1 + elementOverhead > env.params.limits.maxStackMemoryUsage) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_EQUALVERIFY`** (`1189–1217`) on two *different* elements: the comparison pushes
`vchFalse`, the verify fails with `SCRIPT_ERR_EQUALVERIFY`; the opcode was counted. -/
theorem run_equalverify_ne (env : Env) (t : Bytes) (st : State) (a b : Bytes) (rest : List Bytes)
    (hne : a ≠ b) (hstk : st.stack = b :: a :: rest) (he : Exec env st)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hmem : st.memUsed - (b.length + elementOverhead) - (a.length + elementOverhead) +
      elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_EQUALVERIFY] t st = .err .equalverify { st with opCount := st.opCount + 1 } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hmem' : ¬ (env.params.limits.maxStackMemoryUsage < st.memUsed - (b.length + elementOverhead) -
      (a.length + elementOverhead) + elementOverhead) := by omega
  have hne' : ¬ (a = b) := hne
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp
  rfl

/-- **`OP_VERIFY`** (`842–854`) on a true top: popped, its memory released. -/
theorem run_verify_true (env : Env) (t : Bytes) (st : State) (x : Bytes) (rest : List Bytes)
    (hx : castToBool x = true) (hstk : st.stack = x :: rest) (he : Exec env st)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript) :
    run Eval.opExec env [Op.OP_VERIFY] t st =
      .next { st with opCount := st.opCount + 1, stack := rest,
                      memUsed := st.memUsed - (x.length + elementOverhead) } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_VERIFY`** on a false top: `SCRIPT_ERR_VERIFY`; the opcode was counted. -/
theorem run_verify_false (env : Env) (t : Bytes) (st : State) (x : Bytes) (rest : List Bytes)
    (hx : castToBool x = false) (hstk : st.stack = x :: rest) (he : Exec env st)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript) :
    run Eval.opExec env [Op.OP_VERIFY] t st = .err .verify { st with opCount := st.opCount + 1 } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_GREATERTHANOREQUAL`** (`1354–1356`) on operands `b1` (below) and `b2` (top): both
popped, `1` or `0` pushed as a script number. -/
theorem run_gte (env : Env) (t : Bytes) (st : State) (b1 b2 : Bytes) (rest : List Bytes)
    (hstk : st.stack = b2 :: b1 :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hl1 : b1.length ≤ env.params.limits.maxScriptNumLength)
    (hl2 : b2.length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (if decode b1 ≥ decode b2 then 1 else 0)).length + elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_GREATERTHANOREQUAL] t st =
      .next { st with opCount := st.opCount + 1,
                      stack := encode (if decode b1 ≥ decode b2 then 1 else 0) :: rest,
                      memUsed := st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
                        (encode (if decode b1 ≥ decode b2 then 1 else 0)).length + elementOverhead } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hl1' : ¬ (env.params.limits.maxScriptNumLength < b1.length) := by omega
  have hl2' : ¬ (env.params.limits.maxScriptNumLength < b2.length) := by omega
  have hmem' : ¬ (st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (if decode b1 ≥ decode b2 then 1 else 0)).length + elementOverhead >
      env.params.limits.maxStackMemoryUsage) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_SUB`** (`1308–1310`) on operands `b1` (below) and `b2` (top): both popped, the
difference pushed; post-Genesis the result must fit the number width. -/
theorem run_sub (env : Env) (t : Bytes) (st : State) (b1 b2 : Bytes) (rest : List Bytes)
    (hstk : st.stack = b2 :: b1 :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hl1 : b1.length ≤ env.params.limits.maxScriptNumLength)
    (hl2 : b2.length ≤ env.params.limits.maxScriptNumLength)
    (hres : (encode (decode b1 - decode b2)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (decode b1 - decode b2)).length + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_SUB] t st =
      .next { st with opCount := st.opCount + 1,
                      stack := encode (decode b1 - decode b2) :: rest,
                      memUsed := st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
                        (encode (decode b1 - decode b2)).length + elementOverhead } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hl1' : ¬ (env.params.limits.maxScriptNumLength < b1.length) := by omega
  have hl2' : ¬ (env.params.limits.maxScriptNumLength < b2.length) := by omega
  have hres' : ¬ (env.params.limits.maxScriptNumLength < (encode (decode b1 - decode b2)).length) := by omega
  have hmem' : ¬ (st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (decode b1 - decode b2)).length + elementOverhead > env.params.limits.maxStackMemoryUsage) := by
    omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_PICK`** (`1006–1027`): the index popped, the element that deep copied to the top. -/
theorem run_pick (env : Env) (t : Bytes) (st : State) (idx : Bytes) (s : List Bytes) (n : Nat)
    (hstk : st.stack = idx :: s) (hdec : decode idx = n) (hn : n < s.length) (he : Exec env st)
    (hmin : env.requireMinimal = false)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hli : idx.length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed - (idx.length + elementOverhead) + ((s.getD n []).length + elementOverhead) ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_PICK] t st =
      .next { st with opCount := st.opCount + 1, stack := s.getD n [] :: s,
                      memUsed := st.memUsed - (idx.length + elementOverhead) +
                        ((s.getD n []).length + elementOverhead) } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hli' : ¬ (env.params.limits.maxScriptNumLength < idx.length) := by omega
  have hmem' : ¬ (st.memUsed - (idx.length + elementOverhead) + ((s.getD n []).length + elementOverhead) >
      env.params.limits.maxStackMemoryUsage) := by omega
  have hs : ¬ (s = []) := by intro h; subst h; simp at hn
  have hbound : ¬ ((n : Int) < 0 ∨ s.length ≤ n) := by omega
  have hget : s.getD n [] = s[n] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  have hmem'' : ¬ (env.params.limits.maxStackMemoryUsage < st.memUsed - (idx.length + elementOverhead) +
      s[n].length + elementOverhead) := by rw [← hget]; omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp
  all_goals omega

/-- **`OP_ADD`** (`1304–1306`) on operands `b1` (below) and `b2` (top): both popped, the sum
pushed; post-Genesis the result must fit the number width. -/
theorem run_add (env : Env) (t : Bytes) (st : State) (b1 b2 : Bytes) (rest : List Bytes)
    (hstk : st.stack = b2 :: b1 :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hl1 : b1.length ≤ env.params.limits.maxScriptNumLength)
    (hl2 : b2.length ≤ env.params.limits.maxScriptNumLength)
    (hres : (encode (decode b1 + decode b2)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (decode b1 + decode b2)).length + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_ADD] t st =
      .next { st with opCount := st.opCount + 1,
                      stack := encode (decode b1 + decode b2) :: rest,
                      memUsed := st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
                        (encode (decode b1 + decode b2)).length + elementOverhead } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hl1' : ¬ (env.params.limits.maxScriptNumLength < b1.length) := by omega
  have hl2' : ¬ (env.params.limits.maxScriptNumLength < b2.length) := by omega
  have hres' : ¬ (env.params.limits.maxScriptNumLength < (encode (decode b1 + decode b2)).length) := by omega
  have hmem' : ¬ (st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (decode b1 + decode b2)).length + elementOverhead > env.params.limits.maxStackMemoryUsage) := by
    omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_LESSTHANOREQUAL`** (`1351–1353`) on operands `b1` (below) and `b2` (top): both popped,
`1` or `0` pushed as a script number. -/
theorem run_lte (env : Env) (t : Bytes) (st : State) (b1 b2 : Bytes) (rest : List Bytes)
    (hstk : st.stack = b2 :: b1 :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 1 ≤ env.params.limits.maxOpsPerScript)
    (hl1 : b1.length ≤ env.params.limits.maxScriptNumLength)
    (hl2 : b2.length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (if decode b1 ≤ decode b2 then 1 else 0)).length + elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_LESSTHANOREQUAL] t st =
      .next { st with opCount := st.opCount + 1,
                      stack := encode (if decode b1 ≤ decode b2 then 1 else 0) :: rest,
                      memUsed := st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
                        (encode (if decode b1 ≤ decode b2 then 1 else 0)).length + elementOverhead } := by
  have hops' : ¬ (st.opCount + 1 > env.params.limits.maxOpsPerScript) := by omega
  have hl1' : ¬ (env.params.limits.maxScriptNumLength < b1.length) := by omega
  have hl2' : ¬ (env.params.limits.maxScriptNumLength < b2.length) := by omega
  have hmem' : ¬ (st.memUsed - (b2.length + elementOverhead) - (b1.length + elementOverhead) +
      (encode (if decode b1 ≤ decode b2 then 1 else 0)).length + elementOverhead >
      env.params.limits.maxStackMemoryUsage) := by omega
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

/-- **`OP_11`** (`488–507`): the small integer `11` pushed as `[0x0b]`; no opcode counted. -/
theorem run_op11 (env : Env) (t : Bytes) (st : State) (he : Exec env st)
    (hmem : st.memUsed + 1 + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env [Op.OP_11] t st =
      .next { st with stack := [11] :: st.stack, memUsed := st.memUsed + 1 + elementOverhead } := by
  have hmem' : ¬ (env.params.limits.maxStackMemoryUsage < st.memUsed + 1 + elementOverhead) := by omega
  have h11 : encode (11 : Int) = [11] := by decide
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run.eq_2]
  step_simp

end BoltProof.Gadgets
