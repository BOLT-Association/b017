import BsvScript.Eval
import BsvScript.TxContext
import BsvScript.Tx
import BsvScript.Flags
import BsvScript.Params

/-!
# BoltProof.Bridge.Params

Layer 2 plumbing: evaluate one input of a real transaction with the bsv-script-lean consensus
semantics, under post-Chronicle mainnet consensus parameters, and compare the verdict with an
expectation.

Why post-Chronicle: b017's OP_PUSH_TX signs the preimage over
`OP_CHECKSIGVERIFY OP_ENDIF ++ lockingScript` (`splitCtx(ctx, 2)` in `src/lib/boltLib.ts`),
which is the scriptCode the Chronicle rules give code inside the *unlocking* script
(`codeSep ++ lock`). `paramsPreChronicle` is kept as a negative control only.
-/

namespace BoltProof.Bridge

open BsvScript BsvScript.Params BsvScript.Machine BsvScript.Tx BsvScript.TxContext

/-- The block height every vector is judged at: `defaultSpendHeight` (post-Chronicle). -/
def spendHeight : Nat := defaultSpendHeight

/-- Mainnet consensus parameters (block path) at `spendHeight`, UTXOs created at the same height. -/
def params : EvalParams := derive NodeConfig.svMainnetDefault spendHeight spendHeight true

/-- Post-Genesis, pre-Chronicle parameters: a negative control, not the judging set. -/
def paramsPreChronicle : EvalParams := derive NodeConfig.svMainnetDefault 900000 900000 true

/-- The output an input spends: its locking script (hex) and value. -/
structure Prevout where
  script : String
  satoshis : Nat
deriving Repr

/-- What a vector expects of one input. -/
inductive Expect
  /-- The spend must verify. -/
  | valid
  /-- The spend must fail with exactly this `ScriptError.name`. -/
  | invalid (code : String)
  /-- The spend must fail; the code is not pinned yet. -/
  | anyInvalid
  /-- Not evaluated (no prevout available, e.g. an external funding input). -/
  | skip
deriving Repr, DecidableEq

/-- A real transaction with its prevouts and the expected verdict of every input. -/
structure Vec where
  name : String
  family : String
  txHex : String
  prevouts : List Prevout
  expect : List Expect
  note : String := ""
deriving Repr

/-- Decode hex, or `[]`. -/
def hexDecode! (s : String) : BsvScript.Numbers.Bytes := (hexDecode s).getD []

/-- A verdict as a short string. -/
def Verdict.code : Verdict → String
  | .valid => "valid"
  | .invalid e => e.name
  | .unimplemented op => s!"unimplemented:{op}"
  | .undefinedInReference f => s!"undefined:{f}"

/-- The consensus verdict on input `i` of the vector's transaction, under `p`. `none` when the
transaction or the prevout cannot be decoded. -/
def Vec.verdict (p : EvalParams) (v : Vec) (i : Nat) : Option Verdict := do
  let bs ← hexDecode v.txHex
  let tx ← decodeTx bs
  let inp ← tx.inputs[i]?
  let prev ← v.prevouts[i]?
  let script ← hexDecode prev.script
  pure (Eval.verifyScript p (txContext tx i prev.satoshis) inp.scriptSig script)

/-- Does a verdict meet an expectation? -/
def Expect.matches : Expect → Option Verdict → Bool
  | .skip, _ => true
  | .valid, some .valid => true
  | .invalid code, some (.invalid e) => e.name == code
  | .anyInvalid, some (.invalid _) => true
  | _, _ => false

/-- Every input of the vector meets its expectation under `p`. This is the statement the
`native_decide` theorems of `Generated/VectorTheorems.lean` establish. -/
def Vec.check (p : EvalParams) (v : Vec) : Bool :=
  v.expect.length == v.prevouts.length &&
    (List.range v.expect.length).all fun i =>
      match v.expect[i]? with
      | some e => e.matches (v.verdict p i)
      | none => false

end BoltProof.Bridge
