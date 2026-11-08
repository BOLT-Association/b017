import BoltProof.Bridge.Glue.Refine.MinSimple
import BoltProof.Bridge.Generated.Vectors

/-!
# Regression and vacuity guards for the `MinSimpleBOLT` refinement

The refinement theorem `minSimple_refines` (`Refine/MinSimple.lean`) takes a dozen hypotheses about the spend
besides the verdict. These guards evaluate, on the real `MinSimpleBOLT` vectors Layer 2 judges
(`Generated/Vectors.lean`), that the abstraction `spendOf` reads each honest spend as the model expects (its kind,
its outputs, its ancestor) and that every decidable hypothesis of the theorem holds of it, so the theorem applies to
real spends under the residual assumptions alone. Everything here is `native_decide` on concrete data, in the
`BoltProof.Bridge` namespace the axiom audit reserves for evaluator-trusted facts.
-/

set_option autoImplicit false

namespace BoltProof.Bridge.Glue

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Tx BsvScript.Sighash BsvScript.TxContext
open BoltProof.Bridge BoltProof.Bridge.Generated BoltProof.Glue.MinSimple BoltProof.Glue

/-- The stack the unlocking script of input `i` of a vector leaves. -/
def _root_.BoltProof.Bridge.Vec.stack1 (v : Vec) (i : Nat) : Option (List Bytes) := do
  let bs ← hexDecode v.txHex
  let tx ← decodeTx bs
  let inp ← tx.inputs[i]?
  let prev ← v.prevouts[i]?
  let lock ← hexDecode prev.script
  pure (evalScript Eval.opExec (mkEnv params (txContext tx i prev.satoshis) params.flags.forkAdjust (some lock))
    inp.scriptSig [] 0).2.stack

/-- The lock fields and the unlocking arguments of input `i`, read off the prevout script and the stack. -/
def _root_.BoltProof.Bridge.Vec.argsOf (v : Vec) (i : Nat) : Option (Fields × Args) := do
  let st ← v.stack1 i
  let prev ← v.prevouts[i]?
  let lock ← hexDecode prev.script
  let f ← decodeLock lock
  match st with
  | pre :: pk :: sig :: ben :: chg :: fund :: p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 :: p8 :: p9 :: p10 :: p11 :: p12 :: p13 :: p14 :: p15 :: p16 :: p17 :: p18 :: p19 :: p20 :: p21 :: p22 :: p23 :: p24 :: p25 :: _ =>
    some (f, ⟨pre, pk, sig, ben, chg, fund, ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25⟩⟩)
  | _ => none

/-- The spend at input `i` of a vector, as the model sees it. -/
def _root_.BoltProof.Bridge.Vec.spendOf (v : Vec) (i : Nat) : Option (Spend Bytes) := do
  let bs ← hexDecode v.txHex
  let tx ← decodeTx bs
  let (f, a) ← v.argsOf i
  pure (MinSimple.spendOf tx i f a)

/-- The shape of an output, for the guards: token 0, proof 1, P2PKH 2, other 3. -/
def shapeOf : Out Bytes → Nat
  | .token _ => 0
  | .proof _ => 1
  | .p2pkh _ => 2
  | .other => 3

/-- What a guard reads off a spend: its kind, its sighash byte, the shapes of the transaction's outputs,
whether the outputs start with the expected ones, and the shapes of the rebuilt ancestor's outputs. -/
def Spend.guard (s : Spend Bytes) : Kind × Nat × List Nat × Bool × Option (List Nat) :=
  (s.kind, s.sigHashType, s.tx.outputs.map shapeOf,
    s.tx.outputs.take (s.expectedOuts .nft).length == s.expectedOuts .nft,
    s.anc.map fun A => A.outputs.map shapeOf)

/-! ## The honest lifecycle, spend by spend

Each spend of the honest `MinSimpleBOLT` lifecycle, and the melt, read as the model expects: its kind, the
sighash byte, the outputs (token, proof and P2PKH change for a commit; token and change for a settle; change only
for a melt), the expected outputs in front, and, for the second settle, the rebuilt grandparent with its token,
proof and change outputs. -/

theorem guard_commit1 : (Vec.spendOf minsimple_honest_commit1 0).map Spend.guard =
    some (.commit, 0x41, [0, 1, 2], true, none) := by native_decide
theorem guard_settle1 : (Vec.spendOf minsimple_honest_settle1 0).map Spend.guard =
    some (.settle, 0x41, [0, 2], true, none) := by native_decide
theorem guard_commit2 : (Vec.spendOf minsimple_honest_commit2 0).map Spend.guard =
    some (.commit, 0x41, [0, 1, 2], true, none) := by native_decide
theorem guard_settle2 : (Vec.spendOf minsimple_honest_settle2 0).map Spend.guard =
    some (.settle, 0x41, [0, 2], true, some [0, 1, 2]) := by native_decide
theorem guard_melt : (Vec.spendOf minsimple_melt_unfunded 0).map Spend.guard =
    some (.melt, 0x41, [2], true, none) := by native_decide

/-! ## The refinement applies to the real spends

For each honest spend, every decidable hypothesis of `minSimple_refines` is checked on the vector's data, so
`Accepts` follows from the residual assumptions alone. -/

/-- The data of a vector's input `i`: the transaction, the prevout's value and script, the unlocking script. -/
structure Input where
  tx : Tx
  amt : Nat
  lock : Bytes
  scriptSig : Bytes

def _root_.BoltProof.Bridge.Vec.input (v : Vec) (i : Nat) : Option Input := do
  let bs ← hexDecode v.txHex
  let tx ← decodeTx bs
  let inp ← tx.inputs[i]?
  let prev ← v.prevouts[i]?
  let lock ← hexDecode prev.script
  pure ⟨tx, prev.satoshis, lock, inp.scriptSig⟩

def dummyInput : Input := ⟨⟨0, [], [], 0⟩, 0, [], []⟩
def dummyFields : Fields := ⟨[], [], [], [], [], []⟩
def dummyArgs : Args := ⟨[], [], [], [], [], [], ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩⟩

/-- The input, fields and arguments of a vector's spend, with dummies where the vector does not decode (the
guards above say it does). -/
def _root_.BoltProof.Bridge.Vec.inputD (v : Vec) (i : Nat) : Input := (v.input i).getD dummyInput
def _root_.BoltProof.Bridge.Vec.fieldsD (v : Vec) (i : Nat) : Fields := ((v.argsOf i).map Prod.fst).getD dummyFields
def _root_.BoltProof.Bridge.Vec.argsD (v : Vec) (i : Nat) : Args := ((v.argsOf i).map Prod.snd).getD dummyArgs

/-- The first commit of the honest lifecycle satisfies every decidable hypothesis of the refinement: `Accepts`
follows from the residual assumptions alone. -/
theorem commit1_refines (P : Prims Bytes)
    (hres : Residual P (Vec.inputD minsimple_honest_commit1 0).tx 0 (Vec.inputD minsimple_honest_commit1 0).amt
      (Vec.fieldsD minsimple_honest_commit1 0) (Vec.argsD minsimple_honest_commit1 0)) :
    Accepts P .nft (MinSimple.spendOf (Vec.inputD minsimple_honest_commit1 0).tx 0 (Vec.fieldsD minsimple_honest_commit1 0) (Vec.argsD minsimple_honest_commit1 0)) :=
  minSimple_refines P _ 0 _ _ _ [] (Vec.inputD minsimple_honest_commit1 0).scriptSig
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (fun _ => ⟨by native_decide, by native_decide⟩) (by native_decide)
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The second settle of the honest lifecycle, which rebuilds the grandparent, satisfies every decidable
hypothesis of the refinement. -/
theorem settle2_refines (P : Prims Bytes)
    (hres : Residual P (Vec.inputD minsimple_honest_settle2 0).tx 0 (Vec.inputD minsimple_honest_settle2 0).amt
      (Vec.fieldsD minsimple_honest_settle2 0) (Vec.argsD minsimple_honest_settle2 0)) :
    Accepts P .nft (MinSimple.spendOf (Vec.inputD minsimple_honest_settle2 0).tx 0 (Vec.fieldsD minsimple_honest_settle2 0) (Vec.argsD minsimple_honest_settle2 0)) :=
  minSimple_refines P _ 0 _ _ _ [] (Vec.inputD minsimple_honest_settle2 0).scriptSig
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (fun _ => ⟨by native_decide, by native_decide⟩) (by native_decide)
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The melt satisfies every decidable hypothesis of the refinement. -/
theorem melt_refines (P : Prims Bytes)
    (hres : Residual P (Vec.inputD minsimple_melt_unfunded 0).tx 0 (Vec.inputD minsimple_melt_unfunded 0).amt
      (Vec.fieldsD minsimple_melt_unfunded 0) (Vec.argsD minsimple_melt_unfunded 0)) :
    Accepts P .nft (MinSimple.spendOf (Vec.inputD minsimple_melt_unfunded 0).tx 0 (Vec.fieldsD minsimple_melt_unfunded 0) (Vec.argsD minsimple_melt_unfunded 0)) :=
  minSimple_refines P _ 0 _ _ _ [] (Vec.inputD minsimple_melt_unfunded 0).scriptSig
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (fun h => absurd h (by native_decide)) (by native_decide)
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

end BoltProof.Bridge.Glue
