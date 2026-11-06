import BoltProof.Bridge.Glue.SerialBolt.Refine
import BoltProof.Bridge.Glue.Regress
import BoltProof.Bridge.Generated.Vectors

/-!
# Regression and vacuity guards for the `SerialBOLT` refinement

The refinement theorem `serialBolt_refines` (`SerialBolt/Refine.lean`) takes a dozen hypotheses about the spend
besides the verdict. These guards evaluate, on the real `SerialBOLT` vectors Layer 2 judges
(`Generated/Vectors.lean`), that the abstraction `spendOf` reads each honest spend as the model expects (its kind,
its outputs, its ancestor) and that every decidable hypothesis of the theorem holds of it, so the theorem applies to
real spends under the residual assumptions alone. Everything here is `native_decide` on concrete data, in the
`BoltProof.Bridge` namespace the axiom audit reserves for evaluator-trusted facts.
-/

set_option autoImplicit false

namespace BoltProof.Bridge.Glue.SerialBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Tx BsvScript.Sighash BsvScript.TxContext
open BoltProof.Bridge BoltProof.Bridge.Generated BoltProof.Glue.SerialBolt BoltProof.Glue
open BoltProof.Bridge.Glue (shapeOf Input dummyInput)

/-- The lock fields and the unlocking arguments of input `i`, read off the prevout script and the stack: the six
named arguments, then the 27 pieces. -/
def serialArgsOf (v : Vec) (i : Nat) : Option (Fields × Args) := do
  let st ← v.stack1 i
  let prev ← v.prevouts[i]?
  let lock ← hexDecode prev.script
  let f ← decodeLock lock
  match st with
  | pre :: pk :: sig :: ben :: chg :: fund :: p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 :: p8 :: p9 :: p10 :: p11 :: p12 :: p13 :: p14 :: p15 :: p16 :: p17 :: p18 :: p19 :: p20 :: p21 :: p22 :: p23 :: p24 :: p25 :: p26 :: _ =>
    some (f, ⟨pre, pk, sig, ben, chg, fund, ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26⟩⟩)
  | _ => none

/-- The spend at input `i` of a vector, as the model sees it. -/
def serialSpendOf (v : Vec) (i : Nat) : Option (Spend Bytes) := do
  let bs ← hexDecode v.txHex
  let tx ← decodeTx bs
  let (f, a) ← serialArgsOf v i
  pure (SerialBolt.spendOf tx i f a)

/-- What a guard reads off a spend: its kind, its sighash byte, the shapes of the transaction's outputs,
whether the outputs start with the expected ones, and the shapes of the rebuilt ancestor's outputs. -/
def serialGuard (s : Spend Bytes) : Kind × Nat × List Nat × Bool × Option (List Nat) :=
  (s.kind, s.sigHashType, s.tx.outputs.map shapeOf,
    s.tx.outputs.take (s.expectedOuts .nft).length == s.expectedOuts .nft,
    s.anc.map fun A => A.outputs.map shapeOf)

/-! ## The honest lifecycle, spend by spend

Each spend of the honest `SerialBOLT` lifecycle, and the melt, read as the model expects: its kind, the
sighash byte, the outputs (token, proof and P2PKH change for a commit; token and change for a settle; change only
for a melt), the expected outputs in front, and, for the second settle, the rebuilt grandparent with its token,
proof and change outputs. -/

theorem guard_commit1 : (serialSpendOf serial_honest_commit1 0).map serialGuard =
    some (.commit, 0x41, [0, 1, 2], true, none) := by native_decide
theorem guard_settle1 : (serialSpendOf serial_honest_settle1 0).map serialGuard =
    some (.settle, 0x41, [0, 2], true, none) := by native_decide
theorem guard_commit2 : (serialSpendOf serial_honest_commit2 0).map serialGuard =
    some (.commit, 0x41, [0, 1, 2], true, none) := by native_decide
theorem guard_settle2 : (serialSpendOf serial_honest_settle2 0).map serialGuard =
    some (.settle, 0x41, [0, 2], true, some [0, 1, 2]) := by native_decide
theorem guard_melt : (serialSpendOf serial_melt_unfunded 0).map serialGuard =
    some (.melt, 0x41, [2], true, none) := by native_decide

/-! ## The refinement applies to the real spends

For each honest spend, every decidable hypothesis of `serialBolt_refines` is checked on the vector's data, so
`Accepts` follows from the residual assumptions alone. -/

def serialDummyFields : Fields := ⟨[], [], [], [], [], [], [], []⟩
def serialDummyArgs : Args := ⟨[], [], [], [], [], [], ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩⟩

/-- The input, fields and arguments of a vector's spend, with dummies where the vector does not decode (the
guards above say it does). -/
def serialFieldsD (v : Vec) (i : Nat) : Fields := ((serialArgsOf v i).map Prod.fst).getD serialDummyFields
def serialArgsD (v : Vec) (i : Nat) : Args := ((serialArgsOf v i).map Prod.snd).getD serialDummyArgs

/-- The first commit of the honest lifecycle satisfies every decidable hypothesis of the refinement: `Accepts`
follows from the residual assumptions alone. -/
theorem commit1_refines (P : Prims Bytes)
    (hres : Residual P (Vec.inputD serial_honest_commit1 0).tx 0 (Vec.inputD serial_honest_commit1 0).amt
      (serialFieldsD serial_honest_commit1 0) (serialArgsD serial_honest_commit1 0)) :
    Accepts P .nft (SerialBolt.spendOf (Vec.inputD serial_honest_commit1 0).tx 0 (serialFieldsD serial_honest_commit1 0) (serialArgsD serial_honest_commit1 0)) :=
  serialBolt_refines P _ 0 _ _ _ [] (Vec.inputD serial_honest_commit1 0).scriptSig
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩
    (fun _ => ⟨by native_decide, by native_decide⟩) (by native_decide)
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The second settle of the honest lifecycle, which rebuilds the grandparent, satisfies every decidable
hypothesis of the refinement. -/
theorem settle2_refines (P : Prims Bytes)
    (hres : Residual P (Vec.inputD serial_honest_settle2 0).tx 0 (Vec.inputD serial_honest_settle2 0).amt
      (serialFieldsD serial_honest_settle2 0) (serialArgsD serial_honest_settle2 0)) :
    Accepts P .nft (SerialBolt.spendOf (Vec.inputD serial_honest_settle2 0).tx 0 (serialFieldsD serial_honest_settle2 0) (serialArgsD serial_honest_settle2 0)) :=
  serialBolt_refines P _ 0 _ _ _ [] (Vec.inputD serial_honest_settle2 0).scriptSig
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩
    (fun _ => ⟨by native_decide, by native_decide⟩) (by native_decide)
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The melt satisfies every decidable hypothesis of the refinement. -/
theorem melt_refines (P : Prims Bytes)
    (hres : Residual P (Vec.inputD serial_melt_unfunded 0).tx 0 (Vec.inputD serial_melt_unfunded 0).amt
      (serialFieldsD serial_melt_unfunded 0) (serialArgsD serial_melt_unfunded 0)) :
    Accepts P .nft (SerialBolt.spendOf (Vec.inputD serial_melt_unfunded 0).tx 0 (serialFieldsD serial_melt_unfunded 0) (serialArgsD serial_melt_unfunded 0)) :=
  serialBolt_refines P _ 0 _ _ _ [] (Vec.inputD serial_melt_unfunded 0).scriptSig
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩
    (fun h => absurd h (by native_decide)) (by native_decide)
    ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

end BoltProof.Bridge.Glue.SerialBolt
