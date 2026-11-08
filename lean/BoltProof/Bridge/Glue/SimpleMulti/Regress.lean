import BoltProof.Bridge.Glue.Regress
import BoltProof.Bridge.Glue.SimpleMulti.RefineMergeSettle

/-!
# Regression and vacuity guards for the `SimpleMultiBOLT` refinement

The fungible refinement theorems (`simpleMulti_refines_basic`, `simpleMulti_refines_settle_gp`,
`simpleMulti_refines_merge_commit`, `simpleMulti_refines_merge_settle`) take, besides the verdict, hypotheses
about the spend and scope assumptions about its pieces and ancestors. These guards evaluate them on the real
`SimpleMultiBOLT` vectors Layer 2 judges (`Generated/Vectors.lean`): the abstraction reads each honest spend as
the model expects (its kind, mode, outputs), and every decidable hypothesis holds of it, including the scope
assumptions `HonestPiecesB`, the index argument and the decidable parts of `GpRealF` and `GpRealB` against the
real grandparents, so the theorems apply to real spends. Everything here is `native_decide` on concrete data, in
the `BoltProof.Bridge` namespace the axiom audit reserves for evaluator-trusted facts.
-/

set_option autoImplicit false

namespace BoltProof.Bridge.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Tx BsvScript.Sighash BsvScript.TxContext
open BoltProof.Bridge BoltProof.Bridge.Generated BoltProof.Glue.SimpleMulti BoltProof.Glue
open BoltProof.Bridge.Glue (shapeOf Input)

/-- Seventy-five pieces read off a list, in stack order. -/
def piecesOf (l : List Bytes) : Pieces75 := ⟨l.getD 0 [], l.getD 1 [], l.getD 2 [], l.getD 3 [], l.getD 4 [], l.getD 5 [], l.getD 6 [], l.getD 7 [], l.getD 8 [], l.getD 9 [], l.getD 10 [], l.getD 11 [], l.getD 12 [], l.getD 13 [], l.getD 14 [], l.getD 15 [], l.getD 16 [], l.getD 17 [], l.getD 18 [], l.getD 19 [], l.getD 20 [], l.getD 21 [], l.getD 22 [], l.getD 23 [], l.getD 24 [], l.getD 25 [], l.getD 26 [], l.getD 27 [], l.getD 28 [], l.getD 29 [], l.getD 30 [], l.getD 31 [], l.getD 32 [], l.getD 33 [], l.getD 34 [], l.getD 35 [], l.getD 36 [], l.getD 37 [], l.getD 38 [], l.getD 39 [], l.getD 40 [], l.getD 41 [], l.getD 42 [], l.getD 43 [], l.getD 44 [], l.getD 45 [], l.getD 46 [], l.getD 47 [], l.getD 48 [], l.getD 49 [], l.getD 50 [], l.getD 51 [], l.getD 52 [], l.getD 53 [], l.getD 54 [], l.getD 55 [], l.getD 56 [], l.getD 57 [], l.getD 58 [], l.getD 59 [], l.getD 60 [], l.getD 61 [], l.getD 62 [], l.getD 63 [], l.getD 64 [], l.getD 65 [], l.getD 66 [], l.getD 67 [], l.getD 68 [], l.getD 69 [], l.getD 70 [], l.getD 71 [], l.getD 72 [], l.getD 73 [], l.getD 74 []⟩

/-- The unlocking arguments read off the stack the unlocking script leaves, with what lies below them. -/
def argsOfStack : List Bytes → Option (Args × List Bytes)
  | pre :: pk :: sig :: inIdx :: nty :: nbc :: pkh2 :: pkh1 :: chg :: fund :: i1 :: i2 :: i3 :: i4 :: i5 :: rest =>
    if 150 ≤ rest.length then
      some (⟨pre, pk, sig, inIdx, nty, nbc, pkh2, pkh1, chg, fund, i1, i2, i3, i4, i5, piecesOf (rest.take 75),
        piecesOf ((rest.drop 75).take 75)⟩, rest.drop 150)
    else none
  | _ => none

/-- A vector's transaction. -/
def txOf (v : Vec) : Option Tx := do decodeTx (← hexDecode v.txHex)

/-- The lock fields and the unlocking arguments of input `i`. -/
def smArgs (v : Vec) (i : Nat) : Option (Fields × Args × List Bytes) := do
  let st ← v.stack1 i
  let prev ← v.prevouts[i]?
  let lock ← hexDecode prev.script
  let f ← decodeLock lock
  let (a, S) ← argsOfStack st
  pure (f, a, S)

/-- What a guard reads off a spend: its kind, its mode, its sighash byte, the shapes of the transaction's outputs,
and whether the outputs start with the expected ones. -/
def guardF (s : Spend Bytes) : Kind × Mode × Nat × List Nat × Bool :=
  (s.kind, s.mode, s.sigHashType, s.tx.outputs.map shapeOf,
    s.tx.outputs.take (s.expectedOuts .fungible).length == s.expectedOuts .fungible)

/-- The spend at input `i` of a vector, as the model sees it, with the other token input of a merge commit and
the rebuilt ancestors given. -/
def smSpend (v : Vec) (i : Nat) (other : Option (Fields × Outpoint Bytes)) (ancA ancB : Option Tx) :
    Option (Spend Bytes) := do
  let tx ← txOf v
  let (f, a, _) ← smArgs v i
  pure (BoltProof.Glue.SimpleMulti.spendOf tx i f a other ancA ancB)

/-- The other token input of a merge commit, read off input `j`: its lock fields and its outpoint. -/
def smOther (v : Vec) (j : Nat) : Option (Fields × Outpoint Bytes) := do
  let tx ← txOf v
  let (f, _, _) ← smArgs v j
  let inp ← tx.inputs[j]?
  pure (f, ⟨inp.prevHash, inp.prevIndex⟩)

/-! ## The honest lifecycles, spend by spend

Each spend of the two honest `SimpleMultiBOLT` lifecycles, read as the model expects: its kind and mode, the
sighash byte, the outputs (token, proof, the split's second proof and change for a commit; the settled tokens and
change for a settle; change only for a melt), and the expected outputs in front. A merge commit's first input is
read with the other token input, whose balance the merged token carries. -/

theorem guard_a_commit1 : (smSpend smb_honest_a_commit1 0 none none none).map guardF =
    some (.commit, .transfer, 0x41, [0, 1, 2], true) := by native_decide
theorem guard_a_settle1 : (smSpend smb_honest_a_settle1 0 none none none).map guardF =
    some (.settle, .transfer, 0x41, [0, 2], true) := by native_decide
theorem guard_a_commit2 : (smSpend smb_honest_a_commit2 0 none none none).map guardF =
    some (.commit, .transfer, 0x41, [0, 1, 2], true) := by native_decide
theorem guard_a_settle2 : (smSpend smb_honest_a_settle2 0 none none none).map guardF =
    some (.settle, .transfer, 0x41, [0, 2], true) := by native_decide
theorem guard_a_splitCommit : (smSpend smb_honest_a_splitCommit 0 none none none).map guardF =
    some (.commit, .split, 0x41, [0, 1, 1, 2], true) := by native_decide
theorem guard_a_splitSettle : (smSpend smb_honest_a_splitSettle 0 none none none).map guardF =
    some (.settle, .split, 0x41, [0, 0, 2], true) := by native_decide
theorem guard_b_mergeCommit : (smSpend smb_honest_b_mergeCommit 0 (smOther smb_honest_b_mergeCommit 1) none none).map
    guardF = some (.commit, .merge, 0x41, [0, 1, 2], true) := by native_decide
theorem guard_b_mergeSettle : (smSpend smb_honest_b_mergeSettle 0 none none none).map guardF =
    some (.settle, .merge, 0x41, [0, 2], true) := by native_decide
theorem guard_b_melt : (smSpend smb_honest_b_melt 0 none none none).map guardF =
    some (.melt, .transfer, 0x41, [2], true) := by native_decide

/-! ## Decidable forms of the scope assumptions -/

/-- An outpoint field read as the model reads it satisfies a decidable property, checked as a boolean. -/
def outpointAll (b : Bytes) (p : Outpoint Bytes → Bool) : Bool :=
  match BoltProof.Glue.MinSimple.outpointOf b with
  | some q => p q
  | none => true

theorem of_outpointAll {b : Bytes} {p : Outpoint Bytes → Bool} (h : outpointAll b p = true) :
    ∀ q, BoltProof.Glue.MinSimple.outpointOf b = some q → p q = true := by
  intro q hq; unfold outpointAll at h; rw [hq] at h; exact h

def isTokenAt (l : List (Out Bytes)) (j : Nat) : Bool :=
  match l[j]? with
  | some (.token _) => true
  | _ => false

theorem of_isTokenAt {l : List (Out Bytes)} {j : Nat} (h : isTokenAt l j = true) : ∃ t, l[j]? = some (.token t) := by
  unfold isTokenAt at h
  split at h
  · rename_i t ht; exact ⟨t, ht⟩
  · cases h

def isProofAt (l : List (Out Bytes)) (j : Nat) : Bool :=
  match l[j]? with
  | some (.proof _) => true
  | _ => false

theorem of_isProofAt {l : List (Out Bytes)} {j : Nat} (h : isProofAt l j = true) : ∃ pkh, l[j]? = some (.proof pkh) := by
  unfold isProofAt at h
  split at h
  · rename_i pkh hp; exact ⟨pkh, hp⟩
  · cases h

def balsNonneg (G : Tx) : Bool :=
  G.outputs.all fun o => match decodeLock o.scriptPubKey with
    | some g => decide (0 ≤ decode g.bal ∧ 0 ≤ decode g.balCommit)
    | none => true

theorem of_balsNonneg {G : Tx} (h : balsNonneg G = true) :
    ∀ o ∈ G.outputs, ∀ g, decodeLock o.scriptPubKey = some g → 0 ≤ decode g.bal ∧ 0 ≤ decode g.balCommit := by
  intro o ho g hg
  unfold balsNonneg at h
  have := List.all_eq_true.mp h o ho
  rw [hg] at this
  exact of_decide_eq_true this



/-! ## The refinement applies to the real spends

For each honest spend the theorems cover, every decidable hypothesis of the refinement is checked on the vector's
data, so `Accepts` follows from the residual assumptions alone: `Residual` for each token input, and of the real
grandparents only what no evaluation decides (second-preimage freedom of their serialisation and the primitives'
id). The scope assumptions `HonestPiecesB`, the index arguments and the rest of `GpRealF` and `GpRealB` hold of the
honest lifecycles. -/

def dummyFields : Fields := ⟨[], [], [], [], [], [], [], [], [], [], []⟩
def dummyArgs : Args := ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], piecesOf [], piecesOf []⟩
def smFieldsD (v : Vec) (i : Nat) : Fields := ((smArgs v i).map (·.1)).getD dummyFields
def smArgsD (v : Vec) (i : Nat) : Args := ((smArgs v i).map (·.2.1)).getD dummyArgs
def txD (v : Vec) : Tx := (txOf v).getD ⟨0, [], [], 0⟩

instance (b : Bytes) : Decidable (SmbType b) := by unfold SmbType; exact inferInstance

/-- The first transfer commit of lifecycle A. -/
theorem a_commit1_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_a_commit1 0).tx 0 (Vec.inputD smb_honest_a_commit1 0).amt (smFieldsD smb_honest_a_commit1 0) (smArgsD smb_honest_a_commit1 0)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_a_commit1 0).tx 0 (smFieldsD smb_honest_a_commit1 0) (smArgsD smb_honest_a_commit1 0) none none none) :=
  simpleMulti_refines_basic P _ 0 _ _ _ [] (Vec.inputD smb_honest_a_commit1 0).scriptSig ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (fun _ => ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩) (by native_decide) (fun _ => by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    ⟨by native_decide, by native_decide⟩ (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The first transfer settle of lifecycle A, a token without a grandparent. -/
theorem a_settle1_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_a_settle1 0).tx 0 (Vec.inputD smb_honest_a_settle1 0).amt (smFieldsD smb_honest_a_settle1 0) (smArgsD smb_honest_a_settle1 0)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_a_settle1 0).tx 0 (smFieldsD smb_honest_a_settle1 0) (smArgsD smb_honest_a_settle1 0) none none none) :=
  simpleMulti_refines_basic P _ 0 _ _ _ [] (Vec.inputD smb_honest_a_settle1 0).scriptSig ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (fun _ => ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩) (by native_decide) (fun _ => by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    ⟨by native_decide, by native_decide⟩ (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The split commit of lifecycle A. -/
theorem a_splitCommit_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_a_splitCommit 0).tx 0 (Vec.inputD smb_honest_a_splitCommit 0).amt (smFieldsD smb_honest_a_splitCommit 0) (smArgsD smb_honest_a_splitCommit 0)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_a_splitCommit 0).tx 0 (smFieldsD smb_honest_a_splitCommit 0) (smArgsD smb_honest_a_splitCommit 0) none none none) :=
  simpleMulti_refines_basic P _ 0 _ _ _ [] (Vec.inputD smb_honest_a_splitCommit 0).scriptSig ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (fun _ => ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩) (by native_decide) (fun _ => by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    ⟨by native_decide, by native_decide⟩ (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The melt of lifecycle B. -/
theorem b_melt_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_b_melt 0).tx 0 (Vec.inputD smb_honest_b_melt 0).amt (smFieldsD smb_honest_b_melt 0) (smArgsD smb_honest_b_melt 0)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_b_melt 0).tx 0 (smFieldsD smb_honest_b_melt 0) (smArgsD smb_honest_b_melt 0) none none none) :=
  simpleMulti_refines_basic P _ 0 _ _ _ [] (Vec.inputD smb_honest_b_melt 0).scriptSig ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (fun h => absurd h (by native_decide)) (by native_decide) (fun h => absurd h (by native_decide)) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    ⟨by native_decide, by native_decide⟩ (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres (by native_decide) (by native_decide)

/-- The second transfer settle of lifecycle A, which rebuilds the first commit. -/
theorem a_settle2_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_a_settle2 0).tx 0 (Vec.inputD smb_honest_a_settle2 0).amt (smFieldsD smb_honest_a_settle2 0) (smArgsD smb_honest_a_settle2 0))
    (hnsp : BoltProof.Glue.MinSimple.NoSecondPreimage (serTx (txD smb_honest_a_commit1)))
    (hptxid : P.txid (absTx (txD smb_honest_a_commit1)) = Sighash.txid (txD smb_honest_a_commit1)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_a_settle2 0).tx 0 (smFieldsD smb_honest_a_settle2 0) (smArgsD smb_honest_a_settle2 0) none (some (txD smb_honest_a_commit1)) none) :=
  simpleMulti_refines_settle_gp P _ 0 _ _ _ [] (Vec.inputD smb_honest_a_settle2 0).scriptSig (txD smb_honest_a_commit1) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres
    ⟨⟨⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩, by native_decide, hnsp, hptxid, of_isTokenAt (by native_decide),
      fun p hp => of_isProofAt (of_outpointAll (p := fun q => isProofAt (absTx (txD smb_honest_a_commit1)).outputs (q.vout + 1)) (by native_decide) p hp),
      of_balsNonneg (by native_decide)⟩,
      ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩, by native_decide,
      fun p hp => of_decide_eq_true (of_outpointAll (p := fun q => decide (decode (smArgsD smb_honest_a_settle2 0).i5 = (q.vout : Int) + 1)) (by native_decide) p hp)⟩
    (by native_decide) (by native_decide)

/-- The split settle of lifecycle A, which rebuilds the second commit. -/
theorem a_splitSettle_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_a_splitSettle 0).tx 0 (Vec.inputD smb_honest_a_splitSettle 0).amt (smFieldsD smb_honest_a_splitSettle 0) (smArgsD smb_honest_a_splitSettle 0))
    (hnsp : BoltProof.Glue.MinSimple.NoSecondPreimage (serTx (txD smb_honest_a_commit2)))
    (hptxid : P.txid (absTx (txD smb_honest_a_commit2)) = Sighash.txid (txD smb_honest_a_commit2)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_a_splitSettle 0).tx 0 (smFieldsD smb_honest_a_splitSettle 0) (smArgsD smb_honest_a_splitSettle 0) none (some (txD smb_honest_a_commit2)) none) :=
  simpleMulti_refines_settle_gp P _ 0 _ _ _ [] (Vec.inputD smb_honest_a_splitSettle 0).scriptSig (txD smb_honest_a_commit2) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres
    ⟨⟨⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩, by native_decide, hnsp, hptxid, of_isTokenAt (by native_decide),
      fun p hp => of_isProofAt (of_outpointAll (p := fun q => isProofAt (absTx (txD smb_honest_a_commit2)).outputs (q.vout + 1)) (by native_decide) p hp),
      of_balsNonneg (by native_decide)⟩,
      ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩, by native_decide,
      fun p hp => of_decide_eq_true (of_outpointAll (p := fun q => decide (decode (smArgsD smb_honest_a_splitSettle 0).i5 = (q.vout : Int) + 1)) (by native_decide) p hp)⟩
    (by native_decide) (by native_decide)

/-- The merge commit of lifecycle B, at its first token input, given the second's run. -/
theorem b_mergeCommit_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_b_mergeCommit 0).tx 0 (Vec.inputD smb_honest_b_mergeCommit 0).amt (smFieldsD smb_honest_b_mergeCommit 0) (smArgsD smb_honest_b_mergeCommit 0)) (hres' : Residual P (Vec.inputD smb_honest_b_mergeCommit 0).tx 1 (Vec.inputD smb_honest_b_mergeCommit 1).amt (smFieldsD smb_honest_b_mergeCommit 1) (smArgsD smb_honest_b_mergeCommit 1)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_b_mergeCommit 0).tx 0 (smFieldsD smb_honest_b_mergeCommit 0) (smArgsD smb_honest_b_mergeCommit 0)
      (some ((smFieldsD smb_honest_b_mergeCommit 1), ⟨(inputAt (Vec.inputD smb_honest_b_mergeCommit 0).tx 1).prevHash, (inputAt (Vec.inputD smb_honest_b_mergeCommit 0).tx 1).prevIndex⟩)) none none) :=
  simpleMulti_refines_merge_commit P _ 0 _ _ _ [] (Vec.inputD smb_honest_b_mergeCommit 0).scriptSig 1 _ _ _ [] (Vec.inputD smb_honest_b_mergeCommit 1).scriptSig ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) hres hres' (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- The merge settle of lifecycle B, which rebuilds both lineages' commits. -/
theorem b_mergeSettle_refines (P : Prims Bytes) (hres : Residual P (Vec.inputD smb_honest_b_mergeSettle 0).tx 0 (Vec.inputD smb_honest_b_mergeSettle 0).amt (smFieldsD smb_honest_b_mergeSettle 0) (smArgsD smb_honest_b_mergeSettle 0))
    (hnsp : BoltProof.Glue.MinSimple.NoSecondPreimage (serTx (txD smb_honest_b_commit1)))
    (hptxid : P.txid (absTx (txD smb_honest_b_commit1)) = Sighash.txid (txD smb_honest_b_commit1))
    (hptxidB : P.txid (absTx (txD smb_honest_b_lineageB_commit1)) = Sighash.txid (txD smb_honest_b_lineageB_commit1)) :
    Accepts P .fungible (spendOf (Vec.inputD smb_honest_b_mergeSettle 0).tx 0 (smFieldsD smb_honest_b_mergeSettle 0) (smArgsD smb_honest_b_mergeSettle 0) none (some (txD smb_honest_b_commit1)) (some (txD smb_honest_b_lineageB_commit1))) :=
  simpleMulti_refines_merge_settle P _ 0 _ _ _ [] (Vec.inputD smb_honest_b_mergeSettle 0).scriptSig (txD smb_honest_b_commit1) (txD smb_honest_b_lineageB_commit1) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩ (by native_decide) (by native_decide) (by native_decide) hres
    ⟨⟨⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩, by native_decide, hnsp, hptxid, of_isTokenAt (by native_decide),
      fun p hp => of_isProofAt (of_outpointAll (p := fun q => isProofAt (absTx (txD smb_honest_b_commit1)).outputs (q.vout + 1)) (by native_decide) p hp),
      of_balsNonneg (by native_decide)⟩,
      ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩, by native_decide,
      fun p hp => of_decide_eq_true (of_outpointAll (p := fun q => decide (decode (smArgsD smb_honest_b_mergeSettle 0).i5 = (q.vout : Int) + 1)) (by native_decide) p hp)⟩
    ⟨by native_decide, hptxidB, of_isTokenAt (by native_decide), by native_decide, of_isProofAt (by native_decide)⟩ (by native_decide) (by native_decide)

end BoltProof.Bridge.Glue.SimpleMulti
