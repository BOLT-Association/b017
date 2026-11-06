import BoltProof.Bridge.Glue.MinSimple.Spec

/-!
# The rebuild's two data-dependent arms

Two arms of `SerialBOLT`'s grandparent rebuild (suffix 686–1123) turn on the grandparent's own data, so a path
proof cannot decide them from its hypotheses. Each is read here as one step (`sym_block` on its first chunk,
`sym_skipblock` inside an inactive arm):

* suffix 806–815, the grandparent token's `genesisOutpoint` push: the flag (the `OP_BIN2NUM` of the piece that is
  the grandparent's own parent outpoint) popped, and the push on top kept when it holds, else replaced by 36 zero
  bytes (the genesis transaction's lock carries a null `genesisOutpoint`);
* suffix 816–872, the grandparent token's `mintData` push: the piece at depth 55 pushed with the opcode its length
  selects (`OP_0` when empty, a direct push up to 75 bytes, then `OP_PUSHDATA1`, `OP_PUSHDATA2`, `OP_PUSHDATA4`), the
  length bytes being the `OP_NUM2BIN` result `w` the arm computes (`mintPushOf`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SerialBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- The `mintData` push's width, less its payload, as the prologue computes it (suffix 16–30): one byte (a direct
push) up to 75 bytes, two (`OP_PUSHDATA1` and the length) beyond, where the arm also checks the length is at most 255. -/
theorem mintWidth_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {x : Int}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (SerialBolt.c16 ++ (SerialBolt.c20_if ++ (SerialBolt.c21 ++ (SerialBolt.c22_else ++ (SerialBolt.c23 ++ (SerialBolt.c30_endif ++ k)))))) t (St (encode x :: S) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', (¬ x ≤ 75 → x ≤ 255) ∧
      run Eval.opExec env k t (St (encode (if x ≤ 75 then 1 else 2) :: encode x :: S) A m' C k' cs) = r := by
  simp only [SerialBolt.c16, SerialBolt.c20_if, SerialBolt.c21, SerialBolt.c22_else, SerialBolt.c23, SerialBolt.c30_endif, List.cons_append, List.nil_append] at h
  by_cases hx : x ≤ 75
  · sym_all h hx
    exact ⟨_, _, fun h' => absurd hx h', by simp only [hx, ↓reduceIte, show encode 1 = [1] by decide]; with_reducible exact h⟩
  · sym_all h hx
    refine ⟨_, _, fun _ => ?_, by simp only [hx, ↓reduceIte]; with_reducible exact h⟩
    revert h; simp only [castToBool_encode_ite, decide_eq_true_eq] at *; intro h
    with_reducible assumption

macro_rules
  | `(tactic| sym_blockrule "c16" $h:ident $hact:ident) =>
    `(tactic| (obtain ⟨_, _, _, $h:ident⟩ := mintWidth_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))

theorem num2bin_nil_36 : num2bin [] 36 = some (List.replicate 36 0) := by decide

/-- The grandparent's `genesisOutpoint` push: `y` when the flag holds, else the null outpoint. -/
def genesisPushOf (flag y : Bytes) : Bytes := if castToBool flag then y else 36 :: List.replicate 36 0

/-- The arm `[806, 816)`, as one step: the flag popped, the push on top replaced by `genesisPushOf`. -/
theorem genesisArm_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {flag y : Bytes}
    {rest A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (SerialBolt.c806_notif ++ (SerialBolt.c807 ++ (SerialBolt.c815_endif ++ k))) t (St (flag :: y :: rest) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (genesisPushOf flag y :: rest) A m' C k' cs) = r := by
  simp only [SerialBolt.c806_notif, SerialBolt.c807, SerialBolt.c815_endif, List.cons_append, List.nil_append] at h
  cases hflag : castToBool flag
  · sym_all h hflag
    rename_i w hw _ _
    rw [show (decode [36]).toNat = 36 by decide, num2bin_nil_36, Option.some.injEq] at hw
    subst hw
    exact ⟨_, _, by simp only [genesisPushOf, hflag, Bool.false_eq_true, ↓reduceIte]; with_reducible exact h⟩
  · sym_all h hflag
    exact ⟨_, _, by simp only [genesisPushOf, hflag, ↓reduceIte]; with_reducible exact h⟩

/-- The arm inside an inactive arm: stepped over. -/
theorem genesisArm_skip {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {S A : List Bytes} {D : Cond} {cs : Bytes}
    {m kk : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (SerialBolt.c806_notif ++ (SerialBolt.c807 ++ (SerialBolt.c815_endif ++ k))) t (St S A m D kk cs) = r) (hr : r.IsOk) :
    ∃ k', run Eval.opExec env k t (St S A m D k' cs) = r := by
  simp only [SerialBolt.c806_notif, SerialBolt.c807, SerialBolt.c815_endif, List.cons_append, List.nil_append] at h
  sym_skip h hin
  exact ⟨_, h⟩

macro_rules
  | `(tactic| sym_blockrule "c806_notif" $h:ident $hact:ident) =>
    `(tactic| (obtain ⟨_, _, $h:ident⟩ := genesisArm_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))
macro_rules
  | `(tactic| sym_skipblockrule "c806_notif" $h:ident $hin:ident) =>
    `(tactic| (obtain ⟨_, $h:ident⟩ := genesisArm_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf,
      Bool.and_false, Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)))

/-- The width `OP_NUM2BIN` writes a long push's length in: two bytes for `OP_PUSHDATA1` (the second is the sign
byte the arm drops), three for `OP_PUSHDATA2`, five for `OP_PUSHDATA4`. -/
def mintLenWidth (n : Int) : Nat := if n ≤ 255 then 2 else if n ≤ 65535 then 3 else 5

/-- The grandparent's `mintData` push as the arm writes it, `w` the length's `OP_NUM2BIN` word (`mintLenWidth`). -/
def mintPushOf (x w : Bytes) : Bytes :=
  if ((List.length x : Nat) : Int) = 0 then [0]
  else if ((List.length x : Nat) : Int) ≤ 75 then encode ((List.length x : Nat) : Int) ++ x
  else if ((List.length x : Nat) : Int) ≤ 255 then 76 :: (List.take (((List.length w : Nat) : Int) - 1).toNat w ++ x)
  else if ((List.length x : Nat) : Int) ≤ 65535 then 77 :: (List.take (((List.length w : Nat) : Int) - 1).toNat w ++ x)
  else 78 :: (List.take (((List.length w : Nat) : Int) - 1).toNat w ++ x)

/-- The arm `[816, 873)`, as one step: the push of the piece at depth 55 (`rest[54]`, below the accumulator `acc`)
on top, under the width the arm's `OP_NUM2BIN` fixes. -/
theorem mintArm_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {acc : Bytes}
    {rest A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (SerialBolt.c816 ++ (SerialBolt.c822_if ++ (SerialBolt.c823 ++ (SerialBolt.c827_if ++ (SerialBolt.c828_else ++ (SerialBolt.c829 ++ (SerialBolt.c834_if ++ (SerialBolt.c835 ++ (SerialBolt.c839_else ++ (SerialBolt.c840 ++ (SerialBolt.c846_if ++ (SerialBolt.c847 ++ (SerialBolt.c851_else ++ (SerialBolt.c852 ++ (SerialBolt.c856_endif ++ (SerialBolt.c857_endif ++ (SerialBolt.c858 ++ (SerialBolt.c865_endif ++ (SerialBolt.c866 ++ (SerialBolt.c868_else ++ (SerialBolt.c869 ++ (SerialBolt.c872_endif ++ k)))))))))))))))))))))) t (St (acc :: rest) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ (w : Bytes) (m' k' : Nat),
      (¬ ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ 75 →
        num2bin (encode ((List.length (rest[54]?.getD []) : Nat) : Int))
          (mintLenWidth ((List.length (rest[54]?.getD []) : Nat) : Int)) = some w) ∧
      run Eval.opExec env k t (St (mintPushOf (rest[54]?.getD []) w :: acc :: rest) A m' C k' cs) = r := by
  simp only [SerialBolt.c816, SerialBolt.c822_if, SerialBolt.c823, SerialBolt.c827_if, SerialBolt.c828_else, SerialBolt.c829, SerialBolt.c834_if, SerialBolt.c835, SerialBolt.c839_else, SerialBolt.c840, SerialBolt.c846_if, SerialBolt.c847, SerialBolt.c851_else, SerialBolt.c852, SerialBolt.c856_endif, SerialBolt.c857_endif, SerialBolt.c858, SerialBolt.c865_endif, SerialBolt.c866, SerialBolt.c868_else, SerialBolt.c869, SerialBolt.c872_endif, List.cons_append, List.nil_append] at h
  have h65 : decode [255, 255, 0] = 65535 := by decide
  by_cases h0 : ((List.length (rest[54]?.getD []) : Nat) : Int) = 0
  · sym_all h h0
    exact ⟨[], _, _, fun h1 => absurd (by omega) h1, by simp only [mintPushOf, h0, ↓reduceIte]; with_reducible exact h⟩
  by_cases h1 : ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ 75
  · sym_all h h0 h1
    exact ⟨[], _, _, fun h1' => absurd h1 h1', by simp only [mintPushOf, h0, h1, ↓reduceIte]; with_reducible exact h⟩
  by_cases h2 : ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ 255
  · sym_all h h0 h1 h2
    refine ⟨_, _, _, fun _ => ?_, by simp only [mintPushOf, h0, h1, h2, ↓reduceIte]; with_reducible exact h⟩
    simp only [mintLenWidth, h2, ↓reduceIte]
    revert h; simp only [decode_encode, Nat.cast_one, Int.reduceAdd, Int.reduceToNat] at *; intro h
    with_reducible assumption
  have h3' : ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ 65535 ∨
      ¬ ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ 65535 := Classical.em _
  rcases h3' with h3' | h3'
  · have h3 : ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ decode [255, 255, 0] := by rw [h65]; exact h3'
    sym_all h h0 h1 h2 h3
    refine ⟨_, _, _, fun _ => ?_, by simp only [mintPushOf, h0, h1, h2, h3', ↓reduceIte]; with_reducible exact h⟩
    simp only [mintLenWidth, h2, h3', ↓reduceIte]
    revert h; simp only [decode_encode, Int.reduceToNat] at *; intro h
    with_reducible assumption
  · have h3 : ¬ ((List.length (rest[54]?.getD []) : Nat) : Int) ≤ decode [255, 255, 0] := by rw [h65]; exact h3'
    sym_all h h0 h1 h2 h3
    refine ⟨_, _, _, fun _ => ?_, by simp only [mintPushOf, h0, h1, h2, h3', ↓reduceIte]; with_reducible exact h⟩
    simp only [mintLenWidth, h2, h3', ↓reduceIte]
    revert h; simp only [decode_encode, Int.reduceToNat] at *; intro h
    with_reducible assumption

/-- The arm inside an inactive arm: stepped over. -/
theorem mintArm_skip {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {S A : List Bytes} {D : Cond} {cs : Bytes}
    {m kk : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (SerialBolt.c816 ++ (SerialBolt.c822_if ++ (SerialBolt.c823 ++ (SerialBolt.c827_if ++ (SerialBolt.c828_else ++ (SerialBolt.c829 ++ (SerialBolt.c834_if ++ (SerialBolt.c835 ++ (SerialBolt.c839_else ++ (SerialBolt.c840 ++ (SerialBolt.c846_if ++ (SerialBolt.c847 ++ (SerialBolt.c851_else ++ (SerialBolt.c852 ++ (SerialBolt.c856_endif ++ (SerialBolt.c857_endif ++ (SerialBolt.c858 ++ (SerialBolt.c865_endif ++ (SerialBolt.c866 ++ (SerialBolt.c868_else ++ (SerialBolt.c869 ++ (SerialBolt.c872_endif ++ k)))))))))))))))))))))) t (St S A m D kk cs) = r) (hr : r.IsOk) :
    ∃ k', run Eval.opExec env k t (St S A m D k' cs) = r := by
  simp only [SerialBolt.c816, SerialBolt.c822_if, SerialBolt.c823, SerialBolt.c827_if, SerialBolt.c828_else, SerialBolt.c829, SerialBolt.c834_if, SerialBolt.c835, SerialBolt.c839_else, SerialBolt.c840, SerialBolt.c846_if, SerialBolt.c847, SerialBolt.c851_else, SerialBolt.c852, SerialBolt.c856_endif, SerialBolt.c857_endif, SerialBolt.c858, SerialBolt.c865_endif, SerialBolt.c866, SerialBolt.c868_else, SerialBolt.c869, SerialBolt.c872_endif, List.cons_append, List.nil_append] at h
  sym_skip h hin
  exact ⟨_, h⟩

macro_rules
  | `(tactic| sym_blockrule "c816" $h:ident $hact:ident) =>
    `(tactic| (obtain ⟨_, _, _, _, $h:ident⟩ := mintArm_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))
macro_rules
  | `(tactic| sym_skipblockrule "c816" $h:ident $hin:ident) =>
    `(tactic| (obtain ⟨_, $h:ident⟩ := mintArm_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf,
      Bool.and_false, Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)))

end BoltProof.Glue.SerialBolt
