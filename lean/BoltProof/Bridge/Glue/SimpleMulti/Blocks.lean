import BoltProof.Bridge.Glue.SimpleMulti.Spec

/-!
# The fungible rebuild's blocks

Three pieces of the `SimpleMultiBOLT` suffix branch on the ancestor's data rather than on the
arguments, so a path proof cannot decide their conditionals from its hypotheses: the pad-to-16
loop after a balance sum or difference (suffix 797 and 950), the width-dependent optional push of
an ancestor piece inside the two rebuilds (fifty times), and the balance anchor on the ancestor's
type (2660 and 3835). Each is one exporter chunk (`lean/vectors/sections.ts`, the `auto`
landmarks), its run is read here as one step whose result is a function of the stack (`padN 16`,
`optPush`, the predicate `AnchorOK`), and `sym_block` (`Sym/Tactic.lean`) applies these lemmas
whenever `sym_all` meets one of the chunks folded.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-! ## The pad-to-16 loop -/

/-- One iteration: `SIZE 16 LESSTHAN IF 00 CAT ENDIF`. -/
def padIter : Bytes := [0x82, 0x60, 0x9f, 0x63, 0x01, 0x00, 0x7e, 0x68]

/-- What one iteration does: a zero byte appended while the string is shorter than 16 bytes. -/
def pad1 (x : Bytes) : Bytes := if x.length < 16 then x ++ [0] else x

/-- `n` iterations. -/
def padN : Nat → Bytes → Bytes
  | 0, x => x
  | n + 1, x => padN n (pad1 x)

/-- The loop: sixteen iterations. -/
def pad16Block : Bytes := (List.replicate 16 padIter).flatten

theorem padN_eq (n : Nat) (x : Bytes) : padN n x = x ++ List.replicate (min n (16 - x.length)) 0 := by
  induction n generalizing x with
  | zero => simp [padN]
  | succ n ih =>
    rw [padN, ih, pad1]
    split_ifs with hl
    · rw [List.append_assoc, List.singleton_append, ← List.replicate_succ, List.length_append, List.length_singleton]
      congr 2
      omega
    · rw [show 16 - x.length = 0 by omega]
      simp

theorem pad1_shape {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {x : Bytes} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (padIter ++ k) t (St (x :: S) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (pad1 x :: S) A m' C k' cs) = r := by
  simp only [padIter, List.cons_append, List.nil_append] at h
  by_cases hl : (x.length : Int) < 16
  · sym_all h hl
    exact ⟨_, _, by simp only [pad1, show x.length < 16 by omega, ↓reduceIte]; exact h⟩
  · sym_all h hl
    exact ⟨_, _, by simp only [pad1, show ¬ x.length < 16 by omega, ↓reduceIte]; exact h⟩

theorem padN_shape {env : Env} (he : EnvOK env) (n : Nat) {k t : Bytes} {r : GOut} {x : Bytes} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env ((List.replicate n padIter).flatten ++ k) t (St (x :: S) A m C kk cs) = r)
    (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (padN n x :: S) A m' C k' cs) = r := by
  induction n generalizing x m kk with
  | zero => exact ⟨_, _, h⟩
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc] at h
    obtain ⟨_, _, h⟩ := pad1_shape he hact h hr
    exact ih h

/-- The pad-to-16 loop, as one step: the top padded. -/
theorem pad16_shape {env : Env} (he : EnvOK env) {c k t : Bytes} {r : GOut} {x : Bytes} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (c ++ k) t (St (x :: S) A m C kk cs) = r) (hr : r.IsOk) (hc : c = pad16Block) :
    ∃ m' k', run Eval.opExec env k t (St (padN 16 x :: S) A m' C k' cs) = r := by
  subst hc
  exact padN_shape he 16 hact h hr

/-! ## The optional push -/

/-- The optional push's tail, after the width push: `SWAP SIZE ROT EQUAL IF SIZE SWAP CAT ELSE DROP 00
ENDIF CAT`. -/
def optTail : Bytes := [0x7c, 0x82, 0x7b, 0x87, 0x63, 0x82, 0x7c, 0x7e, 0x67, 0x75, 0x01, 0x00, 0x68, 0x7e]

/-- What the tail appends to the accumulator: the piece push-encoded when its size is the width
given, else `OP_0`. -/
def optPush (w p : Bytes) : Bytes := if encode (p.length : Int) = w then encode (p.length : Int) ++ p else [0]

theorem optPush_of_width {w p : Bytes} (hw : encode (p.length : Int) = w) : optPush w p = w ++ p := by
  simp only [optPush, hw, ↓reduceIte]

theorem optPush_of_not_width {w p : Bytes} (hw : ¬ encode (p.length : Int) = w) : optPush w p = [0] := by
  simp only [optPush, hw, ↓reduceIte]

/-- The optional push, as one step: the width and the piece consumed, the accumulator extended. -/
theorem optTail_shape {env : Env} (he : EnvOK env) {c k t : Bytes} {r : GOut} {w p acc : Bytes} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (c ++ k) t (St (w :: p :: acc :: S) A m C kk cs) = r) (hr : r.IsOk) (hc : c = optTail) :
    ∃ m' k', run Eval.opExec env k t (St ((acc ++ optPush w p) :: S) A m' C k' cs) = r := by
  subst hc
  simp only [optTail, List.cons_append, List.nil_append] at h
  by_cases hw : encode (p.length : Int) = w
  · sym_all h hw
    simp only [optPush, hw, ↓reduceIte] at h ⊢
    exact ⟨_, _, h⟩
  · sym_all h hw
    simp only [optPush, hw, ↓reduceIte] at h ⊢
    exact ⟨_, _, h⟩

/-! ## The balance anchor -/

/-- The anchor: on the ancestor's type (duplicated under its `0x25` test), the balance of the
spent token against the ancestor's two balances and its input count, suffix 2660 and 3835. -/
def anchor : Bytes := [0x63, 0x01, 0x43, 0x79, 0x81, 0x51, 0x88, 0x75, 0x93, 0x88, 0x67, 0x76, 0x01, 0x23, 0x87,
  0x63, 0x75, 0x01, 0x42, 0x79, 0x81, 0x51, 0x87, 0x63, 0x94, 0x88, 0x67, 0x01, 0x42, 0x79, 0x81, 0x52, 0x88,
  0x77, 0x87, 0x69, 0x68, 0x67, 0x01, 0x43, 0x79, 0x81, 0x51, 0x88, 0x75, 0x75, 0x88, 0x68, 0x68]

/-- What the anchor verifies, on the type test `c`, the type `ty`, the three balances and the
item `x` at depth 63 of the stack below them (the ancestor's input count): a merge settle's balance
is the sum, a split settle's the difference or the first piece, any other's the first balance. -/
def AnchorOK (c ty n3 n2 n1 x : Bytes) : Prop :=
  (castToBool c = true ∧ encode (decode x) = [1] ∧ n1 = encode (decode n2 + decode n3)) ∨
  (castToBool c = false ∧ ty = [0x23] ∧
    ((encode (decode x) = [1] ∧ n1 = encode (decode n2 - decode n3)) ∨ (encode (decode x) = [2] ∧ n1 = n3))) ∨
  (castToBool c = false ∧ ty ≠ [0x23] ∧ encode (decode x) = [1] ∧ n1 = n2)

theorem encode_two : encode 2 = [2] := by decide

theorem castToBool_ite_one_nil_eq_true (c : Prop) [Decidable c] : castToBool (if c then [1] else []) = true ↔ c := by
  split_ifs with hc <;> simp [hc, castToBool_one, castToBool_nil]

/-- The anchor, as one step: the five items consumed, the relation recorded. -/
theorem anchor_shape {env : Env} (he : EnvOK env) {c k t : Bytes} {r : GOut} {cnd ty n3 n2 n1 : Bytes}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (c ++ k) t (St (cnd :: ty :: n3 :: n2 :: n1 :: S) A m C kk cs) = r) (hr : r.IsOk)
    (hc : c = anchor) :
    AnchorOK cnd ty n3 n2 n1 (S[63]?.getD []) ∧ ∃ m' k', run Eval.opExec env k t (St S A m' C k' cs) = r := by
  subst hc
  simp only [anchor, List.cons_append, List.nil_append] at h
  cases hcnd : castToBool cnd
  · by_cases h23 : ty = [0x23]
    · by_cases h1 : encode (decode (S[63]?.getD [])) = [1]
      · sym_all h hcnd h23 h1
        exact ⟨Or.inr (Or.inl ⟨hcnd, h23, Or.inl ⟨h1, ‹_›⟩⟩), _, _, h⟩
      · sym_all h hcnd h23 h1
        refine ⟨Or.inr (Or.inl ⟨hcnd, h23, Or.inr ⟨?_, (castToBool_ite_one_nil_eq_true _).1 ‹_›⟩⟩), _, _, h⟩
        rwa [← encode_two]
    · sym_all h hcnd h23
      exact ⟨Or.inr (Or.inr ⟨hcnd, h23, ‹_›, ‹_›⟩), _, _, h⟩
  · sym_all h hcnd
    exact ⟨Or.inl ⟨hcnd, ‹_›, ‹_›⟩, _, _, h⟩

/-! ## The blocks inside an inactive arm -/

theorem pad16_skip {env : Env} (he : EnvOK env) {c k t : Bytes} {r : GOut} {S A : List Bytes} {D : Cond} {cs : Bytes}
    {m kk : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (c ++ k) t (St S A m D kk cs) = r) (hr : r.IsOk) (hc : c = pad16Block) :
    ∃ k', run Eval.opExec env k t (St S A m D k' cs) = r := by
  subst hc
  simp only [pad16Block, padIter, List.replicate, List.flatten, List.append_eq, List.cons_append, List.nil_append,
    List.append_assoc] at h
  sym_skip h hin
  exact ⟨_, h⟩

theorem optTail_skip {env : Env} (he : EnvOK env) {c k t : Bytes} {r : GOut} {S A : List Bytes} {D : Cond} {cs : Bytes}
    {m kk : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (c ++ k) t (St S A m D kk cs) = r) (hr : r.IsOk) (hc : c = optTail) :
    ∃ k', run Eval.opExec env k t (St S A m D k' cs) = r := by
  subst hc
  simp only [optTail, List.cons_append, List.nil_append] at h
  sym_skip h hin
  exact ⟨_, h⟩

theorem anchor_skip {env : Env} (he : EnvOK env) {c k t : Bytes} {r : GOut} {S A : List Bytes} {D : Cond} {cs : Bytes}
    {m kk : Nat} (hin : D.isActive = false)
    (h : run Eval.opExec env (c ++ k) t (St S A m D kk cs) = r) (hr : r.IsOk) (hc : c = anchor) :
    ∃ k', run Eval.opExec env k t (St S A m D k' cs) = r := by
  subst hc
  simp only [anchor, List.cons_append, List.nil_append] at h
  sym_skip h hin
  exact ⟨_, h⟩

/-! ## The rules for the drivers

The chunk's kind, the part of its name after the last underscore (`c797_pad16`, `c1465_optTail`,
`c2660_anchor`), selects the rule; each applies the block lemma with the chunk identity by `rfl`. -/

macro_rules
  | `(tactic| sym_blockrule "pad16" $h:ident $hact:ident) =>
    `(tactic| (replace $h := pad16_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr) (by first | rfl | decide)
               obtain ⟨_, _, $h:ident⟩ := $h))
macro_rules
  | `(tactic| sym_blockrule "optTail" $h:ident $hact:ident) =>
    `(tactic| (replace $h := optTail_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr) (by first | rfl | decide)
               obtain ⟨_, _, $h:ident⟩ := $h))
macro_rules
  | `(tactic| sym_blockrule "anchor" $h:ident $hact:ident) =>
    `(tactic| (obtain ⟨_, _, _, $h:ident⟩ := anchor_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr) (by first | rfl | decide)))

macro_rules
  | `(tactic| sym_skipblockrule "pad16" $h:ident $hin:ident) =>
    `(tactic| (replace $h := pad16_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf, Bool.and_false,
                 Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)
                 (by first | rfl | decide)
               obtain ⟨_, $h:ident⟩ := $h))
macro_rules
  | `(tactic| sym_skipblockrule "optTail" $h:ident $hin:ident) =>
    `(tactic| (replace $h := optTail_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf, Bool.and_false,
                 Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)
                 (by first | rfl | decide)
               obtain ⟨_, $h:ident⟩ := $h))
macro_rules
  | `(tactic| sym_skipblockrule "anchor" $h:ident $hin:ident) =>
    `(tactic| (replace $h := anchor_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf, Bool.and_false,
                 Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)
                 (by first | rfl | decide)
               obtain ⟨_, $h:ident⟩ := $h))

/-- The rules apply: a pad loop skipped inside an inactive arm, then one run. -/
example {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {x : Bytes} {S A : List Bytes} {C : Cond} {cs : Bytes}
    {m kk : Nat} (hact : C.isActive = true)
    (h : run Eval.opExec env (0x00 :: (0x63 :: (SimpleMulti.c797_pad16 ++ (0x68 :: (SimpleMulti.c950_pad16 ++ k))))) t
      (St (x :: S) A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env k t (St (padN 16 x :: S) A m' C k' cs) = r := by
  sym_all h
  exact ⟨_, _, h⟩

end BoltProof.Glue.SimpleMulti
