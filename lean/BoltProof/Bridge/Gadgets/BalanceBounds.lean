import BoltProof.Bridge.Gadgets.Parity

/-!
# Lemma 6 at the bytecode level: the balance bounds and the settle-side re-checks

`docs/formal-proof.md` Lemma 6: every input balance is separately bounded `0 ≤ balance ≤ 2¹²⁷−1`
at the moment it is spent; the merge settle re-asserts the computed sum against the same bound;
the split settle re-asserts `remainder ≥ 0`. In the shipped `SimpleMultiBOLT` covenant these are

    01 d 79 76 00 a2 69 55 79 a1 69                  (d = 0x27 at offset 610, d = 0x2d at 621)
    d OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_5 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY

    01 2f 79 01 2f 79 76 00 a2 69 93 76 5e 79 a1 69  (offset 781, inside the merge-settle branch)
    2f OP_PICK 2f OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_ADD OP_DUP OP_14 OP_PICK
    OP_LESSTHANOREQUAL OP_VERIFY

    01 2f 79 01 2f 79 76 00 a2 69 94 76 00 a2 69     (offset 935, inside the split-settle branch)
    2f OP_PICK 2f OP_PICK OP_DUP OP_0 OP_GREATERTHANOREQUAL OP_VERIFY OP_SUB OP_DUP OP_0
    OP_GREATERTHANOREQUAL OP_VERIFY

The bound check copies a balance field (`d` deep), asserts it is non-negative, then asserts it is
at most the bound the covenant keeps five deep (the sixteen bytes `ff…ff7f`, `2¹²⁷ − 1`, pushed at
offset 566), and leaves the stack as it found it. The merge re-check copies the balance and the
other balance, asserts the other is non-negative, adds them and asserts the sum is at most the
bound it keeps twelve deep, leaving the sum on top for the 16-byte field that follows. The split
re-check copies the balance and the piece, asserts the piece is non-negative, subtracts and
asserts the remainder is non-negative, leaving the remainder on top.

This module proves each over bsv-script-lean's own loop: `boundCheck_next_iff`,
`mergeSettle_next_iff` and `splitSettle_next_iff` state that the fragment runs to its end exactly
when the arithmetic predicate holds (with the state it leaves pinned down by the `_accepts`
lemmas) and fails with `SCRIPT_ERR_VERIFY` otherwise (`_refuses`). With `BalanceGuards.lean`
this closes Lemma 6 at the fragment level: the commit-side guards and the settle-side re-checks
are theorems about the instructions themselves, for every input.
-/

set_option autoImplicit false

namespace BoltProof.Gadgets

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- `OP_DUP OP_0 OP_GREATERTHANOREQUAL`: the boolean `top ≥ 0` above the top. -/
def nonNeg : Bytes := [Op.OP_DUP, Op.OP_0, Op.OP_GREATERTHANOREQUAL]

/-- `2f OP_PICK 2f OP_PICK`: the balance field (47 deep) and the field below it, copied up. -/
def pickPair : Bytes := [1, 0x2f, Op.OP_PICK, 1, 0x2f, Op.OP_PICK]

/-- `OP_5 OP_PICK OP_LESSTHANOREQUAL`: the boolean `top ≤ bound` with the bound five deep. -/
def leBound5 : Bytes := [Op.OP_5, Op.OP_PICK, Op.OP_LESSTHANOREQUAL]

/-- `OP_ADD OP_DUP OP_14 OP_PICK OP_LESSTHANOREQUAL`: the sum, then the boolean `sum ≤ bound`
with the bound twelve deep below the sum. -/
def sumLeBound14 : Bytes := [Op.OP_ADD, Op.OP_DUP, Op.OP_14, Op.OP_PICK, Op.OP_LESSTHANOREQUAL]

/-- The bound check of a balance field `d` deep. -/
def boundCheck (d : Nat) : Bytes := [1, d, Op.OP_PICK] ++ nonNeg ++ [Op.OP_VERIFY] ++ leBound5 ++ [Op.OP_VERIFY]

/-- The merge settle's re-check. -/
def mergeSettle : Bytes := pickPair ++ nonNeg ++ [Op.OP_VERIFY] ++ sumLeBound14 ++ [Op.OP_VERIFY]

/-- The split settle's re-check. -/
def splitSettle : Bytes := pickPair ++ nonNeg ++ [Op.OP_VERIFY] ++ [Op.OP_SUB] ++ nonNeg ++ [Op.OP_VERIFY]

/-- The fragments are the bytes quoted in the header. -/
theorem boundCheck_bytes (d : Nat) :
    boundCheck d = [0x01, d, 0x79, 0x76, 0x00, 0xa2, 0x69, 0x55, 0x79, 0xa1, 0x69] := rfl
theorem mergeSettle_bytes :
    mergeSettle = [0x01, 0x2f, 0x79, 0x01, 0x2f, 0x79, 0x76, 0x00, 0xa2, 0x69, 0x93, 0x76, 0x5e, 0x79, 0xa1, 0x69] :=
  rfl
theorem splitSettle_bytes :
    splitSettle = [0x01, 0x2f, 0x79, 0x01, 0x2f, 0x79, 0x76, 0x00, 0xa2, 0x69, 0x94, 0x76, 0x00, 0xa2, 0x69] := rfl

theorem decode_2f : decode [0x2f] = 47 := by decide
theorem decode_05 : decode [5] = 5 := by decide
theorem decode_0e : decode [14] = 14 := by decide

/-- The sub-fragments are framed. -/
theorem framed_nonNeg : framed nonNeg = true := by
  rw [nonNeg]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_pickPair : framed pickPair = true := by
  rw [pickPair]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_leBound5 : framed leBound5 = true := by
  rw [leBound5]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_sumLeBound14 : framed sumLeBound14 = true := by
  rw [sumLeBound14]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_nonNegVerify : framed (nonNeg ++ [Op.OP_VERIFY]) = true := by
  show framed [Op.OP_DUP, Op.OP_0, Op.OP_GREATERTHANOREQUAL, Op.OP_VERIFY] = true
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1

/-- A boolean the comparisons push is `[1]` or `[]`. -/
theorem boolBytes_length_le (p : Prop) [Decidable p] : (encode (if p then 1 else 0)).length ≤ 1 := by
  split <;> simp [encode_zero, vec_1]

/-! ## The sub-fragments -/

/-- `OP_DUP OP_0 OP_GREATERTHANOREQUAL` from `v :: rest`: the boolean `v ≥ 0` above `v`, two
opcodes charged. -/
theorem nonNeg_run (env : Env) (t : Bytes) (st : State) (v : Bytes) (rest : List Bytes)
    (hstk : st.stack = v :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 2 ≤ env.params.limits.maxOpsPerScript)
    (hv : v.length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + v.length + 1 + 2 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env nonNeg t st =
      .next { st with opCount := st.opCount + 2,
                      stack := encode (if decode v ≥ 0 then 1 else 0) :: v :: rest,
                      memUsed := st.memUsed + (encode (if decode v ≥ 0 then 1 else 0)).length +
                        elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hb := boolBytes_length_le (decode v ≥ 0)
  have h1 := run_dup env ([Op.OP_0] ++ [Op.OP_GREATERTHANOREQUAL] ++ t) st v rest hstk ⟨hact, hret, hgen⟩
    (by omega) (by mem_omega)
  have h2 := run_push0 env ([Op.OP_GREATERTHANOREQUAL] ++ t)
    { st with opCount := st.opCount + 1, stack := v :: v :: rest, memUsed := st.memUsed + v.length + elementOverhead }
    ⟨hact, hret, hgen⟩ (by (try dsimp only); mem_omega)
  have h3 := run_gte env t
    { st with opCount := st.opCount + 1, stack := [] :: v :: v :: rest,
              memUsed := st.memUsed + v.length + elementOverhead + elementOverhead }
    v [] (v :: rest) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 1 ≤ _; omega) hv (by mem_omega)
    (by rw [decode_nil]; (try dsimp only); mem_omega)
  rw [decode_nil] at h3
  show run Eval.opExec env ([Op.OP_DUP] ++ ([Op.OP_0] ++ [Op.OP_GREATERTHANOREQUAL])) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_push0, h2]
  simp only [GOut.andThen]
  rw [h3]
  state_congr

/-- `nonNeg ++ [OP_VERIFY]` from `v :: rest` with `v ≥ 0`: `v :: rest` again, three opcodes charged. -/
theorem nonNegVerify_accepts (env : Env) (t : Bytes) (st : State) (v : Bytes) (rest : List Bytes)
    (hstk : st.stack = v :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hv : v.length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + v.length + 1 + 2 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hnn : 0 ≤ decode v) :
    run Eval.opExec env (nonNeg ++ [Op.OP_VERIFY]) t st =
      .next { st with opCount := st.opCount + 3, stack := v :: rest, memUsed := st.memUsed } := by
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run_append _ _ _ _ _ _ framed_nonNeg,
    nonNeg_run env ([Op.OP_VERIFY] ++ t) st v rest hstk ⟨hact, hret, hgen⟩ hmin (by omega) hv hmem]
  simp only [GOut.andThen]
  have hge : decode v ≥ 0 := hnn
  simp only [hge, ite_true, vec_1]
  rw [run_verify_true env t
    { st with opCount := st.opCount + 2, stack := [1] :: v :: rest,
              memUsed := st.memUsed + [1].length + elementOverhead }
    [1] (v :: rest) (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 2 + 1 ≤ _; omega)]
  state_congr

/-- `nonNeg ++ [OP_VERIFY]` from `v :: rest` with `v < 0`: `SCRIPT_ERR_VERIFY`. -/
theorem nonNegVerify_refuses (env : Env) (t : Bytes) (st : State) (v : Bytes) (rest : List Bytes)
    (hstk : st.stack = v :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hv : v.length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + v.length + 1 + 2 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hneg : decode v < 0) :
    ∃ st', run Eval.opExec env (nonNeg ++ [Op.OP_VERIFY]) t st = .err .verify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  rw [run_append _ _ _ _ _ _ framed_nonNeg,
    nonNeg_run env ([Op.OP_VERIFY] ++ t) st v rest hstk ⟨hact, hret, hgen⟩ hmin (by omega) hv hmem]
  simp only [GOut.andThen]
  have hge : ¬ (decode v ≥ 0) := by omega
  simp only [hge, ite_false, encode_zero]
  exact ⟨_, run_verify_false env t
    { st with opCount := st.opCount + 2, stack := [] :: v :: rest,
              memUsed := st.memUsed + ([] : Bytes).length + elementOverhead }
    [] (v :: rest) (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 2 + 1 ≤ _; omega)⟩

/-- `2f OP_PICK 2f OP_PICK` from `s`: the field 47 deep (`x`) and the one below it (`y`) copied
up, `y :: x :: s`, two opcodes charged. -/
theorem pickPair_run (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 2 ≤ env.params.limits.maxOpsPerScript)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + y.length + 1 + 3 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env pickPair t st =
      .next { st with opCount := st.opCount + 2, stack := y :: x :: s,
                      memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have h1 := run_push1 env ([Op.OP_PICK] ++ ([1, 0x2f] ++ [Op.OP_PICK]) ++ t) st 0x2f ⟨hact, hret, hgen⟩ hmin
    (by mem_omega)
  have h2 := run_pick env ([1, 0x2f] ++ [Op.OP_PICK] ++ t)
    { st with stack := [0x2f] :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [0x2f] s 47 rfl decode_2f hlen ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by rw [hx]; (try dsimp only); mem_omega)
  rw [hx] at h2
  have h3 := run_push1 env ([Op.OP_PICK] ++ t)
    { st with opCount := st.opCount + 1, stack := x :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2f].length + elementOverhead) + (x.length + elementOverhead) }
    0x2f ⟨hact, hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  have hget : (x :: s).getD 47 [] = y := by rw [List.getD_cons_succ]; exact hy
  have h4 := run_pick env t
    { st with opCount := st.opCount + 1, stack := [0x2f] :: x :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2f].length + elementOverhead) + (x.length + elementOverhead) +
                1 + elementOverhead }
    [0x2f] (x :: s) 47 rfl decode_2f (by simp only [List.length_cons]; omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget]; (try dsimp only); mem_omega)
  rw [hget] at h4
  show run Eval.opExec env ([1, 0x2f] ++ ([Op.OP_PICK] ++ ([1, 0x2f] ++ [Op.OP_PICK]))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h3]
  simp only [GOut.andThen]
  rw [h4]
  state_congr

/-- `OP_5 OP_PICK OP_LESSTHANOREQUAL` from `x :: s` with the bound four deep in `s`: the boolean
`x ≤ bound` in place of `x`, two opcodes charged. -/
theorem leBound5_run (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x bound : Bytes)
    (hstk : st.stack = x :: s) (hb : s.getD 4 [] = bound) (hlen : 4 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 2 ≤ env.params.limits.maxOpsPerScript)
    (hx : x.length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + bound.length + 1 + 2 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env leBound5 t st =
      .next { st with opCount := st.opCount + 2,
                      stack := encode (if decode x ≤ decode bound then 1 else 0) :: s,
                      memUsed := st.memUsed - (x.length + elementOverhead) +
                        (encode (if decode x ≤ decode bound then 1 else 0)).length + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hbb := boolBytes_length_le (decode x ≤ decode bound)
  have h1 := run_op5 env ([Op.OP_PICK] ++ [Op.OP_LESSTHANOREQUAL] ++ t) st ⟨hact, hret, hgen⟩ (by mem_omega)
  have hget : (x :: s).getD 5 [] = bound := by rw [List.getD_cons_succ]; exact hb
  have h2 := run_pick env ([Op.OP_LESSTHANOREQUAL] ++ t)
    { st with stack := [5] :: x :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [5] (x :: s) 5 rfl decode_05 (by simp only [List.length_cons]; omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget]; (try dsimp only); mem_omega)
  rw [hget] at h2
  have h3 := run_lte env t
    { st with opCount := st.opCount + 1, stack := bound :: x :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([5].length + elementOverhead) + (bound.length + elementOverhead) }
    x bound s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 1 ≤ _; omega) hx hbl
    (by (try dsimp only); mem_omega)
  show run Eval.opExec env ([Op.OP_5] ++ ([Op.OP_PICK] ++ [Op.OP_LESSTHANOREQUAL])) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [h3]
  state_congr

/-- `OP_ADD OP_DUP OP_14 OP_PICK OP_LESSTHANOREQUAL` from `y :: x :: s` with the bound twelve
deep in `s`: the boolean `x + y ≤ bound` above the sum, four opcodes charged. -/
theorem sumLeBound14_run (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y bound : Bytes)
    (hstk : st.stack = y :: x :: s) (hb : s.getD 12 [] = bound) (hlen : 12 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 4 ≤ env.params.limits.maxOpsPerScript)
    (hx : x.length ≤ env.params.limits.maxScriptNumLength)
    (hy : y.length ≤ env.params.limits.maxScriptNumLength)
    (hs : (encode (decode x + decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed - (y.length + elementOverhead) - (x.length + elementOverhead) +
      2 * (encode (decode x + decode y)).length + bound.length + 1 + 3 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env sumLeBound14 t st =
      .next { st with opCount := st.opCount + 4,
                      stack := encode (if decode x + decode y ≤ decode bound then 1 else 0) ::
                        encode (decode x + decode y) :: s,
                      memUsed := st.memUsed - (y.length + elementOverhead) - (x.length + elementOverhead) +
                        (encode (decode x + decode y)).length + elementOverhead +
                        (encode (if decode x + decode y ≤ decode bound then 1 else 0)).length +
                        elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hbb := boolBytes_length_le (decode x + decode y ≤ decode bound)
  have h1 := run_add env ([Op.OP_DUP] ++ ([Op.OP_14] ++ ([Op.OP_PICK] ++ [Op.OP_LESSTHANOREQUAL])) ++ t) st x y s
    hstk ⟨hact, hret, hgen⟩ hmin (by omega) hx hy hs (by mem_omega)
  have h2 := run_dup env ([Op.OP_14] ++ ([Op.OP_PICK] ++ [Op.OP_LESSTHANOREQUAL]) ++ t)
    { st with opCount := st.opCount + 1, stack := encode (decode x + decode y) :: s,
              memUsed := st.memUsed - (y.length + elementOverhead) - (x.length + elementOverhead) +
                (encode (decode x + decode y)).length + elementOverhead }
    (encode (decode x + decode y)) s rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  have h3 := run_op14 env ([Op.OP_PICK] ++ [Op.OP_LESSTHANOREQUAL] ++ t)
    { st with opCount := st.opCount + 1 + 1,
              stack := encode (decode x + decode y) :: encode (decode x + decode y) :: s,
              memUsed := st.memUsed - (y.length + elementOverhead) - (x.length + elementOverhead) +
                (encode (decode x + decode y)).length + elementOverhead + (encode (decode x + decode y)).length +
                elementOverhead }
    ⟨hact, hret, hgen⟩ (by (try dsimp only); mem_omega)
  have hget : (encode (decode x + decode y) :: encode (decode x + decode y) :: s).getD 14 [] = bound := by
    rw [List.getD_cons_succ, List.getD_cons_succ]; exact hb
  have h4 := run_pick env ([Op.OP_LESSTHANOREQUAL] ++ t)
    { st with opCount := st.opCount + 1 + 1,
              stack := [14] :: encode (decode x + decode y) :: encode (decode x + decode y) :: s,
              memUsed := st.memUsed - (y.length + elementOverhead) - (x.length + elementOverhead) +
                (encode (decode x + decode y)).length + elementOverhead + (encode (decode x + decode y)).length +
                elementOverhead + 1 + elementOverhead }
    [14] (encode (decode x + decode y) :: encode (decode x + decode y) :: s) 14 rfl decode_0e
    (by simp only [List.length_cons]; omega) ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
    (by mem_omega) (by rw [hget]; (try dsimp only); mem_omega)
  rw [hget] at h4
  have hdd : decode (encode (decode x + decode y)) = decode x + decode y := decode_encode _
  have h5 := run_lte env t
    { st with opCount := st.opCount + 1 + 1 + 1,
              stack := bound :: encode (decode x + decode y) :: encode (decode x + decode y) :: s,
              memUsed := st.memUsed - (y.length + elementOverhead) - (x.length + elementOverhead) +
                (encode (decode x + decode y)).length + elementOverhead + (encode (decode x + decode y)).length +
                elementOverhead + 1 + elementOverhead - ([14].length + elementOverhead) + (bound.length + elementOverhead) }
    (encode (decode x + decode y)) bound (encode (decode x + decode y) :: s) rfl ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega) hs hbl
    (by rw [hdd]; (try dsimp only); mem_omega)
  rw [hdd] at h5
  show run Eval.opExec env ([Op.OP_ADD] ++ ([Op.OP_DUP] ++ ([Op.OP_14] ++ ([Op.OP_PICK] ++ [Op.OP_LESSTHANOREQUAL])))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [h5]
  state_congr

/-! ## The bound check -/

/-- **Lemma 6's bound, accepted.** With `0 ≤ balance ≤ bound` the check runs to its end, leaving
the stack and the memory counter as it found them and seven opcodes charged. -/
theorem boundCheck_accepts (env : Env) (t : Bytes) (st : State) (s : List Bytes) (d n : Nat) (bal bound : Bytes)
    (hd : decode [d] = n) (hstk : st.stack = s) (hbal : s.getD n [] = bal) (hb : s.getD 4 [] = bound)
    (hlen : n < s.length) (hlen4 : 4 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 7 ≤ env.params.limits.maxOpsPerScript)
    (hbal_l : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + 2 * bal.length + bound.length + 1 + 3 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage)
    (hnn : 0 ≤ decode bal) (hle : decode bal ≤ decode bound) :
    run Eval.opExec env (boundCheck d) t st =
      .next { st with opCount := st.opCount + 7, stack := s, memUsed := st.memUsed } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have h1 := run_push1 env ([Op.OP_PICK] ++ (nonNeg ++ [Op.OP_VERIFY] ++ (leBound5 ++ [Op.OP_VERIFY])) ++ t) st d
    ⟨hact, hret, hgen⟩ hmin (by mem_omega)
  have h2 := run_pick env (nonNeg ++ [Op.OP_VERIFY] ++ (leBound5 ++ [Op.OP_VERIFY]) ++ t)
    { st with stack := [d] :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [d] s n rfl hd hlen ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by rw [hbal]; (try dsimp only); mem_omega)
  rw [hbal] at h2
  have h3 := nonNegVerify_accepts env (leBound5 ++ [Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 1, stack := bal :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) }
    bal s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 3 ≤ _; omega) hbal_l (by (try dsimp only); mem_omega) hnn
  have h4 := leBound5_run env ([Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 1 + 3, stack := bal :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) }
    s bal bound rfl hb hlen4 ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 3 + 2 ≤ _; omega) hbal_l hbl hone
    (by (try dsimp only); mem_omega)
  have hle' : decode bal ≤ decode bound := hle
  simp only [hle', ite_true, vec_1] at h4
  have h5 := run_verify_true env t
    { st with opCount := st.opCount + 1 + 3 + 2, stack := [1] :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) -
                (bal.length + elementOverhead) + [1].length + elementOverhead }
    [1] s (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 3 + 2 + 1 ≤ _; omega)
  show run Eval.opExec env ([1, d] ++ ([Op.OP_PICK] ++ (nonNeg ++ [Op.OP_VERIFY] ++ (leBound5 ++ [Op.OP_VERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_nonNegVerify, h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_leBound5, h4]
  simp only [GOut.andThen]
  rw [h5]
  state_congr

/-- **Lemma 6's bound, refused.** A negative balance or one above the bound fails with
`SCRIPT_ERR_VERIFY`. -/
theorem boundCheck_refuses (env : Env) (t : Bytes) (st : State) (s : List Bytes) (d n : Nat) (bal bound : Bytes)
    (hd : decode [d] = n) (hstk : st.stack = s) (hbal : s.getD n [] = bal) (hb : s.getD 4 [] = bound)
    (hlen : n < s.length) (hlen4 : 4 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 7 ≤ env.params.limits.maxOpsPerScript)
    (hbal_l : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + 2 * bal.length + bound.length + 1 + 3 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage)
    (hbad : decode bal < 0 ∨ decode bound < decode bal) :
    ∃ st', run Eval.opExec env (boundCheck d) t st = .err .verify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have h1 := run_push1 env ([Op.OP_PICK] ++ (nonNeg ++ [Op.OP_VERIFY] ++ (leBound5 ++ [Op.OP_VERIFY])) ++ t) st d
    ⟨hact, hret, hgen⟩ hmin (by mem_omega)
  have h2 := run_pick env (nonNeg ++ [Op.OP_VERIFY] ++ (leBound5 ++ [Op.OP_VERIFY]) ++ t)
    { st with stack := [d] :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [d] s n rfl hd hlen ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by rw [hbal]; (try dsimp only); mem_omega)
  rw [hbal] at h2
  show ∃ st', run Eval.opExec env ([1, d] ++ ([Op.OP_PICK] ++ (nonNeg ++ [Op.OP_VERIFY] ++ (leBound5 ++ [Op.OP_VERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_nonNegVerify]
  by_cases hneg : decode bal < 0
  · obtain ⟨st', h3⟩ := nonNegVerify_refuses env (leBound5 ++ [Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 1, stack := bal :: s,
                memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) }
      bal s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 3 ≤ _; omega) hbal_l (by (try dsimp only); mem_omega) hneg
    rw [h3]
    simp only [GOut.andThen]
    exact ⟨_, rfl⟩
  · have h3 := nonNegVerify_accepts env (leBound5 ++ [Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 1, stack := bal :: s,
                memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) }
      bal s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 3 ≤ _; omega) hbal_l (by (try dsimp only); mem_omega)
      (by omega)
    have h4 := leBound5_run env ([Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 1 + 3, stack := bal :: s,
                memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) }
      s bal bound rfl hb hlen4 ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 3 + 2 ≤ _; omega) hbal_l hbl hone
      (by (try dsimp only); mem_omega)
    have hnle : ¬ (decode bal ≤ decode bound) := by omega
    simp only [hnle, ite_false, encode_zero] at h4
    have h5 := run_verify_false env t
      { st with opCount := st.opCount + 1 + 3 + 2, stack := [] :: s,
                memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) + (bal.length + elementOverhead) -
                  (bal.length + elementOverhead) + ([] : Bytes).length + elementOverhead }
      [] s (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 3 + 2 + 1 ≤ _; omega)
    rw [h3]
    simp only [GOut.andThen]
    rw [run_append _ _ _ _ _ _ framed_leBound5, h4]
    simp only [GOut.andThen]
    rw [h5]
    exact ⟨_, rfl⟩

/-- **Lemma 6's bound as an equivalence.** Under the check's preconditions, it runs to its end
iff `0 ≤ balance ≤ bound`. -/
theorem boundCheck_next_iff (env : Env) (t : Bytes) (st : State) (s : List Bytes) (d n : Nat) (bal bound : Bytes)
    (hd : decode [d] = n) (hstk : st.stack = s) (hbal : s.getD n [] = bal) (hb : s.getD 4 [] = bound)
    (hlen : n < s.length) (hlen4 : 4 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 7 ≤ env.params.limits.maxOpsPerScript)
    (hbal_l : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + 2 * bal.length + bound.length + 1 + 3 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env (boundCheck d) t st = .next st') ↔ (0 ≤ decode bal ∧ decode bal ≤ decode bound) := by
  constructor
  · intro ⟨st', h⟩
    by_contra hbad
    obtain ⟨st'', h'⟩ := boundCheck_refuses env t st s d n bal bound hd hstk hbal hb hlen hlen4 he hmin hops hbal_l hbl
      hone hmem (by omega)
    rw [h] at h'
    cases h'
  · intro ⟨hnn, hle⟩
    exact ⟨_, boundCheck_accepts env t st s d n bal bound hd hstk hbal hb hlen hlen4 he hmin hops hbal_l hbl hone hmem
      hnn hle⟩

/-! ## The merge settle's re-check -/

/-- **Lemma 6's merge re-check, accepted.** With `0 ≤ other` and `balance + other ≤ bound` the
fragment runs to its end, leaving the sum on top and ten opcodes charged. -/
theorem mergeSettle_accepts (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y bound : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hb : s.getD 12 [] = bound)
    (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 10 ≤ env.params.limits.maxOpsPerScript)
    (hxl : x.length ≤ env.params.limits.maxScriptNumLength)
    (hyl : y.length ≤ env.params.limits.maxScriptNumLength)
    (hs : (encode (decode x + decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + 2 * y.length + 2 * (encode (decode x + decode y)).length + bound.length + 1 +
      4 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hnn : 0 ≤ decode y) (hle : decode x + decode y ≤ decode bound) :
    run Eval.opExec env mergeSettle t st =
      .next { st with opCount := st.opCount + 10, stack := encode (decode x + decode y) :: s,
                      memUsed := st.memUsed + (encode (decode x + decode y)).length + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hP := pickPair_run env (nonNeg ++ [Op.OP_VERIFY] ++ (sumLeBound14 ++ [Op.OP_VERIFY]) ++ t) st s x y hstk hx hy
    hlen ⟨hact, hret, hgen⟩ hmin (by omega) hone (by mem_omega)
  have hN := nonNegVerify_accepts env (sumLeBound14 ++ [Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 2, stack := y :: x :: s,
              memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
    y (x :: s) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 ≤ _; omega) hyl (by (try dsimp only); mem_omega) hnn
  have hS := sumLeBound14_run env ([Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 2 + 3, stack := y :: x :: s,
              memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
    s x y bound rfl hb (by omega) ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 + 4 ≤ _; omega) hxl hyl hs hbl hone
    (by (try dsimp only); mem_omega)
  have hle' : decode x + decode y ≤ decode bound := hle
  simp only [hle', ite_true, vec_1] at hS
  have hV := run_verify_true env t
    { st with opCount := st.opCount + 2 + 3 + 4, stack := [1] :: encode (decode x + decode y) :: s,
              memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead - (y.length + elementOverhead) -
                (x.length + elementOverhead) + (encode (decode x + decode y)).length + elementOverhead + [1].length +
                elementOverhead }
    [1] (encode (decode x + decode y) :: s) (by decide) rfl ⟨hact, hret, hgen⟩
    (by show st.opCount + 2 + 3 + 4 + 1 ≤ _; omega)
  show run Eval.opExec env (pickPair ++ (nonNeg ++ [Op.OP_VERIFY] ++ (sumLeBound14 ++ [Op.OP_VERIFY]))) t st = _
  rw [run_append _ _ _ _ _ _ framed_pickPair, hP]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_nonNegVerify, hN]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_sumLeBound14, hS]
  simp only [GOut.andThen]
  rw [hV]
  state_congr

/-- **Lemma 6's merge re-check, refused.** A negative other balance, or a sum above the bound,
fails with `SCRIPT_ERR_VERIFY`. -/
theorem mergeSettle_refuses (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y bound : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hb : s.getD 12 [] = bound)
    (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 10 ≤ env.params.limits.maxOpsPerScript)
    (hxl : x.length ≤ env.params.limits.maxScriptNumLength)
    (hyl : y.length ≤ env.params.limits.maxScriptNumLength)
    (hs : (encode (decode x + decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + 2 * y.length + 2 * (encode (decode x + decode y)).length + bound.length + 1 +
      4 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hbad : decode y < 0 ∨ decode bound < decode x + decode y) :
    ∃ st', run Eval.opExec env mergeSettle t st = .err .verify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hP := pickPair_run env (nonNeg ++ [Op.OP_VERIFY] ++ (sumLeBound14 ++ [Op.OP_VERIFY]) ++ t) st s x y hstk hx hy
    hlen ⟨hact, hret, hgen⟩ hmin (by omega) hone (by mem_omega)
  show ∃ st', run Eval.opExec env (pickPair ++ (nonNeg ++ [Op.OP_VERIFY] ++ (sumLeBound14 ++ [Op.OP_VERIFY]))) t st = _
  rw [run_append _ _ _ _ _ _ framed_pickPair, hP]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_nonNegVerify]
  by_cases hneg : decode y < 0
  · obtain ⟨st', hN⟩ := nonNegVerify_refuses env (sumLeBound14 ++ [Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 2, stack := y :: x :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
      y (x :: s) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 ≤ _; omega) hyl (by (try dsimp only); mem_omega)
      hneg
    rw [hN]
    simp only [GOut.andThen]
    exact ⟨_, rfl⟩
  · have hN := nonNegVerify_accepts env (sumLeBound14 ++ [Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 2, stack := y :: x :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
      y (x :: s) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 ≤ _; omega) hyl (by (try dsimp only); mem_omega)
      (by omega)
    have hS := sumLeBound14_run env ([Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 2 + 3, stack := y :: x :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
      s x y bound rfl hb (by omega) ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 + 4 ≤ _; omega) hxl hyl hs hbl hone
      (by (try dsimp only); mem_omega)
    have hnle : ¬ (decode x + decode y ≤ decode bound) := by omega
    simp only [hnle, ite_false, encode_zero] at hS
    have hV := run_verify_false env t
      { st with opCount := st.opCount + 2 + 3 + 4, stack := [] :: encode (decode x + decode y) :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead - (y.length + elementOverhead) -
                  (x.length + elementOverhead) + (encode (decode x + decode y)).length + elementOverhead +
                  ([] : Bytes).length + elementOverhead }
      [] (encode (decode x + decode y) :: s) (by decide) rfl ⟨hact, hret, hgen⟩
      (by show st.opCount + 2 + 3 + 4 + 1 ≤ _; omega)
    rw [hN]
    simp only [GOut.andThen]
    rw [run_append _ _ _ _ _ _ framed_sumLeBound14, hS]
    simp only [GOut.andThen]
    rw [hV]
    exact ⟨_, rfl⟩

/-- **Lemma 6's merge re-check as an equivalence.** Under the fragment's preconditions, it runs
to its end iff `0 ≤ other` and `balance + other ≤ bound`. -/
theorem mergeSettle_next_iff (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y bound : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hb : s.getD 12 [] = bound)
    (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 10 ≤ env.params.limits.maxOpsPerScript)
    (hxl : x.length ≤ env.params.limits.maxScriptNumLength)
    (hyl : y.length ≤ env.params.limits.maxScriptNumLength)
    (hs : (encode (decode x + decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hbl : bound.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + 2 * y.length + 2 * (encode (decode x + decode y)).length + bound.length + 1 +
      4 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env mergeSettle t st = .next st') ↔
      (0 ≤ decode y ∧ decode x + decode y ≤ decode bound) := by
  constructor
  · intro ⟨st', h⟩
    by_contra hbad
    obtain ⟨st'', h'⟩ := mergeSettle_refuses env t st s x y bound hstk hx hy hb hlen he hmin hops hxl hyl hs hbl hone
      hmem (by omega)
    rw [h] at h'
    cases h'
  · intro ⟨hnn, hle⟩
    exact ⟨_, mergeSettle_accepts env t st s x y bound hstk hx hy hb hlen he hmin hops hxl hyl hs hbl hone hmem hnn hle⟩

/-! ## The split settle's re-check -/

/-- **Lemma 6's split re-check, accepted.** With `0 ≤ piece ≤ balance` the fragment runs to its
end, leaving the remainder on top and nine opcodes charged. -/
theorem splitSettle_accepts (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 9 ≤ env.params.limits.maxOpsPerScript)
    (hxl : x.length ≤ env.params.limits.maxScriptNumLength)
    (hyl : y.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode x - decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + 2 * y.length + 2 * (encode (decode x - decode y)).length + 1 +
      4 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hnn : 0 ≤ decode y) (hle : decode y ≤ decode x) :
    run Eval.opExec env splitSettle t st =
      .next { st with opCount := st.opCount + 9, stack := encode (decode x - decode y) :: s,
                      memUsed := st.memUsed + (encode (decode x - decode y)).length + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hP := pickPair_run env (nonNeg ++ [Op.OP_VERIFY] ++ ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY])) ++ t) st s x y
    hstk hx hy hlen ⟨hact, hret, hgen⟩ hmin (by omega) hone (by mem_omega)
  have hN := nonNegVerify_accepts env ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY]) ++ t)
    { st with opCount := st.opCount + 2, stack := y :: x :: s,
              memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
    y (x :: s) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 ≤ _; omega) hyl (by (try dsimp only); mem_omega) hnn
  have hSub := run_sub env (nonNeg ++ [Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 2 + 3, stack := y :: x :: s,
              memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
    x y s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 + 1 ≤ _; omega) hxl hyl hd
    (by (try dsimp only); mem_omega)
  have hdd : decode (encode (decode x - decode y)) = decode x - decode y := decode_encode _
  have hN2 := nonNegVerify_accepts env t
    { st with opCount := st.opCount + 2 + 3 + 1, stack := encode (decode x - decode y) :: s,
              memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead - (y.length + elementOverhead) -
                (x.length + elementOverhead) + (encode (decode x - decode y)).length + elementOverhead }
    (encode (decode x - decode y)) s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 + 1 + 3 ≤ _; omega) hd
    (by (try dsimp only); mem_omega) (by rw [hdd]; omega)
  show run Eval.opExec env (pickPair ++ (nonNeg ++ [Op.OP_VERIFY] ++ ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ framed_pickPair, hP]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_nonNegVerify, hN]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hSub]
  simp only [GOut.andThen]
  rw [hN2]
  state_congr

/-- **Lemma 6's split re-check, refused.** A negative piece, or a piece above the balance, fails
with `SCRIPT_ERR_VERIFY`. -/
theorem splitSettle_refuses (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 9 ≤ env.params.limits.maxOpsPerScript)
    (hxl : x.length ≤ env.params.limits.maxScriptNumLength)
    (hyl : y.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode x - decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + 2 * y.length + 2 * (encode (decode x - decode y)).length + 1 +
      4 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hbad : decode y < 0 ∨ decode x < decode y) :
    ∃ st', run Eval.opExec env splitSettle t st = .err .verify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hP := pickPair_run env (nonNeg ++ [Op.OP_VERIFY] ++ ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY])) ++ t) st s x y
    hstk hx hy hlen ⟨hact, hret, hgen⟩ hmin (by omega) hone (by mem_omega)
  show ∃ st', run Eval.opExec env (pickPair ++ (nonNeg ++ [Op.OP_VERIFY] ++ ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ framed_pickPair, hP]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_nonNegVerify]
  by_cases hneg : decode y < 0
  · obtain ⟨st', hN⟩ := nonNegVerify_refuses env ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY]) ++ t)
      { st with opCount := st.opCount + 2, stack := y :: x :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
      y (x :: s) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 ≤ _; omega) hyl (by (try dsimp only); mem_omega)
      hneg
    rw [hN]
    simp only [GOut.andThen]
    exact ⟨_, rfl⟩
  · have hN := nonNegVerify_accepts env ([Op.OP_SUB] ++ (nonNeg ++ [Op.OP_VERIFY]) ++ t)
      { st with opCount := st.opCount + 2, stack := y :: x :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
      y (x :: s) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 ≤ _; omega) hyl (by (try dsimp only); mem_omega)
      (by omega)
    have hSub := run_sub env (nonNeg ++ [Op.OP_VERIFY] ++ t)
      { st with opCount := st.opCount + 2 + 3, stack := y :: x :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead }
      x y s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 + 1 ≤ _; omega) hxl hyl hd
      (by (try dsimp only); mem_omega)
    have hdd : decode (encode (decode x - decode y)) = decode x - decode y := decode_encode _
    obtain ⟨st', hN2⟩ := nonNegVerify_refuses env t
      { st with opCount := st.opCount + 2 + 3 + 1, stack := encode (decode x - decode y) :: s,
                memUsed := st.memUsed + x.length + y.length + 2 * elementOverhead - (y.length + elementOverhead) -
                  (x.length + elementOverhead) + (encode (decode x - decode y)).length + elementOverhead }
      (encode (decode x - decode y)) s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 2 + 3 + 1 + 3 ≤ _; omega) hd
      (by (try dsimp only); mem_omega) (by rw [hdd]; omega)
    rw [hN]
    simp only [GOut.andThen]
    rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hSub]
    simp only [GOut.andThen]
    rw [hN2]
    exact ⟨_, rfl⟩

/-- **Lemma 6's split re-check as an equivalence.** Under the fragment's preconditions, it runs
to its end iff `0 ≤ piece ≤ balance`. -/
theorem splitSettle_next_iff (env : Env) (t : Bytes) (st : State) (s : List Bytes) (x y : Bytes)
    (hstk : st.stack = s) (hx : s.getD 47 [] = x) (hy : s.getD 46 [] = y) (hlen : 47 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 9 ≤ env.params.limits.maxOpsPerScript)
    (hxl : x.length ≤ env.params.limits.maxScriptNumLength)
    (hyl : y.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode x - decode y)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + x.length + 2 * y.length + 2 * (encode (decode x - decode y)).length + 1 +
      4 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env splitSettle t st = .next st') ↔ (0 ≤ decode y ∧ decode y ≤ decode x) := by
  constructor
  · intro ⟨st', h⟩
    by_contra hbad
    obtain ⟨st'', h'⟩ := splitSettle_refuses env t st s x y hstk hx hy hlen he hmin hops hxl hyl hd hone hmem (by omega)
    rw [h] at h'
    cases h'
  · intro ⟨hnn, hle⟩
    exact ⟨_, splitSettle_accepts env t st s x y hstk hx hy hlen he hmin hops hxl hyl hd hone hmem hnn hle⟩

end BoltProof.Gadgets
