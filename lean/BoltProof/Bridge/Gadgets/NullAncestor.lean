import BoltProof.Bridge.Gadgets.Steps

/-!
# Lemma 4 at the bytecode level: the null-ancestor check's tail

`docs/formal-proof.md` Lemma 4: when no rebuild runs, the covenant concatenates every ancestor
unlock argument and asserts the total size is `0` (`… cat … size nip 0 equalVerify`). After the
`OP_CAT`s the concatenation sits on top of the stack and the four bytes `82 77 00 88`
(`OP_SIZE OP_NIP OP_0 OP_EQUALVERIFY`) decide it. This module proves, over bsv-script-lean's own
loop (`Gadget.run`), that this fragment

* runs to its end exactly when the concatenation is empty (`nullTail_accepts`), and
* fails with `SCRIPT_ERR_EQUALVERIFY` when it is not (`nullTail_refuses`),

so no fabricated ancestor data can pass the check: the hand proof's "any non-null field makes
the size positive and fails the check" is now a theorem about the instructions themselves.
`nullTail_next_iff` states the two together.
-/

set_option autoImplicit false

namespace BoltProof.Gadgets

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- The tail of the null-ancestor check: `OP_SIZE OP_NIP OP_0 OP_EQUALVERIFY` (`82 77 00 88`). -/
def nullTail : Bytes := [Op.OP_SIZE, Op.OP_NIP, Op.OP_0, Op.OP_EQUALVERIFY]

/-- `OP_0` alone is framed: it reads no data byte. -/
theorem framed_push0 : framed [Op.OP_0] = true := by
  rw [framed.eq_2]
  simp [getOpTail, Op.OP_0, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1, framed.eq_1]

/-- A script number encodes to `[]` only for zero. -/
theorem encode_eq_nil_iff (v : Int) : encode v = [] ↔ v = 0 := by
  constructor
  · intro h
    have := decode_encode v
    rw [h, decode_nil] at this
    exact this.symm
  · rintro rfl
    exact encode_zero

/-- The fragment's run from a state whose top is the concatenation `x`, as one equation: the
three steps before the verify, then the verify's two outcomes. -/
theorem nullTail_run (env : Env) (t : Bytes) (st : State) (x : Bytes) (rest : List Bytes)
    (hstk : st.stack = x :: rest) (he : Exec env st)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hnum : (encode (x.length : Int)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + (encode (x.length : Int)).length + 2 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env nullTail t st =
      run Eval.opExec env [Op.OP_EQUALVERIFY] t
        { st with opCount := st.opCount + 2,
                  stack := [] :: encode (x.length : Int) :: rest,
                  memUsed := st.memUsed + (encode (x.length : Int)).length + elementOverhead -
                    (x.length + elementOverhead) + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have h1 := run_size env ([Op.OP_NIP] ++ ([Op.OP_0] ++ [Op.OP_EQUALVERIFY]) ++ t) st x rest hstk
    ⟨hact, hret, hgen⟩ (by omega) hnum (by omega)
  have h2 := run_nip env ([Op.OP_0] ++ [Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 1, stack := encode (x.length : Int) :: x :: rest,
              memUsed := st.memUsed + (encode (x.length : Int)).length + elementOverhead }
    (encode (x.length : Int)) x rest rfl ⟨hact, hret, hgen⟩
    (by show st.opCount + 1 + 1 ≤ _; omega)
  have h3 := run_push0 env ([Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := encode (x.length : Int) :: rest,
              memUsed := st.memUsed + (encode (x.length : Int)).length + elementOverhead -
                (x.length + elementOverhead) }
    ⟨hact, hret, hgen⟩
    (by show st.memUsed + (encode (x.length : Int)).length + elementOverhead - (x.length + elementOverhead) +
          elementOverhead ≤ _
        omega)
  show run Eval.opExec env ([Op.OP_SIZE] ++ ([Op.OP_NIP] ++ ([Op.OP_0] ++ [Op.OP_EQUALVERIFY]))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_push0, h3]
  simp only [GOut.andThen]

/-- **Lemma 4, accepted.** An empty concatenation passes: the fragment runs to its end with the
concatenation popped (its element overhead given back) and three opcodes charged. -/
theorem nullTail_accepts (env : Env) (t : Bytes) (st : State) (rest : List Bytes)
    (hstk : st.stack = [] :: rest) (he : Exec env st)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hmem : st.memUsed + 2 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env nullTail t st =
      .next { st with opCount := st.opCount + 3, stack := rest, memUsed := st.memUsed - elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hz : encode ((([] : Bytes).length : Nat) : Int) = [] := by simp [encode_zero]
  rw [nullTail_run env t st [] rest hstk ⟨hact, hret, hgen⟩ hops (by simp [encode_zero])
    (by simp [encode_zero]; omega)]
  rw [hz]
  rw [HashLock.run_equalverify_same env t
    { st with opCount := st.opCount + 2, stack := [] :: [] :: rest,
              memUsed := st.memUsed + ([] : Bytes).length + elementOverhead -
                (([] : Bytes).length + elementOverhead) + elementOverhead }
    [] rest rfl hact hret (by show st.opCount + 2 + 1 ≤ _; omega)
    (by dsimp only; simp only [List.length_nil, Nat.add_zero, Nat.zero_add, elementOverhead] at hmem ⊢; omega) hgen]
  congr 1
  all_goals (first | rfl |
    (congr 1 <;> (try simp only [List.length_nil, Nat.add_zero, Nat.zero_add, elementOverhead]) <;> omega))

/-- **Lemma 4, refused.** A non-empty concatenation fails the check with
`SCRIPT_ERR_EQUALVERIFY`: no ancestor data can be injected where no rebuild runs. -/
theorem nullTail_refuses (env : Env) (t : Bytes) (st : State) (x : Bytes) (rest : List Bytes)
    (hx : x ≠ []) (hstk : st.stack = x :: rest) (he : Exec env st)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hnum : (encode (x.length : Int)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + (encode (x.length : Int)).length + 2 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    ∃ st', run Eval.opExec env nullTail t st = .err .equalverify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hne : encode (x.length : Int) ≠ [] := by
    intro h
    have := (encode_eq_nil_iff _).mp h
    have hl : x.length = 0 := by omega
    exact hx (List.length_eq_zero_iff.mp hl)
  rw [nullTail_run env t st x rest hstk ⟨hact, hret, hgen⟩ hops hnum hmem]
  refine ⟨_, run_equalverify_ne env t _ (encode (x.length : Int)) [] rest hne rfl ⟨hact, hret, hgen⟩
    (by show st.opCount + 2 + 1 ≤ _; omega) ?_⟩
  show st.memUsed + (encode (x.length : Int)).length + elementOverhead - (x.length + elementOverhead) +
      elementOverhead - (List.length ([] : Bytes) + elementOverhead) -
      ((encode (x.length : Int)).length + elementOverhead) + elementOverhead ≤ _
  simp only [List.length_nil, Nat.zero_add]
  omega

/-- **Lemma 4 as an equivalence.** Under the fragment's preconditions, it runs to its end iff
the concatenation on top is empty. -/
theorem nullTail_next_iff (env : Env) (t : Bytes) (st : State) (x : Bytes) (rest : List Bytes)
    (hstk : st.stack = x :: rest) (he : Exec env st)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hnum : (encode (x.length : Int)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + (encode (x.length : Int)).length + 2 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env nullTail t st = .next st') ↔ x = [] := by
  constructor
  · intro ⟨st', h⟩
    by_contra hx
    obtain ⟨st'', h'⟩ := nullTail_refuses env t st x rest hx hstk he hops hnum hmem
    rw [h] at h'
    cases h'
  · rintro rfl
    exact ⟨_, nullTail_accepts env t st rest hstk he hops (by simpa [encode_zero] using hmem)⟩

end BoltProof.Gadgets
