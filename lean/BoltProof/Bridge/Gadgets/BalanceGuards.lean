import BoltProof.Bridge.Gadgets.Steps
import BoltProof.Bridge.Gadgets.NullAncestor

/-!
# Lemma 6 at the bytecode level: the split over-take guard

`docs/formal-proof.md` Lemma 6: a split commit enforces `balance − piece ≥ 0` with a single
`sub 0n greaterThanOrEqual verify` (the over-take guard; a zero piece and a zero remainder are
permitted). In the shipped `SimpleMultiBOLT` covenant the guard is the ten bytes

    01 2d 79 01 34 79 94 00 a2 69
    2d OP_PICK 34 OP_PICK OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY

run inside the split-mode branch: `2d OP_PICK` copies the spent balance (45 deep), `34 OP_PICK`
copies the piece (51 deep below it, 52 once the balance is on top), and the rest decides
`balance − piece ≥ 0`. This module proves, over bsv-script-lean's own loop, that the fragment

* runs to its end, leaving the stack as it found it, exactly when `piece ≤ balance`
  (`splitGuard_accepts`, `splitGuard_next_iff`), and
* fails with `SCRIPT_ERR_VERIFY` when `piece > balance` (`splitGuard_refuses`),

for every input: the over-take guard cannot be satisfied by an inflating split.
-/

set_option autoImplicit false

namespace BoltProof.Gadgets

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- Normalise list lengths and the overhead constant everywhere, then decide the arithmetic. -/
macro "mem_omega" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add, elementOverhead] at *; omega))

/-- The split over-take guard: `2d OP_PICK 34 OP_PICK OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY`. -/
def splitGuard : Bytes :=
  [1, 0x2d, Op.OP_PICK, 1, 0x34, Op.OP_PICK, Op.OP_SUB, Op.OP_0, Op.OP_GREATERTHANOREQUAL, Op.OP_VERIFY]

/-- A one-byte push is framed: `0x01` reads exactly the byte that follows it. -/
theorem framed_push1 (b : Nat) : framed [1, b] = true := by
  rw [framed.eq_2]
  simp [getOpTail, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1, framed.eq_1]

/-- The depth bytes the guard pushes decode to their indices. -/
theorem decode_2d : decode [0x2d] = 45 := by decide
theorem decode_34 : decode [0x34] = 52 := by decide

/-- The run of the guard up to its verify, as one equation: the two picks copy `bal` and
`piece`, the subtraction and the comparison leave the boolean `balance − piece ≥ 0` on top. -/
theorem splitGuard_run (env : Env) (t : Bytes) (st : State) (s : List Bytes) (bal piece : Bytes)
    (hstk : st.stack = s) (hbal : s.getD 45 [] = bal) (hpiece : s.getD 51 [] = piece)
    (hlen : 51 < s.length) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hb : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hp : piece.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode bal - decode piece)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + bal.length + piece.length + (encode (decode bal - decode piece)).length + 1 +
      3 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env splitGuard t st =
      run Eval.opExec env [Op.OP_VERIFY] t
        { st with opCount := st.opCount + 4,
                  stack := encode (if decode bal - decode piece ≥ 0 then 1 else 0) :: s,
                  memUsed := st.memUsed + (encode (if decode bal - decode piece ≥ 0 then 1 else 0)).length +
                    elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hE : Exec env st := ⟨hact, hret, hgen⟩
  have hrlen : (encode (if decode bal - decode piece ≥ 0 then 1 else 0)).length ≤ 1 := by
    split <;> simp [encode_zero, vec_1]
  -- 1. push 2d
  have h1 := run_push1 env ([Op.OP_PICK] ++ ([1, 0x34] ++ ([Op.OP_PICK] ++ ([Op.OP_SUB] ++ ([Op.OP_0] ++
    ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY]))))) ++ t) st 0x2d hE hmin (by omega)
  -- 2. pick 45 → bal
  have h2 := run_pick env ([1, 0x34] ++ ([Op.OP_PICK] ++ ([Op.OP_SUB] ++ ([Op.OP_0] ++
    ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY])))) ++ t)
    { st with stack := [0x2d] :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [0x2d] s 45 rfl decode_2d (by omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by show st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + ((s.getD 45 []).length + elementOverhead) ≤ _
        rw [hbal]; mem_omega)
  rw [hbal] at h2
  -- 3. push 34
  have h3 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_SUB] ++ ([Op.OP_0] ++
    ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY]))) ++ t)
    { st with opCount := st.opCount + 1, stack := bal :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) }
    0x34 ⟨hact, hret, hgen⟩ hmin
    (by show st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) + 1 +
          elementOverhead ≤ _
        mem_omega)
  -- 4. pick 52 → piece
  have hget52 : (bal :: s).getD 52 [] = piece := by
    rw [List.getD_cons_succ]; exact hpiece
  have h4 := run_pick env ([Op.OP_SUB] ++ ([Op.OP_0] ++ ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY])) ++ t)
    { st with opCount := st.opCount + 1, stack := [0x34] :: bal :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
                1 + elementOverhead }
    [0x34] (bal :: s) 52 rfl decode_34 (by mem_omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget52]
        show st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) + 1 +
          elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) ≤ _
        mem_omega)
  rw [hget52] at h4
  -- 5. sub
  have h5 := run_sub env ([Op.OP_0] ++ ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY]) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := piece :: bal :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
                1 + elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) }
    bal piece s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 ≤ _; omega) hb hp hd
    (by show st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
          1 + elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) -
          (piece.length + elementOverhead) - (bal.length + elementOverhead) + (encode (decode bal - decode piece)).length + elementOverhead ≤ _
        mem_omega)
  -- 6. push 0
  have h6 := run_push0 env ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := encode (decode bal - decode piece) :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
                1 + elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) -
                (piece.length + elementOverhead) - (bal.length + elementOverhead) + (encode (decode bal - decode piece)).length + elementOverhead }
    ⟨hact, hret, hgen⟩
    (by show st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
          1 + elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) -
          (piece.length + elementOverhead) - (bal.length + elementOverhead) + (encode (decode bal - decode piece)).length + elementOverhead +
          elementOverhead ≤ _
        mem_omega)
  -- 7. greaterthanorequal
  have hdd : decode (encode (decode bal - decode piece)) = decode bal - decode piece := decode_encode _
  have h7 := run_gte env ([Op.OP_VERIFY] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := [] :: encode (decode bal - decode piece) :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
                1 + elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) -
                (piece.length + elementOverhead) - (bal.length + elementOverhead) + (encode (decode bal - decode piece)).length + elementOverhead +
                elementOverhead }
    (encode (decode bal - decode piece)) [] s rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega) hd
    (by mem_omega)
    (by rw [decode_nil, hdd]
        show st.memUsed + 1 + elementOverhead - ([0x2d].length + elementOverhead) + (bal.length + elementOverhead) +
          1 + elementOverhead - ([0x34].length + elementOverhead) + (piece.length + elementOverhead) -
          (piece.length + elementOverhead) - (bal.length + elementOverhead) + (encode (decode bal - decode piece)).length + elementOverhead +
          elementOverhead - (List.length ([] : Bytes) + elementOverhead) - ((encode (decode bal - decode piece)).length + elementOverhead) +
          (encode (if decode bal - decode piece ≥ 0 then 1 else 0)).length + elementOverhead ≤ _
        simp only [List.length_nil]
        mem_omega)
  rw [decode_nil, hdd] at h7
  -- assemble
  show run Eval.opExec env ([1, 0x2d] ++ ([Op.OP_PICK] ++ ([1, 0x34] ++ ([Op.OP_PICK] ++ ([Op.OP_SUB] ++
    ([Op.OP_0] ++ ([Op.OP_GREATERTHANOREQUAL] ++ [Op.OP_VERIFY]))))))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h5]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_push0, h6]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h7]
  simp only [GOut.andThen]
  congr 1
  congr 1
  mem_omega

/-- **Lemma 6, accepted.** With `piece ≤ balance` the guard runs to its end, leaving the stack
and the memory counter as it found them and five opcodes charged. -/
theorem splitGuard_accepts (env : Env) (t : Bytes) (st : State) (s : List Bytes) (bal piece : Bytes)
    (hstk : st.stack = s) (hbal : s.getD 45 [] = bal) (hpiece : s.getD 51 [] = piece)
    (hlen : 51 < s.length) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hb : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hp : piece.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode bal - decode piece)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + bal.length + piece.length + (encode (decode bal - decode piece)).length + 1 +
      3 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hle : decode piece ≤ decode bal) :
    run Eval.opExec env splitGuard t st =
      .next { st with opCount := st.opCount + 5, stack := s, memUsed := st.memUsed } := by
  obtain ⟨hact, hret, hgen⟩ := he
  rw [splitGuard_run env t st s bal piece hstk hbal hpiece hlen ⟨hact, hret, hgen⟩ hmin hops hb hp hd hone hmem]
  have hge : decode bal - decode piece ≥ 0 := by omega
  simp only [hge, if_true, vec_1]
  rw [run_verify_true env t
    { st with opCount := st.opCount + 4, stack := [1] :: s, memUsed := st.memUsed + [1].length + elementOverhead }
    [1] s (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 4 + 1 ≤ _; omega)]
  congr 1
  all_goals (first | rfl |
    (congr 1 <;> (try simp only [List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add, elementOverhead]) <;>
      omega))

/-- **Lemma 6, refused.** With `piece > balance` the guard fails with `SCRIPT_ERR_VERIFY`: an
inflating split is refused at its commit. -/
theorem splitGuard_refuses (env : Env) (t : Bytes) (st : State) (s : List Bytes) (bal piece : Bytes)
    (hstk : st.stack = s) (hbal : s.getD 45 [] = bal) (hpiece : s.getD 51 [] = piece)
    (hlen : 51 < s.length) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hb : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hp : piece.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode bal - decode piece)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + bal.length + piece.length + (encode (decode bal - decode piece)).length + 1 +
      3 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage)
    (hgt : decode bal < decode piece) :
    ∃ st', run Eval.opExec env splitGuard t st = .err .verify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  rw [splitGuard_run env t st s bal piece hstk hbal hpiece hlen ⟨hact, hret, hgen⟩ hmin hops hb hp hd hone hmem]
  have hge : ¬ (decode bal - decode piece ≥ 0) := by omega
  simp only [hge, if_false, encode_zero]
  exact ⟨_, run_verify_false env t
    { st with opCount := st.opCount + 4, stack := [] :: s, memUsed := st.memUsed + [].length + elementOverhead }
    [] s (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 4 + 1 ≤ _; omega)⟩

/-- **Lemma 6 as an equivalence.** Under the guard's preconditions, it runs to its end iff
`piece ≤ balance`. -/
theorem splitGuard_next_iff (env : Env) (t : Bytes) (st : State) (s : List Bytes) (bal piece : Bytes)
    (hstk : st.stack = s) (hbal : s.getD 45 [] = bal) (hpiece : s.getD 51 [] = piece)
    (hlen : 51 < s.length) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hb : bal.length ≤ env.params.limits.maxScriptNumLength)
    (hp : piece.length ≤ env.params.limits.maxScriptNumLength)
    (hd : (encode (decode bal - decode piece)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + bal.length + piece.length + (encode (decode bal - decode piece)).length + 1 +
      3 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env splitGuard t st = .next st') ↔ decode piece ≤ decode bal := by
  constructor
  · intro ⟨st', h⟩
    by_contra hgt
    obtain ⟨st'', h'⟩ := splitGuard_refuses env t st s bal piece hstk hbal hpiece hlen he hmin hops hb hp hd hone
      hmem (by omega)
    rw [h] at h'
    cases h'
  · intro hle
    exact ⟨_, splitGuard_accepts env t st s bal piece hstk hbal hpiece hlen he hmin hops hb hp hd hone hmem hle⟩

end BoltProof.Gadgets
