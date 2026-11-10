import BoltProof.Model.Family
import BoltProof.Bridge.Gadgets.BalanceGuards

/-!
# Lemma 7 at the bytecode level: the fungible parity check

`docs/formal-proof.md` Lemma 7 (state machine), as the covenant evaluates it when a token is
spent — `txoType` the *spent* token's type, `nextTxoType` the *produced* token's type:

    spentIsCommitTyped = txoType mod 2
    if spentIsCommitTyped: assert nextTxoType == txoType − 1
    else:                  assert nextTxoType mod 2 == 1

In the shipped `SimpleMultiBOLT` covenant this is the 29 bytes at offset 528 of the suffix

    01 1a 79 52 97 76 63 01 26 79 8b 01 1c 79 88 68 76 01 27 79 52 97 7c 63 00 67 51 68 88

    1a OP_PICK OP_2 OP_MOD OP_DUP
    OP_IF 26 OP_PICK OP_1ADD 1c OP_PICK OP_EQUALVERIFY OP_ENDIF
    OP_DUP 27 OP_PICK OP_2 OP_MOD OP_SWAP
    OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF OP_EQUALVERIFY

`1a OP_PICK` copies the spent type (26 deep), `OP_2 OP_MOD` its parity bit `p`; inside the
`OP_IF` (taken when `p = 1`, a commit-typed token being settled) `26 OP_PICK OP_1ADD` is the
produced type plus one and `1c OP_PICK OP_EQUALVERIFY` asserts it is byte-for-byte the spent
type; then `27 OP_PICK OP_2 OP_MOD` is the produced type's parity and the
`OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF OP_EQUALVERIFY` asserts it equals `1 − p`. The parity bit `p`
is left on the stack for the branches that follow.

This module proves, over bsv-script-lean's own loop, that the fragment runs to its end exactly
when Lemma 7's predicate holds (`parityCheck_next_iff`), with the state it leaves pinned down
(`parityCheck_accepts_commit`, `parityCheck_accepts_settle`), and fails with
`SCRIPT_ERR_EQUALVERIFY` otherwise (`parityCheck_refuses_*`); `parityCheck_edge_iff` restates
the result on the six defined type bytes as the model's own edge relation `Fam.edge .fungible`.
The fragment is proved from its four sub-fragments, each with its own run lemma.
-/

set_option autoImplicit false

namespace BoltProof.Gadgets

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- Close `.next R = .next C` for two state records that agree up to arithmetic on the counters. -/
macro "state_congr" : tactic =>
  `(tactic| (congr 1; all_goals (first | rfl | (congr 1 <;> (try simp only [List.length_cons, List.length_nil,
      Nat.add_zero, Nat.zero_add, elementOverhead] at *) <;> omega))))

/-- The head: `1a OP_PICK OP_2 OP_MOD OP_DUP` — the spent type's parity bit, twice. -/
def parityHead : Bytes := [1, 0x1a, Op.OP_PICK, Op.OP_2, Op.OP_MOD, Op.OP_DUP]

/-- The settle-side branch: `OP_IF 26 OP_PICK OP_1ADD 1c OP_PICK OP_EQUALVERIFY OP_ENDIF`. -/
def parityBranch : Bytes :=
  [Op.OP_IF, 1, 0x26, Op.OP_PICK, Op.OP_1ADD, 1, 0x1c, Op.OP_PICK, Op.OP_EQUALVERIFY, Op.OP_ENDIF]

/-- The produced type's parity: `OP_DUP 27 OP_PICK OP_2 OP_MOD OP_SWAP`. -/
def parityNext : Bytes := [Op.OP_DUP, 1, 0x27, Op.OP_PICK, Op.OP_2, Op.OP_MOD, Op.OP_SWAP]

/-- The complement of the parity bit: `OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF`. -/
def parityFlip : Bytes := [Op.OP_IF, Op.OP_0, Op.OP_ELSE, Op.OP_1, Op.OP_ENDIF]

/-- The whole parity check. -/
def parityCheck : Bytes := parityHead ++ parityBranch ++ parityNext ++ parityFlip ++ [Op.OP_EQUALVERIFY]

/-- The check is the 29 bytes quoted in the header. -/
theorem parityCheck_bytes :
    parityCheck = [0x01, 0x1a, 0x79, 0x52, 0x97, 0x76, 0x63, 0x01, 0x26, 0x79, 0x8b, 0x01, 0x1c, 0x79,
      0x88, 0x68, 0x76, 0x01, 0x27, 0x79, 0x52, 0x97, 0x7c, 0x63, 0x00, 0x67, 0x51, 0x68, 0x88] := by
  decide

/-- The depth bytes the check pushes decode to their indices. -/
theorem decode_1a : decode [0x1a] = 26 := by decide
theorem decode_26 : decode [0x26] = 38 := by decide
theorem decode_1c : decode [0x1c] = 28 := by decide
theorem decode_27 : decode [0x27] = 39 := by decide
theorem decode_2 : decode [2] = 2 := by decide

/-- A non-push opcode reads no data: framing continues after it. -/
theorem framed_cons_op (op : Nat) (rest : Bytes) (hop : Op.OP_PUSHDATA4 < op) :
    framed (op :: rest) = framed rest := by
  rw [framed.eq_2]
  have : ¬ op ≤ Op.OP_PUSHDATA4 := by omega
  simp [getOpTail, this]

/-- A one-byte push reads exactly the byte after it. -/
theorem framed_cons_push1 (b : Nat) (rest : Bytes) : framed (1 :: b :: rest) = framed rest := by
  rw [framed.eq_2]
  simp [getOpTail, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1]

/-- `OP_0` reads no data. -/
theorem framed_cons_push0 (rest : Bytes) : framed (Op.OP_0 :: rest) = framed rest := by
  rw [framed.eq_2]
  simp [getOpTail, Op.OP_0, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1]

/-- The sub-fragments are framed: every push reads its data inside the fragment. -/
theorem framed_parityHead : framed parityHead = true := by
  rw [parityHead]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_parityBranch : framed parityBranch = true := by
  rw [parityBranch]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_parityNext : framed parityNext = true := by
  rw [parityNext]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1
theorem framed_parityFlip : framed parityFlip = true := by
  rw [parityFlip]
  repeat (first | rw [framed_cons_push1] | rw [framed_cons_push0] | rw [framed_cons_op _ _ (by decide)])
  exact framed.eq_1

/-- The conditional state after a taken `OP_IF` is active. -/
theorem isActive_opIf_true (c : Cond) (h : c.isActive = true) : (c.opIf true).isActive = true := by
  simpa [Cond.opIf, Cond.isActive] using h

/-- The conditional state after a skipped `OP_IF` is inactive. -/
theorem isActive_opIf_false (c : Cond) : (c.opIf false).isActive = false := by
  simp [Cond.opIf, Cond.isActive]

/-- After `OP_ELSE` the taken branch's complement is inactive. -/
theorem isActive_opIf_true_opElse (c : Cond) : ((c.opIf true).opElse).isActive = false := by
  simp [Cond.opIf, Cond.opElse, Cond.isActive]

/-- After `OP_ELSE` the skipped branch's complement is active. -/
theorem isActive_opIf_false_opElse (c : Cond) (h : c.isActive = true) :
    ((c.opIf false).opElse).isActive = true := by
  simpa [Cond.opIf, Cond.opElse, Cond.isActive] using h

/-! ## The head -/

/-- `1a OP_PICK OP_2 OP_MOD OP_DUP` from a stack `s` whose 27th element is the spent type `ty`:
the parity bit of `ty`, twice, three opcodes charged. -/
theorem parityHead_run (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty : Bytes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = ty) (hlen : 26 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + ty.length + 2 * (encode (Int.tmod (decode ty) 2)).length + 1 + 2 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityHead t st =
      .next { st with opCount := st.opCount + 3,
                      stack := encode (Int.tmod (decode ty) 2) :: encode (Int.tmod (decode ty) 2) :: s,
                      memUsed := st.memUsed + 2 * (encode (Int.tmod (decode ty) 2)).length +
                        2 * elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hE : Exec env st := ⟨hact, hret, hgen⟩
  -- 1. push 1a
  have h1 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_2] ++ ([Op.OP_MOD] ++ [Op.OP_DUP])) ++ t) st 0x1a hE hmin
    (by mem_omega)
  -- 2. pick 26 → ty
  have h2 := run_pick env ([Op.OP_2] ++ ([Op.OP_MOD] ++ [Op.OP_DUP]) ++ t)
    { st with stack := [0x1a] :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [0x1a] s 26 rfl decode_1a hlen ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by show st.memUsed + 1 + elementOverhead - ([0x1a].length + elementOverhead) +
          ((s.getD 26 []).length + elementOverhead) ≤ _
        rw [hty]; mem_omega)
  rw [hty] at h2
  -- 3. OP_2
  have h3 := run_op2 env ([Op.OP_MOD] ++ [Op.OP_DUP] ++ t)
    { st with opCount := st.opCount + 1, stack := ty :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x1a].length + elementOverhead) +
                (ty.length + elementOverhead) }
    ⟨hact, hret, hgen⟩ (by mem_omega)
  -- 4. mod
  have h4 := run_mod env ([Op.OP_DUP] ++ t)
    { st with opCount := st.opCount + 1, stack := [2] :: ty :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x1a].length + elementOverhead) +
                (ty.length + elementOverhead) + 1 + elementOverhead }
    ty [2] s rfl ⟨hact, hret, hgen⟩ hmin (by rw [decode_2]; decide)
    (by show st.opCount + 1 + 1 ≤ _; omega) hlt (by mem_omega)
    (by rw [decode_2]; mem_omega)
  rw [decode_2] at h4
  -- 5. dup
  have h5 := run_dup env t
    { st with opCount := st.opCount + 1 + 1, stack := encode (Int.tmod (decode ty) 2) :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([0x1a].length + elementOverhead) +
                (ty.length + elementOverhead) + 1 + elementOverhead - ([2].length + elementOverhead) -
                (ty.length + elementOverhead) + (encode (Int.tmod (decode ty) 2)).length + elementOverhead }
    (encode (Int.tmod (decode ty) 2)) s rfl ⟨hact, hret, hgen⟩
    (by show st.opCount + 1 + 1 + 1 ≤ _; omega) (by mem_omega)
  -- assemble
  show run Eval.opExec env ([1, 0x1a] ++ ([Op.OP_PICK] ++ ([Op.OP_2] ++ ([Op.OP_MOD] ++ [Op.OP_DUP])))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [h5]
  state_congr

/-! ## The settle-side branch -/

/-- `OP_IF … OP_ENDIF` taken (`p = 1`, a commit-typed token being settled) with the produced
type plus one equal, byte for byte, to the spent type: the branch runs through, leaving `p` on
top, six opcodes charged. -/
theorem parityBranch_one (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx ep : Bytes)
    (hstk : st.stack = [1] :: ep :: s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx)
    (hlen : 37 < s.length) (heq : encode (decode nx + 1) = ty)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 6 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + nx.length + 2 * ty.length + 1 + 3 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityBranch t st =
      .next { st with opCount := st.opCount + 6, stack := ep :: s,
                      memUsed := st.memUsed - (1 + elementOverhead) } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hact' : (st.cond.opIf true).isActive = true := isActive_opIf_true st.cond hact
  -- 1. OP_IF on [1]
  have h1 := run_if_one env ([1, 0x26] ++ ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++
    ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))))) ++ t) st (ep :: s) hstk ⟨hact, hret, hgen⟩ (by omega)
  -- 2. push 26
  have h2 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++
    ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF])))) ++ t)
    { st with opCount := st.opCount + 1, stack := ep :: s, memUsed := st.memUsed - (1 + elementOverhead),
              cond := st.cond.opIf true }
    0x26 ⟨hact', hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  -- 3. pick 38 → nx
  have hget38 : (ep :: s).getD 38 [] = nx := by rw [List.getD_cons_succ]; exact hnx
  have h3 := run_pick env ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))) ++ t)
    { st with opCount := st.opCount + 1, stack := [0x26] :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead, cond := st.cond.opIf true }
    [0x26] (ep :: s) 38 rfl decode_26 (by simp only [List.length_cons]; omega) ⟨hact', hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget38]; (try dsimp only); mem_omega)
  rw [hget38] at h3
  -- 4. 1add → ty
  have h4 := run_1add env ([1, 0x1c] ++ ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF])) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := nx :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead), cond := st.cond.opIf true }
    nx (ep :: s) rfl ⟨hact', hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 ≤ _; omega) hln
    (by rw [heq]; exact hlt) (by rw [heq]; (try dsimp only); mem_omega)
  rw [heq] at h4
  -- 5. push 1c
  have h5 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]) ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := ty :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + ty.length + elementOverhead,
              cond := st.cond.opIf true }
    0x1c ⟨hact', hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  -- 6. pick 28 → ty
  have hget28 : (ty :: ep :: s).getD 28 [] = ty := by
    rw [List.getD_cons_succ, List.getD_cons_succ]; exact hty
  have h6 := run_pick env ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := [0x1c] :: ty :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + ty.length + elementOverhead + 1 +
                elementOverhead,
              cond := st.cond.opIf true }
    [0x1c] (ty :: ep :: s) 28 rfl decode_1c (by simp only [List.length_cons]; omega) ⟨hact', hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget28]; (try dsimp only); mem_omega)
  rw [hget28] at h6
  -- 7. equalverify, equal
  have h7 := HashLock.run_equalverify_same env ([Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1 + 1, stack := ty :: ty :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + ty.length + elementOverhead + 1 +
                elementOverhead - ([0x1c].length + elementOverhead) + (ty.length + elementOverhead),
              cond := st.cond.opIf true }
    ty (ep :: s) rfl hact' hret (by show st.opCount + 1 + 1 + 1 + 1 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega) hgen
  -- 8. endif
  have h8 := run_endif_if env t
    { st with opCount := st.opCount + 1 + 1 + 1 + 1 + 1, stack := ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + ty.length + elementOverhead + 1 +
                elementOverhead - ([0x1c].length + elementOverhead) + (ty.length + elementOverhead) -
                (ty.length + elementOverhead) - (ty.length + elementOverhead) + 1 + elementOverhead -
                (1 + elementOverhead),
              cond := st.cond.opIf true }
    st.cond true rfl hret hgen (by show st.opCount + 1 + 1 + 1 + 1 + 1 + 1 ≤ _; omega)
  -- assemble
  show run Eval.opExec env ([Op.OP_IF] ++ ([1, 0x26] ++ ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++
    ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))))))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h5]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h6]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h7]
  simp only [GOut.andThen]
  rw [h8]
  state_congr

/-- `OP_IF … OP_ENDIF` taken with the produced type plus one *different* from the spent type:
`SCRIPT_ERR_EQUALVERIFY`. -/
theorem parityBranch_one_refuses (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx ep : Bytes)
    (hstk : st.stack = [1] :: ep :: s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx)
    (hlen : 37 < s.length) (hne : encode (decode nx + 1) ≠ ty)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 6 ≤ env.params.limits.maxOpsPerScript)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hl1 : (encode (decode nx + 1)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + nx.length + ty.length + (encode (decode nx + 1)).length + 1 + 3 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    ∃ st', run Eval.opExec env parityBranch t st = .err .equalverify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hact' : (st.cond.opIf true).isActive = true := isActive_opIf_true st.cond hact
  have h1 := run_if_one env ([1, 0x26] ++ ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++
    ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))))) ++ t) st (ep :: s) hstk ⟨hact, hret, hgen⟩ (by omega)
  have h2 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++
    ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF])))) ++ t)
    { st with opCount := st.opCount + 1, stack := ep :: s, memUsed := st.memUsed - (1 + elementOverhead),
              cond := st.cond.opIf true }
    0x26 ⟨hact', hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  have hget38 : (ep :: s).getD 38 [] = nx := by rw [List.getD_cons_succ]; exact hnx
  have h3 := run_pick env ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))) ++ t)
    { st with opCount := st.opCount + 1, stack := [0x26] :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead, cond := st.cond.opIf true }
    [0x26] (ep :: s) 38 rfl decode_26 (by simp only [List.length_cons]; omega) ⟨hact', hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget38]; (try dsimp only); mem_omega)
  rw [hget38] at h3
  have h4 := run_1add env ([1, 0x1c] ++ ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF])) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := nx :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead), cond := st.cond.opIf true }
    nx (ep :: s) rfl ⟨hact', hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 ≤ _; omega) hln hl1
    (by (try dsimp only); mem_omega)
  have h5 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]) ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := encode (decode nx + 1) :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + (encode (decode nx + 1)).length +
                elementOverhead,
              cond := st.cond.opIf true }
    0x1c ⟨hact', hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  have hget28 : (encode (decode nx + 1) :: ep :: s).getD 28 [] = ty := by
    rw [List.getD_cons_succ, List.getD_cons_succ]; exact hty
  have h6 := run_pick env ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := [0x1c] :: encode (decode nx + 1) :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + (encode (decode nx + 1)).length +
                elementOverhead + 1 + elementOverhead,
              cond := st.cond.opIf true }
    [0x1c] (encode (decode nx + 1) :: ep :: s) 28 rfl decode_1c (by simp only [List.length_cons]; omega)
    ⟨hact', hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget28]; (try dsimp only); mem_omega)
  rw [hget28] at h6
  have h7 := run_equalverify_ne env ([Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1 + 1, stack := ty :: encode (decode nx + 1) :: ep :: s,
              memUsed := st.memUsed - (1 + elementOverhead) + 1 + elementOverhead - ([0x26].length + elementOverhead) +
                (nx.length + elementOverhead) - (nx.length + elementOverhead) + (encode (decode nx + 1)).length +
                elementOverhead + 1 + elementOverhead - ([0x1c].length + elementOverhead) + (ty.length + elementOverhead),
              cond := st.cond.opIf true }
    (encode (decode nx + 1)) ty (ep :: s) hne rfl ⟨hact', hret, hgen⟩
    (by show st.opCount + 1 + 1 + 1 + 1 + 1 ≤ _; omega) (by (try dsimp only); mem_omega)
  show ∃ st', run Eval.opExec env ([Op.OP_IF] ++ ([1, 0x26] ++ ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++
    ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))))))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h5]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h6]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h7]
  simp only [GOut.andThen]
  exact ⟨_, rfl⟩

/-- `OP_IF … OP_ENDIF` skipped (`p = 0`, a settle-typed token being committed): the branch's
pushes are parsed and its four opcodes counted, nothing executes, `p` stays on top. -/
theorem parityBranch_nil (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ep : Bytes)
    (hstk : st.stack = [] :: ep :: s) (he : Exec env st)
    (hops : st.opCount + 6 ≤ env.params.limits.maxOpsPerScript) :
    run Eval.opExec env parityBranch t st =
      .next { st with opCount := st.opCount + 6, stack := ep :: s, memUsed := st.memUsed - elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hin : (st.cond.opIf false).isActive = false := isActive_opIf_false st.cond
  have h1 := run_if_nil env ([1, 0x26] ++ ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++
    ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))))) ++ t) st (ep :: s) hstk ⟨hact, hret, hgen⟩ (by omega)
  have h2 := run_skip_push1 env ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++
    ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF])))) ++ t)
    { st with opCount := st.opCount + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    0x26 ⟨hin, hret, hgen⟩
  have h3 := run_skip_op env ([Op.OP_1ADD] ++ ([1, 0x1c] ++ ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))) ++ t)
    { st with opCount := st.opCount + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    Op.OP_PICK ⟨hin, hret, hgen⟩ (Or.inl rfl) (by show st.opCount + 1 + 1 ≤ _; omega)
  have h4 := run_skip_op env ([1, 0x1c] ++ ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF])) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    Op.OP_1ADD ⟨hin, hret, hgen⟩ (Or.inr (Or.inl rfl)) (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
  have h5 := run_skip_push1 env ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]) ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    0x1c ⟨hin, hret, hgen⟩
  have h6 := run_skip_op env ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    Op.OP_PICK ⟨hin, hret, hgen⟩ (Or.inl rfl) (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega)
  have h7 := run_skip_op env ([Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1 + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    Op.OP_EQUALVERIFY ⟨hin, hret, hgen⟩ (Or.inr (Or.inr rfl)) (by show st.opCount + 1 + 1 + 1 + 1 + 1 ≤ _; omega)
  have h8 := run_endif_if env t
    { st with opCount := st.opCount + 1 + 1 + 1 + 1 + 1, stack := ep :: s, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    st.cond false rfl hret hgen (by show st.opCount + 1 + 1 + 1 + 1 + 1 + 1 ≤ _; omega)
  show run Eval.opExec env ([Op.OP_IF] ++ ([1, 0x26] ++ ([Op.OP_PICK] ++ ([Op.OP_1ADD] ++ ([1, 0x1c] ++
    ([Op.OP_PICK] ++ ([Op.OP_EQUALVERIFY] ++ [Op.OP_ENDIF]))))))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h5]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h6]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h7]
  simp only [GOut.andThen]
  rw [h8]
  state_congr

/-! ## The produced type's parity -/

/-- `OP_DUP 27 OP_PICK OP_2 OP_MOD OP_SWAP` from `p :: s` whose 38th element is the produced
type `nx`: `p :: (nx mod 2) :: p :: s`, four opcodes charged. -/
theorem parityNext_run (env : Env) (t : Bytes) (st : State) (s : List Bytes) (nx ep : Bytes)
    (hstk : st.stack = ep :: s) (hnx : s.getD 37 [] = nx) (hlen : 37 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 4 ≤ env.params.limits.maxOpsPerScript)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + ep.length + nx.length + (encode (Int.tmod (decode nx) 2)).length + 1 +
      3 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityNext t st =
      .next { st with opCount := st.opCount + 4,
                      stack := ep :: encode (Int.tmod (decode nx) 2) :: ep :: s,
                      memUsed := st.memUsed + ep.length + (encode (Int.tmod (decode nx) 2)).length +
                        2 * elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have h1 := run_dup env ([1, 0x27] ++ ([Op.OP_PICK] ++ ([Op.OP_2] ++ ([Op.OP_MOD] ++ [Op.OP_SWAP]))) ++ t)
    st ep s hstk ⟨hact, hret, hgen⟩ (by omega) (by mem_omega)
  have h2 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_2] ++ ([Op.OP_MOD] ++ [Op.OP_SWAP])) ++ t)
    { st with opCount := st.opCount + 1, stack := ep :: ep :: s,
              memUsed := st.memUsed + ep.length + elementOverhead }
    0x27 ⟨hact, hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  have hget39 : (ep :: ep :: s).getD 39 [] = nx := by
    rw [List.getD_cons_succ, List.getD_cons_succ]; exact hnx
  have h3 := run_pick env ([Op.OP_2] ++ ([Op.OP_MOD] ++ [Op.OP_SWAP]) ++ t)
    { st with opCount := st.opCount + 1, stack := [0x27] :: ep :: ep :: s,
              memUsed := st.memUsed + ep.length + elementOverhead + 1 + elementOverhead }
    [0x27] (ep :: ep :: s) 39 rfl decode_27 (by simp only [List.length_cons]; omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget39]; (try dsimp only); mem_omega)
  rw [hget39] at h3
  have h4 := run_op2 env ([Op.OP_MOD] ++ [Op.OP_SWAP] ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := nx :: ep :: ep :: s,
              memUsed := st.memUsed + ep.length + elementOverhead + 1 + elementOverhead -
                ([0x27].length + elementOverhead) + (nx.length + elementOverhead) }
    ⟨hact, hret, hgen⟩ (by (try dsimp only); mem_omega)
  have h5 := run_mod env ([Op.OP_SWAP] ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := [2] :: nx :: ep :: ep :: s,
              memUsed := st.memUsed + ep.length + elementOverhead + 1 + elementOverhead -
                ([0x27].length + elementOverhead) + (nx.length + elementOverhead) + 1 + elementOverhead }
    nx [2] (ep :: ep :: s) rfl ⟨hact, hret, hgen⟩ hmin (by rw [decode_2]; decide)
    (by show st.opCount + 1 + 1 + 1 ≤ _; omega) hln (by mem_omega)
    (by rw [decode_2]; (try dsimp only); mem_omega)
  rw [decode_2] at h5
  have h6 := run_swap env t
    { st with opCount := st.opCount + 1 + 1 + 1, stack := encode (Int.tmod (decode nx) 2) :: ep :: ep :: s,
              memUsed := st.memUsed + ep.length + elementOverhead + 1 + elementOverhead -
                ([0x27].length + elementOverhead) + (nx.length + elementOverhead) + 1 + elementOverhead -
                ([2].length + elementOverhead) - (nx.length + elementOverhead) +
                (encode (Int.tmod (decode nx) 2)).length + elementOverhead }
    (encode (Int.tmod (decode nx) 2)) ep (ep :: s) rfl ⟨hact, hret, hgen⟩
    (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega)
  show run Eval.opExec env ([Op.OP_DUP] ++ ([1, 0x27] ++ ([Op.OP_PICK] ++ ([Op.OP_2] ++ ([Op.OP_MOD] ++
    [Op.OP_SWAP]))))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h5]
  simp only [GOut.andThen]
  rw [h6]
  state_congr

/-! ## The complement of the parity bit -/

/-- `OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF` on `[1]`: `[]` pushed in its place, three opcodes charged. -/
theorem parityFlip_one (env : Env) (t : Bytes) (st : State) (rest : List Bytes)
    (hstk : st.stack = [1] :: rest) (he : Exec env st)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hmem : st.memUsed + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityFlip t st =
      .next { st with opCount := st.opCount + 3, stack := [] :: rest,
                      memUsed := st.memUsed - (1 + elementOverhead) + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hact' : (st.cond.opIf true).isActive = true := isActive_opIf_true st.cond hact
  have hin : ((st.cond.opIf true).opElse).isActive = false := isActive_opIf_true_opElse st.cond
  have h1 := run_if_one env ([Op.OP_0] ++ ([Op.OP_ELSE] ++ ([Op.OP_1] ++ [Op.OP_ENDIF])) ++ t) st rest hstk
    ⟨hact, hret, hgen⟩ (by omega)
  have h2 := run_push0 env ([Op.OP_ELSE] ++ ([Op.OP_1] ++ [Op.OP_ENDIF]) ++ t)
    { st with opCount := st.opCount + 1, stack := rest, memUsed := st.memUsed - (1 + elementOverhead),
              cond := st.cond.opIf true }
    ⟨hact', hret, hgen⟩ (by (try dsimp only); mem_omega)
  have h3 := run_else env ([Op.OP_1] ++ [Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1, stack := [] :: rest,
              memUsed := st.memUsed - (1 + elementOverhead) + elementOverhead, cond := st.cond.opIf true }
    st.cond true rfl hret hgen (by show st.opCount + 1 + 1 ≤ _; omega)
  have h4 := run_skip_op1 env ([Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := [] :: rest,
              memUsed := st.memUsed - (1 + elementOverhead) + elementOverhead, cond := (st.cond.opIf true).opElse }
    ⟨hin, hret, hgen⟩
  have h5 := run_endif_else env t
    { st with opCount := st.opCount + 1 + 1, stack := [] :: rest,
              memUsed := st.memUsed - (1 + elementOverhead) + elementOverhead, cond := (st.cond.opIf true).opElse }
    st.cond true rfl hret hgen (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
  show run Eval.opExec env ([Op.OP_IF] ++ ([Op.OP_0] ++ ([Op.OP_ELSE] ++ ([Op.OP_1] ++ [Op.OP_ENDIF])))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_push0, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [h5]

/-- `OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF` on `[]`: `[1]` pushed in its place, three opcodes charged. -/
theorem parityFlip_nil (env : Env) (t : Bytes) (st : State) (rest : List Bytes)
    (hstk : st.stack = [] :: rest) (he : Exec env st)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hmem : st.memUsed + 1 + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityFlip t st =
      .next { st with opCount := st.opCount + 3, stack := [1] :: rest,
                      memUsed := st.memUsed - elementOverhead + 1 + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hin : (st.cond.opIf false).isActive = false := isActive_opIf_false st.cond
  have hact' : ((st.cond.opIf false).opElse).isActive = true := isActive_opIf_false_opElse st.cond hact
  have h1 := run_if_nil env ([Op.OP_0] ++ ([Op.OP_ELSE] ++ ([Op.OP_1] ++ [Op.OP_ENDIF])) ++ t) st rest hstk
    ⟨hact, hret, hgen⟩ (by omega)
  have h2 := run_skip_push0 env ([Op.OP_ELSE] ++ ([Op.OP_1] ++ [Op.OP_ENDIF]) ++ t)
    { st with opCount := st.opCount + 1, stack := rest, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    ⟨hin, hret, hgen⟩
  have h3 := run_else env ([Op.OP_1] ++ [Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1, stack := rest, memUsed := st.memUsed - (0 + elementOverhead),
              cond := st.cond.opIf false }
    st.cond false rfl hret hgen (by show st.opCount + 1 + 1 ≤ _; omega)
  have h4 := run_op1 env ([Op.OP_ENDIF] ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := rest, memUsed := st.memUsed - (0 + elementOverhead),
              cond := (st.cond.opIf false).opElse }
    ⟨hact', hret, hgen⟩ (by (try dsimp only); mem_omega)
  have h5 := run_endif_else env t
    { st with opCount := st.opCount + 1 + 1, stack := [1] :: rest,
              memUsed := st.memUsed - (0 + elementOverhead) + 1 + elementOverhead, cond := (st.cond.opIf false).opElse }
    st.cond false rfl hret hgen (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
  show run Eval.opExec env ([Op.OP_IF] ++ ([Op.OP_0] ++ ([Op.OP_ELSE] ++ ([Op.OP_1] ++ [Op.OP_ENDIF])))) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_push0, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h4]
  simp only [GOut.andThen]
  rw [h5]
  state_congr

/-! ## The whole check -/

/-- The parity bit of a non-negative script number is `0` or `1`. -/
theorem tmod_two_cases (z : Int) (hz : 0 ≤ z) : Int.tmod z 2 = 0 ∨ Int.tmod z 2 = 1 := by
  rw [Int.tmod_eq_emod_of_nonneg hz]; omega

/-- `encode` is injective (`decode_encode`). -/
theorem encode_inj {x y : Int} (h : encode x = encode y) : x = y := by
  have := congrArg decode h
  rwa [decode_encode, decode_encode] at this

/-- **Lemma 7, accepted at a settle.** The spent type is odd (commit-typed) and the produced type
plus one is, byte for byte, the spent type: the check runs through, leaving the parity bit `[1]`
on top with seventeen opcodes charged. -/
theorem parityCheck_accepts_commit (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx : Bytes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx) (hlen : 37 < s.length)
    (hodd : Int.tmod (decode ty) 2 = 1) (heq : encode (decode nx + 1) = ty) (hnn : 0 ≤ decode nx)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 17 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + nx.length + 2 * ty.length + 3 + 5 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityCheck t st =
      .next { st with opCount := st.opCount + 17, stack := [1] :: s,
                      memUsed := st.memUsed + 1 + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hep : encode (Int.tmod (decode ty) 2) = [1] := by rw [hodd]; exact vec_1
  have hq : Int.tmod (decode nx) 2 = 0 := by
    have h1 : decode ty = decode nx + 1 := by rw [← heq, decode_encode]
    rw [h1, Int.tmod_eq_emod_of_nonneg (by omega)] at hodd
    rw [Int.tmod_eq_emod_of_nonneg hnn]
    omega
  have heq0 : encode (Int.tmod (decode nx) 2) = [] := by rw [hq]; exact encode_zero
  have hH := parityHead_run env (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])) ++ t) st s ty
    hstk hty (by omega) ⟨hact, hret, hgen⟩ hmin (by omega) hlt hone (by rw [hep]; mem_omega)
  rw [hep] at hH
  have hB := parityBranch_one env (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY]) ++ t)
    { st with opCount := st.opCount + 3, stack := [1] :: [1] :: s,
              memUsed := st.memUsed + 2 * [1].length + 2 * elementOverhead }
    s ty nx [1] rfl hty hnx hlen heq ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 3 + 6 ≤ _; omega) hlt hln hone
    (by (try dsimp only); mem_omega)
  have hN := parityNext_run env (parityFlip ++ [Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 3 + 6, stack := [1] :: s,
              memUsed := st.memUsed + 2 * [1].length + 2 * elementOverhead - (1 + elementOverhead) }
    s nx [1] rfl hnx hlen ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 3 + 6 + 4 ≤ _; omega) hln hone
    (by rw [heq0]; (try dsimp only); mem_omega)
  rw [heq0] at hN
  have hF := parityFlip_one env ([Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 3 + 6 + 4, stack := [1] :: [] :: [1] :: s,
              memUsed := st.memUsed + 2 * [1].length + 2 * elementOverhead - (1 + elementOverhead) + [1].length +
                ([] : Bytes).length + 2 * elementOverhead }
    ([] :: [1] :: s) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 3 + 6 + 4 + 3 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  have hV := HashLock.run_equalverify_same env t
    { st with opCount := st.opCount + 3 + 6 + 4 + 3, stack := [] :: [] :: [1] :: s,
              memUsed := st.memUsed + 2 * [1].length + 2 * elementOverhead - (1 + elementOverhead) + [1].length +
                ([] : Bytes).length + 2 * elementOverhead - (1 + elementOverhead) + elementOverhead }
    [] ([1] :: s) rfl hact hret (by show st.opCount + 3 + 6 + 4 + 3 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega) hgen
  show run Eval.opExec env (parityHead ++ (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ framed_parityHead, hH]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityBranch, hB]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityNext, hN]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityFlip, hF]
  simp only [GOut.andThen]
  rw [hV]
  state_congr

/-- **Lemma 7, accepted at a commit.** The spent type is even (settle-typed) and the produced
type is odd: the check runs through, leaving the parity bit `[]` on top with seventeen opcodes
charged. -/
theorem parityCheck_accepts_settle (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx : Bytes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx) (hlen : 37 < s.length)
    (heven : Int.tmod (decode ty) 2 = 0) (hqodd : Int.tmod (decode nx) 2 = 1)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 17 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + ty.length + nx.length + 2 + 4 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env parityCheck t st =
      .next { st with opCount := st.opCount + 17, stack := [] :: s,
                      memUsed := st.memUsed + elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hep : encode (Int.tmod (decode ty) 2) = [] := by rw [heven]; exact encode_zero
  have heq1 : encode (Int.tmod (decode nx) 2) = [1] := by rw [hqodd]; exact vec_1
  have hH := parityHead_run env (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])) ++ t) st s ty
    hstk hty (by omega) ⟨hact, hret, hgen⟩ hmin (by omega) hlt hone (by rw [hep]; mem_omega)
  rw [hep] at hH
  have hB := parityBranch_nil env (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY]) ++ t)
    { st with opCount := st.opCount + 3, stack := [] :: [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead }
    s [] rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 3 + 6 ≤ _; omega)
  have hN := parityNext_run env (parityFlip ++ [Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 3 + 6, stack := [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead - elementOverhead }
    s nx [] rfl hnx hlen ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 3 + 6 + 4 ≤ _; omega) hln hone
    (by rw [heq1]; (try dsimp only); mem_omega)
  rw [heq1] at hN
  have hF := parityFlip_nil env ([Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 3 + 6 + 4, stack := [] :: [1] :: [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead - elementOverhead + ([] : Bytes).length +
                [1].length + 2 * elementOverhead }
    ([1] :: [] :: s) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 3 + 6 + 4 + 3 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  have hV := HashLock.run_equalverify_same env t
    { st with opCount := st.opCount + 3 + 6 + 4 + 3, stack := [1] :: [1] :: [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead - elementOverhead + ([] : Bytes).length +
                [1].length + 2 * elementOverhead - elementOverhead + 1 + elementOverhead }
    [1] ([] :: s) rfl hact hret (by show st.opCount + 3 + 6 + 4 + 3 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega) hgen
  show run Eval.opExec env (parityHead ++ (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ framed_parityHead, hH]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityBranch, hB]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityNext, hN]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityFlip, hF]
  simp only [GOut.andThen]
  rw [hV]
  state_congr

/-- **Lemma 7, refused at a settle.** The spent type is odd but the produced type plus one is not
the spent type: `SCRIPT_ERR_EQUALVERIFY` — a commit-typed token settles only to its own
settle type. -/
theorem parityCheck_refuses_commit (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx : Bytes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx) (hlen : 37 < s.length)
    (hodd : Int.tmod (decode ty) 2 = 1) (hne : encode (decode nx + 1) ≠ ty)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 17 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hl1 : (encode (decode nx + 1)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + nx.length + ty.length + (encode (decode nx + 1)).length + 3 + 5 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    ∃ st', run Eval.opExec env parityCheck t st = .err .equalverify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hep : encode (Int.tmod (decode ty) 2) = [1] := by rw [hodd]; exact vec_1
  have hH := parityHead_run env (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])) ++ t) st s ty
    hstk hty (by omega) ⟨hact, hret, hgen⟩ hmin (by omega) hlt hone (by rw [hep]; mem_omega)
  rw [hep] at hH
  obtain ⟨st', hB⟩ := parityBranch_one_refuses env (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY]) ++ t)
    { st with opCount := st.opCount + 3, stack := [1] :: [1] :: s,
              memUsed := st.memUsed + 2 * [1].length + 2 * elementOverhead }
    s ty nx [1] rfl hty hnx hlen hne ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 3 + 6 ≤ _; omega) hln hl1 hone
    (by (try dsimp only); mem_omega)
  refine ⟨st', ?_⟩
  show run Eval.opExec env (parityHead ++ (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ framed_parityHead, hH]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityBranch, hB]
  simp only [GOut.andThen]

/-- **Lemma 7, refused at a commit.** The spent type is even and so is the produced type:
`SCRIPT_ERR_EQUALVERIFY` — a settle-typed token is followed only by a commit-typed one. -/
theorem parityCheck_refuses_settle (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx : Bytes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx) (hlen : 37 < s.length)
    (heven : Int.tmod (decode ty) 2 = 0) (hqeven : Int.tmod (decode nx) 2 = 0)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 17 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + ty.length + nx.length + 2 + 4 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    ∃ st', run Eval.opExec env parityCheck t st = .err .equalverify st' := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hep : encode (Int.tmod (decode ty) 2) = [] := by rw [heven]; exact encode_zero
  have heq0 : encode (Int.tmod (decode nx) 2) = [] := by rw [hqeven]; exact encode_zero
  have hH := parityHead_run env (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])) ++ t) st s ty
    hstk hty (by omega) ⟨hact, hret, hgen⟩ hmin (by omega) hlt hone (by rw [hep]; mem_omega)
  rw [hep] at hH
  have hB := parityBranch_nil env (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY]) ++ t)
    { st with opCount := st.opCount + 3, stack := [] :: [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead }
    s [] rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 3 + 6 ≤ _; omega)
  have hN := parityNext_run env (parityFlip ++ [Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 3 + 6, stack := [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead - elementOverhead }
    s nx [] rfl hnx hlen ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 3 + 6 + 4 ≤ _; omega) hln hone
    (by rw [heq0]; (try dsimp only); mem_omega)
  rw [heq0] at hN
  have hF := parityFlip_nil env ([Op.OP_EQUALVERIFY] ++ t)
    { st with opCount := st.opCount + 3 + 6 + 4, stack := [] :: [] :: [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead - elementOverhead + ([] : Bytes).length +
                ([] : Bytes).length + 2 * elementOverhead }
    ([] :: [] :: s) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 3 + 6 + 4 + 3 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  have hV := run_equalverify_ne env t
    { st with opCount := st.opCount + 3 + 6 + 4 + 3, stack := [1] :: [] :: [] :: s,
              memUsed := st.memUsed + 2 * ([] : Bytes).length + 2 * elementOverhead - elementOverhead + ([] : Bytes).length +
                ([] : Bytes).length + 2 * elementOverhead - elementOverhead + 1 + elementOverhead }
    [] [1] ([] :: s) (by decide) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 3 + 6 + 4 + 3 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  show ∃ st', run Eval.opExec env (parityHead ++ (parityBranch ++ (parityNext ++ (parityFlip ++ [Op.OP_EQUALVERIFY])))) t st = _
  rw [run_append _ _ _ _ _ _ framed_parityHead, hH]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityBranch, hB]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityNext, hN]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ framed_parityFlip, hF]
  simp only [GOut.andThen]
  rw [hV]
  exact ⟨_, rfl⟩

/-- **Lemma 7 as an equivalence.** For non-negative types, under the check's preconditions, it
runs to its end iff the hand proof's predicate holds: an odd (commit-typed) spent type forces the
produced type to be one less, byte for byte; an even (settle-typed) spent type forces an odd one. -/
theorem parityCheck_next_iff (env : Env) (t : Bytes) (st : State) (s : List Bytes) (ty nx : Bytes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = ty) (hnx : s.getD 37 [] = nx) (hlen : 37 < s.length)
    (hnt : 0 ≤ decode ty) (hnn : 0 ≤ decode nx)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 17 ≤ env.params.limits.maxOpsPerScript)
    (hlt : ty.length ≤ env.params.limits.maxScriptNumLength)
    (hln : nx.length ≤ env.params.limits.maxScriptNumLength)
    (hl1 : (encode (decode nx + 1)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + nx.length + 2 * ty.length + (encode (decode nx + 1)).length + 3 + 5 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env parityCheck t st = .next st') ↔
      ((Int.tmod (decode ty) 2 = 1 ∧ encode (decode nx + 1) = ty) ∨
        (Int.tmod (decode ty) 2 = 0 ∧ Int.tmod (decode nx) 2 = 1)) := by
  constructor
  · rintro ⟨st', h⟩
    rcases tmod_two_cases _ hnt with h0 | h1
    · rcases tmod_two_cases _ hnn with q0 | q1
      · exfalso
        obtain ⟨st'', h'⟩ := parityCheck_refuses_settle env t st s ty nx hstk hty hnx hlen h0 q0 he hmin hops
          hlt hln hone (by omega)
        rw [h] at h'
        cases h'
      · exact Or.inr ⟨h0, q1⟩
    · by_cases heq : encode (decode nx + 1) = ty
      · exact Or.inl ⟨h1, heq⟩
      · exfalso
        obtain ⟨st'', h'⟩ := parityCheck_refuses_commit env t st s ty nx hstk hty hnx hlen h1 heq he hmin hops
          hlt hln hl1 hone (by omega)
        rw [h] at h'
        cases h'
  · rintro (⟨h1, heq⟩ | ⟨h0, q1⟩)
    · exact ⟨_, parityCheck_accepts_commit env t st s ty nx hstk hty hnx hlen h1 heq hnn he hmin hops hlt hln hone
        (by omega)⟩
    · exact ⟨_, parityCheck_accepts_settle env t st s ty nx hstk hty hnx hlen h0 q1 he hmin hops hlt hln hone
        (by omega)⟩

/-- **Lemma 7 as the model's edge relation.** On the six defined fungible type bytes, carried as
their minimal encodings, the check runs through exactly when `Fam.edge .fungible a b` holds: the
Layer-1 interface's `commit_type`/`settle_type` clauses are what these 29 bytes enforce. -/
theorem parityCheck_edge_iff (env : Env) (t : Bytes) (st : State) (s : List Bytes) (a b : Nat)
    (ha : a ∈ Fam.fungible.settleTypes ∨ a ∈ Fam.fungible.commitTypes)
    (hb : b ∈ Fam.fungible.settleTypes ∨ b ∈ Fam.fungible.commitTypes)
    (hstk : st.stack = s) (hty : s.getD 26 [] = encode a) (hnx : s.getD 37 [] = encode b)
    (hlen : 37 < s.length)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 17 ≤ env.params.limits.maxOpsPerScript)
    (hlt : (encode (a : Int)).length ≤ env.params.limits.maxScriptNumLength)
    (hln : (encode (b : Int)).length ≤ env.params.limits.maxScriptNumLength)
    (hl1 : (encode ((b : Int) + 1)).length ≤ env.params.limits.maxScriptNumLength)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + (encode (b : Int)).length + 2 * (encode (a : Int)).length +
      (encode ((b : Int) + 1)).length + 3 + 5 * elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    (∃ st', run Eval.opExec env parityCheck t st = .next st') ↔ Fam.edge .fungible a b := by
  rw [parityCheck_next_iff env t st s (encode a) (encode b) hstk hty hnx hlen (by rw [decode_encode]; omega)
    (by rw [decode_encode]; omega) he hmin hops hlt hln (by rw [decode_encode]; exact hl1) hone
    (by rw [decode_encode]; exact hmem)]
  simp only [decode_encode]
  simp only [Fam.settleTypes, Fam.commitTypes, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with (rfl | rfl | rfl) | rfl | rfl | rfl <;> rcases hb with (rfl | rfl | rfl) | rfl | rfl | rfl <;> decide

end BoltProof.Gadgets
