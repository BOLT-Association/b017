import BoltProof.Model.Family
import BoltProof.Bridge.Gadgets.Parity

/-!
# Lemma 7 at the bytecode level: the NFT covenant's type selector

In the NFT family (`MinSimpleBOLT`, `AuthBOLT`, `SerialBOLT`) the produced token's type is not
*checked* but *written* by the covenant: the serialized output it welds into `hashOutputs`
(Lemma 2) carries the type field `01 00` (type `0x00`, settle-typed) when the spent token is
commit-typed and `01 21` (type `0x21`, commit-typed) otherwise. Two fragments do this:

* the prologue derives the flag from the spent `txoType` field — `OP_DUP OP_BIN2NUM
  OP_0NOTEQUAL` (`76 81 92`, offset 6 of the `MinSimpleBOLT` and `AuthBOLT` suffixes, 39 of
  `SerialBOLT`'s), i.e. `txoType ≠ 0`;
* the selector reads that flag back and appends the type field to the output being built —
  `d OP_PICK OP_IF 0100 OP_ELSE 0121 OP_ENDIF OP_CAT` (`01 d 79 63 02 01 00 67 02 01 21 68 7e`,
  with the depth `d = 0x17` at offset 534 of `MinSimpleBOLT` and 543 of `AuthBOLT`, `d = 0x18`
  at offset 589 of `SerialBOLT`).

This module proves both over bsv-script-lean's own loop: `nftFlag_run` (the flag is the
boolean `txoType ≠ 0`), `nftTypeSel_run_commit` / `nftTypeSel_run_settle` (the selector appends
exactly the type byte Lemma 7 dictates and changes nothing else), and `nftTypeSel_edge` (on the
family's two defined type bytes the written type is a `Fam.edge .nft` successor of the spent
one). Since the serialized outputs are bound by `hashOutputs`, the NFT family's state machine
holds by construction: no spender input participates in the choice.
-/

set_option autoImplicit false

namespace BoltProof.Gadgets

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget

/-- The prologue's flag: `OP_DUP OP_BIN2NUM OP_0NOTEQUAL`, `txoType ≠ 0` above the type. -/
def nftFlag : Bytes := [Op.OP_DUP, Op.OP_BIN2NUM, Op.OP_0NOTEQUAL]

/-- The type selector at depth byte `d`: `d OP_PICK OP_IF 0100 OP_ELSE 0121 OP_ENDIF OP_CAT`. -/
def nftTypeSel (d : Nat) : Bytes :=
  [1, d, Op.OP_PICK, Op.OP_IF, 2, 1, 0, Op.OP_ELSE, 2, 1, 0x21, Op.OP_ENDIF, Op.OP_CAT]

/-- The selector is the 13 bytes quoted in the header. -/
theorem nftTypeSel_bytes (d : Nat) :
    nftTypeSel d = [0x01, d, 0x79, 0x63, 0x02, 0x01, 0x00, 0x67, 0x02, 0x01, 0x21, 0x68, 0x7e] := rfl

/-- A two-byte push is framed: `0x02` reads exactly the two bytes that follow it. -/
theorem framed_push2 (b1 b2 : Nat) : framed [2, b1, b2] = true := by
  rw [framed.eq_2]
  simp [getOpTail, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1, framed.eq_1]

/-- The depth bytes the three NFT covenants use decode to their indices. -/
theorem decode_17 : decode [0x17] = 23 := by decide
theorem decode_18 : decode [0x18] = 24 := by decide

/-! ## The flag -/

/-- `OP_DUP OP_BIN2NUM OP_0NOTEQUAL` from a stack whose top is the spent type `ty`: the
boolean `ty ≠ 0` (as a script number, `[1]` or `[]`) pushed above it, three opcodes charged. -/
theorem nftFlag_run (env : Env) (t : Bytes) (st : State) (ty : Bytes) (rest : List Bytes)
    (hstk : st.stack = ty :: rest) (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 3 ≤ env.params.limits.maxOpsPerScript)
    (hlen : (encode (decode ty)).length ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + ty.length + (encode (decode ty)).length + 1 + 2 * elementOverhead ≤
      env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env nftFlag t st =
      .next { st with opCount := st.opCount + 3,
                      stack := encode (if decode ty = 0 then 0 else 1) :: ty :: rest,
                      memUsed := st.memUsed + (encode (if decode ty = 0 then 0 else 1)).length +
                        elementOverhead } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hb : (encode (if decode ty = 0 then 0 else 1)).length ≤ 1 := by
    split <;> simp [encode_zero, vec_1]
  have h1 := run_dup env ([Op.OP_BIN2NUM] ++ [Op.OP_0NOTEQUAL] ++ t) st ty rest hstk ⟨hact, hret, hgen⟩
    (by omega) (by mem_omega)
  have h2 := run_bin2num env ([Op.OP_0NOTEQUAL] ++ t)
    { st with opCount := st.opCount + 1, stack := ty :: ty :: rest,
              memUsed := st.memUsed + ty.length + elementOverhead }
    ty (ty :: rest) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 1 ≤ _; omega) hlen
    (by (try dsimp only); mem_omega)
  have h3 := run_0notequal env t
    { st with opCount := st.opCount + 1 + 1, stack := encode (decode ty) :: ty :: rest,
              memUsed := st.memUsed + ty.length + elementOverhead - (ty.length + elementOverhead) +
                (encode (decode ty)).length + elementOverhead }
    (encode (decode ty)) (ty :: rest) rfl ⟨hact, hret, hgen⟩ hmin (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
    hlen (by rw [decode_encode]; (try dsimp only); mem_omega)
  rw [decode_encode] at h3
  show run Eval.opExec env ([Op.OP_DUP] ++ ([Op.OP_BIN2NUM] ++ [Op.OP_0NOTEQUAL])) t st = _
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h2]
  simp only [GOut.andThen]
  rw [h3]
  state_congr

/-! ## The selector -/

/-- The selector with the flag `[1]` (the spent token is commit-typed): the type field `01 00`
is appended to the output being built on top, five opcodes charged. -/
theorem nftTypeSel_run_commit (env : Env) (t : Bytes) (st : State) (s : List Bytes) (acc : Bytes)
    (d n : Nat) (hd : decode [d] = n + 1)
    (hstk : st.stack = acc :: s) (hf : s.getD n [] = [1]) (hlen : n < s.length)
    (hacc : acc.length + elementOverhead ≤ st.memUsed)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + 2 + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env (nftTypeSel d) t st =
      .next { st with opCount := st.opCount + 5, stack := (acc ++ [1, 0]) :: s,
                      memUsed := st.memUsed + 2 } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hact' : (st.cond.opIf true).isActive = true := isActive_opIf_true st.cond hact
  have hin : ((st.cond.opIf true).opElse).isActive = false := isActive_opIf_true_opElse st.cond
  have hget : (acc :: s).getD (n + 1) [] = [1] := by rw [List.getD_cons_succ]; exact hf
  -- 1. push d
  have h1 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_IF] ++ ([2, 1, 0] ++ ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++
    ([Op.OP_ENDIF] ++ [Op.OP_CAT]))))) ++ t) st d ⟨hact, hret, hgen⟩ hmin (by mem_omega)
  -- 2. pick the flag
  have h2 := run_pick env ([Op.OP_IF] ++ ([2, 1, 0] ++ ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++
    ([Op.OP_ENDIF] ++ [Op.OP_CAT])))) ++ t)
    { st with stack := [d] :: acc :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [d] (acc :: s) (n + 1) rfl hd (by simp only [List.length_cons]; omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget]; (try dsimp only); mem_omega)
  rw [hget] at h2
  -- 3. OP_IF on [1]
  have h3 := run_if_one env ([2, 1, 0] ++ ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT]))) ++ t)
    { st with opCount := st.opCount + 1, stack := [1] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                ([1].length + elementOverhead) }
    (acc :: s) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 1 ≤ _; omega)
  -- 4. push 01 00
  have h4 := run_push2 env ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT])) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                ([1].length + elementOverhead) - (1 + elementOverhead),
              cond := st.cond.opIf true }
    1 0 ⟨hact', hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  -- 5. OP_ELSE
  have h5 := run_else env ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT]) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := [1, 0] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                ([1].length + elementOverhead) - (1 + elementOverhead) + 2 + elementOverhead,
              cond := st.cond.opIf true }
    st.cond true rfl hret hgen (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
  -- 6. the skipped push 01 21
  have h6 := run_skip_push2 env ([Op.OP_ENDIF] ++ [Op.OP_CAT] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := [1, 0] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                ([1].length + elementOverhead) - (1 + elementOverhead) + 2 + elementOverhead,
              cond := (st.cond.opIf true).opElse }
    1 0x21 ⟨hin, hret, hgen⟩
  -- 7. OP_ENDIF
  have h7 := run_endif_else env ([Op.OP_CAT] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := [1, 0] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                ([1].length + elementOverhead) - (1 + elementOverhead) + 2 + elementOverhead,
              cond := (st.cond.opIf true).opElse }
    st.cond true rfl hret hgen (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega)
  -- 8. OP_CAT
  have h8 := run_cat env t
    { st with opCount := st.opCount + 1 + 1 + 1 + 1, stack := [1, 0] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                ([1].length + elementOverhead) - (1 + elementOverhead) + 2 + elementOverhead }
    acc [1, 0] s rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 1 + 1 + 1 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  show run Eval.opExec env ([1, d] ++ ([Op.OP_PICK] ++ ([Op.OP_IF] ++ ([2, 1, 0] ++ ([Op.OP_ELSE] ++
    ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT]))))))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push2 _ _), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h5]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push2 _ _), h6]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h7]
  simp only [GOut.andThen]
  rw [h8]
  state_congr

/-- The selector with the flag `[]` (the spent token is settle-typed): the type field `01 21`
is appended to the output being built on top, five opcodes charged. -/
theorem nftTypeSel_run_settle (env : Env) (t : Bytes) (st : State) (s : List Bytes) (acc : Bytes)
    (d n : Nat) (hd : decode [d] = n + 1)
    (hstk : st.stack = acc :: s) (hf : s.getD n [] = []) (hlen : n < s.length)
    (hacc : acc.length + elementOverhead ≤ st.memUsed)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + 2 + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    run Eval.opExec env (nftTypeSel d) t st =
      .next { st with opCount := st.opCount + 5, stack := (acc ++ [1, 0x21]) :: s,
                      memUsed := st.memUsed + 2 } := by
  obtain ⟨hact, hret, hgen⟩ := he
  have hin : (st.cond.opIf false).isActive = false := isActive_opIf_false st.cond
  have hact' : ((st.cond.opIf false).opElse).isActive = true := isActive_opIf_false_opElse st.cond hact
  have hget : (acc :: s).getD (n + 1) [] = [] := by rw [List.getD_cons_succ]; exact hf
  have h1 := run_push1 env ([Op.OP_PICK] ++ ([Op.OP_IF] ++ ([2, 1, 0] ++ ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++
    ([Op.OP_ENDIF] ++ [Op.OP_CAT]))))) ++ t) st d ⟨hact, hret, hgen⟩ hmin (by mem_omega)
  have h2 := run_pick env ([Op.OP_IF] ++ ([2, 1, 0] ++ ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++
    ([Op.OP_ENDIF] ++ [Op.OP_CAT])))) ++ t)
    { st with stack := [d] :: acc :: s, memUsed := st.memUsed + 1 + elementOverhead }
    [d] (acc :: s) (n + 1) rfl hd (by simp only [List.length_cons]; omega) ⟨hact, hret, hgen⟩ hmin
    (by show st.opCount + 1 ≤ _; omega) (by mem_omega)
    (by rw [hget]; (try dsimp only); mem_omega)
  rw [hget] at h2
  have h3 := run_if_nil env ([2, 1, 0] ++ ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT]))) ++ t)
    { st with opCount := st.opCount + 1, stack := [] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                (([] : Bytes).length + elementOverhead) }
    (acc :: s) rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 1 ≤ _; omega)
  have h4 := run_skip_push2 env ([Op.OP_ELSE] ++ ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT])) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                (([] : Bytes).length + elementOverhead) - (0 + elementOverhead),
              cond := st.cond.opIf false }
    1 0 ⟨hin, hret, hgen⟩
  have h5 := run_else env ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT]) ++ t)
    { st with opCount := st.opCount + 1 + 1, stack := acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                (([] : Bytes).length + elementOverhead) - (0 + elementOverhead),
              cond := st.cond.opIf false }
    st.cond false rfl hret hgen (by show st.opCount + 1 + 1 + 1 ≤ _; omega)
  have h6 := run_push2 env ([Op.OP_ENDIF] ++ [Op.OP_CAT] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                (([] : Bytes).length + elementOverhead) - (0 + elementOverhead),
              cond := (st.cond.opIf false).opElse }
    1 0x21 ⟨hact', hret, hgen⟩ hmin (by (try dsimp only); mem_omega)
  have h7 := run_endif_else env ([Op.OP_CAT] ++ t)
    { st with opCount := st.opCount + 1 + 1 + 1, stack := [1, 0x21] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                (([] : Bytes).length + elementOverhead) - (0 + elementOverhead) + 2 + elementOverhead,
              cond := (st.cond.opIf false).opElse }
    st.cond false rfl hret hgen (by show st.opCount + 1 + 1 + 1 + 1 ≤ _; omega)
  have h8 := run_cat env t
    { st with opCount := st.opCount + 1 + 1 + 1 + 1, stack := [1, 0x21] :: acc :: s,
              memUsed := st.memUsed + 1 + elementOverhead - ([d].length + elementOverhead) +
                (([] : Bytes).length + elementOverhead) - (0 + elementOverhead) + 2 + elementOverhead }
    acc [1, 0x21] s rfl ⟨hact, hret, hgen⟩ (by show st.opCount + 1 + 1 + 1 + 1 + 1 ≤ _; omega)
    (by (try dsimp only); mem_omega)
  show run Eval.opExec env ([1, d] ++ ([Op.OP_PICK] ++ ([Op.OP_IF] ++ ([2, 1, 0] ++ ([Op.OP_ELSE] ++
    ([2, 1, 0x21] ++ ([Op.OP_ENDIF] ++ [Op.OP_CAT]))))))) t st = _
  rw [run_append _ _ _ _ _ _ (framed_push1 _), h1]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), hstk, h2]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h3]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push2 _ _), h4]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h5]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (framed_push2 _ _), h6]
  simp only [GOut.andThen]
  rw [run_append _ _ _ _ _ _ (HashLock.framed_single _ (by decide)), h7]
  simp only [GOut.andThen]
  rw [h8]
  state_congr

/-- **Lemma 7 for the NFT family, by construction.** With the flag the prologue derives from a
spent type byte `a` of the family (`0x00` or `0x21`; `nftFlag_run`), the selector writes a type
byte `b` with `Fam.edge .nft a b` and changes nothing else. -/
theorem nftTypeSel_edge (env : Env) (t : Bytes) (st : State) (s : List Bytes) (acc : Bytes)
    (d n a : Nat) (hd : decode [d] = n + 1)
    (ha : a ∈ Fam.nft.settleTypes ∨ a ∈ Fam.nft.commitTypes)
    (hstk : st.stack = acc :: s) (hf : s.getD n [] = encode (if (a : Int) = 0 then 0 else 1))
    (hlen : n < s.length) (hacc : acc.length + elementOverhead ≤ st.memUsed)
    (he : Exec env st) (hmin : env.requireMinimal = false)
    (hops : st.opCount + 5 ≤ env.params.limits.maxOpsPerScript)
    (hone : 1 ≤ env.params.limits.maxScriptNumLength)
    (hmem : st.memUsed + 2 + elementOverhead ≤ env.params.limits.maxStackMemoryUsage) :
    ∃ b : Nat, Fam.edge .nft a b ∧
      run Eval.opExec env (nftTypeSel d) t st =
        .next { st with opCount := st.opCount + 5, stack := (acc ++ [1, b]) :: s,
                        memUsed := st.memUsed + 2 } := by
  simp only [Fam.settleTypes, Fam.commitTypes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · refine ⟨0x21, by decide, ?_⟩
    exact nftTypeSel_run_settle env t st s acc d n hd hstk (by simpa [encode_zero] using hf) hlen hacc
      ⟨he.act, he.ret, he.gen⟩ hmin hops hone hmem
  · refine ⟨0x00, by decide, ?_⟩
    exact nftTypeSel_run_commit env t st s acc d n hd hstk (by simpa [vec_1] using hf) hlen hacc
      ⟨he.act, he.ret, he.gen⟩ hmin hops hone hmem

end BoltProof.Gadgets
