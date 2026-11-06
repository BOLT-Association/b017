import BoltProof.Bridge.Glue.AuthBolt.PushTx

/-!
# The paths through the `AuthBOLT` suffix: the settle paths without a grandparent

One theorem per path the suffix can take, each a symbolic run of the whole suffix under the
hypotheses that decide its conditionals (`sym_all`), stopping at the `OP_PUSH_TX` block
(`AuthBolt/PushTx.lean`) and at the two proved fragments to record that they are reached, and
closing `Enforced`, `Reached` and `Ends` from the facts the run leaves. The eleven theorems are
assembled in `AuthBolt/Sound.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.AuthBolt

open BoltProof.Glue.MinSimple (reached_of_append)

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- A settle at genesis of a token without a grandparent: the issuer guard holds, the pieces are empty. -/
theorem settle_noGp_genesis {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : decode f.parent = 0) (hgp : decode f.gp = 0) (hpre : castToBool a.pre = true)
    (h : run Eval.opExec env (AuthBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    Enforced env f a cs ∧ Reached env f a k t r cs ∧ Ends env a k t r C cs := by
  simp only [AuthBolt.suffix, Fields.stack, Args.stack, Pieces.stack, AuthBolt.c0, AuthBolt.c6_nftFlag, AuthBolt.c9, AuthBolt.c18_if, AuthBolt.c19, AuthBolt.c24_endif, AuthBolt.c25, AuthBolt.c37_if, AuthBolt.c423, AuthBolt.c492_notif, AuthBolt.c493, AuthBolt.c511_endif, AuthBolt.c512, AuthBolt.c517_notif, AuthBolt.c518, AuthBolt.c520_else, AuthBolt.c521, AuthBolt.c523_endif, AuthBolt.c524, AuthBolt.c531_notif, AuthBolt.c532, AuthBolt.c535_else, AuthBolt.c536, AuthBolt.c540_endif, AuthBolt.c541, AuthBolt.c556, AuthBolt.c568_if, AuthBolt.c569, AuthBolt.c575_else, AuthBolt.c576, AuthBolt.c578_endif, AuthBolt.c579, AuthBolt.c598_notif, AuthBolt.c599, AuthBolt.c601_else, AuthBolt.c602, AuthBolt.c603_endif, AuthBolt.c604, AuthBolt.c622_if, AuthBolt.c623, AuthBolt.c782, AuthBolt.c970, AuthBolt.c986_else, AuthBolt.c987, AuthBolt.c1098_endif, AuthBolt.c1099, AuthBolt.c1125_else, AuthBolt.c1126, AuthBolt.c1141_endif, AuthBolt.c1142,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hgp hpre
  rw [pushTxBlock_eq] at h
  have hpt : PushTxReached env a.pre cs := by
    obtain ⟨r', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr
    exact ⟨_, _, _, _, _, _, r', by simp [hact], hst, hok⟩
  replace h := pushTx_shape he (by simp [hact]) h hr
  obtain ⟨_, _, h⟩ := h
  sym_all h hty hpar hgp hpre
  have hsel : Reaches env 543 k t r cs (fun S => S.getD 23 [] = f.ty) := by
    refine ⟨?sS, ?sA, ?sm, ?sC, ?sk, ?srun, ?sact, ?sP⟩
    case srun =>
      rw [suffix_drop_543_append]
      simp only [AuthBolt.c556, AuthBolt.c568_if, AuthBolt.c569, AuthBolt.c575_else, AuthBolt.c576, AuthBolt.c578_endif, AuthBolt.c579, AuthBolt.c598_notif, AuthBolt.c599, AuthBolt.c601_else, AuthBolt.c602, AuthBolt.c603_endif, AuthBolt.c604, AuthBolt.c622_if, AuthBolt.c623, AuthBolt.c782, AuthBolt.c970, AuthBolt.c986_else, AuthBolt.c987, AuthBolt.c1098_endif, AuthBolt.c1099, AuthBolt.c1125_else, AuthBolt.c1126, AuthBolt.c1141_endif, AuthBolt.c1142, List.cons_append, List.nil_append]
      exact h
    case sact => simp [hact]
    case sP => rw [hty]; rfl
  simp only [AuthBolt.c543_nftTypeSel17, List.cons_append] at h
  sym_all h hty hpar hgp hpre
  have hnull : Reaches env 1094 k t r cs (fun S => S.head? = some a.ps.cat) := by
    refine ⟨?nS, ?nA, ?nm, ?nC, ?nk, ?nrun, ?nact, ?nP⟩
    case nrun =>
      rw [suffix_drop_1094_append]
      simp only [AuthBolt.c1098_endif, AuthBolt.c1099, AuthBolt.c1125_else, AuthBolt.c1126, AuthBolt.c1141_endif, AuthBolt.c1142, List.cons_append, List.nil_append]
      exact h
    case nact => simp [hact]
    case nP => rfl
  simp only [AuthBolt.c1094_nullTail, List.cons_append] at h
  sym_all h hty hpar hgp hpre
  auth_norm h
  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun _ hg => absurd hgp hg, fun _ => ⟨(by fact), (by fact)⟩,
      fun _ => (by fact), (by fact), (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact

/-- A settle after genesis of a token without a grandparent: the issuer guard holds, the pieces are empty. -/
theorem settle_noGp_later {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : ¬ decode f.parent = 0) (hgp : decode f.gp = 0) (hpre : castToBool a.pre = true)
    (h : run Eval.opExec env (AuthBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    Enforced env f a cs ∧ Reached env f a k t r cs ∧ Ends env a k t r C cs := by
  simp only [AuthBolt.suffix, Fields.stack, Args.stack, Pieces.stack, AuthBolt.c0, AuthBolt.c6_nftFlag, AuthBolt.c9, AuthBolt.c18_if, AuthBolt.c19, AuthBolt.c24_endif, AuthBolt.c25, AuthBolt.c37_if, AuthBolt.c423, AuthBolt.c492_notif, AuthBolt.c493, AuthBolt.c511_endif, AuthBolt.c512, AuthBolt.c517_notif, AuthBolt.c518, AuthBolt.c520_else, AuthBolt.c521, AuthBolt.c523_endif, AuthBolt.c524, AuthBolt.c531_notif, AuthBolt.c532, AuthBolt.c535_else, AuthBolt.c536, AuthBolt.c540_endif, AuthBolt.c541, AuthBolt.c556, AuthBolt.c568_if, AuthBolt.c569, AuthBolt.c575_else, AuthBolt.c576, AuthBolt.c578_endif, AuthBolt.c579, AuthBolt.c598_notif, AuthBolt.c599, AuthBolt.c601_else, AuthBolt.c602, AuthBolt.c603_endif, AuthBolt.c604, AuthBolt.c622_if, AuthBolt.c623, AuthBolt.c782, AuthBolt.c970, AuthBolt.c986_else, AuthBolt.c987, AuthBolt.c1098_endif, AuthBolt.c1099, AuthBolt.c1125_else, AuthBolt.c1126, AuthBolt.c1141_endif, AuthBolt.c1142,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hgp hpre
  rw [pushTxBlock_eq] at h
  have hpt : PushTxReached env a.pre cs := by
    obtain ⟨r', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr
    exact ⟨_, _, _, _, _, _, r', by simp [hact], hst, hok⟩
  replace h := pushTx_shape he (by simp [hact]) h hr
  obtain ⟨_, _, h⟩ := h
  sym_all h hty hpar hgp hpre
  have hsel : Reaches env 543 k t r cs (fun S => S.getD 23 [] = f.ty) := by
    refine ⟨?sS, ?sA, ?sm, ?sC, ?sk, ?srun, ?sact, ?sP⟩
    case srun =>
      rw [suffix_drop_543_append]
      simp only [AuthBolt.c556, AuthBolt.c568_if, AuthBolt.c569, AuthBolt.c575_else, AuthBolt.c576, AuthBolt.c578_endif, AuthBolt.c579, AuthBolt.c598_notif, AuthBolt.c599, AuthBolt.c601_else, AuthBolt.c602, AuthBolt.c603_endif, AuthBolt.c604, AuthBolt.c622_if, AuthBolt.c623, AuthBolt.c782, AuthBolt.c970, AuthBolt.c986_else, AuthBolt.c987, AuthBolt.c1098_endif, AuthBolt.c1099, AuthBolt.c1125_else, AuthBolt.c1126, AuthBolt.c1141_endif, AuthBolt.c1142, List.cons_append, List.nil_append]
      exact h
    case sact => simp [hact]
    case sP => rw [hty]; rfl
  simp only [AuthBolt.c543_nftTypeSel17, List.cons_append] at h
  sym_all h hty hpar hgp hpre
  have hnull : Reaches env 1094 k t r cs (fun S => S.head? = some a.ps.cat) := by
    refine ⟨?nS, ?nA, ?nm, ?nC, ?nk, ?nrun, ?nact, ?nP⟩
    case nrun =>
      rw [suffix_drop_1094_append]
      simp only [AuthBolt.c1098_endif, AuthBolt.c1099, AuthBolt.c1125_else, AuthBolt.c1126, AuthBolt.c1141_endif, AuthBolt.c1142, List.cons_append, List.nil_append]
      exact h
    case nact => simp [hact]
    case nP => rfl
  simp only [AuthBolt.c1094_nullTail, List.cons_append] at h
  sym_all h hty hpar hgp hpre
  auth_norm h
  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun _ hg => absurd hgp hg, fun _ => ⟨(by fact), (by fact)⟩,
      fun _ => (by fact), (by fact), (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact

end BoltProof.Glue.AuthBolt
