import BoltProof.Bridge.Glue.MinSimple.PushTx

/-!
# The paths through the `MinSimpleBOLT` suffix: the melt paths

One theorem per path the suffix can take, each a symbolic run of the whole suffix under the
hypotheses that decide its conditionals (`sym_all`), stopping at the `OP_PUSH_TX` block
(`MinSimple/PushTx.lean`) and at the two proved fragments to record that they are reached, and
closing `Enforced`, `Reached` and `Ends` from the facts the run leaves. The eleven theorems are
assembled in `MinSimple/Sound.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.MinSimple

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- A melt of a type-`0x00` token at genesis: the issuer guard holds. -/
theorem melt_commit_genesis {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00]) (hpar : decode f.parent = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, MinSimple.c0, MinSimple.c6_nftFlag, MinSimple.c9, MinSimple.c18_if, MinSimple.c19, MinSimple.c24_endif, MinSimple.c25, MinSimple.c28_if, MinSimple.c29, MinSimple.c150, MinSimple.c271, MinSimple.c414, MinSimple.c483_notif, MinSimple.c484, MinSimple.c502_endif, MinSimple.c503, MinSimple.c508_notif, MinSimple.c509, MinSimple.c511_else, MinSimple.c512, MinSimple.c514_endif, MinSimple.c515, MinSimple.c522_notif, MinSimple.c523, MinSimple.c526_else, MinSimple.c527, MinSimple.c531_endif, MinSimple.c532, MinSimple.c534_nftTypeSel17, MinSimple.c547, MinSimple.c559_if, MinSimple.c560, MinSimple.c566_else, MinSimple.c567, MinSimple.c569_endif, MinSimple.c570, MinSimple.c589_notif, MinSimple.c590, MinSimple.c592_else, MinSimple.c593, MinSimple.c594_endif, MinSimple.c595, MinSimple.c613_if, MinSimple.c614, MinSimple.c774, MinSimple.c966, MinSimple.c968_else, MinSimple.c969, MinSimple.c1072_nullTail, MinSimple.c1076_endif, MinSimple.c1077, MinSimple.c1103_else, MinSimple.c1104, MinSimple.c1119_endif, MinSimple.c1120,
    List.cons_append, List.nil_append] at h
  sym_all h hty hpar hpre
  enforced_norm h
  exact ⟨⟨fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a type-`0x00` token after genesis: no guard. -/
theorem melt_commit_later {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00]) (hpar : ¬ decode f.parent = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, MinSimple.c0, MinSimple.c6_nftFlag, MinSimple.c9, MinSimple.c18_if, MinSimple.c19, MinSimple.c24_endif, MinSimple.c25, MinSimple.c28_if, MinSimple.c29, MinSimple.c150, MinSimple.c271, MinSimple.c414, MinSimple.c483_notif, MinSimple.c484, MinSimple.c502_endif, MinSimple.c503, MinSimple.c508_notif, MinSimple.c509, MinSimple.c511_else, MinSimple.c512, MinSimple.c514_endif, MinSimple.c515, MinSimple.c522_notif, MinSimple.c523, MinSimple.c526_else, MinSimple.c527, MinSimple.c531_endif, MinSimple.c532, MinSimple.c534_nftTypeSel17, MinSimple.c547, MinSimple.c559_if, MinSimple.c560, MinSimple.c566_else, MinSimple.c567, MinSimple.c569_endif, MinSimple.c570, MinSimple.c589_notif, MinSimple.c590, MinSimple.c592_else, MinSimple.c593, MinSimple.c594_endif, MinSimple.c595, MinSimple.c613_if, MinSimple.c614, MinSimple.c774, MinSimple.c966, MinSimple.c968_else, MinSimple.c969, MinSimple.c1072_nullTail, MinSimple.c1076_endif, MinSimple.c1077, MinSimple.c1103_else, MinSimple.c1104, MinSimple.c1119_endif, MinSimple.c1120,
    List.cons_append, List.nil_append] at h
  sym_all h hty hpar hpre
  enforced_norm h
  exact ⟨⟨fun hG => absurd hG (not_guard_commit hty hpar), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a type-`0x21` token without a grandparent: the issuer guard holds. -/
theorem melt_settle_noGp {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hgp : decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, MinSimple.c0, MinSimple.c6_nftFlag, MinSimple.c9, MinSimple.c18_if, MinSimple.c19, MinSimple.c24_endif, MinSimple.c25, MinSimple.c28_if, MinSimple.c29, MinSimple.c150, MinSimple.c271, MinSimple.c414, MinSimple.c483_notif, MinSimple.c484, MinSimple.c502_endif, MinSimple.c503, MinSimple.c508_notif, MinSimple.c509, MinSimple.c511_else, MinSimple.c512, MinSimple.c514_endif, MinSimple.c515, MinSimple.c522_notif, MinSimple.c523, MinSimple.c526_else, MinSimple.c527, MinSimple.c531_endif, MinSimple.c532, MinSimple.c534_nftTypeSel17, MinSimple.c547, MinSimple.c559_if, MinSimple.c560, MinSimple.c566_else, MinSimple.c567, MinSimple.c569_endif, MinSimple.c570, MinSimple.c589_notif, MinSimple.c590, MinSimple.c592_else, MinSimple.c593, MinSimple.c594_endif, MinSimple.c595, MinSimple.c613_if, MinSimple.c614, MinSimple.c774, MinSimple.c966, MinSimple.c968_else, MinSimple.c969, MinSimple.c1072_nullTail, MinSimple.c1076_endif, MinSimple.c1077, MinSimple.c1103_else, MinSimple.c1104, MinSimple.c1119_endif, MinSimple.c1120,
    List.cons_append, List.nil_append] at h
  sym_all h hty hgp hpre
  enforced_norm h
  exact ⟨⟨fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a type-`0x21` token at genesis with a grandparent: the issuer guard holds. -/
theorem melt_settle_genesis {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : decode f.parent = 0) (hgp : ¬ decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, MinSimple.c0, MinSimple.c6_nftFlag, MinSimple.c9, MinSimple.c18_if, MinSimple.c19, MinSimple.c24_endif, MinSimple.c25, MinSimple.c28_if, MinSimple.c29, MinSimple.c150, MinSimple.c271, MinSimple.c414, MinSimple.c483_notif, MinSimple.c484, MinSimple.c502_endif, MinSimple.c503, MinSimple.c508_notif, MinSimple.c509, MinSimple.c511_else, MinSimple.c512, MinSimple.c514_endif, MinSimple.c515, MinSimple.c522_notif, MinSimple.c523, MinSimple.c526_else, MinSimple.c527, MinSimple.c531_endif, MinSimple.c532, MinSimple.c534_nftTypeSel17, MinSimple.c547, MinSimple.c559_if, MinSimple.c560, MinSimple.c566_else, MinSimple.c567, MinSimple.c569_endif, MinSimple.c570, MinSimple.c589_notif, MinSimple.c590, MinSimple.c592_else, MinSimple.c593, MinSimple.c594_endif, MinSimple.c595, MinSimple.c613_if, MinSimple.c614, MinSimple.c774, MinSimple.c966, MinSimple.c968_else, MinSimple.c969, MinSimple.c1072_nullTail, MinSimple.c1076_endif, MinSimple.c1077, MinSimple.c1103_else, MinSimple.c1104, MinSimple.c1119_endif, MinSimple.c1120,
    List.cons_append, List.nil_append] at h
  sym_all h hty hpar hgp hpre
  enforced_norm h
  exact ⟨⟨fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a type-`0x21` token after genesis with a grandparent: no guard. -/
theorem melt_settle_later {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : ¬ decode f.parent = 0) (hgp : ¬ decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, MinSimple.c0, MinSimple.c6_nftFlag, MinSimple.c9, MinSimple.c18_if, MinSimple.c19, MinSimple.c24_endif, MinSimple.c25, MinSimple.c28_if, MinSimple.c29, MinSimple.c150, MinSimple.c271, MinSimple.c414, MinSimple.c483_notif, MinSimple.c484, MinSimple.c502_endif, MinSimple.c503, MinSimple.c508_notif, MinSimple.c509, MinSimple.c511_else, MinSimple.c512, MinSimple.c514_endif, MinSimple.c515, MinSimple.c522_notif, MinSimple.c523, MinSimple.c526_else, MinSimple.c527, MinSimple.c531_endif, MinSimple.c532, MinSimple.c534_nftTypeSel17, MinSimple.c547, MinSimple.c559_if, MinSimple.c560, MinSimple.c566_else, MinSimple.c567, MinSimple.c569_endif, MinSimple.c570, MinSimple.c589_notif, MinSimple.c590, MinSimple.c592_else, MinSimple.c593, MinSimple.c594_endif, MinSimple.c595, MinSimple.c613_if, MinSimple.c614, MinSimple.c774, MinSimple.c966, MinSimple.c968_else, MinSimple.c969, MinSimple.c1072_nullTail, MinSimple.c1076_endif, MinSimple.c1077, MinSimple.c1103_else, MinSimple.c1104, MinSimple.c1119_endif, MinSimple.c1120,
    List.cons_append, List.nil_append] at h
  sym_all h hty hpar hgp hpre
  enforced_norm h
  exact ⟨⟨fun hG => absurd hG (not_guard_settle hpar hgp), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

end BoltProof.Glue.MinSimple
