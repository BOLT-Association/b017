import BoltProof.Bridge.Glue.SerialBolt.PushTx

/-!
# The paths through the `SerialBOLT` suffix: the melts

One theorem per path the suffix can take, each a symbolic run of the whole suffix under the
hypotheses that decide its conditionals (`sym_all`), stopping at the `OP_PUSH_TX` block
(`SerialBolt/PushTx.lean`) and at the two proved fragments to record that they are reached, and
closing `Enforced`, `Reached` and `Ends` from the facts the run leaves. The twelve theorems are
assembled in `SerialBolt/Sound.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.SerialBolt

open BoltProof.Glue.MinSimple (reached_of_append)

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- A melt of a commit-typed token at genesis: the issuer guard holds. -/
theorem melt_commit_genesis {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00]) (hpar : decode f.parent = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, SerialBolt.c0, SerialBolt.c11_if, SerialBolt.c12, SerialBolt.c15_endif, SerialBolt.c31, SerialBolt.c39_nftFlag, SerialBolt.c42, SerialBolt.c51_if, SerialBolt.c52, SerialBolt.c57_endif, SerialBolt.c58, SerialBolt.c61_if, SerialBolt.c62, SerialBolt.c183, SerialBolt.c304, SerialBolt.c447, SerialBolt.c516_if, SerialBolt.c517, SerialBolt.c528_endif, SerialBolt.c529, SerialBolt.c538_notif, SerialBolt.c539, SerialBolt.c557_endif, SerialBolt.c558, SerialBolt.c563_notif, SerialBolt.c564, SerialBolt.c566_else, SerialBolt.c567, SerialBolt.c569_endif, SerialBolt.c570, SerialBolt.c577_notif, SerialBolt.c578, SerialBolt.c581_else, SerialBolt.c582, SerialBolt.c586_endif, SerialBolt.c587, SerialBolt.c589_nftTypeSel18, SerialBolt.c602, SerialBolt.c614_if, SerialBolt.c615, SerialBolt.c621_else, SerialBolt.c622, SerialBolt.c624_endif, SerialBolt.c625, SerialBolt.c634_if, SerialBolt.c635, SerialBolt.c641_endif, SerialBolt.c642, SerialBolt.c662_notif, SerialBolt.c663, SerialBolt.c665_else, SerialBolt.c666, SerialBolt.c667_endif, SerialBolt.c668, SerialBolt.c686_if, SerialBolt.c687, SerialBolt.c873, SerialBolt.c1054, SerialBolt.c1124_else, SerialBolt.c1125, SerialBolt.c1232_nullTail, SerialBolt.c1236_endif, SerialBolt.c1237, SerialBolt.c1263_else, SerialBolt.c1264, SerialBolt.c1279_endif, SerialBolt.c1280,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hpre
  serial_norm h
  exact ⟨⟨(by fact), fun hp => absurd hpar hp, fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a commit-typed token after genesis: no guard. -/
theorem melt_commit_later {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00]) (hpar : ¬ decode f.parent = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, SerialBolt.c0, SerialBolt.c11_if, SerialBolt.c12, SerialBolt.c15_endif, SerialBolt.c31, SerialBolt.c39_nftFlag, SerialBolt.c42, SerialBolt.c51_if, SerialBolt.c52, SerialBolt.c57_endif, SerialBolt.c58, SerialBolt.c61_if, SerialBolt.c62, SerialBolt.c183, SerialBolt.c304, SerialBolt.c447, SerialBolt.c516_if, SerialBolt.c517, SerialBolt.c528_endif, SerialBolt.c529, SerialBolt.c538_notif, SerialBolt.c539, SerialBolt.c557_endif, SerialBolt.c558, SerialBolt.c563_notif, SerialBolt.c564, SerialBolt.c566_else, SerialBolt.c567, SerialBolt.c569_endif, SerialBolt.c570, SerialBolt.c577_notif, SerialBolt.c578, SerialBolt.c581_else, SerialBolt.c582, SerialBolt.c586_endif, SerialBolt.c587, SerialBolt.c589_nftTypeSel18, SerialBolt.c602, SerialBolt.c614_if, SerialBolt.c615, SerialBolt.c621_else, SerialBolt.c622, SerialBolt.c624_endif, SerialBolt.c625, SerialBolt.c634_if, SerialBolt.c635, SerialBolt.c641_endif, SerialBolt.c642, SerialBolt.c662_notif, SerialBolt.c663, SerialBolt.c665_else, SerialBolt.c666, SerialBolt.c667_endif, SerialBolt.c668, SerialBolt.c686_if, SerialBolt.c687, SerialBolt.c873, SerialBolt.c1054, SerialBolt.c1124_else, SerialBolt.c1125, SerialBolt.c1232_nullTail, SerialBolt.c1236_endif, SerialBolt.c1237, SerialBolt.c1263_else, SerialBolt.c1264, SerialBolt.c1279_endif, SerialBolt.c1280,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hpre
  serial_norm h
  exact ⟨⟨(by fact), fun _ => (by fact), fun hG => absurd hG (not_guard_commit hty hpar), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt at genesis of a settle-typed token without a grandparent: the issuer guard holds. -/
theorem melt_settle_noGp_genesis {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : decode f.parent = 0) (hgp : decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, SerialBolt.c0, SerialBolt.c11_if, SerialBolt.c12, SerialBolt.c15_endif, SerialBolt.c31, SerialBolt.c39_nftFlag, SerialBolt.c42, SerialBolt.c51_if, SerialBolt.c52, SerialBolt.c57_endif, SerialBolt.c58, SerialBolt.c61_if, SerialBolt.c62, SerialBolt.c183, SerialBolt.c304, SerialBolt.c447, SerialBolt.c516_if, SerialBolt.c517, SerialBolt.c528_endif, SerialBolt.c529, SerialBolt.c538_notif, SerialBolt.c539, SerialBolt.c557_endif, SerialBolt.c558, SerialBolt.c563_notif, SerialBolt.c564, SerialBolt.c566_else, SerialBolt.c567, SerialBolt.c569_endif, SerialBolt.c570, SerialBolt.c577_notif, SerialBolt.c578, SerialBolt.c581_else, SerialBolt.c582, SerialBolt.c586_endif, SerialBolt.c587, SerialBolt.c589_nftTypeSel18, SerialBolt.c602, SerialBolt.c614_if, SerialBolt.c615, SerialBolt.c621_else, SerialBolt.c622, SerialBolt.c624_endif, SerialBolt.c625, SerialBolt.c634_if, SerialBolt.c635, SerialBolt.c641_endif, SerialBolt.c642, SerialBolt.c662_notif, SerialBolt.c663, SerialBolt.c665_else, SerialBolt.c666, SerialBolt.c667_endif, SerialBolt.c668, SerialBolt.c686_if, SerialBolt.c687, SerialBolt.c873, SerialBolt.c1054, SerialBolt.c1124_else, SerialBolt.c1125, SerialBolt.c1232_nullTail, SerialBolt.c1236_endif, SerialBolt.c1237, SerialBolt.c1263_else, SerialBolt.c1264, SerialBolt.c1279_endif, SerialBolt.c1280,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hgp hpre
  serial_norm h
  exact ⟨⟨(by fact), fun hp => absurd hpar hp, fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt after genesis of a settle-typed token without a grandparent: the issuer guard holds. -/
theorem melt_settle_noGp_later {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : ¬ decode f.parent = 0) (hgp : decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, SerialBolt.c0, SerialBolt.c11_if, SerialBolt.c12, SerialBolt.c15_endif, SerialBolt.c31, SerialBolt.c39_nftFlag, SerialBolt.c42, SerialBolt.c51_if, SerialBolt.c52, SerialBolt.c57_endif, SerialBolt.c58, SerialBolt.c61_if, SerialBolt.c62, SerialBolt.c183, SerialBolt.c304, SerialBolt.c447, SerialBolt.c516_if, SerialBolt.c517, SerialBolt.c528_endif, SerialBolt.c529, SerialBolt.c538_notif, SerialBolt.c539, SerialBolt.c557_endif, SerialBolt.c558, SerialBolt.c563_notif, SerialBolt.c564, SerialBolt.c566_else, SerialBolt.c567, SerialBolt.c569_endif, SerialBolt.c570, SerialBolt.c577_notif, SerialBolt.c578, SerialBolt.c581_else, SerialBolt.c582, SerialBolt.c586_endif, SerialBolt.c587, SerialBolt.c589_nftTypeSel18, SerialBolt.c602, SerialBolt.c614_if, SerialBolt.c615, SerialBolt.c621_else, SerialBolt.c622, SerialBolt.c624_endif, SerialBolt.c625, SerialBolt.c634_if, SerialBolt.c635, SerialBolt.c641_endif, SerialBolt.c642, SerialBolt.c662_notif, SerialBolt.c663, SerialBolt.c665_else, SerialBolt.c666, SerialBolt.c667_endif, SerialBolt.c668, SerialBolt.c686_if, SerialBolt.c687, SerialBolt.c873, SerialBolt.c1054, SerialBolt.c1124_else, SerialBolt.c1125, SerialBolt.c1232_nullTail, SerialBolt.c1236_endif, SerialBolt.c1237, SerialBolt.c1263_else, SerialBolt.c1264, SerialBolt.c1279_endif, SerialBolt.c1280,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hgp hpre
  serial_norm h
  exact ⟨⟨(by fact), fun _ => (by fact), fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a settle-typed token at genesis with a grandparent: the issuer guard holds. -/
theorem melt_settle_genesis {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : decode f.parent = 0) (hgp : ¬ decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, SerialBolt.c0, SerialBolt.c11_if, SerialBolt.c12, SerialBolt.c15_endif, SerialBolt.c31, SerialBolt.c39_nftFlag, SerialBolt.c42, SerialBolt.c51_if, SerialBolt.c52, SerialBolt.c57_endif, SerialBolt.c58, SerialBolt.c61_if, SerialBolt.c62, SerialBolt.c183, SerialBolt.c304, SerialBolt.c447, SerialBolt.c516_if, SerialBolt.c517, SerialBolt.c528_endif, SerialBolt.c529, SerialBolt.c538_notif, SerialBolt.c539, SerialBolt.c557_endif, SerialBolt.c558, SerialBolt.c563_notif, SerialBolt.c564, SerialBolt.c566_else, SerialBolt.c567, SerialBolt.c569_endif, SerialBolt.c570, SerialBolt.c577_notif, SerialBolt.c578, SerialBolt.c581_else, SerialBolt.c582, SerialBolt.c586_endif, SerialBolt.c587, SerialBolt.c589_nftTypeSel18, SerialBolt.c602, SerialBolt.c614_if, SerialBolt.c615, SerialBolt.c621_else, SerialBolt.c622, SerialBolt.c624_endif, SerialBolt.c625, SerialBolt.c634_if, SerialBolt.c635, SerialBolt.c641_endif, SerialBolt.c642, SerialBolt.c662_notif, SerialBolt.c663, SerialBolt.c665_else, SerialBolt.c666, SerialBolt.c667_endif, SerialBolt.c668, SerialBolt.c686_if, SerialBolt.c687, SerialBolt.c873, SerialBolt.c1054, SerialBolt.c1124_else, SerialBolt.c1125, SerialBolt.c1232_nullTail, SerialBolt.c1236_endif, SerialBolt.c1237, SerialBolt.c1263_else, SerialBolt.c1264, SerialBolt.c1279_endif, SerialBolt.c1280,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hgp hpre
  serial_norm h
  exact ⟨⟨(by fact), fun hp => absurd hpar hp, fun _ => (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

/-- A melt of a settle-typed token after genesis with a grandparent: no guard. -/
theorem melt_settle_later {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x21]) (hpar : ¬ decode f.parent = 0) (hgp : ¬ decode f.gp = 0) (hpre : castToBool a.pre = false)
    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    EnforcedMelt env f a ∧ Ends env a k t r C cs := by
  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, SerialBolt.c0, SerialBolt.c11_if, SerialBolt.c12, SerialBolt.c15_endif, SerialBolt.c31, SerialBolt.c39_nftFlag, SerialBolt.c42, SerialBolt.c51_if, SerialBolt.c52, SerialBolt.c57_endif, SerialBolt.c58, SerialBolt.c61_if, SerialBolt.c62, SerialBolt.c183, SerialBolt.c304, SerialBolt.c447, SerialBolt.c516_if, SerialBolt.c517, SerialBolt.c528_endif, SerialBolt.c529, SerialBolt.c538_notif, SerialBolt.c539, SerialBolt.c557_endif, SerialBolt.c558, SerialBolt.c563_notif, SerialBolt.c564, SerialBolt.c566_else, SerialBolt.c567, SerialBolt.c569_endif, SerialBolt.c570, SerialBolt.c577_notif, SerialBolt.c578, SerialBolt.c581_else, SerialBolt.c582, SerialBolt.c586_endif, SerialBolt.c587, SerialBolt.c589_nftTypeSel18, SerialBolt.c602, SerialBolt.c614_if, SerialBolt.c615, SerialBolt.c621_else, SerialBolt.c622, SerialBolt.c624_endif, SerialBolt.c625, SerialBolt.c634_if, SerialBolt.c635, SerialBolt.c641_endif, SerialBolt.c642, SerialBolt.c662_notif, SerialBolt.c663, SerialBolt.c665_else, SerialBolt.c666, SerialBolt.c667_endif, SerialBolt.c668, SerialBolt.c686_if, SerialBolt.c687, SerialBolt.c873, SerialBolt.c1054, SerialBolt.c1124_else, SerialBolt.c1125, SerialBolt.c1232_nullTail, SerialBolt.c1236_endif, SerialBolt.c1237, SerialBolt.c1263_else, SerialBolt.c1264, SerialBolt.c1279_endif, SerialBolt.c1280,
    List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h hty hpar hgp hpre
  serial_norm h
  exact ⟨⟨(by fact), fun _ => (by fact), fun hG => absurd hG (not_guard_settle hpar hgp), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩

end BoltProof.Glue.SerialBolt
