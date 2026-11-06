#!/usr/bin/env python3
"""Generate the AuthBOLT path theorems (lean/BoltProof/Bridge/Glue/AuthBolt/Paths*.lean)."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os
PROBE = os.environ.get("PROBE") == "1"
import sys
CH = 'c0 c6_nftFlag c9 c18_if c19 c24_endif c25 c37_if c38 c159 c280 c423 c492_notif c493 c511_endif c512 c517_notif c518 c520_else c521 c523_endif c524 c531_notif c532 c535_else c536 c540_endif c541 c543_nftTypeSel17 c556 c568_if c569 c575_else c576 c578_endif c579 c598_notif c599 c601_else c602 c603_endif c604 c622_if c623 c782 c970 c986_else c987 c1094_nullTail c1098_endif c1099 c1125_else c1126 c1141_endif c1142'.split()
BLOCK = {'c38','c159','c280'}
def chunks(exclude):
    return ', '.join('AuthBolt.'+c for c in CH if c not in exclude)
def after(off, exclude):
    i = CH.index(off)
    return ', '.join('AuthBolt.'+c for c in CH[i+1:] if c not in exclude)

def theorem(name, doc, hyps, args, null, closing, melt=False):
    hyp_txt = ' '.join('(%s : %s)' % hv for hv in hyps)
    concl = ('EnforcedMelt env f a ∧ Ends env a k t r C cs' if melt
             else 'Enforced env f a cs ∧ Reached env f a k t r cs ∧ Ends env a k t r C cs')
    out = []
    out.append('/-- %s -/' % doc)
    out.append('theorem %s {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}' % name)
    out.append('    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)')
    out.append('    %s' % hyp_txt)
    out.append('    (h : run Eval.opExec env (AuthBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)')
    out.append('    (hr : r.IsOk) :')
    out.append('    %s := by' % concl)
    if melt:
        out.append('  simp only [AuthBolt.suffix, Fields.stack, Args.stack, Pieces.stack, %s,' % chunks(set()))
        out.append('    List.cons_append, List.nil_append] at h')
        out.append('  sym_all h %s' % args)
        out.append('  auth_norm h')
        out.append('  trace_state\n  sorry' if PROBE else closing)
        return '\n'.join(out) + '\n'
    excl = BLOCK | {'c543_nftTypeSel17'} | ({'c1094_nullTail'} if null else set())
    out.append('  simp only [AuthBolt.suffix, Fields.stack, Args.stack, Pieces.stack, %s,' % chunks(excl))
    out.append('    List.cons_append, List.nil_append, List.append_assoc] at h')
    out.append('  sym_all h %s' % args)
    out.append('  rw [pushTxBlock_eq] at h')
    out.append('  have hpt : PushTxReached env a.pre cs := by')
    out.append('    obtain ⟨r\', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr')
    out.append('    exact ⟨_, _, _, _, _, _, r\', by simp [hact], hst, hok⟩')
    out.append('  replace h := pushTx_shape he (by simp [hact]) h hr')
    out.append('  obtain ⟨_, _, h⟩ := h')
    out.append('  sym_all h %s' % args)
    out.append('  have hsel : Reaches env 543 k t r cs (fun S => S.getD 23 [] = f.ty) := by')
    out.append('    refine ⟨?sS, ?sA, ?sm, ?sC, ?sk, ?srun, ?sact, ?sP⟩')
    out.append('    case srun =>')
    out.append('      rw [suffix_drop_543_append]')
    out.append('      simp only [%s, List.cons_append, List.nil_append]' % after('c543_nftTypeSel17', {'c1094_nullTail'} if null else set()))
    out.append('      exact h')
    out.append('    case sact => simp [hact]')
    out.append('    case sP => rw [hty]; rfl')
    out.append('  simp only [AuthBolt.c543_nftTypeSel17, List.cons_append] at h')
    out.append('  sym_all h %s' % args)
    if null:
        out.append('  have hnull : Reaches env 1094 k t r cs (fun S => S.head? = some a.ps.cat) := by')
        out.append('    refine ⟨?nS, ?nA, ?nm, ?nC, ?nk, ?nrun, ?nact, ?nP⟩')
        out.append('    case nrun =>')
        out.append('      rw [suffix_drop_1094_append]')
        out.append('      simp only [%s, List.cons_append, List.nil_append]' % after('c1094_nullTail', set()))
        out.append('      exact h')
        out.append('    case nact => simp [hact]')
        out.append('    case nP => rfl')
        out.append('  simp only [AuthBolt.c1094_nullTail, List.cons_append] at h')
        out.append('  sym_all h %s' % args)
    out.append('  auth_norm h')
    out.append('  trace_state\n  sorry' if PROBE else closing)
    return '\n'.join(out) + '\n'

HTY0 = ('hty', 'f.ty = [0x00]')
HTY21 = ('hty', 'f.ty = [0x21]')
GEN = ('hpar', 'decode f.parent = 0')
NGEN = ('hpar', '¬ decode f.parent = 0')
GP0 = ('hgp', 'decode f.gp = 0')
NGP = ('hgp', '¬ decode f.gp = 0')
PRE = ('hpre', 'castToBool a.pre = true')
NPRE = ('hpre', 'castToBool a.pre = false')

def close_commit(issuer, parent_pos=None):
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun hs _ => absurd hs (commit_ne_settle hty), fun _ => ⟨(by fact), (by fact)⟩,
      %s, (by fact), (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, commitOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact''' % issuer

def close_settle_null(issuer):
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun _ hg => absurd hgp hg, fun _ => ⟨(by fact), (by fact)⟩,
      %s, (by fact), (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact''' % issuer

def close_settle_rebuild(issuer):
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun _ _ => ⟨_, _, _, _, (by fact), (by fact), (by fact), (by fact), (by fact), (by fact)⟩,
      fun hn => absurd hn (not_null_cond hty hgp), %s, (by fact), (by fact), (by fact), (by fact), (by fact)⟩,
    ⟨hsel, fun hn => absurd hn (not_null_cond hty hgp)⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact''' % issuer

def close_melt(issuer):
    return '''  exact ⟨⟨%s, (by fact), (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩''' % issuer

ISS_YES = 'fun _ => (by fact)'
ISS_COMMIT_NO = 'fun hG => absurd hG (not_guard_commit hty hpar)'
ISS_SETTLE_NO = 'fun hG => absurd hG (not_guard_settle hpar hgp)'

PATHS = {
 'commit_genesis': dict(doc='A commit at genesis (`parent = 0`): the issuer guard holds, the pieces are empty.',
    hyps=[HTY0, GEN, PRE], args='hty hpar hpre', null=True, closing=close_commit(ISS_YES, True)),
 'commit_later': dict(doc='A commit after genesis: the issuer guard does not fire, the pieces are empty.',
    hyps=[HTY0, NGEN, PRE], args='hty hpar hpre', null=True, closing=close_commit(ISS_COMMIT_NO, False)),
 'settle_noGp_genesis': dict(doc='A settle at genesis of a token without a grandparent: the issuer guard holds, the pieces are empty.',
    hyps=[HTY21, GEN, GP0, PRE], args='hty hpar hgp hpre', null=True, closing=close_settle_null(ISS_YES)),
 'settle_noGp_later': dict(doc='A settle after genesis of a token without a grandparent: the issuer guard holds, the pieces are empty.',
    hyps=[HTY21, NGEN, GP0, PRE], args='hty hpar hgp hpre', null=True, closing=close_settle_null(ISS_YES)),
 'settle_genesis': dict(doc='A settle at genesis with a grandparent: the issuer guard holds, the grandparent is rebuilt.',
    hyps=[HTY21, GEN, NGP, PRE], args='hty hpar hgp hpre', null=False, closing=close_settle_rebuild(ISS_YES)),
 'settle_later': dict(doc='A settle after genesis with a grandparent: no guard, the grandparent is rebuilt.',
    hyps=[HTY21, NGEN, NGP, PRE], args='hty hpar hgp hpre', null=False, closing=close_settle_rebuild(ISS_SETTLE_NO)),
 'melt_commit_genesis': dict(doc='A melt of a type-`0x00` token at genesis: the issuer guard holds.',
    hyps=[HTY0, GEN, NPRE], args='hty hpar hpre', null=False, closing=close_melt(ISS_YES), melt=True),
 'melt_commit_later': dict(doc='A melt of a type-`0x00` token after genesis: no guard.',
    hyps=[HTY0, NGEN, NPRE], args='hty hpar hpre', null=False, closing=close_melt(ISS_COMMIT_NO), melt=True),
 'melt_settle_noGp': dict(doc='A melt of a type-`0x21` token without a grandparent: the issuer guard holds.',
    hyps=[HTY21, GP0, NPRE], args='hty hgp hpre', null=False, closing=close_melt(ISS_YES), melt=True),
 'melt_settle_genesis': dict(doc='A melt of a type-`0x21` token at genesis with a grandparent: the issuer guard holds.',
    hyps=[HTY21, GEN, NGP, NPRE], args='hty hpar hgp hpre', null=False, closing=close_melt(ISS_YES), melt=True),
 'melt_settle_later': dict(doc='A melt of a type-`0x21` token after genesis with a grandparent: no guard.',
    hyps=[HTY21, NGEN, NGP, NPRE], args='hty hpar hgp hpre', null=False, closing=close_melt(ISS_SETTLE_NO), melt=True),
}

HEADER = '''import BoltProof.Bridge.Glue.AuthBolt.PushTx

/-!
# The paths through the `AuthBOLT` suffix%s

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

'''
FOOTER = 'end BoltProof.Glue.AuthBolt\n'

def file(names, title):
    body = '\n'.join(theorem(n, **PATHS[n]) for n in names)
    return HEADER % title + body + '\n' + FOOTER

if __name__ == '__main__':
    which = sys.argv[1]
    names = sys.argv[2:]
    sys.stdout.write(file(names, which))
