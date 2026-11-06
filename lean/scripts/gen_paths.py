#!/usr/bin/env python3
"""Generate the MinSimpleBOLT path theorems (lean/BoltProof/Bridge/Glue/MinSimple/Paths*.lean)."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import sys
CH = ['c0','c6_nftFlag','c9','c18_if','c19','c24_endif','c25','c28_if','c29','c150','c271','c414','c483_notif','c484','c502_endif','c503','c508_notif','c509','c511_else','c512','c514_endif','c515','c522_notif','c523','c526_else','c527','c531_endif','c532','c534_nftTypeSel17','c547','c559_if','c560','c566_else','c567','c569_endif','c570','c589_notif','c590','c592_else','c593','c594_endif','c595','c613_if','c614','c774','c966','c968_else','c969','c1072_nullTail','c1076_endif','c1077','c1103_else','c1104','c1119_endif','c1120']
BLOCK = {'c29','c150','c271'}
def chunks(exclude):
    return ', '.join('MinSimple.'+c for c in CH if c not in exclude)
def after(off, exclude):
    i = CH.index(off)
    return ', '.join('MinSimple.'+c for c in CH[i+1:] if c not in exclude)

def theorem(name, doc, hyps, args, null, closing, melt=False):
    hyp_txt = ' '.join('(%s : %s)' % hv for hv in hyps)
    concl = ('EnforcedMelt env f a ∧ Ends env a k t r C cs' if melt
             else 'Enforced env f a cs ∧ Reached env f a k t r cs ∧ Ends env a k t r C cs')
    out = []
    out.append('/-- %s -/' % doc)
    out.append('theorem %s {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}' % name)
    out.append('    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)')
    out.append('    %s' % hyp_txt)
    out.append('    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)')
    out.append('    (hr : r.IsOk) :')
    out.append('    %s := by' % concl)
    if melt:
        out.append('  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, %s,' % chunks(set()))
        out.append('    List.cons_append, List.nil_append] at h')
        out.append('  sym_all h %s' % args)
        out.append('  enforced_norm h')
        out.append(closing)
        return '\n'.join(out) + '\n'
    excl = BLOCK | {'c534_nftTypeSel17'} | ({'c1072_nullTail'} if null else set())
    out.append('  simp only [MinSimple.suffix, Fields.stack, Args.stack, Pieces.stack, %s,' % chunks(excl))
    out.append('    List.cons_append, List.nil_append, List.append_assoc] at h')
    out.append('  sym_all h %s' % args)
    out.append('  rw [pushTxBlock_eq] at h')
    out.append('  have hpt : PushTxReached env a.pre cs := by')
    out.append('    obtain ⟨r\', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr')
    out.append('    exact ⟨_, _, _, _, _, _, r\', by simp [hact], hst, hok⟩')
    out.append('  replace h := pushTx_shape he (by simp [hact]) h hr')
    out.append('  obtain ⟨_, _, h⟩ := h')
    out.append('  sym_all h %s' % args)
    out.append('  have hsel : Reaches env 534 k t r cs (fun S => S.getD 23 [] = f.ty) := by')
    out.append('    refine ⟨?sS, ?sA, ?sm, ?sC, ?sk, ?srun, ?sact, ?sP⟩')
    out.append('    case srun =>')
    out.append('      rw [suffix_drop_534_append]')
    out.append('      simp only [%s, List.cons_append, List.nil_append]' % after('c534_nftTypeSel17', {'c1072_nullTail'} if null else set()))
    out.append('      exact h')
    out.append('    case sact => simp [hact]')
    out.append('    case sP => rw [hty]; rfl')
    out.append('  simp only [MinSimple.c534_nftTypeSel17, List.cons_append] at h')
    out.append('  sym_all h %s' % args)
    if null:
        out.append('  have hnull : Reaches env 1072 k t r cs (fun S => S.head? = some a.ps.cat) := by')
        out.append('    refine ⟨?nS, ?nA, ?nm, ?nC, ?nk, ?nrun, ?nact, ?nP⟩')
        out.append('    case nrun =>')
        out.append('      rw [suffix_drop_1072_append]')
        out.append('      simp only [%s, List.cons_append, List.nil_append]' % after('c1072_nullTail', set()))
        out.append('      exact h')
        out.append('    case nact => simp [hact]')
        out.append('    case nP => rfl')
        out.append('  simp only [MinSimple.c1072_nullTail, List.cons_append] at h')
        out.append('  sym_all h %s' % args)
    out.append('  enforced_norm h')
    out.append(closing)
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
      %s, (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, commitOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact''' % issuer

def close_settle_null(issuer):
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun _ hg => absurd hgp hg, fun _ => ⟨(by fact), (by fact)⟩,
      %s, (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact''' % issuer

def close_settle_rebuild(issuer):
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), ?_, fun _ _ => ⟨_, _, _, (by fact), (by fact), (by fact), (by fact), (by fact)⟩,
      fun hn => absurd hn (not_null_cond hty hgp), %s, (by fact), (by fact), (by fact), (by fact)⟩,
    ⟨hsel, fun hn => absurd hn (not_null_cond hty hgp)⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, issuerPush, hty, hpar, ↓reduceIte]
  fact''' % issuer

def close_melt(issuer):
    return '''  exact ⟨⟨%s, (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩''' % issuer

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

HEADER = '''import BoltProof.Bridge.Glue.MinSimple.PushTx

/-!
# The paths through the `MinSimpleBOLT` suffix%s

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

'''
FOOTER = 'end BoltProof.Glue.MinSimple\n'

def file(names, title):
    body = '\n'.join(theorem(n, **PATHS[n]) for n in names)
    return HEADER % title + body + '\n' + FOOTER

if __name__ == '__main__':
    which = sys.argv[1]
    names = sys.argv[2:]
    sys.stdout.write(file(names, which))
