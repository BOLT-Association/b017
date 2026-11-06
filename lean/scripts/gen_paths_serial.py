#!/usr/bin/env python3
"""Generate the SerialBOLT path theorems (lean/BoltProof/Bridge/Glue/SerialBolt/Paths/*.lean), written to stdout:
`gen_paths_serial.py "<title suffix>" <path names>...`; `PROBE=1` replaces each closing by `trace_state; sorry`."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os
PROBE = os.environ.get("PROBE") == "1"
import sys
CH = 'c0 c11_if c12 c15_endif c16 c20_if c21 c22_else c23 c30_endif c31 c39_nftFlag c42 c51_if c52 c57_endif c58 c61_if c62 c183 c304 c447 c516_if c517 c528_endif c529 c538_notif c539 c557_endif c558 c563_notif c564 c566_else c567 c569_endif c570 c577_notif c578 c581_else c582 c586_endif c587 c589_nftTypeSel18 c602 c614_if c615 c621_else c622 c624_endif c625 c634_if c635 c641_endif c642 c662_notif c663 c665_else c666 c667_endif c668 c686_if c687 c806_notif c807 c815_endif c816 c822_if c823 c827_if c828_else c829 c834_if c835 c839_else c840 c846_if c847 c851_else c852 c856_endif c857_endif c858 c865_endif c866 c868_else c869 c872_endif c873 c1054 c1124_else c1125 c1232_nullTail c1236_endif c1237 c1263_else c1264 c1279_endif c1280'.split()
BLOCK = {'c62','c183','c304'}
ARMS = {'c16','c20_if','c21','c22_else','c23','c30_endif','c806_notif','c807','c815_endif','c816','c822_if','c823','c827_if','c828_else','c829','c834_if','c835','c839_else','c840','c846_if','c847','c851_else','c852','c856_endif','c857_endif','c858','c865_endif','c866','c868_else','c869','c872_endif'}
def chunks(exclude):
    return ', '.join('SerialBolt.'+c for c in CH if c not in exclude)
def after(off, exclude):
    i = CH.index(off)
    return ', '.join('SerialBolt.'+c for c in CH[i+1:] if c not in exclude)

def theorem(name, doc, hyps, args, null, closing, melt=False):
    hyp_txt = ' '.join('(%s : %s)' % hv for hv in hyps)
    concl = ('EnforcedMelt env f a ∧ Ends env a k t r C cs' if melt
             else 'Enforced env f a cs ∧ Reached env f a k t r cs ∧ Ends env a k t r C cs')
    out = []
    out.append('/-- %s -/' % doc)
    out.append('theorem %s {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}' % name)
    out.append('    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)')
    out.append('    %s' % hyp_txt)
    out.append('    (h : run Eval.opExec env (SerialBolt.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)')
    out.append('    (hr : r.IsOk) :')
    out.append('    %s := by' % concl)
    if melt:
        out.append('  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, %s,' % chunks(ARMS))
        out.append('    List.cons_append, List.nil_append, List.append_assoc] at h')
        out.append('  sym_all h %s' % args)
        out.append('  serial_norm h')
        out.append('  trace_state\n  sorry' if PROBE else closing)
        return '\n'.join(out) + '\n'
    excl = BLOCK | ARMS | {'c589_nftTypeSel18'} | ({'c1232_nullTail'} if null else set())
    out.append('  simp only [SerialBolt.suffix, Fields.stack, Args.stack, Pieces.stack, %s,' % chunks(excl))
    out.append('    List.cons_append, List.nil_append, List.append_assoc] at h')
    out.append('  sym_all h %s' % args)
    out.append('  rw [pushTxBlock_eq] at h')
    out.append('  have hpt : PushTxReached env a.pre cs := by')
    out.append('    obtain ⟨r\', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr')
    out.append('    exact ⟨_, _, _, _, _, _, r\', by simp [hact], hst, hok⟩')
    out.append('  replace h := pushTx_shape he (by simp [hact]) h hr')
    out.append('  obtain ⟨_, _, h⟩ := h')
    out.append('  sym_all h %s' % args)
    out.append('  have hsel : Reaches env 589 k t r cs (fun S => S.getD 24 [] = f.ty) := by')
    out.append('    refine ⟨?sS, ?sA, ?sm, ?sC, ?sk, ?srun, ?sact, ?sP⟩')
    out.append('    case srun =>')
    out.append('      rw [suffix_drop_589_append]')
    out.append('      simp only [%s, List.cons_append, List.nil_append]' % after('c589_nftTypeSel18', ARMS | ({'c1232_nullTail'} if null else set())))
    out.append('      exact h')
    out.append('    case sact => simp [hact]')
    out.append('    case sP => rw [hty]; rfl')
    out.append('  simp only [SerialBolt.c589_nftTypeSel18, List.cons_append] at h')
    out.append('  sym_all h %s' % args)
    if null:
        out.append('  have hnull : Reaches env 1232 k t r cs (fun S => S.head? = some a.ps.cat) := by')
        out.append('    refine ⟨?nS, ?nA, ?nm, ?nC, ?nk, ?nrun, ?nact, ?nP⟩')
        out.append('    case nrun =>')
        out.append('      rw [suffix_drop_1232_append]')
        out.append('      simp only [%s, List.cons_append, List.nil_append]' % after('c1232_nullTail', ARMS))
        out.append('      exact h')
        out.append('    case nact => simp [hact]')
        out.append('    case nP => rfl')
        out.append('  simp only [SerialBolt.c1232_nullTail, List.cons_append] at h')
        out.append('  sym_all h %s' % args)
    out.append('  serial_norm h')
    if not null:
        # the rebuild computes the grandparent's input-lock length word twice
        out.append('  num2bin_dedup')
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
MINT = ('hm', '((f.mint.length : Nat) : Int) ≤ 75')

ME_GEN = 'fun hp => absurd hpar hp'
ME_LATER = 'fun _ => (by fact)'
GN_GEN = 'fun _ => (by fact)'
GN_LATER = 'fun hp => absurd hp hpar'
def mg(gen): return (ME_GEN, GN_GEN) if gen else (ME_LATER, GN_LATER)

def close_commit(issuer, gen):
    me, gn = mg(gen)
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), (by fact), %s, %s, ?_, fun hs _ => absurd hs (commit_ne_settle hty),
      fun _ => ⟨(by fact), (by fact)⟩, %s, (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, commitOuts, hty, hpar, ↓reduceIte]
  fact''' % (me, gn, issuer)

def close_settle_null(issuer, gen):
    me, gn = mg(gen)
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), (by fact), %s, %s, ?_, fun _ hg => absurd hgp hg,
      fun _ => ⟨(by fact), (by fact)⟩, %s, (by fact), (by fact), (by fact), (by fact)⟩, ⟨hsel, fun _ => hnull⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, hty, hpar, ↓reduceIte]
  fact''' % (me, gn, issuer)

def close_settle_rebuild(issuer, gen):
    me, gn = mg(gen)
    return '''  refine ⟨⟨hpt, (by fact), (by fact), (by fact), (by fact), %s, %s, ?_,
      fun _ _ => ⟨_, _, _, _, _, _, _, (by fact), (by fact), (by fact), (by fact), (by fact), (by fact), (by fact),
        (by fact), (by fact)⟩,
      fun hn => absurd hn (not_null_cond hty hgp), %s, (by fact), (by fact), (by fact), (by fact)⟩,
    ⟨hsel, fun hn => absurd hn (not_null_cond hty hgp)⟩, _, _, _, _, h⟩
  simp (config := { decide := true }) only [expectedOuts, settleOuts, hty, hpar, ↓reduceIte]
  fact''' % (me, gn, issuer)

def close_melt(issuer, gen):
    me, gn = mg(gen)
    return '''  exact ⟨⟨(by fact), %s, %s, (by fact), (by fact), (by fact), (by fact)⟩, _, _, _, _, h⟩''' % (me, issuer)

ISS_YES = 'fun _ => (by fact)'
ISS_COMMIT_NO = 'fun hG => absurd hG (not_guard_commit hty hpar)'
ISS_SETTLE_NO = 'fun hG => absurd hG (not_guard_settle hpar hgp)'

PATHS = {
 'commit_genesis': dict(doc='A commit at genesis (`parent = 0`): the issuer guard holds, the pieces are empty.',
    hyps=[HTY0, GEN, PRE], args='hty hpar hpre', null=True, closing=close_commit(ISS_YES, True)),
 'commit_later': dict(doc='A commit after genesis: the issuer guard does not fire, the pieces are empty.',
    hyps=[HTY0, NGEN, PRE], args='hty hpar hpre', null=True, closing=close_commit(ISS_COMMIT_NO, False)),
 'settle_noGp_genesis': dict(doc='A settle at genesis of a token without a grandparent: the issuer guard holds, the pieces are empty.',
    hyps=[HTY21, GEN, GP0, PRE], args='hty hpar hgp hpre', null=True, closing=close_settle_null(ISS_YES, True)),
 'settle_noGp_later': dict(doc='A settle after genesis of a token without a grandparent: the issuer guard holds, the pieces are empty.',
    hyps=[HTY21, NGEN, GP0, PRE], args='hty hpar hgp hpre', null=True, closing=close_settle_null(ISS_YES, False)),
 'settle_genesis': dict(doc='A settle at genesis with a grandparent: the issuer guard holds, the grandparent is rebuilt.',
    hyps=[HTY21, GEN, NGP, PRE], args='hty hpar hgp hpre', null=False, closing=close_settle_rebuild(ISS_YES, True)),
 'settle_later': dict(doc='A settle after genesis with a grandparent: no guard, the grandparent is rebuilt.',
    hyps=[HTY21, NGEN, NGP, PRE], args='hty hpar hgp hpre', null=False, closing=close_settle_rebuild(ISS_SETTLE_NO, False)),
 'melt_commit_genesis': dict(doc='A melt of a type-`0x00` token at genesis: the issuer guard holds.',
    hyps=[HTY0, GEN, NPRE], args='hty hpar hpre', null=False, closing=close_melt(ISS_YES, True), melt=True),
 'melt_commit_later': dict(doc='A melt of a type-`0x00` token after genesis: no guard.',
    hyps=[HTY0, NGEN, NPRE], args='hty hpar hpre', null=False, closing=close_melt(ISS_COMMIT_NO, False), melt=True),
 'melt_settle_noGp_genesis': dict(doc='A melt at genesis of a type-`0x21` token without a grandparent: the issuer guard holds.',
    hyps=[HTY21, GEN, GP0, NPRE], args='hty hpar hgp hpre', null=False, closing=close_melt(ISS_YES, True), melt=True),
 'melt_settle_noGp_later': dict(doc='A melt after genesis of a type-`0x21` token without a grandparent: the issuer guard holds.',
    hyps=[HTY21, NGEN, GP0, NPRE], args='hty hpar hgp hpre', null=False, closing=close_melt(ISS_YES, False), melt=True),
 'melt_settle_genesis': dict(doc='A melt of a type-`0x21` token at genesis with a grandparent: the issuer guard holds.',
    hyps=[HTY21, GEN, NGP, NPRE], args='hty hpar hgp hpre', null=False, closing=close_melt(ISS_YES, True), melt=True),
 'melt_settle_later': dict(doc='A melt of a type-`0x21` token after genesis with a grandparent: no guard.',
    hyps=[HTY21, NGEN, NGP, NPRE], args='hty hpar hgp hpre', null=False, closing=close_melt(ISS_SETTLE_NO, False), melt=True),
}

HEADER = '''import BoltProof.Bridge.Glue.SerialBolt.PushTx

/-!
# The paths through the `SerialBOLT` suffix%s

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
%s
namespace BoltProof.Glue.SerialBolt

open BoltProof.Glue.MinSimple (reached_of_append)

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

'''
PPOPTS = 'set_option pp.deepTerms true\nset_option pp.maxSteps 10000000\nset_option pp.proofs false\n'
FOOTER = 'end BoltProof.Glue.SerialBolt\n'

def file(names, title):
    body = '\n'.join(theorem(n, **PATHS[n]) for n in names)
    return HEADER % (title, PPOPTS if PROBE else '') + body + '\n' + FOOTER

if __name__ == '__main__':
    which = sys.argv[1]
    names = sys.argv[2:]
    sys.stdout.write(file(names, which))
