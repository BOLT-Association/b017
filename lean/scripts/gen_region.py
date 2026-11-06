#!/usr/bin/env python3
"""Generate lean/BoltProof/Bridge/Glue/SimpleMulti/Regions.lean: the fungible suffix's three rebuild-phase regions read as
one step each, from their isolated probes (probe_arm.py): the first rebuild (suffix 1426–2714, key `c1426`), the second
rebuild's arm (2715–3896, key `c2715_if`, two cases on the spent lock's output index) and the null arm (3899–4651, key
`c3899`). Entry stack `t0 :: T` (the arm's `t1 :: t0 :: T`), alt stack `A`."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chunks as C, facts as F
SP = WORK
def ats(s):
    """`T[n]?.getD []` as `(at T n)`, and the same for `(t0 :: T)[n]?.getD []`."""
    s = re.sub(r'T\[(\d+)\]\?\.getD \[\]', r'(item T \1)', s)
    return s
def split_state(hb, tail):
    """(items above `tail` in the main stack as `x :: y ::` text, the alt stack text) of the final state in `hb`"""
    hb = ' '.join(hb.split())
    i = hb.index('(St ')
    # the main stack is the first balanced group after `(St `
    k = i + 4; d = 0; start = k
    while True:
        if hb[k] == '(': d += 1
        elif hb[k] == ')':
            d -= 1
            if d == 0: break
        k += 1
    main = hb[start+1:k].strip()
    assert main.endswith(':: ' + tail) or main == tail, main[-40:]
    above = main[:-len(tail)].rstrip() if main != tail else ''
    rest = hb[k+1:].strip()
    if rest.startswith('('):
        d = 0
        for k2, ch in enumerate(rest):
            if ch == '(': d += 1
            elif ch == ')':
                d -= 1
                if d == 0: alt = rest[:k2+1]; break
    else:
        alt = rest.split()[0]
    return ats(F.rename(above)), ats(F.rename(alt))
def region(name, key, a, b, entry, probes, doc):
    """probes: list of (caseHyps [(hname, prop)], probe file). One case: a plain block; two: an `if` on the first hyp."""
    seq = C.seq(C.names(a, b)); unfold = C.unfold(a, b, keep=[(1961, 2426), (2591, 2609), (3186, 3623), (3773, 3790)])
    out = []
    cases = []
    for hyps, path in probes:
        fs, ws, hb = F.read(path)
        fs = [(n, ats(t)) for n, t in fs]
        st, alt = split_state(hb, 'T')
        cases.append((hyps, fs, ws, st, alt))
    # the widths of all cases, distinct names per case
    allws = []
    for ci, (hyps, fs, ws, st, alt) in enumerate(cases):
        allws += [f'{w}' for w in ws]
    assert len(set(allws)) == len(allws), 'width names clash across cases'
    out.append(f'/-! ### `{name}`\n\n{doc} -/\n')
    for ci, (hyps, fs, ws, st, alt) in enumerate(cases):
        cname = f'{name}' + (f'_{ci}' if len(cases) > 1 else '')
        binders = '(t0 : Bytes) (T : List Bytes)' + (f' ({" ".join(ws)} : Bytes)' if ws else '')
        out.append(f'/-- The stack above `T` after the region' + (f' (case {ci})' if len(cases) > 1 else '') + '. -/')
        out.append(f'def {cname}_stack {binders} : List Bytes :=\n  {st} T\n')
        for fi, (_, ft) in enumerate(fs):
            out.append(f'/-- Fact {fi} of the region. -/')
            out.append(f'abbrev {cname}_fact{fi} {binders} : Prop :=\n  {ft}\n')
    # statement
    hypbinders = ''
    results = []
    for ci, (hyps, fs, ws, st, alt) in enumerate(cases):
        cname = f'{name}' + (f'_{ci}' if len(cases) > 1 else '')
        cond = ' → '.join(f'{p}' for _, p in hyps)
        wargs = ' '.join(ws)
        factconj = ' ∧ '.join(f'{cname}_fact{fi} t0 T {wargs}'.rstrip() for fi in range(len(fs))) if fs else 'True'
        results.append((cond, factconj, f'{cname}_stack t0 T {wargs}'.rstrip(), alt))
    out.append(f'theorem {name}_shape {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{t0 : Bytes}} {{T A : List Bytes}}')
    out.append(f'    {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)')
    out.append(f'    (h : run Eval.opExec env ({seq}) t (St (t0 :: T) A m C kk cs) = r) (hr : r.IsOk) :')
    if len(cases) == 1:
        cond, factconj, st, alt = results[0]
        exists = ' '.join(cases[0][2])
        out.append(f'    ∃ ({exists} : Bytes) (m\' k\' : Nat),' if exists else '    ∃ (m\' k\' : Nat),')
        out.append(f'      ({factconj}) ∧')
        out.append(f'      run Eval.opExec env k t (St ({st}) ({alt}) m\' C k\' cs) = r := by')
        out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
        out.append(f'  sym_all h')
        holes = ', '.join('_' for _ in cases[0][2])
        nf = len(cases[0][1])
        assums = ('⟨' + ', '.join('(by with_reducible assumption)' for _ in range(nf)) + '⟩') if nf > 1 else ('(by with_reducible assumption)' if nf == 1 else 'trivial')
        out.append(f'  refine ⟨{holes + ", " if holes else ""}?mm, ?kk, {assums}, ?run⟩')
        out.append(f'  case run =>')
        out.append(f'    simp only [{name}_stack]')
        out.append(f'    with_reducible exact h\n')
    else:
        # two cases on one hypothesis h0 : P0 (case 0) and its negation (case 1)
        exists = ' '.join(w for c in cases for w in c[2])
        (c0, f0, s0, a0), (c1, f1, s1, a1) = results
        p0 = ats(cases[0][0][0][1])
        out.append(f'    ∃ ({exists} : Bytes) (m\' k\' : Nat),')
        out.append(f'      (({p0}) → {f0}) ∧')
        out.append(f'      (¬ ({p0}) → {f1}) ∧')
        out.append(f'      run Eval.opExec env k t (St (if {p0} then {s0} else {s1}) ({a0}) m\' C k\' cs) = r := by')
        out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
        out.append(f'  by_cases h0 : {p0}')
        for ci, (hyps, fs, ws, st, alt) in enumerate(cases):
            holes = []
            for cj, c in enumerate(cases):
                holes += (['_'] * len(c[2])) if cj == ci else (['[]'] * len(c[2]))
            assums = ', '.join('(by with_reducible assumption)' for _ in fs) or 'trivial'
            other = 'fun h1 => absurd h0 h1' if ci == 0 else 'fun h1 => absurd h1 h0'
            own = f'fun _ => ⟨{assums}⟩'
            parts = [own, other] if ci == 0 else [other, own]
            out.append(f'  · sym_all h h0')
            out.append(f'    refine ⟨{", ".join(holes)}, ?mm, ?kk, {parts[0]}, {parts[1]}, ?run⟩')
            out.append(f'    case run =>')
            out.append(f'      simp only [{name}_{ci}_stack, h0, ↓reduceIte, not_false_eq_true, not_true_eq_false]')
            out.append(f'      with_reducible exact h')
        out.append('')
    # skip lemma
    out.append(f'/-- The region inside an inactive arm: stepped over. -/')
    out.append(f'theorem {name}_skip {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{S A : List Bytes}} {{D : Cond}} {{cs : Bytes}}')
    out.append(f'    {{m kk : Nat}} (hin : D.isActive = false)')
    out.append(f'    (h : run Eval.opExec env ({seq}) t (St S A m D kk cs) = r) (hr : r.IsOk) :')
    out.append(f'    ∃ k\', run Eval.opExec env k t (St S A m D k\' cs) = r := by')
    out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
    out.append(f'  sym_skip h hin')
    out.append(f'  exact ⟨_, h⟩\n')
    # rules
    nws = sum(len(c[2]) for c in cases)
    pat = ', '.join(['_'] * nws + ['_', '_'] + (['_'] if len(cases) == 1 else ['_', '_']))
    out.append(f'macro_rules\n  | `(tactic| sym_blockrule "{key}" $h:ident $hact:ident) =>')
    out.append(f'    `(tactic| (obtain ⟨{pat}, $h:ident⟩ := {name}_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))')
    out.append(f'macro_rules\n  | `(tactic| sym_skipblockrule "{key}" $h:ident $hin:ident) =>')
    out.append(f'    `(tactic| (obtain ⟨_, $h:ident⟩ := {name}_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf,')
    out.append(f'      Bool.and_false, Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)))\n')
    return '\n'.join(out)
def arm3(name, key, a, b, p0, probef, probe0, probe1, doc):
    """an arm `flag :: t1 :: t0 :: T` with the alt stack `a1 :: a2 :: A`: three cases, the flag off, and on with `p0` or its negation"""
    seq = C.seq(C.names(a, b)); unfold = C.unfold(a, b, keep=[(1961, 2426), (2591, 2609), (3186, 3623), (3773, 3790)])
    cases = []
    for ci, path in enumerate((probef, probe0, probe1)):
        fs, ws, hb = F.read(path)
        fs = [(n, ats(t)) for n, t in fs]
        st, alt = split_state(hb, 'T')
        # the cases' widths get distinct names (each probe names its own `w10`, …)
        suf = lambda x: re.sub(r'\bw(\d+)\b', lambda m: f'w{m.group(1)}c{ci}', x)
        fs = [(n, suf(t)) for n, t in fs]; ws = [suf(w) for w in ws]; st = suf(st); alt = suf(alt)
        cases.append((fs, ws, st, alt))
    out = [f'/-! ### `{name}`\n\n{doc} -/\n']
    for ci, (fs, ws, st, alt) in enumerate(cases):
        binders = '(t1 t0 a1 a2 : Bytes) (T : List Bytes)' + (f' ({" ".join(ws)} : Bytes)' if ws else '')
        out.append(f'/-- The stack above `T` after the arm (case {ci}: ' + ['the flag off', 'the flag on and the index 0', 'the flag on and the index non-zero'][ci] + '). -/')
        out.append(f'def {name}_{ci}_stack {binders} : List Bytes :=\n  {st} T\n')
        for fi, (_, ft) in enumerate(fs):
            out.append(f'/-- Fact {fi} of case {ci}. -/')
            out.append(f'abbrev {name}_{ci}_fact{fi} {binders} : Prop :=\n  {ft}\n')
    exists = ' '.join(w for c in cases for w in c[1])
    calls = [f'{name}_{ci}_stack t1 t0 a1 a2 T {" ".join(c[1])}'.rstrip() for ci, c in enumerate(cases)]
    def conj(ci):
        fs, ws = cases[ci][0], cases[ci][1]
        return ' ∧ '.join(f'{name}_{ci}_fact{fi} t1 t0 a1 a2 T {" ".join(ws)}'.rstrip() for fi in range(len(fs))) if fs else 'True'
    out.append(f'theorem {name}_shape {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{flag t1 t0 a1 a2 : Bytes}} {{T A : List Bytes}}')
    out.append(f'    {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)')
    out.append(f'    (h : run Eval.opExec env ({seq}) t (St (flag :: t1 :: t0 :: T) (a1 :: a2 :: A) m C kk cs) = r) (hr : r.IsOk) :')
    out.append(f'    ∃ ({exists} : Bytes) (m\' k\' : Nat),' if exists else '    ∃ (m\' k\' : Nat),')
    out.append(f'      (castToBool flag = false → {conj(0)}) ∧')
    out.append(f'      (castToBool flag = true → ({p0}) → {conj(1)}) ∧')
    out.append(f'      (castToBool flag = true → ¬ ({p0}) → {conj(2)}) ∧')
    out.append(f'      run Eval.opExec env k t (St (if castToBool flag = true then (if {p0} then {calls[1]} else {calls[2]}) else {calls[0]}) ({cases[0][3]}) m\' C k\' cs) = r := by')
    out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
    out.append(f'  cases hflag : castToBool flag')
    def leaf(ci, hyps):
        holes = []
        for cj, c in enumerate(cases):
            holes += (['_'] * len(c[1])) if cj == ci else (['[]'] * len(c[1]))
        nf = len(cases[ci][0])
        body = ('⟨' + ', '.join('(by with_reducible assumption)' for _ in range(nf)) + '⟩') if nf > 1 else ('(by with_reducible assumption)' if nf == 1 else 'trivial')
        own = f'fun _ => {body}'
        if ci == 1: own = 'fun _ _ => ' + own[len('fun _ => '):]
        if ci == 2: own = 'fun _ _ => ' + own[len('fun _ => '):]
        parts = []
        for cj in range(3):
            if cj == ci: parts.append(own)
            elif cj == 0: parts.append('fun hf => by simp [hflag] at hf')
            elif ci == 0: parts.append('fun hf => by simp [hflag] at hf')
            elif cj == 1: parts.append('fun _ h1 => absurd h1 h0')
            else: parts.append('fun _ h1 => absurd h0 h1')
        return holes, parts
    # case flag = false
    holes, parts = leaf(0, [])
    out.append(f'  · sym_all h hflag')
    out.append(f'    refine ⟨{", ".join(holes)}, ?mm0, ?kk0, {parts[0]}, {parts[1]}, {parts[2]}, ?run0⟩')
    out.append(f'    case run0 =>')
    out.append(f'      simp only [{name}_0_stack, hflag, Bool.false_eq_true, ↓reduceIte]')
    out.append(f'      with_reducible exact h')
    out.append(f'  · by_cases h0 : {p0}')
    for ci in (1, 2):
        holes, parts = leaf(ci, [])
        out.append(f'    · sym_all h hflag h0')
        out.append(f'      refine ⟨{", ".join(holes)}, ?mm{ci}, ?kk{ci}, {parts[0]}, {parts[1]}, {parts[2]}, ?run{ci}⟩')
        out.append(f'      case run{ci} =>')
        out.append(f'        simp only [{name}_{ci}_stack, hflag, h0, ↓reduceIte, not_false_eq_true, not_true_eq_false]')
        out.append(f'        with_reducible exact h')
    out.append('')
    out.append(f'/-- The arm inside an inactive arm: stepped over. -/')
    out.append(f'theorem {name}_skip {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{S A : List Bytes}} {{D : Cond}} {{cs : Bytes}}')
    out.append(f'    {{m kk : Nat}} (hin : D.isActive = false)')
    out.append(f'    (h : run Eval.opExec env ({seq}) t (St S A m D kk cs) = r) (hr : r.IsOk) :')
    out.append(f'    ∃ k\', run Eval.opExec env k t (St S A m D k\' cs) = r := by')
    out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
    out.append(f'  sym_skip h hin')
    out.append(f'  exact ⟨_, h⟩\n')
    nws = sum(len(c[1]) for c in cases)
    pat = ', '.join(['_'] * nws + ['_', '_', '_', '_', '_'])
    out.append(f'macro_rules\n  | `(tactic| sym_blockrule "{key}" $h:ident $hact:ident) =>')
    out.append(f'    `(tactic| (obtain ⟨{pat}, $h:ident⟩ := {name}_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))')
    out.append(f'macro_rules\n  | `(tactic| sym_skipblockrule "{key}" $h:ident $hin:ident) =>')
    out.append(f'    `(tactic| (obtain ⟨_, $h:ident⟩ := {name}_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf,')
    out.append(f'      Bool.and_false, Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)))\n')
    return '\n'.join(out)
HEADER = """import BoltProof.Bridge.Glue.SimpleMulti.Arms

/-!
# The rebuild phase's regions

The `OP_IF` at suffix 1425 opens the rebuild of the ancestors (a commit token with a grandparent)
and its `OP_ELSE` the null check of the pieces. Three regions inside are read as one step each, on
an abstract stack `t0 :: T` whose items the facts name as `T[n]?.getD []`: the first rebuild with
its anchor (1426–2714, up to the merge flag's push), the second rebuild's arm (2715–3896, opened by
the merge flag, with two cases on the spent lock's `outputIndexN` at depth 39), and the null arm
(3899–4651). The gate and the merge flag themselves stay with the path proof, whose hypotheses
decide them. Generated by the glue's `gen_region.py` from the region probes; regenerate rather than
edit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

"""
if __name__ == '__main__':
    parts = [HEADER]
    parts.append(region('rebuildA', 'c1426', 1426, 2715, 't0 :: T', [([], f'{SP}/RebA.out')],
        'The first rebuild and its anchor (suffix 1426–2714): the rebuilt transaction from the pieces at depths 63–137 of `T` with the preimage\'s fields, hashed against the grandparent, the balances anchored, the merge flag left on top.'))
    parts.append(region('nullArm', 'c3899', 3899, 4652, 't0 :: T', [([], f'{SP}/NullArm.out')],
        'The null arm (suffix 3899–4651): the 150 pieces at depths 63–212 of `T` concatenate to nothing; the stack as it was.'))
    if all(os.path.exists(f'{SP}/{n}.out') for n in ('RebBf', 'RebB0', 'RebB1')):
        parts.append(arm3('rebuildB', 'c2715_if', 2715, 3897, 'decode (item T 39) = 0',
            f'{SP}/RebBf.out', f'{SP}/RebB0.out', f'{SP}/RebB1.out',
            'The second rebuild\'s arm (suffix 2715–3896), opened by the merge flag: the other lineage\'s transaction from the pieces at depths 63–137 of `T`, hashed against `ogp`, by the spent lock\'s `outputIndexN` (depth 39); nothing when the flag is off.'))
    parts.append('end BoltProof.Glue.SimpleMulti\n')
    open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Regions.lean', 'w').write('\n'.join(parts))
    print('ok')
