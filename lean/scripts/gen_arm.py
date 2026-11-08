#!/usr/bin/env python3
"""Generate lean/BoltProof/Bridge/Glue/SimpleMulti/Arms.lean: the four conditional arms of the rebuilds read as one step,
from the isolated arm probes (probe_arm.py output: ArmInA, ArmOutA, ArmInB, ArmOutB)."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chunks as C
SP = WORK
SUP = {'⁰':'0','¹':'1','²':'2','³':'3','⁴':'4','⁵':'5','⁶':'6','⁷':'7','⁸':'8','⁹':'9'}
def casts(s):
    """`↑(E)` (a Nat cast to Int, as the pretty printer writes it) as `((E : Nat) : Int)`, so it elaborates."""
    out = ''; i = 0
    while True:
        j = s.find('↑(', i)
        if j < 0: out += s[i:]; return out
        out += s[i:j]
        depth = 0; k = j + 1
        while True:
            if s[k] == '(': depth += 1
            elif s[k] == ')':
                depth -= 1
                if depth == 0: break
            k += 1
        inner = casts(s[j+2:k])   # a cast inside the cast's argument
        out += '((' + inner + ' : Nat) : Int)'
        i = k + 1
def rename(s):
    def w(m): return 'w' + ''.join(SUP[c] for c in m.group(1))
    s = re.sub(r'w✝([⁰¹²³⁴⁵⁶⁷⁸⁹]+)', w, s)
    s = re.sub(r'↑\s+\(', '↑(', s)
    s = casts(s)
    s = re.sub(r'↑(\w+)', r'((\1 : Nat) : Int)', s)
    return s
def hblock(txt):
    lines = txt.splitlines(); out = []; on = False
    for l in lines:
        if l.startswith('h :'): on = True; continue
        if on and l.startswith('⊢'): break
        if on: out.append(l)
    return '\n'.join(out)
def facts(txt):
    """the left✝ facts (whole statements) and the Bytes-typed width variables, in order"""
    out = []; cur = None; ws = []
    for l in txt.splitlines():
        m = re.match(r'^(left✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*) :(.*)$', l)
        if m:
            if cur: out.append(cur)
            cur = m.group(2).strip(); continue
        m2 = re.match(r'^(w✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*) : (Numbers\.)?Bytes$', l)
        if m2:
            if cur: out.append(cur); cur = None
            ws.append(m2.group(1)); continue
        if l and not l[0].isspace():
            if cur: out.append(cur); cur = None
            continue
        if cur is not None: cur += ' ' + l.strip()
    if cur: out.append(cur)
    out.reverse(); ws.reverse()   # the probe lists them newest first
    return [rename(f) for f in out], [rename(w) for w in ws]
def stack_expr(hb):
    """the top element's expression: between `(St` and the alt-stack line"""
    hb = ' '.join(hb.split())
    i = hb.index('(St'); j = hb.rindex(':: rest)')
    body = hb[i+3:j].strip()
    assert body.startswith('('), body[:40]
    body = body[1:].strip()   # the stack list's own parenthesis
    assert body.startswith('('), body[:40]
    # strip one pair of outer parentheses
    depth = 0; end = None
    for k, ch in enumerate(body):
        if ch == '(': depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0: end = k; break
    assert end == len(body) - 1, (end, len(body))
    return rename(' '.join(body[1:-1].split()))
def arm(name, key, a, b, inp, txt, doc):
    hb = hblock(txt); expr = stack_expr(hb); fs, ws = facts(txt)
    seq = C.seq(C.names(a, b)); unfold = C.unfold(a, b)
    alt = 'a1 :: a2 :: A' if inp else 'A'
    wargs = ' '.join(ws)
    binders = f'(flag acc a1 a2 : Bytes) (rest : List Bytes) ({wargs} : Bytes)' if inp and ws else '(flag acc : Bytes) (rest : List Bytes)'
    call = f'{name} flag acc a1 a2 rest {wargs}' if inp else f'{name} flag acc rest'
    out = []
    out.append(f'/-- {doc} -/')
    out.append(f'def {name} {binders} : Bytes :=\n  {expr}\n')
    if fs:
        factconj = ' ∧\n      '.join(f'({f})' for f in fs)
        exists = ' '.join(ws)
        out.append(f'/-- The arm `[{a}, {b})`, as one step: the flag popped; if it holds, the accumulator extended by `{name}` under the')
        out.append(f'widths and bounds the arm fixes, else unchanged; the rest of the stack and the alt stack as they were. -/')
        out.append(f'theorem {name}_shape {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{flag acc a1 a2 : Bytes}}')
        out.append(f'    {{rest A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)')
        out.append(f'    (h : run Eval.opExec env ({seq}) t (St (flag :: acc :: rest) ({alt}) m C kk cs) = r) (hr : r.IsOk) :')
        out.append(f'    ∃ ({exists} : Bytes) (m\' k\' : Nat),')
        out.append(f'      (castToBool flag = true → {factconj}) ∧')
        out.append(f'      run Eval.opExec env k t (St ((if castToBool flag then {call} else acc) :: rest) ({alt}) m\' C k\' cs) = r := by')
        out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
        out.append(f'  cases hflag : castToBool flag')
        out.append(f'  · sym_all h hflag')
        nils = ', '.join('[]' for _ in ws)
        out.append(f'    exact ⟨{nils}, _, _, fun h => by simp at h, by simp only [hflag, Bool.false_eq_true, ↓reduceIte]; with_reducible exact h⟩')
        out.append(f'  · sym_all h hflag')
        holes = ', '.join('_' for _ in ws)
        assums = ', '.join('(by with_reducible assumption)' for _ in fs)
        out.append(f'    refine ⟨{holes}, ?mm, ?kk, fun _ => ⟨{assums}⟩, ?run⟩')
        out.append(f'    case run =>')
        out.append(f'      simp only [{name}, hflag, ↓reduceIte]')
        out.append(f'      with_reducible exact h\n')
    else:
        out.append(f'/-- The arm `[{a}, {b})`, as one step: the flag popped; if it holds, the accumulator extended by `{name}`, else unchanged. -/')
        out.append(f'theorem {name}_shape {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{flag acc : Bytes}}')
        out.append(f'    {{rest A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)')
        out.append(f'    (h : run Eval.opExec env ({seq}) t (St (flag :: acc :: rest) A m C kk cs) = r) (hr : r.IsOk) :')
        out.append(f'    ∃ m\' k\', run Eval.opExec env k t (St ((if castToBool flag then {call} else acc) :: rest) A m\' C k\' cs) = r := by')
        out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
        out.append(f'  cases hflag : castToBool flag')
        out.append(f'  · sym_all h hflag')
        out.append(f'    exact ⟨_, _, by simp only [hflag, Bool.false_eq_true, ↓reduceIte]; with_reducible exact h⟩')
        out.append(f'  · sym_all h hflag')
        out.append(f'    exact ⟨_, _, by simp only [{name}, hflag, ↓reduceIte]; with_reducible exact h⟩\n')
    out.append(f'/-- The arm inside an inactive arm: stepped over. -/')
    out.append(f'theorem {name}_skip {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{S A : List Bytes}} {{D : Cond}} {{cs : Bytes}}')
    out.append(f'    {{m kk : Nat}} (hin : D.isActive = false)')
    out.append(f'    (h : run Eval.opExec env ({seq}) t (St S A m D kk cs) = r) (hr : r.IsOk) :')
    out.append(f'    ∃ k\', run Eval.opExec env k t (St S A m D k\' cs) = r := by')
    out.append(f'  simp only [{unfold}, List.cons_append, List.nil_append] at h')
    out.append(f'  sym_skip h hin')
    out.append(f'  exact ⟨_, h⟩\n')
    # rules
    if fs:
        out.append(f'macro_rules\n  | `(tactic| sym_blockrule "{key}" $h:ident $hact:ident) =>')
        pat = ', '.join('_' for _ in ws)
        out.append(f'    `(tactic| (obtain ⟨{pat}, _, _, _, $h:ident⟩ := {name}_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))')
    else:
        out.append(f'macro_rules\n  | `(tactic| sym_blockrule "{key}" $h:ident $hact:ident) =>')
        out.append(f'    `(tactic| (obtain ⟨_, _, $h:ident⟩ := {name}_shape $(Lean.mkIdent `he) $hact $h $(Lean.mkIdent `hr)))')
    out.append(f'macro_rules\n  | `(tactic| sym_skipblockrule "{key}" $h:ident $hin:ident) =>')
    out.append(f'    `(tactic| (obtain ⟨_, $h:ident⟩ := {name}_skip $(Lean.mkIdent `he) (by simp only [isActive_opIf, isActive_opElse_opIf,')
    out.append(f'      Bool.and_false, Bool.and_true, Bool.false_and, Bool.not_true, Bool.not_false, $hin:ident]) $h $(Lean.mkIdent `hr)))\n')
    return '\n'.join(out)
HEADER = """import BoltProof.Bridge.Glue.SimpleMulti.Blocks

/-!
# The rebuilds' conditional arms

Four arms of the fungible rebuilds (suffix 1961–2425 and 3186–3621, the second input of the
rebuilt transaction; 2591–2607 and 3773–3788, its second output) open on a flag the ancestor's
data decides, so a path proof cannot enter or skip them from its hypotheses. Each is read here as
one step (`sym_block` on its first chunk, `sym_skipblock` inside an inactive arm): the flag popped,
the accumulator on top extended by the arm's bytes when the flag holds, under the widths the arm's
`OP_NUM2BIN`s fix and the size bounds it checks, and unchanged otherwise; the rest of the stack and
the alt stack as they were. The definitions are the arms' effects read off their symbolic runs
(`optPush` from `Blocks.lean`; `rest[n]?.getD []` is the item at depth `n` below the accumulator).

Generated by the glue's `gen_arm.py` from the arm probes; regenerate rather than edit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

"""
parts = [HEADER]
parts.append(arm('secondInA', 'c1961_if', 1961, 2426, True, open(f'{SP}/ArmInA.out').read(),
    'The second input of the first rebuilt transaction (suffix 1962–2424), as the arm appends it to the accumulator: the ancestor pieces at depths 156–183 below it, the two alt-stack items, and the widths `w2`, `w3`, `w4`, `w5`, `w8` the arm computes.'))
parts.append(arm('secondOutA', 'c2591_if', 2591, 2609, False, open(f'{SP}/ArmOutA.out').read(),
    'The second output of the first rebuilt transaction (suffix 2592–2607): the pieces at depths 31, 13 and 141 and `OP_EQUALVERIFY OP_CHECKSIG`.'))
parts.append(arm('secondInB', 'c3186_if', 3186, 3623, True, open(f'{SP}/ArmInB.out').read(),
    'The second input of the second rebuilt transaction (suffix 3187–3621), the pieces at depths 82–109.'))
parts.append(arm('secondOutB', 'c3773_if', 3773, 3790, False, open(f'{SP}/ArmOutB.out').read(),
    'The second output of the second rebuilt transaction (suffix 3774–3788): the pieces at depths 32, 14 and 67.'))
parts.append('end BoltProof.Glue.SimpleMulti\n')
open(LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Arms.lean', 'w').write('\n'.join(parts))
print('ok')
