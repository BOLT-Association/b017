#!/usr/bin/env python3
"""Read a path probe's output (probe_sm.py): the facts the run left, the width variables, and the final stack."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re, sys
SUP = {'⁰':'0','¹':'1','²':'2','³':'3','⁴':'4','⁵':'5','⁶':'6','⁷':'7','⁸':'8','⁹':'9'}
SUPC = '[⁰¹²³⁴⁵⁶⁷⁸⁹]'
def casts(s):
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
        inner = casts(s[j+2:k]); k += 1
        # field notation after the group (`↑(a ++ b).length`) belongs to the cast's argument
        while s.startswith('.length', k): inner = '(' + inner + ').length'; k += len('.length')
        out += '((' + inner + ' : Nat) : Int)'
        i = k
def rename(s):
    s = re.sub(r'w✝(' + SUPC + '+)', lambda m: 'w' + ''.join(SUP[c] for c in m.group(1)), s)
    s = re.sub(r'↑\s+\(', '↑(', s)
    s = casts(s)
    s = re.sub(r'↑(\w+)', r'((\1 : Nat) : Int)', s)
    return ' '.join(s.split())
def read(path):
    """-> (facts [(name, text)] oldest first, widths [names] oldest first, hblock text)"""
    txt = open(path).read()
    facts = []; cur = None; ws = []; hb = []; inh = False
    for l in txt.splitlines():
        if inh:
            if l.startswith('⊢'): inh = False
            else: hb.append(l)
            continue
        m = re.match(r'^(left✝' + SUPC + r'*) :(.*)$', l)
        if m:
            if cur: facts.append(cur)
            cur = [m.group(1), m.group(2)]; continue
        m2 = re.match(r'^((?:w✝' + SUPC + r'* ?)+) : (Numbers\.)?Bytes$', l)
        if m2:
            if cur: facts.append(cur); cur = None
            ws += m2.group(1).split(); continue
        if l.startswith('h :'):
            if cur: facts.append(cur); cur = None
            inh = True
            rest = l[3:].strip()
            if rest: hb.append(rest)   # the whole hypothesis on one line
            continue
        if l and not l[0].isspace():
            if cur: facts.append(cur); cur = None
            continue
        if cur is not None: cur[1] += ' ' + l
    if cur: facts.append(cur)
    facts.reverse(); ws.reverse()
    return [(n, rename(t)) for n, t in facts], [rename(w) for w in ws], rename('\n'.join(hb))
if __name__ == '__main__':
    fs, ws, hb = read(sys.argv[1])
    print('widths:', ws)
    for n, t in fs:
        print(n, ':', t if len(sys.argv) < 3 else (t[:int(sys.argv[2])] + ('…' if len(t) > int(sys.argv[2]) else '')))
