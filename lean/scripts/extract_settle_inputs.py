#!/usr/bin/env python3
"""Extract the settle side files gen_settle.py reads from a settle probe's output.
usage: extract_settle_inputs.py [--dest DIR] [--head] [PROBE ...]   (default probes: F1_settle21 F7_settle23 F8_settle25)

Reads `$GLUE_WORK/<probe>.out` (the `probe_sm.py` output: the one goal `trace_state` prints after `sym_all`) and writes
to DIR (default `$GLUE_WORK`):
  <probe>.gateT.txt  the stack under the gate flag: the second argument `T` of `rebuildA_fact0 t0 T w8 ... w42`, the
                     first rebuild's fact the block rule `c1392` (`rebuildA_shape`) leaves, in parentheses;
  <probe>.outs.txt   the outputs fact: the hypothesis `Hash.hash256 (... ++ a.chg) = ...` (the settled outputs and the
                     change blob against `hashOutputs`), the only `Hash.hash256` hypothesis whose argument ends in `a.chg`;
  <probe>.zeros.txt  the zero pads: one line `<name> <n>` per hypothesis `num2bin [] (decode n) = some <name>` in the
                     first 400000 characters (the run's `OP_NUM2BIN` of an empty push, `zeros n`), which gen_settle.py
                     substitutes into the two facts above.
The facts are written on one line, whitespace collapsed as `facts.rename` does (gen_settle.py collapses it again).
These three files are all gen_settle.py reads of a probe, so lean/scripts/settle-inputs/ (where they are committed)
regenerates the settle files without rerunning the probes (`check_generated.py` does exactly that).
With --head, also writes DIR/<probe>.out: the first lines of the output, up to the end of both facts and at least the
400000 characters the zero pads are read from, so DIR alone is enough to run this script again.
The full outputs are 90-210 MB; the head is what any script reads of them."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
import argparse, os, re

ZERO_MAP_CHARS = 400000   # the zero pads are named in the goal's first hypotheses
# a zero pad: the run's `OP_NUM2BIN` of an empty push to `n` bytes, named by an inaccessible width variable
ZERO_RE = re.compile(r'num2bin \[\] \(decode (\(encode (\d+)\)|\[(\d+)(?:, 0)?\])\)\.toNat = some (w✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*)')


def zero_pads(text):
    """[(name, n)] of the zero pads named in `text`, in order of appearance."""
    return [(w, int(a or b)) for _, a, b, w in ZERO_RE.findall(text)]
PROBES = ['F1_settle21', 'F7_settle23', 'F8_settle25']

def balanced(s, i):
    d = 0
    for k in range(i, len(s)):
        if s[k] == '(': d += 1
        elif s[k] == ')':
            d -= 1
            if d == 0: return s[i:k + 1]
    raise ValueError('unbalanced term at %d' % i)

def term(s, i):
    """The argument starting at s[i]: a parenthesised term or an atom."""
    if s[i] == '(': return balanced(s, i)
    j = s.find(' ', i)
    return s[i:] if j < 0 else s[i:j]

def hyps(path):
    """-> ([(statement, end char offset)] of the goal's hypotheses in order, the lines read). Stops once both facts are
    found and ZERO_MAP_CHARS characters are read."""
    out = []; cur = None; lines = []; chars = 0; found = set()
    def close():
        if cur is None: return
        text = ' '.join(''.join(cur).split())
        if ' : ' in text:
            stmt = text.split(' : ', 1)[1]
            out.append((stmt, chars))
            if stmt.startswith('rebuildA_fact0 '): found.add('gate')
            if stmt.startswith('Hash.hash256 (') and outs_arg(stmt) is not None: found.add('outs')
    with open(path, encoding='utf-8') as fh:
        for l in fh:
            if l[:1] not in ('', ' ', '\n'):
                close(); cur = None
                if len(found) == 2 and chars >= ZERO_MAP_CHARS: break
                cur = [l]
            elif cur is not None:
                cur.append(l)
            lines.append(l); chars += len(l)
        else:
            close()
    return out, lines

def outs_arg(stmt):
    try: a = balanced(stmt, len('Hash.hash256 '))
    except ValueError: return None   # a hypothesis the head cuts off
    return a if a[1:-1].endswith(' ++ a.chg') else None

def extract(probe, src, dest, head):
    path = os.path.join(src, probe + '.out')
    hs, lines = hyps(path)
    gate = [s for s, _ in hs if s.startswith('rebuildA_fact0 ')]
    outs = [s for s, _ in hs if s.startswith('Hash.hash256 (') and outs_arg(s) is not None]
    assert len(gate) == 1, (probe, 'rebuildA_fact0 hypotheses', len(gate))
    assert len(outs) == 1, (probe, 'outputs hypotheses', len(outs))
    g = gate[0]; i = len('rebuildA_fact0 ')
    t0 = term(g, i); i += len(t0) + 1
    T = term(g, i)
    assert T.startswith('(') and T.endswith(')'), (probe, T[:40])
    os.makedirs(dest, exist_ok=True)
    open(os.path.join(dest, probe + '.gateT.txt'), 'w', encoding='utf-8').write(T + '\n')
    open(os.path.join(dest, probe + '.outs.txt'), 'w', encoding='utf-8').write(outs[0] + '\n')
    zs = zero_pads(''.join(lines)[:ZERO_MAP_CHARS])
    assert zs, (probe, 'no zero pads')
    open(os.path.join(dest, probe + '.zeros.txt'), 'w', encoding='utf-8').write(''.join(f'{w} {n}\n' for w, n in zs))
    msg = f'{probe}: gateT {len(T)} chars (t0 = {t0}), outs {len(outs[0])} chars, {len(zs)} zero pads'
    if head:
        assert os.path.abspath(dest) != os.path.abspath(src), '--head would overwrite the full output'
        need = max(ZERO_MAP_CHARS, max(e for s, e in hs if s in (g, outs[0])))
        n = 0; keep = []
        for l in lines:
            keep.append(l); n += len(l)
            if n >= need: break
        open(os.path.join(dest, probe + '.out'), 'w', encoding='utf-8').write(''.join(keep))
        msg += f', head {len(keep)} lines, {n} chars'
    print(msg)

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--src', default=WORK, help='directory holding <probe>.out (default $GLUE_WORK)')
    p.add_argument('--dest', default=None, help='directory to write to (default: the source directory)')
    p.add_argument('--head', action='store_true', help='also write the head of each .out to DEST')
    p.add_argument('probes', nargs='*', default=PROBES)
    args = p.parse_args()
    for probe in args.probes:
        extract(probe, args.src, args.dest or args.src, args.head)
