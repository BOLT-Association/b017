"""Flag closed literal facts that are false in a probe output. usage: false_facts.py <name>..."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re, sys
SP=WORK
def enc(n):
    if n == 0: return []
    neg = n < 0; m = abs(n); out = []
    while m: out.append(m & 0xff); m >>= 8
    if out[-1] & 0x80: out.append(0x80 if neg else 0)
    elif neg: out[-1] |= 0x80
    return out
def lst(s): return [int(x) for x in s.split(',')] if s.strip() else []
def check(v):
    m = re.fullmatch(r'encode (\d+) = \[([\d, ]*)\]', v)
    if m: return enc(int(m.group(1))) == lst(m.group(2))
    m = re.fullmatch(r'\[([\d, ]*)\] = \[([\d, ]*)\]', v)
    if m: return lst(m.group(1)) == lst(m.group(2))
    m = re.fullmatch(r'¬decode \(encode (\d+)\) = 0', v)
    if m: return int(m.group(1)) != 0
    m = re.fullmatch(r'encode (\d+) = encode (\d+)', v)
    if m: return m.group(1) == m.group(2)
    return None
for name in sys.argv[1:]:
    bad = []; n = 0
    with open(f'{SP}/{name}.out') as fh:
        for line in fh:
            m = re.match(r'^(left[^:]*|right[^:]*|h[^:]*) : (.*)$', line.rstrip('\n'))
            if not m: continue
            r = check(m.group(2).strip())
            if r is None: continue
            n += 1
            if r is False: bad.append(m.group(2).strip())
    print(f'{name}: {n} literal facts, false: {bad}')
