#!/usr/bin/env python3
"""Regenerate the chunk-name lists of lean/BoltProof/Bridge/Glue/SimpleMulti/Reaches.lean from Generated/Chunks.lean:
the suffix_drop_N_append identities and the simp-only unfold lists of the reaches theorems."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re
chunks=open(LEAN + '/BoltProof/Bridge/Generated/Chunks.lean').read()
blk=chunks[chunks.index('namespace BoltProof.Bridge.Generated.SimpleMulti'):chunks.index('end BoltProof.Bridge.Generated.SimpleMulti')]
names=re.findall(r'^def (c\d+\w*) : List Nat', blk, re.M)
start=lambda n: int(re.match(r'c(\d+)', n).group(1))
def nested(ns, tail='k'):
    return ' ++ ('.join('SimpleMulti.'+n for n in ns) + ' ++ ' + tail + ')'*(len(ns)-1)
def nested_closed(ns):
    return ' ++ ('.join('SimpleMulti.'+n for n in ns) + ')'*(len(ns)-1)
p=LEAN + '/BoltProof/Bridge/Glue/SimpleMulti/Reaches.lean'
src=open(p).read()
# 1. drop lemmas
def drop_lemma(N):
    ns=[n for n in names if start(n)>=N]
    assert start(ns[0])==N, N
    return (f"theorem suffix_drop_{N}_append (k : Bytes) :\n"
            f"    SimpleMulti.suffix.drop {N} ++ k = {nested(ns)} := by\n"
            f"  have : SimpleMulti.suffix.drop {N} = {nested_closed(ns)} := by decide +kernel\n"
            f"  rw [this]; simp only [List.append_assoc]\n")
def repl_drop(m):
    return drop_lemma(int(m.group(1)))
src=re.sub(r'theorem suffix_drop_(\d+)_append \(k : Bytes\) :\n.*?\n.*?\n  rw \[this\]; simp only \[List\.append_assoc\]\n', repl_drop, src)
# 2. simp lists: each reaches theorem's `simp only [stack38, SimpleMulti.c423, ...` unfolds the chunks in [423, target)
lines=src.split('\n')
target=None
for i,l in enumerate(lines):
    m=re.search(r'Reaches env (\d+) k t r cs', l)
    if m: target=int(m.group(1))
    if l.startswith('  simp only [stack38, Pieces75.stack, SimpleMulti.c423'):
        ns=[n for n in names if 423<=start(n)<target and not re.search(r'_(pad16|optTail|anchor|ite32|ite43)$', n)]
        tail=l[l.index(', List.cons_append'):]
        lines[i]='  simp only [stack38, Pieces75.stack, '+', '.join('SimpleMulti.'+n for n in ns)+tail
src='\n'.join(lines)
open(p,'w').write(src)
print('ok', len(names))
