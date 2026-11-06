#!/usr/bin/env python3
"""The SimpleMulti chunk names (lean/BoltProof/Bridge/Generated/Chunks.lean) and helpers to write chunk sequences."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re, sys
chunks=open(LEAN + '/BoltProof/Bridge/Generated/Chunks.lean').read()
blk=chunks[chunks.index('namespace BoltProof.Bridge.Generated.SimpleMulti'):chunks.index('end BoltProof.Bridge.Generated.SimpleMulti')]
NAMES=re.findall(r'^def (c\d+\w*) : List Nat', blk, re.M)
start=lambda n:int(re.match(r'c(\d+)',n).group(1))
FOLDED=re.compile(r'_(pad16|optTail|anchor|ite32|ite43)$')
def names(a, b):
    """chunk names with a <= start < b"""
    return [n for n in NAMES if a<=start(n)<b]
def seq(ns, tail='k'):
    """right-nested `SimpleMulti.c ++ (… ++ tail)`"""
    return ' ++ ('.join('SimpleMulti.'+n for n in ns) + ' ++ ' + tail + ')'*(len(ns)-1)
def unfold(a, b, keep=()):
    """the simp list unfolding the chunks in [a, b) that are not blocks nor in `keep` ranges [(s,e),…]"""
    out=[]
    for n in names(a,b):
        if FOLDED.search(n): continue
        if any(s<=start(n)<e for s,e in keep): continue
        out.append('SimpleMulti.'+n)
    return ', '.join(out)
if __name__=='__main__':
    a,b=int(sys.argv[1]),int(sys.argv[2])
    print(seq(names(a,b)))
