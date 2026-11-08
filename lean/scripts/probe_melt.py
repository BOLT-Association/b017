#!/usr/bin/env python3
"""Fungible melt probe: run the whole suffix symbolically from the lock stack under hypotheses and print where it stops.
usage: probe_sm.py <name> "<hyp1>" "<hyp2>" ...   (each "(hname : prop)"); env PROBE_EXTRA adds tactic lines after sym_all.
The hypothesis names are passed to sym_all. Output: the sym_all info lines, errors, and `h` at the stop."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os, re, subprocess, sys
name=sys.argv[1]; hyps=sys.argv[2:]
hnames=[re.match(r'\((\w+)', h).group(1) for h in hyps]
chunks=open(LEAN + '/BoltProof/Bridge/Generated/Chunks.lean').read()
blk=chunks[chunks.index('namespace BoltProof.Bridge.Generated.SimpleMulti'):chunks.index('end BoltProof.Bridge.Generated.SimpleMulti')]
names=re.findall(r'^def (c\d+\w*) : List Nat', blk, re.M)
start=lambda n:int(re.match(r'c(\d+)',n).group(1))
ARMS=[(1961,2426),(2591,2609),(3186,3623),(3773,3790),(1426,2715),(2715,3897),(3899,4652)]+[tuple(map(int,r.split('-'))) for r in os.environ.get('PROBE_KEEP','').split(',') if r]
unfold=', '.join('SimpleMulti.'+n for n in names if start(n)>=0 and not re.search(r'_(pad16|optTail|anchor|ite32|ite43)$', n) and not any(s<=start(n)<e for s,e in ARMS))
extra=os.environ.get('PROBE_EXTRA','')
lean=f"""import BoltProof.Bridge.Glue.SimpleMulti.Reaches
import BoltProof.Bridge.Glue.SimpleMulti.Enforced
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
namespace BoltProof.Glue.SimpleMulti
open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (reached_of_append)
theorem probe {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{f : Fields}} {{a : Args}}
    {{S A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)
    {' '.join(hyps)}
    (h : run Eval.opExec env (SimpleMulti.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) : True := by
  simp only [SimpleMulti.suffix, Fields.stack, Args.stack, {unfold}, List.cons_append, List.nil_append, List.append_assoc] at h
  sym_all h {' '.join(hnames)}
{extra}
  trace_state
  trivial
end BoltProof.Glue.SimpleMulti
"""
os.makedirs(LEAN + '/Scratch', exist_ok=True)
open(f'{LEAN}/Scratch/{name}.lean','w').write(lean)
out=subprocess.run(["bash","-c",f'export PATH="$HOME/.elan/bin:$PATH"; cd {LEAN} && time lake env lean Scratch/{name}.lean'],capture_output=True,text=True)
full=out.stdout+out.stderr
open(f'{WORK}/{name}.out','w').write(full)
keep=[]; inh=False
for line in full.splitlines():
    if re.match(r'^(h|left|right|h\w*)[✝ ]', line) or line.startswith('h :'): inh=True
    elif line and not line[0].isspace(): inh=False
    if inh or 'sym_' in line or 'error' in line or line.startswith('real'): keep.append(line)
print('\n'.join(keep)[:20000])
