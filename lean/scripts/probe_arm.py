#!/usr/bin/env python3
"""Probe one conditional arm of the fungible suffix in isolation.
usage: probe_arm.py <name> <start> <end> "<stack>" "<alt>" "<hyp>"...   (chunks with start <= off < end; blocks stay folded)"""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chunks as C
name, a, b, stack, alt = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
hyps = sys.argv[6:]
hnames = [re.match(r'\((\w+)', h).group(1) for h in hyps]
lean = f"""import BoltProof.Bridge.Glue.SimpleMulti.Arms
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
namespace BoltProof.Glue.SimpleMulti
open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
theorem probe {{env : Env}} (he : EnvOK env) {{k t : Bytes}} {{r : GOut}} {{flag acc a1 a2 t0 t1 : Bytes}}
    {{rest T A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}} (hact : C.isActive = true)
    {' '.join(hyps)}
    (h : run Eval.opExec env ({C.seq(C.names(a, b))}) t (St ({stack}) ({alt}) m C kk cs) = r)
    (hr : r.IsOk) : True := by
  simp only [{C.unfold(a, b, keep=[(1961, 2426), (2591, 2609), (3186, 3623), (3773, 3790)])}, List.cons_append, List.nil_append] at h
  sym_all h {' '.join(hnames)}
  trace_state
  trivial
end BoltProof.Glue.SimpleMulti
"""
open(f'{LEAN}/Scratch/{name}.lean', 'w').write(lean)
out = subprocess.run(["bash", "-c", f'export PATH="$HOME/.elan/bin:$PATH"; cd {LEAN} && time lake env lean Scratch/{name}.lean'], capture_output=True, text=True)
full = out.stdout + out.stderr
open(f'{WORK}/{name}.out', 'w').write(full)
keep = []; inh = False
for line in full.splitlines():
    if line.startswith('h :'): inh = True
    elif line and not line[0].isspace(): inh = False
    if inh or 'sym_' in line or 'error' in line or line.startswith('real'): keep.append(line)
print('\n'.join(keep)[:30000])
