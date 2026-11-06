#!/usr/bin/env python3
"""Probe harness: run sym_run over a span of chunks from a given entry stack and print the exit state.
usage: probe.py <Family> <first_chunk_index> <last_chunk_index> "<stack expr>" ["<extra tactic lines>"]
Chunks are the generated names c<idx>_<off>[...] of lean/BoltProof/Bridge/Generated/Chunks.lean."""
import os as _os
LEAN = _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))
WORK = _os.environ.get('GLUE_WORK', _os.path.join(LEAN, '.lake', 'glue-work'))
_os.makedirs(WORK, exist_ok=True)
import re, subprocess, sys
fam, a, b, stack = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
extra = sys.argv[5] if len(sys.argv) > 5 else ""
src = open(LEAN + '/BoltProof/Bridge/Generated/Chunks.lean').read()
block = src[src.index(f"namespace BoltProof.Bridge.Generated.{fam}"):src.index(f"end BoltProof.Bridge.Generated.{fam}")]
names = re.findall(r"^def (c\d+_\w+) : List Nat", block, re.M)
sel = [n for n in names if a <= int(n[1:4]) <= b]
prog = " ++ (".join(sel) + ")" * (len(sel) - 1) if len(sel) > 1 else sel[0]
unfold = ", ".join(f"{fam}.{n}" for n in sel)
progq = prog.replace("c", f"{fam}.c")
lean = f"""import BoltProof.Bridge.Glue.Sym.Tactic
import BoltProof.Bridge.Generated.Chunks
set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
namespace BoltProof.Glue
open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
theorem probe {{env : Env}} {{k t : Bytes}} {{r : GOut}} {{S A : List Bytes}} {{C : Cond}} {{cs : Bytes}} {{m kk : Nat}}
    {{issuer gp parent ty com pkh pre pk sig ben chg fund : Bytes}}
    {{p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Bytes}}
    {{x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Bytes}}
    (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env ({progq} ++ k) t (St ({stack}) A m C kk cs) = r) (hr : r.IsOk) : True := by
  simp only [{unfold}, List.cons_append, List.nil_append] at h
  sym_run h
{extra}
  trace_state
  trivial
end BoltProof.Glue
"""
open(LEAN + '/Scratch/Probe.lean', 'w').write(lean)
out = subprocess.run(["bash", "-c", f'export PATH="$HOME/.elan/bin:$PATH"; cd {LEAN} && lake env lean Scratch/Probe.lean'],
                     capture_output=True, text=True).stdout
# print the info lines and the hypothesis h and other interesting hyps
keep = []; inh = False
for line in out.splitlines():
    if line.startswith("h :") or line.startswith("h✝") : inh = True
    elif line and not line[0].isspace(): inh = False
    if inh or "sym_" in line or "error" in line: keep.append(line)
print("\n".join(keep))
