# The glue's generators

The glue (`lean/BoltProof/Bridge/Glue/`, planned in `lean/GLUE-PLAN.md`) has long, regular files: one theorem per path
through a suffix, the vocabulary of the rebuilds, the chunk lists the drivers unfold. They were written by these
scripts, which stay here so the files can be regenerated after a change to a covenant or to the driver rather than
edited by hand. A generated file says so in its header. The scripts need Python 3 only; each computes the `lean/`
directory from its own location.

Probe outputs go to `$GLUE_WORK` (default `lean/.lake/glue-work/`); the Lean files the probes run go to `lean/Scratch/`,
which git ignores. Generators that read probe outputs need the probe run first.

| Script | Writes | Reads |
|---|---|---|
| `gen_paths.py`, `gen_paths_auth.py`, `gen_paths_serial.py` | the path theorems of `MinSimple/Paths/`, `AuthBolt/Paths/`, `SerialBolt/Paths/`, to stdout | the chunk names (in the script) |
| `gen_sm.py` | `SimpleMulti/Paths/*.lean`, `SimpleMulti/Paths.lean` | — |
| `gen_sound.py`, `gen_melt.py`, `gen_refute.py`, `gen_abs.py`, `gen_gate.py` | `SimpleMulti/Sound.lean`, `Melt.lean`, `Refute.lean`, `Lock.lean`, `GateItems.lean` | — |
| `gen_region.py` | `SimpleMulti/Regions.lean` | the region probes (`RebA.out`, `RebB0.out`, `RebB1.out`, `RebBf.out`, `NullArm.out`) |
| `gen_arm.py` | `SimpleMulti/Arms.lean` | the arm probes of `probe_arm.py` (`ArmInA.out`, `ArmOutA.out`, `ArmInB.out`, `ArmOutB.out`) |
| `gen_settle.py` | `SimpleMulti/Settle.lean`, `SimpleMulti/Settle/*.lean` | `Regions.lean`, the settle probes of `probe_sm.py` (`*.out`, `*.gateT.txt`, `*.outs.txt`) |
| `gen_rebuilt.py`, `gen_rebuiltB.py` | `SimpleMulti/Rebuilt.lean` (from `rebuilt_tmpl.lean`), `SimpleMulti/RebuiltB.lean` | `Regions.lean`, `Settle.lean` |
| `gen_drops.py`, `gen_smregress.py` | the chunk lists of `SimpleMulti/Reaches.lean`, the guards of `SimpleMulti/Regress.lean` (in place) | `Generated/Chunks.lean` |
| `probe.py`, `probe_sm.py`, `probe_melt.py`, `probe_arm.py` | a probe file in `lean/Scratch/` and its output in `$GLUE_WORK` | `Generated/Chunks.lean` |
| `facts.py`, `facts_ser.py`, `false_facts.py`, `disasm_ser.py` | — (read a probe's output: its facts, its literal facts that are false, a disassembly of a chunk span) | probe outputs, `Generated/Chunks.lean` |
| `chunks.py` | — (the fungible chunk names and sequence helpers, imported by the others) | `Generated/Chunks.lean` |

The path generators take a title and the path names, for example

```
python3 gen_paths_serial.py ": the commit paths" commit_genesis commit_later > ../BoltProof/Bridge/Glue/SerialBolt/Paths/Commit.lean
```

and with `PROBE=1` replace each path's closing by `trace_state; sorry`, which prints the facts the run leaves.
