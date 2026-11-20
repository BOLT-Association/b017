# The glue's generators

The glue (`lean/BoltProof/Bridge/Glue/`, described in `lean/README.md`) has long, regular files: one theorem per path
through a suffix, the vocabulary of the rebuilds, the chunk lists the drivers unfold. They were written by these
scripts, which stay here so the files can be regenerated after a change to a covenant or to the driver rather than
edited by hand. A generated file says so in its header. The scripts need Python 3 only; each computes the `lean/`
directory from its own location.

Probe outputs go to `$GLUE_WORK` (default `lean/.lake/glue-work/`); the Lean files the probes run go to `lean/Scratch/`,
which git ignores. Generators that read probe outputs need the probe run first. `$GLUE_WORK` is under `lean/.lake/`, so
nothing in it is ever committed: whatever a generator reads besides the full probe outputs is committed next to the
scripts instead (the settles' side files, `settle-inputs/`), and `check_generated.py` proves the committed inputs are
enough (see below).

| Script | Writes | Reads |
|---|---|---|
| `gen_paths.py`, `gen_paths_auth.py`, `gen_paths_serial.py` | the path theorems of `MinSimple/Paths/`, `AuthBolt/Paths/`, `SerialBolt/Paths/`, to stdout | the chunk names (in the script) |
| `gen_sm.py` | `SimpleMulti/Paths/*.lean`, `SimpleMulti/Paths.lean` | — |
| `gen_sound.py`, `gen_melt.py`, `gen_refute.py`, `gen_abs.py`, `gen_gate.py` | `SimpleMulti/Sound.lean`, `Melt.lean`, `Refute.lean`, `Lock.lean`, `GateItems.lean` | — |
| `gen_region.py` | `SimpleMulti/Regions.lean` | the region probes (`RebA.out`, `RebB0.out`, `RebB1.out`, `RebBf.out`, `NullArm.out`) |
| `gen_arm.py` | `SimpleMulti/Arms.lean` | the arm probes of `probe_arm.py` (`ArmInA.out`, `ArmOutA.out`, `ArmInB.out`, `ArmOutB.out`) |
| `gen_settle.py` | `SimpleMulti/Settle.lean`, `SimpleMulti/Settle/*.lean` | `Regions.lean`, the three side files per settle probe (`*.gateT.txt`, `*.outs.txt`, `*.zeros.txt`), committed in `settle-inputs/` (its README has the probe commands) |
| `extract_settle_inputs.py` | the settle side files, from the settle probes' outputs | `$GLUE_WORK/<probe>.out` of `probe_sm.py` |
| `gen_rebuilt.py`, `gen_rebuiltB.py` | `SimpleMulti/Rebuilt.lean` (from `rebuilt_tmpl.lean`), `SimpleMulti/RebuiltB.lean` | `Regions.lean`, `Settle.lean` |
| `gen_rebuiltB_parse.py` | `SimpleMulti/RebuiltBParse.lean`, `AnchorB.lean`, `GpWeldB.lean` (the second rebuild's parse, token and weld) | `rebuilt_tmpl.lean`, `Anchor.lean`, `GpWeld.lean`, rewritten for the second rebuild's stack (items shifted by one, the first piece set, the alt-stack items the first rebuild left) |
| `gen_drops.py`, `gen_smregress.py` | the chunk lists of `SimpleMulti/Reaches.lean`, the guards of `SimpleMulti/Regress.lean` (in place; the hand-written part above the guards is kept) | `Generated/Chunks.lean`, the file itself |
| `check_generated.py` | no file (runs every generator below whose inputs are committed and fails if any output differs from the committed file; restores the files afterwards) | everything those generators read |
| `probe.py`, `probe_sm.py`, `probe_melt.py`, `probe_arm.py` | a probe file in `lean/Scratch/` and its output in `$GLUE_WORK` | `Generated/Chunks.lean` |
| `facts.py`, `facts_ser.py`, `false_facts.py`, `disasm_ser.py` | — (read a probe's output: its facts, its literal facts that are false, a disassembly of a chunk span) | probe outputs, `Generated/Chunks.lean` |
| `chunks.py` | — (the fungible chunk names and sequence helpers, imported by the others) | `Generated/Chunks.lean` |

The path generators take a title and the path names, for example

```
python3 gen_paths_serial.py ": the commit paths" commit_genesis commit_later > ../BoltProof/Bridge/Glue/SerialBolt/Paths/Commit.lean
```

and with `PROBE=1` replace each path's closing by `trace_state; sorry`, which prints the facts the run leaves.

## Keeping the generated files reproducible

```
python3 lean/scripts/check_generated.py    # 12 generators, 20 files; CI's lean-proof job runs it before the build
```

It runs, in dependency order, `gen_abs`, `gen_drops`, `gen_settle` (from `settle-inputs/`), `gen_gate`, `gen_rebuilt`,
`gen_rebuiltB`, `gen_rebuiltB_parse`, `gen_sm`, `gen_melt`, `gen_refute`, `gen_sound` and `gen_smregress`, and compares
each output with the committed bytes. It does not cover `gen_region.py` and `gen_arm.py` (they read full probe outputs,
rerun as above) or the argument-driven `gen_paths*.py`. The rules it enforces:

* **Never edit a generated file by hand.** Change its generator (or the template it reads), regenerate, and commit
  both; a hand edit is lost the next time anyone regenerates, and the check fails until the generator writes it.
  (`Regress.lean`'s guards were once edited by hand after `gen_smregress.py` last ran; regenerating silently broke
  them. The generator now writes the edited form, and runs idempotently.)
* **Commit every input a generator reads, except a full probe output.** A file left under `$GLUE_WORK` is lost with
  the machine. When a generator needs a few facts out of a probe's 100 MB output, extract them into small side files
  and commit those (`extract_settle_inputs.py` and `settle-inputs/` do this for the settles; until 2026-11-20 their
  side files were never committed, so the settles could not be regenerated anywhere else).
* **A new generator joins `GENERATORS` in `check_generated.py`**, after the generators whose outputs it reads.
* After a covenant change (new bytecode), rerun the probes, regenerate in the order above, rebuild, then run the check:
  it must report 0 differ with the new files committed.

## Pitfalls met on the way

* The driver records `OP_EQUALVERIFY` and `OP_VERIFY` facts without checking them, so a path theorem can be vacuous:
  scan every probe's output with `false_facts.py`, and let the soundness theorem's case split show that each path's
  hypotheses are the ones a real run meets.
* The branches of a many-case proof must not share named holes, and each case's `OP_NUM2BIN` widths need their own
  names, or later binders shadow earlier ones.
* A tactic syntax imported from another family's spec shadows one of the same name (`enforced_norm` against
  `auth_norm`): a normaliser that silently does nothing makes a `fact` search run unbounded instead of failing.
* A rebuild that computes the same `OP_NUM2BIN` word twice gives two witnesses the same hypothesis; identify them
  first (`num2bin_dedup`), or a hash fact fails to match deep in a `++` chain and the unifier blows up instead of
  failing.
* A normaliser that runs `simp (config := {decide := true})` at every hypothesis hangs on the run hypothesis and the
  hash equations. The gate stack keeps unfused drops that the facts fuse, so the normaliser carries `List.drop_drop`
  and the literal simprocs. `simp` keeps an `if`'s decidability instance under a cast, invisible in printed goals,
  so `factD` closes such an equation by the hypothesis with the same right-hand side at default transparency.
* Region and block lemmas name stack items through the reducible accessor `item T n`; a statement that spells
  `T[n]?.getD []` a hundred times spends twenty seconds in instance resolution. The `sym_block` hooks fire only when
  the program is syntactically a constant appended to a tail; unifying `c ++ k` against a bare variable does not
  return.
* A full fungible path as one run (about 1850 instructions over some 230 stack items) elaborates in five minutes and
  peaks at 8 GB, since every step's state is retained in the proof. `Regions.lean` folds the rebuilds, so a path is
  about 625 instructions and a file of three builds in under two minutes; `Settle/Split.lean` still peaks near 8 GB,
  and `Refute.lean` is killed when built beside it on a 16 GB machine.
