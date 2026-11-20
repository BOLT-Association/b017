# The settle probe inputs

`gen_settle.py` writes `SimpleMulti/Settle.lean` and `SimpleMulti/Settle/{Transfer,Split,Merge}.lean` from three
`probe_sm.py` runs and two side files per run, all read from `$GLUE_WORK` (default `lean/.lake/glue-work/`, which git
ignores):

| Probe | Mode | `.out` | `.gateT.txt` | `.outs.txt` | `.zeros.txt` |
|---|---|---|---|---|---|
| `F1_settle21` | transfer (spent type `0x21`, next `0x20`) | 90 MB | here | here | here |
| `F7_settle23` | split (`0x23` → `0x22`) | 89 MB | here | here | here |
| `F8_settle25` | merge (`0x25` → `0x24`) | 112 MB | here | here | here |

The three side files per probe are all `gen_settle.py` reads of it, so this folder alone regenerates the settle files:
`GLUE_WORK=lean/scripts/settle-inputs python3 lean/scripts/gen_settle.py`, which `lean/scripts/check_generated.py` (and
CI) runs on every change.

The `.out` files are too large to commit; the commands below recreate them in a few minutes. The six side files
here are what `extract_settle_inputs.py` cuts out of those outputs: diff a rerun against them. No other file under
`$GLUE_WORK` is read by a generator without being written by a script: the other generators read only `.out` files of
the probe scripts (`gen_region.py`, `gen_arm.py`).

These files were rebuilt on 2026-11-20 (the originals were never committed) and checked: from them, `gen_settle.py`
regenerated all four committed files byte for byte on `main` at `8651c06`. They were then regenerated the same day
for the suffix without `outputIndexN` (4513 bytes; the lock's index byte and its six ancestor mirrors removed), with
the index-byte hypotheses dropped from the probes (below).

## Recreate

From the repository root, with the Lean build done (`cd lean && lake build`; the probes import
`BoltProof.Bridge.Glue.SimpleMulti.Reaches` and `.Enforced`). The three probes are independent and can run in parallel;
on the 4700-byte suffix a 4-core, 16 GB machine took `F1` 8m44s, `F7` 4m22s and `F8` 4m46s, partly at the same
time; on the 4513-byte suffix the three took about 3 minutes each, run at the same time on a 20-thread machine.

```bash
export GLUE_WORK=$PWD/lean/.lake/glue-work && mkdir -p $GLUE_WORK
```

```bash
python3 lean/scripts/probe_sm.py F1_settle21 "(hty : f.ty = [0x21])" "(hnty : a.nty = [0x20])" "(hgp : ¬ decode f.gp = 0)" "(hpar : ¬ decode f.parent = 0)" > $GLUE_WORK/F1_settle21.summary
```

```bash
python3 lean/scripts/probe_sm.py F7_settle23 "(hty : f.ty = [0x23])" "(hnty : a.nty = [0x22])" "(hgp : ¬ decode f.gp = 0)" "(hpar : ¬ decode f.parent = 0)" "(hpk : decode a.pkh1 = 0)" > $GLUE_WORK/F7_settle23.summary
```

```bash
python3 lean/scripts/probe_sm.py F8_settle25 "(hty : f.ty = [0x25])" "(hnty : a.nty = [0x24])" "(hgp : ¬ decode f.gp = 0)" "(hpar : ¬ decode f.parent = 0)" > $GLUE_WORK/F8_settle25.summary
```

Each writes `$GLUE_WORK/<probe>.out` (the full output); the `.summary` is the script's own excerpt, which nothing
reads. A good run contains no `error` and starts with the driver's count: `sym_all: 607 instructions, 2 blocks` (`F1`),
`603 instructions, 3 blocks` (`F7`), `604 instructions, 3 blocks` (`F8`) (on the 4700-byte suffix 628, 623 and 625).

The hypotheses fix the case `gen_settle.py` expects, with the token at input 0 and a grandparent:

| Hypothesis | Why |
|---|---|
| `hty`, `hnty` | the mode: the spent type and the next type |
| `hgp : ¬ decode f.gp = 0` | a grandparent: the gate (suffix 1425) enters the first rebuild, so the block rule `c1426` (`rebuildA_shape`) records the stack |
| `hpar : ¬ decode f.parent = 0` | the issuer guard's flag reads `[]`, which `gen_settle.py` rewrites to `encode (if decode f.parent = 0 then 1 else 0)` |
| `hpk : decode a.pkh1 = 0` (split) | the first token output first; `settleOuts_22` restores both orders |

On the 4700-byte suffix three more hypotheses fixed index bytes: `hidx : decode a.inIdx = 0` (the new token's index
byte), `hi : decode a.i2 = 0` (the split's second token's) and `hoi : decode f.outIdx = 0` (the merge's second
rebuild, which had a second case for a non-zero spent index). The suffix without `outputIndexN` writes no index byte
and its second rebuild has one case, so a settle reads neither `a.inIdx` nor `a.i2` and the probes need none of them.

The hypothesis names do not reach the generated files; only the terms do.

## Extract

```bash
python3 lean/scripts/extract_settle_inputs.py
```

For each probe it reads `$GLUE_WORK/<probe>.out` (only the goal's first hypotheses: it stops after about 400 000
characters) and writes, each on one line with whitespace collapsed:

- `<probe>.gateT.txt`: the stack under the gate flag, the second argument `T` of the hypothesis
  `rebuildA_fact0 t0 T w8 … w42` that the block rule `c1392` leaves (`t0` is the outpoint,
  `List.take 36 (List.drop 68 a.pre)`), with its parentheses;
- `<probe>.outs.txt`: the outputs fact, the one hypothesis `Hash.hash256 (… ++ a.chg) = …` (the settled outputs and the
  change blob against `hashOutputs`);
- `<probe>.zeros.txt`: the zero pads, one line `<name> <n>` per `num2bin [] (decode …) = some w✝ⁿ` fact in the first
  400 000 characters (the run's `OP_NUM2BIN` of an empty push to `n` bytes), which `gen_settle.py` writes as `zeros n`.

Then check them against this folder:

```bash
for f in lean/scripts/settle-inputs/*.txt; do cmp "$f" "$GLUE_WORK/$(basename "$f")"; done
```

`--src DIR` and `--dest DIR` read and write elsewhere; `--head` also writes the head of each `.out` to `--dest` (the
part this script reads, about 400 KB), for a small copy that reruns the extraction without the probes.

## Generate

```bash
GLUE_WORK=lean/scripts/settle-inputs python3 lean/scripts/gen_settle.py   # or $GLUE_WORK after a fresh extraction
```

```bash
git diff --exit-code -- lean/BoltProof/Bridge/Glue/SimpleMulti/Settle.lean lean/BoltProof/Bridge/Glue/SimpleMulti/Settle/
```

`gen_settle.py` overwrites the four files in place; an empty diff is the check. It reads only `Regions.lean` and the
three side files per probe, never a probe's `.out` (until 2026-11-20 it read each `.out`'s head for the zero pads, which
`<probe>.zeros.txt` now carries). `lean/scripts/check_generated.py` runs this check together with every other
reproducible generator; CI runs it on every change. After a covenant change: rerun the probes, extract, copy the nine
side files here, regenerate, rebuild, and commit the side files with the generated files.
