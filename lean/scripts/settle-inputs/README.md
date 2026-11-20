# The settle probe inputs

`gen_settle.py` writes `SimpleMulti/Settle.lean` and `SimpleMulti/Settle/{Transfer,Split,Merge}.lean` from three
`probe_sm.py` runs and two side files per run, all read from `$GLUE_WORK` (default `lean/.lake/glue-work/`, which git
ignores):

| Probe | Mode | `.out` | `.gateT.txt` | `.outs.txt` |
|---|---|---|---|---|
| `F1_settle21` | transfer (spent type `0x21`, next `0x20`) | 185 MB | here | here |
| `F7_settle23` | split (`0x23` → `0x22`) | 184 MB | here | here |
| `F8_settle25` | merge (`0x25` → `0x24`) | 209 MB | here | here |

The `.out` files are too large to commit; the commands below recreate them in about 10 minutes. The six side files
here are what `extract_settle_inputs.py` cuts out of those outputs: diff a rerun against them. No other file under
`$GLUE_WORK` is read by a generator without being written by a script: the other generators read only `.out` files of
the probe scripts (`gen_region.py`, `gen_arm.py`).

These files were rebuilt on 2026-11-20 (the originals were never committed) and checked: from them, `gen_settle.py`
regenerates all four committed files byte for byte on `main` at `8651c06`.

## Recreate

From the repository root, with the Lean build done (`cd lean && lake build`; the probes import
`BoltProof.Bridge.Glue.SimpleMulti.Reaches` and `.Enforced`). The three probes are independent and can run in parallel;
on a 4-core, 16 GB machine they took `F1` 8m44s, `F7` 4m22s and `F8` 4m46s, partly at the same time.

```bash
export GLUE_WORK=$PWD/lean/.lake/glue-work && mkdir -p $GLUE_WORK
```

```bash
python3 lean/scripts/probe_sm.py F1_settle21 "(hty : f.ty = [0x21])" "(hnty : a.nty = [0x20])" "(hgp : ¬ decode f.gp = 0)" "(hpar : ¬ decode f.parent = 0)" "(hidx : decode a.inIdx = 0)" > $GLUE_WORK/F1_settle21.summary
```

```bash
python3 lean/scripts/probe_sm.py F7_settle23 "(hty : f.ty = [0x23])" "(hnty : a.nty = [0x22])" "(hgp : ¬ decode f.gp = 0)" "(hpar : ¬ decode f.parent = 0)" "(hidx : decode a.inIdx = 0)" "(hpk : decode a.pkh1 = 0)" "(hi : decode a.i2 = 0)" > $GLUE_WORK/F7_settle23.summary
```

```bash
python3 lean/scripts/probe_sm.py F8_settle25 "(hty : f.ty = [0x25])" "(hnty : a.nty = [0x24])" "(hgp : ¬ decode f.gp = 0)" "(hpar : ¬ decode f.parent = 0)" "(hidx : decode a.inIdx = 0)" "(hoi : decode f.outIdx = 0)" > $GLUE_WORK/F8_settle25.summary
```

Each writes `$GLUE_WORK/<probe>.out` (the full output); the `.summary` is the script's own excerpt, which nothing
reads. A good run contains no `error` and starts with the driver's count: `sym_all: 628 instructions, 2 blocks` (`F1`),
`623 instructions, 3 blocks` (`F7`), `625 instructions, 3 blocks` (`F8`).

The hypotheses fix the case `gen_settle.py` expects, with the token at input 0 and a grandparent:

| Hypothesis | Why |
|---|---|
| `hty`, `hnty` | the mode: the spent type and the next type |
| `hgp : ¬ decode f.gp = 0` | a grandparent: the gate (suffix 1425) enters the first rebuild, so the block rule `c1426` (`rebuildA_shape`) records the stack |
| `hpar : ¬ decode f.parent = 0` | the issuer guard's flag reads `[]`, which `gen_settle.py` rewrites to `encode (if decode f.parent = 0 then 1 else 0)` |
| `hidx : decode a.inIdx = 0` | the index byte reads `0`, rewritten to `inIdxByte a` |
| `hpk : decode a.pkh1 = 0`, `hi : decode a.i2 = 0` (split) | the first token output first, the second's index byte `1` (rewritten to `splitIdx a`); `settleOuts_22` restores both cases |
| `hoi : decode f.outIdx = 0` (merge) | one case of the second rebuild: the spent lock's output index zero (`rebuildB_1`) |

The hypothesis names do not reach the generated files; only the terms do.

## Extract

```bash
python3 lean/scripts/extract_settle_inputs.py
```

For each probe it reads `$GLUE_WORK/<probe>.out` (only the goal's first hypotheses: it stops after about 400 000
characters) and writes, each on one line with whitespace collapsed:

- `<probe>.gateT.txt`: the stack under the gate flag, the second argument `T` of the hypothesis
  `rebuildA_fact0 t0 T w10 … w46` that the block rule `c1426` leaves (`t0` is the outpoint,
  `List.take 36 (List.drop 68 a.pre)`), with its parentheses;
- `<probe>.outs.txt`: the outputs fact, the one hypothesis `Hash.hash256 (… ++ a.chg) = …` (the settled outputs and the
  change blob against `hashOutputs`).

Then check them against this folder:

```bash
for f in lean/scripts/settle-inputs/*.txt; do cmp "$f" "$GLUE_WORK/$(basename "$f")"; done
```

`--src DIR` and `--dest DIR` read and write elsewhere; `--head` also writes the head of each `.out` to `--dest` (the
part `gen_settle.py` and this script read, about 400 KB), for a small copy that reruns without the probes.

## Generate

```bash
python3 lean/scripts/gen_settle.py
```

```bash
git diff --exit-code -- lean/BoltProof/Bridge/Glue/SimpleMulti/Settle.lean lean/BoltProof/Bridge/Glue/SimpleMulti/Settle/
```

`gen_settle.py` overwrites the four files in place; an empty diff is the check. Of each `.out` it reads the first
400 000 characters (`zero_map`: the `num2bin [] (decode …) = some w✝ⁿ` facts that name the zero pads `zeros n`); the rest
comes from the side files and `Regions.lean`.
