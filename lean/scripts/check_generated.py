#!/usr/bin/env python3
"""Check that every glue generator still reproduces the file it generated.

usage: python3 lean/scripts/check_generated.py [--keep]

The glue's regular files are generated (`lean/scripts/gen_*.py`) and committed; a generator that no longer reproduces
its file means either the file was edited by hand or the generator was changed without regenerating, and either way
the next person to regenerate silently loses work. This script runs, in dependency order, every generator whose inputs
are committed (the generated Lean files themselves, `rebuilt_tmpl.lean`, `Generated/Chunks.lean` and, for the settles,
the side files in `lean/scripts/settle-inputs/`) and compares each output with the committed bytes (line endings
normalised). It restores the original files afterwards unless `--keep` is given, so it is safe on a dirty tree.
Exit 0 when every output matches, 1 otherwise (each differing file is listed).

Not covered: the generators that need a probe's full output (`gen_region.py`, `gen_arm.py`, which read the region and
arm probes under `$GLUE_WORK`; rerun the probes as `lean/scripts/README.md` describes), and the argument-driven
`gen_paths*.py`, which write to stdout.
"""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
SM = os.path.join(LEAN, 'BoltProof', 'Bridge', 'Glue', 'SimpleMulti')


def sm(*names):
    return [os.path.join(SM, n) for n in names]


# (generator, extra environment, files it writes), in dependency order: each reads only committed files or the
# outputs of the generators before it
GENERATORS = [
    ('gen_abs.py', {}, sm('Lock.lean')),
    ('gen_drops.py', {}, sm('Reaches.lean')),
    ('gen_settle.py', {'GLUE_WORK': os.path.join(HERE, 'settle-inputs')},
     sm('Settle.lean', 'Settle/Transfer.lean', 'Settle/Split.lean', 'Settle/Merge.lean')),
    ('gen_gate.py', {}, sm('GateItems.lean')),
    ('gen_rebuilt.py', {}, sm('Rebuilt.lean')),
    ('gen_rebuiltB.py', {}, sm('RebuiltB.lean')),
    ('gen_rebuiltB_parse.py', {}, sm('RebuiltBParse.lean', 'AnchorB.lean', 'GpWeldB.lean')),
    ('gen_sm.py', {}, sm('Paths.lean', 'Paths/CommitTransfer.lean', 'Paths/CommitSplit.lean', 'Paths/CommitMerge.lean')),
    ('gen_melt.py', {}, sm('Melt.lean')),
    ('gen_refute.py', {}, sm('Refute.lean')),
    ('gen_sound.py', {}, sm('Sound.lean')),
    ('gen_smregress.py', {}, sm('Regress.lean')),
]


def read(p):
    with open(p, 'rb') as fh:
        return fh.read()


def norm(b):
    return b.replace(b'\r\n', b'\n')


def main():
    keep = '--keep' in sys.argv
    files = [f for _, _, fs in GENERATORS for f in fs]
    before = {f: read(f) for f in files}
    bad, failed = [], []
    try:
        for gen, extra, outs in GENERATORS:
            env = dict(os.environ, PYTHONUTF8='1', **extra)
            r = subprocess.run([sys.executable, os.path.join(HERE, gen)], cwd=LEAN, env=env,
                               capture_output=True, text=True, encoding='utf-8')
            if r.returncode != 0:
                failed.append((gen, (r.stderr or r.stdout).strip().splitlines()[-1:]))
                continue
            for f in outs:
                if norm(read(f)) != norm(before[f]):
                    bad.append((gen, os.path.relpath(f, LEAN)))
    finally:
        if not keep:
            for f, b in before.items():
                with open(f, 'wb') as fh:
                    fh.write(b)
    for gen, msg in failed:
        print(f'FAILED  {gen}: {msg}')
    for gen, f in bad:
        print(f'DIFFERS {f} (from {gen}): the committed file is not what its generator writes')
    n = sum(len(o) for _, _, o in GENERATORS)
    print(f'{len(GENERATORS)} generators, {n} files: {len(failed)} failed, {len(bad)} differ')
    if bad and not keep:
        print('rerun with --keep and inspect `git diff` to see the differences')
    return 1 if (bad or failed) else 0


if __name__ == '__main__':
    sys.exit(main())
