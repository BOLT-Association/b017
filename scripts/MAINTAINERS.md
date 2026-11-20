# Maintainers
## Regenerating the contracts
All three templates are patched from the sibling toolchain's frozen production artifacts:

```
npm run build:contract     # SimpleMultiBOLT (scripts/build-simple-multi.mjs); build-time only
npm run build:nft          # MinSimpleBOLT + AuthBOLT (scripts/build-min-simple-bolt.mjs)
```

The `scripts/` folder holds these regeneration tools. They are **not** part of `npm run build`
(`tsconfig` excludes them) and are **not** published (the tarball ships only `dist/`). They
require the `sx` compiler to be present at a sibling `../sx` path — that toolchain is **not**
vendored in this repo, so these scripts only run in a checkout where `../sx` exists.

The two NFT templates (`MinSimpleBOLT`, `AuthBOLT`) are regenerated from the sibling toolchain's production artifacts with
`npm run build:nft` (it also rewrites `test/fixtures/*.lockSuffix.hex`). Run it after any change to the sx
production contracts, then `npm test`.

Consumers never need any of this — the package ships the pre-compiled templates.

## Coverage

- `npm run coverage:gaps` runs the suite with coverage and lists every uncovered branch and statement as
  `file:line`, plus the count of `v8 ignore` markers in `src/`. It exits 1 while anything is uncovered.
- `npm run coverage:readme` rewrites the test counts and the coverage table in `README.md` from that run.
  Never edit those figures by hand. `npm run coverage:check` fails if the README is out of date.
- `vitest.config.ts` holds `coverage.thresholds`: a floor, so coverage cannot fall silently. The target is 100.

## The Lean proof (`lean/`)

- `npm run lean:vectors` regenerates `lean/BoltProof/Bridge/Generated/` and `lean/vectors/vectors.json` from the
  test builders. Run it after any change to a covenant template, to `test/helpers/*`, or to the pinned
  expectations in `lean/vectors/export.test.ts`; commit the result. CI regenerates and fails on drift.
- `cd lean && lake exe cache get && lake build && lake exe boltvectors`, then `node scripts/lean-axiom-check.mjs`
  from the root, is what the `lean-proof` CI job runs. `lake build BoltProofCore` alone (Layer 1) needs no
  Mathlib and takes seconds.
- To bump bsv-script-lean: change `rev` in `lean/lakefile.toml`, copy its `lean-toolchain`, `lake update bsvscript`,
  rebuild, re-run `boltvectors` and re-triage any changed verdict. Never run a bare `lake update`.
- An unexpected verdict in `boltvectors` is a **finding** about the bytes or the engine, not a reason to edit an
  expectation silently: record it in `lean/README.md` and `CHANGELOG.md` first.
- `python3 lean/scripts/check_generated.py` reruns the glue's generators and fails if any no longer writes its
  committed file (CI runs it too). Never edit a generated glue file by hand: change its generator and regenerate
  (`lean/scripts/README.md`).

## Releasing

- Bump `version` in `package.json` (and `package-lock.json`), move the CHANGELOG's Unreleased entries under the new
  version with the date, update the README status line, and merge to `main`. CI's `publish` job publishes the new
  version after `build-test` passes; a version already on npm is skipped. Under 0.x a breaking change bumps the
  minor version.
- Publishing uses npm **trusted publishing** (OIDC), not a token: on npmjs.com, the `b017` package's settings list a
  trusted publisher of type GitHub Actions with organization `BOLT-Association`, repository `b017` and workflow
  `ci.yml` (no environment). Each run exchanges its GitHub identity token (`id-token: write`) for a short-lived
  publish token, with provenance attached automatically. There is no `NPM_TOKEN` secret to rotate; the job needs npm
  11.5.1 or later, which it installs. If the workflow file is renamed, update the trusted publisher on npmjs.com.
- A failed publish is rerun with `gh run rerun <run id> --failed`: the version check makes it safe to repeat.
