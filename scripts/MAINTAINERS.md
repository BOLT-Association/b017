# Maintainers
## Regenerating the contracts
The compiled artifacts + template suffixes are produced once from the BOLT `sx` toolchain:

```
npm run build:contract     # build-time only; consumers never need this
```

The `scripts/` folder holds these regeneration tools. They are **not** part of `npm run build`
(`tsconfig` excludes them) and are **not** published (the tarball ships only `dist/`). They
require the `sx` compiler to be present at a sibling `../sx` path — that toolchain is **not**
vendored in this repo, so `build:contract` only runs in a checkout where `../sx` exists.

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
