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

Consumers never need any of this — the package ships the pre-compiled templates.