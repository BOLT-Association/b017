# Changelog

All notable changes to **b017** are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project aims to follow
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

See [`docs/ROADMAP.md`](docs/ROADMAP.md) for planned work.

## [0.0.0-b] — 2026-06-23

First public beta. The library is functional and fully tested; the API may still change
before `0.1.0`.

### Added
- `SimpleMultiBOLT` fungible token class — mint / transfer / split / merge / melt, each
  producing a real, script-valid Bitcoin transaction verified by the `@bsv/sdk` Spend engine.
- NFT token templates: `MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`, plus the
  `pay2Proof` UTXO template.
- Off-chain scanner: `recognizeType` / `REGISTRY` strict fingerprinting, and
  `verifyEvent` / `verifyEvents` for validating BOLT transactional events — one event
  (mint, commit→settle pair, or melt) or a whole batch (issuer-pinned, every commit
  paired with its settle).
- Pre-compiled `.sx` contracts embedded in the templates — **no sx compiler at runtime**.
- `@bsv/sdk` as the single peer dependency (no `@elas_co/ts` runtime dependency).

### Packaging
- Build now cleans `dist/` before `tsc` so the published tarball contains no stale artifacts.
- Added `repository`, `bugs`, `homepage`, and `keywords` metadata.

[Unreleased]: https://github.com/BOLT-Association/b017
[0.0.0-b]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b
