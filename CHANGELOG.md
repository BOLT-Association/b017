# Changelog

All notable changes to **b017** are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project aims to follow
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Security
- **`SimpleMultiBOLT`: the six red-team fixes now ship in the template.** The published `0.0.0-b2`
  bytecode carried only the original fabricated-hop anchor; a red-team campaign then found and
  closed six further covenant defects, three node-verified on a regtest teranode, now compiled in:
  B1 (`balanceCommit` unchecked -> split inflation to 2^127-1), S1 (co-spent proof not bound to the
  bolt -> a token doubles itself), S2 (rebuilt ancestor's issuer never checked -> counterfeit),
  S3 (splitter swaps bolt order -> theft + freeze), F3 (a zero grandparent disabled the anchor ->
  a non-issuer settles from nothing, contained to one hop), C5 (a signature-length window bricked
  ~1 in 52,000 tokens).

### Changed
- **BREAKING for existing tokens.** The `SimpleMultiBOLT` static bytecode changed, so its fingerprint
  changed: `368c45fdf92164e4e0869c9062be84621ea8ef040e8591399bf6ff3b8c819b11` (was
  `76cfa45595bfb866010d8f87b9b88d6e27b79a9ab3007119dd00eb0138810c8f`). `recognizeType` no longer
  recognises tokens minted with `0.0.0-b2`/`-b1` bytecode - they classify as untrusted and are
  invisible to `verifyEvents`, wallet balances and scans. The data-push layout (`LAYOUTS`) is
  unchanged, so all TS-side argument construction is identical.
- **Tokens minted with pre-fix bytecode remain exploitable and must be reissued.** The vulnerable
  covenant travels in each token's own locking script; upgrading this library does not protect coins
  already on chain.

### Removed
- **BREAKING: dropped the `MinSimpleDiscountBOLT` and `MinSimpleBalanceBOLT` templates.** The
  package now ships two token contracts: `SimpleMultiBOLT` (fungible) and `MinSimpleBOLT` (identity
  NFT), plus the `pay2Proof` UTXO template. The `MinSimpleDiscountTemplate` and
  `MinSimpleBalanceTemplate` exports, their `TokenType` union members, their `LAYOUTS`/`REGISTRY`
  entries and their fixtures are gone. `recognizeType` / `verifyEvents` no longer classify those
  types; any consumer importing the removed templates or naming those type strings must update.
  The kept contracts are unchanged (same bytecode, same fingerprints).
- Coverage for the kept NFT is preserved: `test/lib/minSimpleLifecycle.test.ts` exercises the
  `MinSimpleBOLT` mint/commit/settle and a 2-hop ancestor reconstruction through `verifyTx`,
  standing in for the removed Discount coupon and ancestor-golden tests.

See [`docs/ROADMAP.md`](docs/ROADMAP.md) for planned work.

## [0.0.0-b2] - 2026-09-05

### Security
- **`SimpleMultiBOLT`: fixed a balance-inflation forgery (the "fabricated hop").** A past
  recipient of a token could clone a settled token's bytes into an output they funded
  themselves, give it any balance they liked, and roll it forward, co-spending the real proof
  they legitimately held from the transfer they had received. Every existing check passed:
  the commit paid only themselves, the settle rebuilt a genuine grandparent commit and
  consumed a real predecessor UTXO that they could sign for. Nothing tied the balance to
  anything. **A regtest teranode running GoBDK consensus accepted the whole chain.**

  The settle now reads `balance`, `balanceCommit` and `txoType` off the ancestor it has just
  rebuilt, derives the single balance that ancestor authorised (transfer, merge sum, or
  either split piece), and requires the balance of the token being spent to equal it. Both
  sides of that comparison already existed on chain, so **nothing new is stored**: no new
  token field, no new proof field, and no change to the data-push layout.

  There is no gap between the two halves. The rebuild is assembled from fields the spender
  supplies, so a forger must choose: give the ancestor's real fields and the reconstruction
  hashes correctly but authorises the true balance, not the invented one; or doctor them so
  the balance agrees and the reconstruction stops hashing to `grandparentOutpoint`.

  Verified on a real node, not only in simulation: the same rig that accepted the forgery now
  rejects the forged settle (`TX_INVALID (31)`), with the honest prefix still accepted and a
  byte-tampered control still rejected, reproduced across two independent runs.

### Changed
- **BREAKING for existing tokens.** The `SimpleMultiBOLT` covenant bytecode changed, so its
  static-code fingerprint changed. `recognizeType` will no longer recognise tokens minted
  with `0.0.0-b1` bytecode; they classify as untrusted. The API is unchanged, and the
  data-push layout is unchanged, so `LAYOUTS` and all TS-side argument construction are
  identical to `0.0.0-b1`.

  This is a deliberate clean break, and it has a practical consequence worth stating: an old
  token is not merely distrusted, it is **invisible** to anything built on `recognizeType` /
  `verifyEvents`, including wallet balances and scans. There is no legacy recogniser and none
  is planned. If you hold or index `0.0.0-b1` tokens, identify them before upgrading, because
  afterwards this library will not help you find them.
- **Tokens minted with `0.0.0-b1` bytecode remain inflatable and must be reissued.** Upgrading
  this library does not protect coins already on chain: the vulnerable covenant travels in the
  token's own locking script. Reissue is the only remedy.

### Notes
- The NFT templates (`MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`) are **unaffected**,
  and not merely untested: their ancestor rebuild splices in the token's own balance field
  rather than accepting the ancestor's as an argument, so the value already sits inside the
  pre-image of the hash that must equal `grandparentOutpoint`. An invented balance fails the
  hash. They also have no split or merge, so there is no transition to check.
- `test/repro-fabricated-hop.test.ts` deliberately still asserts that the pre-fix chain
  verifies. It is the record of what a node accepted, and it recognises its fixture against a
  pinned `0.0.0-b1` fingerprint rather than the live registry.

## [0.0.0-b1] — 2026-06-24

### Fixed
- README title typo: "Bicoin" → "Bitcoin". Docs-only republish (no code changes).

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
[0.0.0-b2]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b2
[0.0.0-b1]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b1
[0.0.0-b]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b
