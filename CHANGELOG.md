# Changelog

All notable changes to **b017** are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project aims to follow
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- **`AuthBOLT`: a new identity-NFT type** (`AuthBoltTemplate`, `AUTH_DATA_MAX_BYTES`, `TokenType` `"AuthBOLT"`).
  `MinSimpleBOLT` (zero-funding) plus an owner-supplied `authOrMiscData` of up to 75 bytes: the first unlock
  argument, created in a commit and authenticated in the settle, which rebuilds its grandparent commit (whose
  scriptSig leads with the value) and binds it to the grandparent txid. The commit's own owner signature does
  NOT cover it. Same six-push lock layout as `MinSimpleBOLT`; recognised by its suffix fingerprint
  `378932c162a2fb2344ae7357664268608a05efa2fc07be60b6dbf35984dcf669`. `unlock()` refuses a value over 75 bytes
  (the lock refuses it too). Node-verified (contract-level broadcast suite) 16/16 on a Bitcoin SV regtest and a
  teranode regtest; the b017 library tests run on the `@bsv/sdk` Spend engine.
- **Zero-funding spends in `singleSpendUnlock` / `singleAncestorPieces`.** The funding input and the change
  output are detected from the tx (`[token, proof?, funding?]`, `[token, p2pb?, change?]`) instead of assumed
  last, and an unfunded or change-less ancestor commit is passed as empty (OP_0) pieces. `SingleLayout`
  (`MIN_SIMPLE_LAYOUT`, `AUTH_BOLT_LAYOUT`) parameterises the 37-arg and 39-arg unlock layouts.
- Documented (README, template headers): a minted token received by SPV does not prove the sender holds the
  issuer key - the issuer-signed **commit** spending it (funded or not) must accompany it, and a token carrying
  `authOrMiscData` must travel with its signed commit **and** settle as the package.
- Tests: `minSimpleZF` (43, the zero-funding matrix + 11 rebuild-mismatch refusals), `minSimpleAttack` (16, the
  first MinSimple red-team suite), `authBolt` (53 incl. a 27-cell path-coverage gate), AuthBolt template and
  scanner (`nftScan`) tests. `npm run build:nft` regenerates both NFT templates from the compiled contract artifacts.

### Security
- **`SimpleMultiBOLT`: the six red-team fixes now ship in the template.** The published `0.0.0-b2`
- **`SimpleMultiBOLT`: the six red-team fixes now ship in the template.** The published `0.0.0-b2`
  bytecode carried only the original fabricated-hop anchor; a red-team campaign then found and
  closed six further covenant defects - five node-verified on a regtest teranode in both directions
  (B1, S1, S2, S3, F3); C5 confirmed in simulation and a 4M-signature measurement (its check is a
  basic signature-length bound with no node/simulator divergence) - now compiled in:
  B1 (`balanceCommit` unchecked -> split inflation to 2^127-1), S1 (co-spent proof not bound to the
  bolt -> a token doubles itself), S2 (rebuilt ancestor's issuer never checked -> counterfeit),
  S3 (splitter swaps bolt order -> theft + freeze), F3 (a zero grandparent disabled the anchor ->
  a non-issuer settles from nothing, contained to one hop), C5 (a signature-length window bricked
  ~1 in 52,000 tokens).

### Security
- **The scanner now EXECUTES scripts.** `verifyEvents` / `verifyEvent` used to be purely structural: a forged commit
  (a stranger's mint, a commit and settle the stranger signed with their own key, which the covenant's issuer guard
  refuses at the commit) passed with `ok: true`. Reproduced, then fixed: every input whose source tx is supplied is run
  on the `@bsv/sdk` Spend engine, and a failure returns `ok: false` with `script execution failed: tx <id> input <n>`.
  This also closes the redteam2 "misreads" C1-C4 (hand-patched second settle, hidden token input, novel txoType,
  inflated balance), which the structure check alone accepted. For mined txs the node already did this; for off-chain
  (SPV / zero-funding) packages nothing had.

### Changed
- **BREAKING (scanner): every input's source tx must now be supplied.** `verifyEvents` / `verifyEvent` refuse an input
  whose source is missing (`source tx <id> of tx <id> input <n> was not supplied`), including funding inputs and the
  mint's funding parent; previously external funding was waved through. Supply sources by attaching `sourceTransaction`,
  by including the parent in the batch, or by sending BEEF. Results gain `sources: { txid, proven }[]`.
- **Added: BEEF.** Event txs may be given as Atomic BEEF (BRC-95) over BEEF V2 (BRC-96), hex or bytes; new exports
  `toAtomicBeef`, `fromBeef`, `isBeef`. BEEF V1 (BRC-62) and a non-self-contained BEEF are refused. BUMPs are not
  checked against block headers (use a `ChainTracker`).
- **BREAKING (scanner): a lone mint is no longer a valid event.** `verifyEvents` / `verifyEvent` now refuse a mint
  that no commit in the same event/batch spends, returning `{ ok: false, unauthenticated: true, reason: "unauthenticated
  mint ..." }` (all token types). A mint only names an `issuerPubKey`; the issuer guard runs when the genesis is first
  spent, so a mint alone proves nothing about who holds the key. This verdict is not a signature failure.
  A mint with its commit + settle (funded or not) is accepted as before. `ScanResult` / `EventResult` gain
  `unauthenticated?: boolean`. Tests: `test/scanner/unauthenticatedMint.test.ts`.
- **BREAKING for existing tokens: `MinSimpleBOLT` is now the zero-funding contract** (the zero-funding build, lock
  1265 -> 1275 bytes) in place of `MSBolt.opt3`. Its static bytecode changed, so its fingerprint changed:
  `5dc9c1ddd27e2c91f919531ad82a32c9ce8da772ab87e39af05c2c3361970122` (was
  `2892679d85ef021d754036094ecd77e14f0c3934a23a48e09e7da337e50f823d`). `recognizeType` no longer recognises
  `MinSimpleBOLT` tokens minted with the old bytecode; they must be REISSUED (the covenant travels in each
  token's locking script). The lock layout and the 37-arg unlock layout are unchanged.
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
  package now ships three token contracts: `SimpleMultiBOLT` (fungible), `MinSimpleBOLT` (identity
  NFT) and `AuthBOLT` (identity NFT + auth data), plus the `pay2Proof` UTXO template. The `MinSimpleDiscountTemplate` and
  `MinSimpleBalanceTemplate` exports, their `TokenType` union members, their `LAYOUTS`/`REGISTRY`
  entries and their fixtures are gone. `recognizeType` / `verifyEvents` no longer classify those
  types; any consumer importing the removed templates or naming those type strings must update.
  The kept contracts are unchanged (same bytecode, same fingerprints).
- Coverage for the kept NFT is preserved: `test/lib/minSimpleLifecycle.test.ts` exercises the
  `MinSimpleBOLT` mint/commit/settle and a 2-hop ancestor reconstruction through `verifyTx`,
  standing in for the removed Discount coupon and ancestor-golden tests.

### Fixed
- **`SimpleMultiBOLT`: the second piece of a split could not be transferred or split again.** A settle
  co-spends its ancestor commit's proof, and a split commit carries two (vout 1 for piece A, vout 2
  for piece B). The builder picked `outputs.length >= 5 ? 2 : 1`, which is always 1 for the 4-output
  split commit, so piece B co-spent piece A's proof and its settle failed. The proof vout is now
  looked up by the owner's pubKeyHash. Builder-only: the covenant and bytecode are unchanged. Piece B
  still has to bring its own funding, because the split settle's change pays piece A.
- **`verifyTx` rejected correctly signed inputs with an nSequence of 0.** It passed
  `sequence || 0xffffffff` to the Spend engine, turning a signed non-final sequence into final and
  breaking the sighash. It now uses `??`.

### Documentation
- README: test and coverage figures refreshed (128 tests across 17 files; 99.5% statements,
  100% functions, 96.3% branches), and the NFT is described as the single `MinSimpleBOLT` identity
  token rather than a template family.
- Restored the scanner suite (`test/scanner/verifyEvents.test.ts`) that was deleted with the Discount
  and Balance goldens, rebuilt over live `SimpleMultiBOLT` chains.

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
- **BREAKING for existing tokens: `MinSimpleBOLT` is now the zero-funding contract** (the zero-funding build, lock
  1265 -> 1275 bytes) in place of `MSBolt.opt3`. Its static bytecode changed, so its fingerprint changed:
  `5dc9c1ddd27e2c91f919531ad82a32c9ce8da772ab87e39af05c2c3361970122` (was
  `2892679d85ef021d754036094ecd77e14f0c3934a23a48e09e7da337e50f823d`). `recognizeType` no longer recognises
  `MinSimpleBOLT` tokens minted with the old bytecode; they must be REISSUED (the covenant travels in each
  token's locking script). The lock layout and the 37-arg unlock layout are unchanged.
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

[Unreleased]: https://github.com/BOLT-Association/b017/compare/v0.0.0-b2...HEAD
[0.0.0-b2]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b2
[0.0.0-b1]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b1
[0.0.0-b]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b
