# b017 — Roadmap

Forward-looking direction for the BOLT token library. Not commitments; captured so the
shape of the work is visible. (The in-flight pass — role folders, primitive dedupe +
builder convergence, the `verifyEvent`/`verifyTokenChain` token-event model, and signing
injection — is tracked separately and is not repeated here.)

## Expand the token library
- Add token types via a per-type **descriptor** (push layout + compiled artifact + field
  map) instead of bespoke per-type files — adding a type becomes data, not code.
- Realise the queued **SimpleBalanceBolt** (NFT + 8-byte balance) and re-introduce an
  optional **swap** action to the fungible contract.
- Give the NFT family symmetric token **classes** (today template-only) so the high-level
  API matches `SimpleMultiBOLT`.

## Deepen fingerprinting
Today recognition is shallow: leading push-lengths + a sha256 of the static contract suffix.
- Registry/contract **versioning** — recognise multiple revisions per type; `recognizeType`
  returns `{ type, version }`.
- **Semantic field validation**, not just lengths: `txoType` in the known set, issuerPubKey a
  valid compressed point, well-formed outpoints; tolerate trailing ops; classify "unknown +
  reason" rather than a bare `null`.
- A published **fingerprint spec** so third parties can recognise b017 tokens independently;
  property-based / fuzz tests for the recogniser.

## Strengthen token-chain processing
- The `verifyEvent` / `verifyTokenChain` model (token event = commit→settle pair; fingerprint
  every interface — strict golden for tokens, loose for change/funding) extends to validating
  the lineage as a **DAG** over longer / branched histories.
- Typed results + machine-readable error reasons; an indexer-friendly streaming / incremental
  API; performance + memory for large BEEFs.

## Library hardening
- `tsconfig strict: true`; remove `any` casts; type the `BOLT` abstract methods (today `any`,
  and they diverge from the concrete classes).
- Drop the stored owner `privKey` on the token class — take a per-op signer instead. The SDK
  signing injection is already used at the template level (`tpl.unlock(key)` returns the `{sign}`
  the SDK invokes); the class only caches the owner key to feed those templates across its
  multi-step builder flow (`process.env.BOLT_VERIFIER` already removed). An API change that ripples
  through the stateful builder + the demo bridge, so deferred as its own focused PR.
- Single source of truth for the two parallel index maps (`LAYOUTS` in `scan/fingerprints.ts`
  + `FIELDS` in `scan/verifyTokenChain.ts`) → derive both from one per-type descriptor.
- Real fee/size estimation (today `nftSpend.estimateLength` hardcodes `2000`).
- Resolve the class-vs-file name mismatches (`SimpleMultiBOLT` lives in `tokens/MultiBOLT.ts`),
  then cut `0.1.0` and `npm publish`. The release scaffolding is in place as of `0.0.0-b`
  (README, CHANGELOG, and CI under `.github/workflows/ci.yml`); still wanted is the hermetic
  browser walk in CI and resolving the naming before the first stable tag.

## Demo / infrastructure
- Fix live SPV determinism at the source: on teranode v0.15.2 the merkle-service never
  receives `BlockMessage.Coinbase`, so the BUMP is intermittent. Fixing it makes the SPV
  proof — not just broadcast-acceptance — deterministic for the live demo.
