# b017 — Roadmap

Forward-looking direction for the BOLT token library. Not commitments; captured so the
shape of the work is visible. (The in-flight pass — role folders, primitive dedupe +
builder convergence, the `verifyEvent`/`verifyEvents` transactional-event model, and signing
injection — is tracked separately and is not repeated here.)

## Expand the token library
- Add token types via a per-type **descriptor** (push layout + compiled artifact + field
  map) instead of bespoke per-type files — adding a type becomes data, not code.
- Realise the queued **SimpleBalanceBolt** (NFT + 8-byte balance) and re-introduce an
  optional **swap** action to the fungible contract.
- Give the NFT family symmetric token **classes** (today template-only) so the high-level
  API matches `SimpleMultiBOLT`.
- **AutoBOLT** — a "commit & auto-settle" variant whose settle is permissionless (no recipient
  signature), so settlement can be automated and value can be *donated* / pushed. Design note:
  [`AutoBOLT-design.md`](AutoBOLT-design.md). TENTATIVE (probably redundant/unnecessary)
- FreeBOLT / OpenBOLT — / HookBOLT / WrapBOLT ? MUST VALIDATE PROTOCOL LOGIC BEFORE Arbitrary Code Execution
- MetaNetBOLT / MNetBOLT / MetaBOLT

## Harden fingerprinting & validation
Recognition is no longer a shallow per-script check. Golden recognition — `recognizeType`
(leading-push layout + `sha256` of the static contract code) and `recognizeP2P` (the b017 proof
output) — now feeds the `verifyEvent` / `verifyEvents` scanner, which validates whole
**transactional events**: it categorises each tx by its `txoType` action, fingerprints *every*
interface (strict-golden for token in/out and proof outputs; loose shape for change/funding), pins
the issuer across a batch, and pairs every commit with its settle via `parentOutpoint` — failing
closed with machine-readable reasons, off a single-source `REGISTRY` derived from the templates.

Remaining **hardening** (the future-validation direction):
- Registry/contract **versioning** — recognise multiple revisions per type; `recognizeType`
  returns `{ type, version }`.
- Lift **semantic field validation** into the recogniser itself, not only the event layer:
  `txoType` in the known set, issuerPubKey a valid compressed point, well-formed outpoints;
  tolerate trailing ops; classify "unknown + reason" rather than a bare `null`.
- A published **fingerprint spec** so third parties can recognise b017 tokens independently, with
  property-based / fuzz tests for the recogniser.

## Strengthen event processing
- The `verifyEvent` / `verifyEvents` model (transactional event = commit→settle pair; fingerprint
  every interface — strict golden for tokens, loose for change/funding) extends to validating
  a batch's events as a **DAG** over longer / branched histories.
- Typed results + machine-readable error reasons; an indexer-friendly streaming / incremental
  API; performance + memory for large BEEFs.

## The internet as a sidechain — why this is trustworthy

The direction this library points at is treating **the public internet as a sidechain**: BOLT
events (a mint, a commit→settle pair, a melt) are self-proving, so they don't have to travel over
the main chain to be trusted — they can be handed peer-to-peer over any transport (HTTP, a
message bus, a file) and **verified locally** by the recipient with `verifyEvents` before they
act. The chain is where things *settle*; the internet is where they *move*.

The reason you can trust that arrangement is not optimism — it is that **it shrinks the set of
parties who can cheat you**. With a conventional ledger you are exposed to a long line of
intermediaries who *could* defraud you (a custodian, an indexer, a bridge, a validator set), and
your safety depends on all of them behaving. A self-proving BOLT event removes that line almost
entirely: per-token unforgeability (proven — see [`formal-proof.md`](formal-proof.md)) means a
counterfeit, a stolen token, an inflated balance, or a spliced history is cryptographically
rejected by the recipient *regardless of who relayed it*. A bad actor in the middle cannot forge,
alter, or substitute the asset; the worst they can do is fail to deliver it, which you detect
immediately. So you are simply **dealing with fewer bad actors** — the protocol designs the
cheatable middlemen out, instead of asking you to trust them.

What that leaves is a short, honest list of who you *do* still have to trust — exactly the two
residual assumptions called out in [`formal-proof.md`](formal-proof.md) §1.6: the **issuer**
(for supply-honesty — the protocol proves each token is genuine, not that the issuer hasn't
over-minted) and the **chain's hash power** (for final settlement). Everyone else on the wire —
relays, caches, indexers, counterparties you've never met — moves from "trusted" to "irrelevant",
because the event proves itself. Writing this architecture down as a referenceable spec (transport
envelope, batch/DAG verification semantics, the trust-surface argument above) is itself a roadmap
item, so the claim can be engaged with on its own terms rather than as a slogan.

## Library hardening
- `tsconfig strict: true`; remove `any` casts; type the `BOLT` abstract methods (today `any`,
  and they diverge from the concrete classes).
- Drop the stored owner `privKey` on the token class — take a per-op signer instead. The SDK
  signing injection is already used at the template level (`tpl.unlock(key)` returns the `{sign}`
  the SDK invokes); the class only caches the owner key to feed those templates across its
  multi-step builder flow (`process.env.BOLT_VERIFIER` already removed). An API change that ripples
  through the stateful builder + the demo bridge, so deferred as its own focused PR.
- Single source of truth for the two parallel index maps (`LAYOUTS` in `scan/fingerprints.ts`
  + `FIELDS` in `scan/verifyEvents.ts`) → derive both from one per-type descriptor.
- Real fee/size estimation (today `nftSpend.estimateLength` hardcodes `2000`).
- Resolve the class-vs-file name mismatches (`SimpleMultiBOLT` lives in `tokens/MultiBOLT.ts`),
  then cut `0.1.0`. The release scaffolding is in place (README + badges, CHANGELOG, and CI
  under `.github/workflows/ci.yml` with coverage upload and version-gated `npm publish` on push
  to `main`); still wanted is the hermetic browser walk in CI and resolving the naming before
  the first stable tag.

