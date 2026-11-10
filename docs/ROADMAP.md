# b017 — Roadmap

Forward-looking direction for the BOLT token library. Not commitments; captured so the
shape of the work is visible. (The in-flight pass — role folders, primitive dedupe +
builder convergence, the `verifyEvent`/`verifyEvents` transactional-event model, and signing
injection — is tracked separately and is not repeated here.)

## The genesis family (shipped, see the CHANGELOG)
Three contracts that store the token's genesis outpoint in every output, so a token names its
own asset in O(1) instead of by walking its chain. They are now in this package (templates,
classes, scanner recognition and asset pinning); what remains is the EventListener suffix:
- **FixedBOLT** (fungible, from SimpleMultiBOLT): one mint, a fixed supply. Tokens merge only
  with tokens of the same mint; the genesis outpoint is the asset id.
- **OpenBOLT** (fungible, from FixedBOLT): one issuer, many mints. Tokens from different mints of
  the same issuer merge, and a merge re-roots the stored outpoint (`lastMergeOrGenesisOutpoint`);
  merges across issuers are refused.
- **SerialBOLT** (NFT, from MinSimpleBOLT): each token carries its own mint outpoint as a serial,
  so two NFTs from one issuer, even from one mint transaction, are told apart.

All three lead their lock with the outpoint plus a variable-length `mintData` that only the mint
carries (every later output carries `OP_0`). Remaining: an EventListener suffix for the genesis
family, and token classes for the NFT family (`SerialBOLT` is template-only, like `MinSimpleBOLT`).

## Expand the token library
- Add token types via a per-type **descriptor** (push layout + compiled artifact + field
  map) instead of bespoke per-type files — adding a type becomes data, not code.
- Realise the queued **SimpleBalanceBolt** (NFT + 8-byte balance) and re-introduce an
  optional **swap** action to the fungible contract.
- Give the NFT family symmetric token **classes** (today template-only) so the high-level
  API matches `SimpleMultiBOLT`.
- **AutoBOLT** — a "commit & auto-settle" variant whose settle is permissionless (no recipient
  signature), so settlement can be automated and value can be *donated* / pushed. Design note:
  [`AutoBOLT-design.md`](AutoBOLT-design.md). Motivation is no longer "probably redundant": beyond
  the donation feature, permissionless settle carries a standalone **security** rationale — it
  *erases the durable unfinalized-commit state* — and is **load-bearing for MetaNetBOLT** (finalising
  content nodes whose publisher is offline). Still **gated on the formal proof** — now
  machine-checked for the shipped families (`lean/`); an AutoBOLT variant needs its own covenant
  interface and vectors there before it ships.
- FreeBOLT / OpenBOLT — / HookBOLT / WrapBOLT ? MUST VALIDATE PROTOCOL LOGIC BEFORE Arbitrary Code Execution
- **MetaNetBOLT** — tokenised, Layer-1-validated Metanet domains: the issuer key is the stable MURL
  root, nodes are *settled* BOLT txs, sites are served peer-to-peer as self-proving BEEFs (SPV +
  `verifyEvents`). Design note: [`MetaNetBOLT-design.md`](MetaNetBOLT-design.md). (a.k.a. MNetBOLT /
  MetaBOLT.)

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

## Deferred: align the NFT issuer guard with the fungible rule
The two families derive "the issuer must sign this spend" differently (both prologues are decoded
in [`issuer-guard.md`](issuer-guard.md)). The fungible prologue requires the issuer whenever the
grandparent outpoint is zero. The NFT prologue (`is2ndTx`) additionally requires `txoType != 0`, so
it lets a zero-grandparent *resting* token be committed by a non-issuer and relies on the settle to
refuse it (`minSimpleAttack` B1). The NFT family is not exposed by this — no balance, and the settle
does refuse — so this is an **optimisation, not a fix**, and it sits on the long finger:
- **Change:** drop the `txoType` term from the NFT derivation so both families read
  `needsIssuer = isGenesis || grandparentOutpoint == 0`. One rule to reason about, one lemma, the
  orphan refused at its commit rather than its settle, and a few opcodes fewer in the prologue (the
  exact saving must be measured, not assumed: the NFT prologue's stack shuffle and its
  `hasGrandparent` are reused downstream).
- **Cost:** new NFT bytecode, so a new fingerprint for `MinSimpleBOLT`, `AuthBOLT` and `SerialBOLT`
  and a **reissue** of tokens on the current bytes; the prologue length shifts the rebuild's `signCtx`
  slice offset, which must be recounted (the F3 fix's 36 to 41 tripwire); the full lifecycle and
  attack suites re-run, with `minSimpleAttack` B1.0 flipped from "lone commit accepted" to "refused
  at the commit".
- **Do it when** the NFT bytecode is being rebuilt for another reason (the NFT token classes or
  `SerialBOLT` work above), never on its own.

## Deferred: drop the fungible lock's index byte (`outputIndexN`)
The fungible lock carries an index byte (`outputIndexN`, lock chunk 7) that nothing reads. On chain,
each spend writes the new token's byte afresh from its own `inputIndexN` argument (or from the `i2`
slot for a split settle's second token), never from the spent token's; the ancestor rebuild hashes the
ancestor's bytes as supplied; the balance anchor's index comes from the proof-vout argument `i5`; and
the one place a lock's byte is read, the merge settle's choice between its two prevouts orders, reads
the spent merge-commit token's byte, which both merge paths write as 0, so only that branch ever runs.
Off chain, `multiBoltLib` copies the byte as a rebuild piece and the scanner and the builders locate
tokens by position and proofs by key hash. The Lean development found this (`lean/README.md`, Finding 6);
twenty vectors (`smb_probe_idx_*`) and `test/lib/indexByte.test.ts` show that a token whose byte
disagrees with its position stays spendable through every operation. The byte is dead weight: one push
per token output and the write that fills it on every path. `inputIndexN` is **not** dead: it is the
merge-role flag that orders `hashPrevouts` for a merge commit's second token input, and it stays.
- **Change:** remove the push from the lock and its write from every spend path (`inIdxByte`,
  `splitIdx`), and let the merge settle keep only the prevouts order its zero branch builds. `i2` keeps
  its interop role; `inputIndexN` keeps its merge role.
- **Cost:** new fungible bytecode, so new fingerprints for `SimpleMultiBOLT`, `FixedBOLT` and `OpenBOLT`
  and a **reissue** of tokens on the current bytes; the lock layout shifts (`LAYOUTS`/`FIELDS`, the
  rebuild's piece list and widths, `multiBoltLib`'s field map), and the Lean glue's stack offsets and
  `Residual`'s piece hypotheses are recounted; the lifecycle, attack and index-byte suites re-run and the
  Lean vectors regenerate.
- **Do it when** the fungible bytecode is being rebuilt for another reason (the descriptor work above or a
  genesis-family change), never on its own.

## Deferred: shrink the vector checks' trust base (drop `native_decide`)
The transaction-replay checks — the 107 vectors / 245 inputs run under `lake exe boltvectors`, and the
`Regress.lean` guards — are discharged with `native_decide`: the kernel trusts Lean's *compiled* evaluator
for them, recorded as one auxiliary axiom per theorem (`lean/README.md`, "What is still trusted"). It is the
one place Layer 2 trusts the compiled evaluator over the kernel; Layer 1 (the model theorems) and the
symbolic enforcement glue use only the three standard axioms. Reducing these to ordinary kernel evaluation
would remove that auxiliary axiom and leave the *whole* development on the three standard axioms, tightening
the trust base to its floor.
- **Change:** replace `native_decide` with kernel-checked evaluation for the vector verdicts and the
  regression guards — either `decide` (kernel reduction of each script run) or, where that is too slow, a
  reflection / `Decidable`-instance proof, or reusing the symbolic fragment machinery to *prove* each vector's
  outcome rather than evaluate it.
- **Cost:** kernel reduction of real BSV script executions across 245 inputs is orders of magnitude slower
  than the compiled evaluator — which is *why* `native_decide` is used — so a brute `decide` is likely
  infeasible within the 90-minute CI budget at the current vector scale. A tractable route probably proves the
  verdicts structurally rather than by evaluation, which is real per-vector-shape work.
- **Note:** a trust-base reduction, not a correctness fix. The native evaluator is already an accepted,
  documented trust item; nothing depends on this to stand, and the shipped guarantee is unchanged. Do it only
  if "three standard axioms everywhere" is judged worth the engineering.

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
- Resolve the class-vs-file name mismatches (`SimpleMultiBOLT` lives in `tokens/MultiBOLT.ts`)
  before the first stable `1.0.0` (`0.1.0` is cut). The release scaffolding is in place (README + badges, CHANGELOG, and CI
  under `.github/workflows/ci.yml` with coverage upload and version-gated `npm publish` on push
  to `main`); still wanted is the hermetic browser walk in CI and resolving the naming before
  the first stable tag.

