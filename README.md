# b017; Bicoin Original Layer-1 Token Protocol

[![CI](https://github.com/BOLT-Association/b017/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/BOLT-Association/b017/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/BOLT-Association/b017/branch/main/graph/badge.svg)](https://codecov.io/gh/BOLT-Association/b017)
[![npm version](https://img.shields.io/npm/v/b017.svg?logo=npm)](https://www.npmjs.com/package/b017)
[![TypeScript](https://img.shields.io/badge/TypeScript-5.7-3178C6?logo=typescript&logoColor=white)](https://www.typescriptlang.org/)

> **Status: `0.0.0-b` (beta).** Considered Live-Network-Testing Ready (Production next). The API is working and fully tested
> (126/126 unit tests, **99% statement / 98% function / 95% branch coverage**) but may still change before `0.1.0`. See
> [`docs/ROADMAP.md`](docs/ROADMAP.md) for what's next.

Standalone TypeScript library for the **Bicoin Original Layer-1 Token** protocol on BSV — a fungible & optimised
**SimpleMultiBOLT** (16-byte balance (x2 Bitcoin's base layer limit); mint / transfer / split / merge / melt), a family of
minimal **NFT** templates, and an off-chain **scanner** that recognises and verifies
**transactional events**. The only runtime dependency is a peer `@bsv/sdk`.

Every protocol action is a **transactional event**: a transfer / split / merge is a **commit → settle
pair** of txs, while a mint (genesis) and a melt (terminal) are single-tx events. Because events
share this shape, they can be collected into a **batch**, transmitted together, and parsed & validated for
authenticity & provenance by a multistep inspection.

**Why these tokens can't be counterfeited:** the token state (issuer, lineage, owner, balance)
is bound into a self-validating Bitcoin Script covenant via a dual hash-commitment, so forging
a token would require breaking SHA-256 or ECDSA. See [`docs/unforgeability.md`](docs/unforgeability.md)
for the argument and the forgery tests that demonstrate it, and
[`docs/formal-proof.md`](docs/formal-proof.md) for the rigorous treatment (4 theorems, 7 lemmas,
full attack-vector analysis).

## Install / build

```
npm install
npm run build          # clean + tsc -> dist/ (JS + .d.ts)
npm test               # vitest (126 tests)
npm run test:coverage  # vitest + v8 coverage -> coverage/ (text + HTML report)
```

`@bsv/sdk` is a **peer dependency** — your application provides the single shared instance.

## Usage — the fungible token

```ts
import { SimpleMultiBOLT } from "b017";
import { PrivateKey } from "@bsv/sdk";

const issuer = PrivateKey.fromRandom();

// mint(privKey, fundingTx, mintData, balance16) — balance is 16 LE bytes
const token = await new SimpleMultiBOLT().mint(issuer, fundingTx, "", balance16);

// transfer = commit + settle to a new owner key
await token.transfer(recipientKey);

// split into two tokens (amount16 = the second piece's balance, 16 LE bytes).
// fundingSource is { tx, vout, key } — a UTXO the operation can spend for fees.
const [main, piece] = await token.split(keyA, keyB, amount16, fundingSource);

// merge `piece` back into `main` under a new owner key
const merged = await main.merge(piece, keyC, fundingSource);

// melt — spend the token output away (no token survives)
await merged.melt();
```

Every operation builds a real, script-valid Bitcoin transaction, verified by the `@bsv/sdk`
Spend engine before it is returned. **Broadcasting is the caller's responsibility** — the
library never touches the network. The signed `Transaction` is available as `token.tx`.

## Usage — recognising & verifying events (the scanner)

```ts
import {
  recognizeType,   // (lockingScript, expected?) -> TokenType | null
  verifyEvent,     // validate ONE event (a mint, a commit→settle pair, or a melt)
  verifyEvents,    // validate a BATCH of events end to end
} from "b017";

const type = recognizeType(tx.outputs[0].lockingScript); // "SimpleMultiBOLT" | "MinSimpleBOLT" | ... | null

// Inspect a batch of transactional events for authenticity. Recognises the type, pins the issuer
// across the whole batch, fingerprints every interface, then pairs the events: every commit must
// be matched by a settle that links back via parentOutpoint, and vice-versa.
const r = verifyEvents(txs, { trustedIssuerPubKey });
// -> { ok, type, issuerPubKeyHex, events: [{ kind: "transfer" | "split" | ..., txids }] }
```

Recognition is strict: a script matches only if **both** the leading data-push layout **and**
the sha256 of the static contract code match a registered type, so a tampered contract body or
a non-token script is rejected. An event is well-formed only if its txs pair up — a lone mint or
melt is a valid single-tx event, but an orphan settle or an unsettled commit is rejected.

A commit and its settle are bound **two** independent ways: the **token lineage** (the settle's
token `parentOutpoint` references the commit's token output — the binding the scanner asserts), and,
in general, a **funding chain** (the settle's funding input spends the commit's **change** output, so
the pair is chained at the satoshi level too). The funding chain is a construction property — a
caller can fund the settle from elsewhere — so the scanner does not require it.

## What's inside

The tree is organised by role: `tokens/` (token classes + their contract templates), `lib/` (the
reusable engine — shared primitives plus the **single**-token, **multi**-token, and **scanner**
sub-libraries).

| Path | Role |
| --- | --- |
| `src/tokens/MultiBOLT.ts` | `SimpleMultiBOLT` — the fungible token class (mint/transfer/split/merge/melt). |
| `src/tokens/BOLT.ts` | `BOLT` — the abstract token base class. |
| `src/tokens/templates/SimpleMulti.sx.template.ts` | Runtime lock/unlock/melt assembler for the fungible contract (compiled ASM suffix embedded). |
| `src/tokens/templates/MinSimple*.sx.template.ts` | Single-token (NFT) lock templates: `MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`. |
| `src/tokens/templates/pay2Proof.ts` | The `pay2Proof` UTXO template (the b017 marker proof output). |
| `src/lib/boltLib.ts` | Layout-agnostic primitives (`verifyTx`, `buildOutpoint`, `splitCtx`, …) shared by both streams. |
| `src/lib/single/` | Single-token (NFT) engine: `singleSpend` (unlock assembler) + `singleAncestor` (back-reach reconstruction). |
| `src/lib/multi/multiBoltLib.ts` | Fungible-token engine: ancestor reconstruction for `SimpleMultiBOLT`. |
| `src/lib/scanner/fingerprints.ts` | Per-type recognition (`recognizeType`, golden `recognizeP2P`) + the type `REGISTRY`. |
| `src/lib/scanner/verifyEvents.ts` | Off-chain event validator: batch verifier + per-event checker (`verifyEvents`, `verifyEvent`). |

> Naming note: the `SimpleMultiBOLT` **class** currently lives in `tokens/MultiBOLT.ts`.
> Resolving that file/class name mismatch is tracked in the ROADMAP.

The full public API is the named exports of [`src/index.ts`](src/index.ts).

## Testing & coverage

The whole codebase is unit-tested with [Vitest](https://vitest.dev). The `test/` tree mirrors `src/`
by concern (`test/tokens`, `test/templates`, `test/lib`, `test/lib`-level `scanner/`), with shared
fixtures in `test/fixtures` and helpers in `test/helpers`.

```
npm test               # 126 tests across 18 files
npm run test:coverage  # the same suite + a v8 coverage report (text to stdout, HTML in coverage/)
```

Latest run — **every source module is covered**, all above 98% statements:

| Metric | Coverage |
| --- | --- |
| Statements | **99.1%** (1737/1752) |
| Functions | **98.0%** (96/98) |
| Lines | **99.1%** |
| Branches | **95.1%** (645/678) |

The handful of uncovered branches are fail-safe guards (e.g. a `0xff` >4 GB script-length prefix, or a
type/issuer check an upstream fingerprint already guarantees), annotated `v8 ignore` with the reason inline.

What the suite verifies: each contract template is byte-faithful to its sx-compiled artifact and
spends under the `@bsv/sdk` Spend engine; the scanner's accept/reject decisions match the on-chain
contract over genuine lineages and every counterfeit class (including **strict golden p2Proof
fingerprinting** on commit proof outputs and settle proof inputs); and the library **fails closed**
on malformed input (bad hex, non-arrays, tampered markers) rather than throwing.

## Why Teranode + BOLT + Emergent Automation is the killer stablecoin platform

A stablecoin is only as good as the three layers underneath it: where it **settles**, how its
**integrity** is proven, and who can **operate** it. Most platforms nail one and compromise the other
two. This stack is the first to get all three right at once — because each layer removes the exact
bottleneck the next one needs gone.

**1. Teranode — unbounded settlement, fixed micro-fees.** Teranode is BSV's horizontally-scaling
node: throughput grows with hardware instead of hitting a protocol ceiling, so the base layer
absorbs millions of transactions per second at sub-cent, *non-auctioned* fees. A stablecoin meant to
be spent — not just held — needs settlement that never congests and never surprises you with a gas
spike. There is no block-space auction to front-run, no L2 to bridge into, no rollup withdrawal
delay. Final settlement *is* the base layer.

**2. BOLT — the asset that proves itself.** A BOLT token is a real Bitcoin UTXO whose entire validity
(issuer, lineage, owner, balance) is bound into a self-validating Script covenant via a dual
hash-commitment. Forging one means breaking SHA-256 or ECDSA — not out-voting a validator set or
finding a contract bug. This is the decisive difference from the two incumbent designs:

- **vs. account-based stablecoins (centralised ledgers):** no issuer database to trust, freeze, or
  reconcile. The coin carries its own proof; anyone can verify provenance from the chain.
- **vs. smart-contract stablecoins (global-state chains):** no shared global contract to congest, no
  re-entrancy/upgrade-key risk, no gas war. Each token validates **independently and in parallel** —
  which is exactly what lets Teranode's parallelism actually scale. Validation is *local and
  SPV-friendly*: this library's off-chain **scanner** (`verifyEvents`) reaches the same accept/reject
  verdict as the on-chain contract, with **strict golden p2Proof fingerprinting** on every commit
  proof output and settle proof input — so a holder verifies a payment with a light client, not a
  full chain replay. The 16-byte balance field carries denominations up to 2× Bitcoin's base limit,
  enough for any fiat unit at any scale.

**3. Emergent Automation — an economy that runs itself.** Because a BOLT token is a pure, stateless
UTXO with deterministic, self-contained validation and a single peer dependency (`@bsv/sdk`), it is
the ideal instrument for autonomous, machine-to-machine commerce. Software agents can mint, pay,
split, merge, and **verify** stablecoin value at machine speed with no custodian, no indexer, and no
human in the loop — every transfer is a self-proving *event* (a commit→settle pair) that another
agent can validate locally before acting on it. Provenance becomes a function call, not a trust
relationship.

**The combination is the point.** Settlement that never congests (Teranode) + an asset that proves
its own integrity without a trusted third party or a global-state chain (BOLT) + value that
autonomous agents can move and verify without intermediaries (Emergent Automation). A stablecoin
needs cheap unbounded settlement, trustless verifiable integrity, and programmable automation
*simultaneously* — and this is the only stack where all three reinforce each other instead of
trading off. That is what makes it not just *a* stablecoin platform, but the killer one.

## License

Open BSV License Version 5 — see [`LICENSE.txt`](LICENSE.txt).

<p align="center">
  <picture>
    <source media="(prefers-color-scheme: light)" srcset="docs/assets/bolt-logo-light.png">
    <source media="(prefers-color-scheme: dark)" srcset="docs/assets/bolt-logo.png">
    <img src="docs/assets/bolt-logo-light.png" alt="Bolt" width="420">
  </picture>
</p>
