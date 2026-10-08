# b017; Bitcoin Original Layer-1 Token Protocol

[![CI](https://github.com/BOLT-Association/b017/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/BOLT-Association/b017/actions/workflows/ci.yml)
[![coverage](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/BOLT-Association/b017/badges/coverage.json)](https://github.com/BOLT-Association/b017/actions/workflows/ci.yml)
[![npm version](https://img.shields.io/npm/v/b017.svg?logo=npm)](https://www.npmjs.com/package/b017)
[![TypeScript](https://img.shields.io/badge/TypeScript-5.7-3178C6?logo=typescript&logoColor=white)](https://www.typescriptlang.org/)

> **Status: `0.0.0-b2` (beta).** Considered Live-Network-Testing Ready (Production next). The API is working and fully tested
> (625/625 unit tests, **99% statement / 100% function / 98% branch coverage**) but may still change before `0.1.0`. See
> [`docs/ROADMAP.md`](docs/ROADMAP.md) for what's next.

Standalone TypeScript library for the **Bitcoin Original Layer-1 Token** protocol on BSV — a fungible & optimised
**SimpleMultiBOLT** (16-byte balance (x2 Bitcoin's base layer limit); mint / transfer / split / merge / melt), a minimal
identity **NFT** (`MinSimpleBOLT`, zero-funding), its credential variant `AuthBOLT` (an arbitrary data field `authOrMiscData` of up to 75 bytes), and an off-chain **scanner** that recognises and verifies
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

This is **third-party per-token unforgeability**: each unit is internally well-formed and traces
to an issuer-signed mint. It is *not* a claim about **supply-honesty** (an issuer can mint many
independent genesis tokens — reserve/cap trust is an issuer matter) or **network-level security**
(reorg resistance inherits honest-majority hash power). See [`formal-proof.md`](docs/formal-proof.md)
§1.6 for the exact boundary.

## Install / build

```
npm install
npm run build          # clean + tsc -> dist/ (JS + .d.ts)
npm test               # vitest (625 tests)
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
  verifyEvent,     // validate ONE event (a commit→settle pair, or a melt) - same verdict as verifyEvents
  verifyEvents,    // validate a BATCH of events end to end (offline)
  verifyAndBroadcast, // verifyEvents + your broadcast of the batch's anchor (settle N-1 / the mint)
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
a non-token script is rejected. An event is well-formed only if its txs pair up - a melt is a
valid single-tx event (standing on the settle it spends, its anchor), but an orphan settle or an unsettled commit is
rejected, by `verifyEvent` as well as `verifyEvents`. A **mint** is accepted only
with a commit in the same event/batch that spends it; a lone mint returns `{ ok: false, unauthenticated: true }`
(see "Receiving a token off-chain" below). The scanner also **executes** every input whose source tx is supplied (the
covenant and the signatures, on the `@bsv/sdk` Spend engine), because structure alone cannot tell a forged commit
from a real one and off-chain txs have not been validated by a node; a failure returns `ok: false` with
`script execution failed: tx <id> input <n>: ...`. **Every input's source tx must be supplied** (attached as
`sourceTransaction`, or another tx in the batch, or inside a BEEF); an input whose source is missing is refused
(`source tx <id> of tx <id> input <n> was not supplied`). Send the package as **BEEF**: each event tx may be a
Transaction, raw hex, or Atomic BEEF over BEEF V2 (hex / bytes), whose subject is the tx; `toAtomicBeef(tx)` /
`fromBeef(bytes)` / `isBeef(x)` are exported. BEEF V1 (BRC-62) and a BEEF that is not self-contained (an unproven tx
that does not have all its inputs in the BEEF) are refused. The result's `sources` lists the txs the event spends that
are not part of it, each with `proven` (it carries a BUMP). The scanner checks a BUMP against a block header only
for an **anchor**, and only when you supply your headers (`isKnownBlockRoot`, or a `chainTracker` to
`verifyAndBroadcast`). The BUMPs of the other `sources` are **not** checked: verify those with your `ChainTracker`
(`Beef.verify` / `merklePath.verify`).

A commit and its settle are bound **two** independent ways: the **token lineage** (the settle's
token `parentOutpoint` references the commit's token output — the binding the scanner asserts), and,
in general, a **funding chain** (the settle's funding input spends the commit's **change** output, so
the pair is chained at the satoshi level too). The funding chain is a construction property — a
caller can fund the settle from elsewhere — so the scanner does not require it.

### Receiving a token off-chain (SPV): what must travel with it

Sending someone a **minted** token over SPV does not prove that the sender holds the issuer key. A mint is
just an output whose lock names an `issuerPubKey`; anyone can create one naming anybody's key (so
`verifyEvents` refuses a lone mint as `unauthenticated`). The issuer guard runs when the
genesis token is first **spent**, so the proof is the first **commit**:

- **Ownership of a minted token:** the mint must come with a **commit tx spending it**, signed by the issuer
  key. This holds whether or not the commit is funded (an unfunded commit is SPV-only and never mined, but it
  still executes the covenant, which demands `issuerPubKey == the signer` at genesis). `verifyEvents` runs that
  covenant, so a commit forged by a stranger is refused on execution.
- **A token carrying `authOrMiscData` (`AuthBOLT`):** the value is created in a commit but authenticated only
  by the **settle**, which rebuilds its grandparent commit and binds the value to that commit's txid. The commit's
  own signature does **not** cover it. So the **signed commit and settle travel together as the data package**;
  a commit alone, or a settle without its commit, does not authenticate the data.
- A later hop to a new holder repeats the pattern: commit + settle (and the p2pb proof input a back-reaching
  settle spends), unfunded or funded, are what the recipient verifies.
- **The anchor travels too, and is broadcast.** The anchor is the token tx the package stands on: the settle before
  its first commit (settle N-1), or the mint at genesis. So a package is `[mint, c1, s1]` or `[sN-1, cN, sN]`.
  `verifyEvents` validates the anchor like an event tx (fingerprint, issuer, structure, script execution) and names
  it in `anchors`, but it is offline and its execution reaches the anchor's own inputs only. Use
  `verifyAndBroadcast(txs, broadcastAnchor)`: it runs `verifyEvents`, then your broadcaster sends each anchor and
  reports `accepted`, `already-seen` or `rejected`. The anchor must be a tx the network has seen and will therefore
  mine (or has already mined): that is what shows the history behind it is real. A rejected anchor, a throwing
  broadcaster or an unknown status is `ok: false`. The events standing on the anchor need not be broadcast: they can
  stay off chain, and be funded and broadcast only when the receiver, the sender or both require it.
- **An unfunded anchor needs an SPV proof.** An anchor with no funding input pays no fee, so the network has no
  reason to mine it and seeing it proves nothing. Such an anchor can still be mined (a friendly miner), so it is
  accepted only once it has been: it must carry a merkle path into a block header you know. Pass your headers as
  `isKnownBlockRoot: (merkleRoot, height) => boolean`, or hand `verifyAndBroadcast` a `chainTracker` (the
  `@bsv/sdk` ChainTracker shape). Without a verified proof the batch is refused (`unfunded anchor <id>: ...`), by
  `verifyEvents`, `verifyEvent` and `verifyAndBroadcast` alike, and nothing is broadcast. Unfunded **events** on a
  funded anchor are unaffected.
- **A header-proven anchor is taken as mined.** Any anchor (funded or not) whose merkle path proves it into a header
  you know was validated by consensus: the scanner does not re-execute its inputs and does not need its sources. That
  is what lets a mined anchor travel as BEEF, which stops at proven txs. Your header lookup is the trust root here:
  answer `true` only for real block headers. A merkle path with no known header changes nothing (the anchor is
  executed like any other, and its sources must be supplied). Only anchors get this; event txs are always executed.
- **Value conservation is checked.** An **anchor** whose outputs exceed its inputs is refused (`anchor <id> creates
  value ...`): no node accepts that. An **event** tx that does so is not refused, only reported in
  `offChainOnly: [{ txid, inputSats, outputSats }]`: a commit / settle that is never broadcast (an `AuthBOLT` event
  certifying auth data) is valid off chain, it just cannot be broadcast as built. Pass `requireBroadcastable: true`
  to refuse such a batch instead.
- **`SimpleMultiBOLT` requires funding and change.** Zero-funding hops are for the NFT types (`MinSimpleBOLT`,
  `AuthBOLT`) only; a MultiBOLT settle never has to rebuild an unfunded commit.
- **Send it as BEEF** (Atomic BEEF over BEEF V2, `toAtomicBeef(tx)`): each tx travels with the txs it spends, back to
  txs a block has proven (BUMP). The recipient needs every source to execute the scripts, so a bare tx is refused.

## What's inside

The tree is organised by role: `tokens/` (token classes + their contract templates), `lib/` (the
reusable engine — shared primitives plus the **single**-token, **multi**-token, and **scanner**
sub-libraries).

| Path | Role |
| --- | --- |
| `src/tokens/MultiBOLT.ts` | `SimpleMultiBOLT` — the fungible token class (mint/transfer/split/merge/melt). |
| `src/tokens/BOLT.ts` | `BOLT` — the abstract token base class. |
| `src/tokens/templates/SimpleMulti.sx.template.ts` | Runtime lock/unlock/melt assembler for the fungible contract (compiled ASM suffix embedded). |
| `src/tokens/templates/MinSimple.sx.template.ts` | Single-token (NFT) lock / unlock / melt template: `MinSimpleBOLT` (identity; a commit or settle may carry no funding input and change is optional, so p2p / SPV hops never need to be mined). |
| `src/tokens/templates/AuthBolt.sx.template.ts` | `AuthBOLT`: carries an arbitrary data field `authOrMiscData` (<= 75 B, a direct push) created in a commit and authenticated by the next settle. Same lock layout as `MinSimpleBOLT`; told apart by its suffix fingerprint. Lock / unlock / melt. |
| `src/tokens/templates/pay2Proof.ts` | The `pay2Proof` UTXO template (the b017 marker proof output). |
| `src/lib/boltLib.ts` | Layout-agnostic primitives (`verifyTx`, `buildOutpoint`, `splitCtx`, …) shared by both streams. |
| `src/lib/single/` | Single-token (NFT) engine: `singleSpend` (unlock assembler) + `singleAncestor` (back-reach reconstruction). |
| `src/lib/multi/multiBoltLib.ts` | Fungible-token engine: ancestor reconstruction for `SimpleMultiBOLT`. |
| `src/lib/scanner/fingerprints.ts` | Per-type recognition (`recognizeType`, golden `recognizeP2P`) + the type `REGISTRY`. |
| `src/lib/scanner/verifyEvents.ts` | Off-chain event validator: batch verifier, per-event checker, and the anchor broadcast wrapper (`verifyEvents`, `verifyEvent`, `verifyAndBroadcast`). |
| `src/lib/scanner/beef.ts` | The off-chain data package: Atomic BEEF over BEEF V2 (`toAtomicBeef`, `fromBeef`, `isBeef`). |

> Naming note: the `SimpleMultiBOLT` **class** currently lives in `tokens/MultiBOLT.ts`.
> Resolving that file/class name mismatch is tracked in the ROADMAP.

The full public API is the named exports of [`src/index.ts`](src/index.ts).

## Testing & coverage

The whole codebase is unit-tested with [Vitest](https://vitest.dev). The `test/` tree mirrors `src/`
by concern (`test/tokens`, `test/templates`, `test/lib`, `test/scanner`), with shared
fixtures in `test/fixtures` and helpers in `test/helpers`.

```
npm test               # 625 tests across 34 files
npm run test:coverage  # the same suite + a v8 coverage report (text to stdout, HTML in coverage/)
```

Latest run — **every source module is covered**, all above 98% statements:

| Metric | Coverage |
| --- | --- |
| Statements | **99.7%** (2060/2066) |
| Functions | **100.0%** (125/125) |
| Lines | **99.7%** |
| Branches | **98.3%** (1028/1045) |

Fail-safe guards that cannot fire (e.g. a `0xff` >4 GB script-length prefix, or a type/issuer check an
upstream fingerprint already guarantees) are annotated `v8 ignore` with the reason inline. Most of the
remaining gaps are also unreachable: `@bsv/sdk`'s `Spend.validate()` throws rather than returning
`false`, and `tx.id()` fails on a missing unlocking script before `verifyTx`'s own guard runs.

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

**What is proven vs. assumed.** To be precise about the integrity layer: what the BOLT covenant
*proves* (see [`docs/formal-proof.md`](docs/formal-proof.md)) is **third-party per-token
unforgeability** — authenticity, ownership, per-genesis balance conservation, and state-machine
integrity — plus local, SPV-friendly verification of all of the above. Two things this layer does
*not* prove, and that a stablecoin still depends on, are **trust assumptions, not theorems**:
**issuer supply-honesty** (the protocol stops anyone from forging *a* token, but an issuer can
mint as many genesis tokens as it likes — matching the float to a reserve is an issuer/governance
matter) and **honest-majority settlement** (final settlement is only as immutable as the chain's
hash power). The stack is designed so those two assumptions are the *only* ones left standing —
but they are assumptions, and §1.6 of the proof says exactly where the proven part ends.

## License

Open BSV License Version 5 — see [`LICENSE.txt`](LICENSE.txt).

<p align="center">
  <picture>
    <source media="(prefers-color-scheme: light)" srcset="docs/assets/bolt-logo-light.png">
    <source media="(prefers-color-scheme: dark)" srcset="docs/assets/bolt-logo.png">
    <img src="docs/assets/bolt-logo-light.png" alt="Bolt" width="420">
  </picture>
</p>
