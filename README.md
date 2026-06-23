# b017

> **Status: `0.0.0-b` (beta).** The API is working and fully tested (43/43) but may still
> change before `0.1.0`. See [`docs/ROADMAP.md`](docs/ROADMAP.md) for what's next.

Standalone TypeScript library for **BOLT layer-1 tokens** on BSV — the fungible
**SimpleMultiBOLT** (16-byte balance; mint / transfer / split / merge / melt), a family of
minimal **NFT** templates, and an off-chain **scanner** that recognises and verifies BOLT
token chains. The `.sx` contracts are **pre-compiled and embedded**; there is **no sx
compiler at runtime**. The only runtime dependency is a peer `@bsv/sdk`.

**Why these tokens can't be counterfeited:** the token state (issuer, lineage, owner, balance)
is bound into a self-validating Bitcoin Script covenant via a dual hash-commitment, so forging
a token would require breaking SHA-256 or ECDSA. See [`docs/unforgeability.md`](docs/unforgeability.md)
for the full argument and the forgery tests that demonstrate it.

## Install / build

```
npm install
npm run build      # clean + tsc -> dist/ (JS + .d.ts)
npm test           # vitest (43 tests)
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

## Usage — recognising & verifying tokens (the scanner)

```ts
import {
  recognizeType,        // (lockingScript, expected?) -> TokenType | null
  verifyTokenChain,     // validate a BOLT lineage end to end
  verifyEvent,          // classify a single commit/settle token event
} from "b017";

const type = recognizeType(tx.outputs[0].lockingScript); // "SimpleMultiBOLT" | "MinSimpleBOLT" | ... | null
```

Recognition is strict: a script matches only if **both** the leading data-push layout **and**
the sha256 of the static contract code match a registered type, so a tampered contract body or
a non-token script is rejected.

## What's inside

| Path | Role |
| --- | --- |
| `src/tokens/MultiBOLT.ts` | `SimpleMultiBOLT` — the fungible token class (mint/transfer/split/merge/melt). |
| `src/tokens/BOLT.ts` | `BOLT` — the abstract token base class. |
| `src/templates/SimpleMulti.sx.template.ts` | Runtime lock/unlock/melt assembler for the fungible contract (compiled ASM suffix embedded). |
| `src/templates/MinSimple*.sx.template.ts` | NFT lock templates: `MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`. |
| `src/templates/pay2Proof.ts` | The `pay2Proof` UTXO template (P2PKH + b017 proof output). |
| `src/lib/boltLib.ts` | Layout-agnostic helpers (`verifyTx`, `buildOutpoint`, …). |
| `src/scan/fingerprints.ts` | Per-type recognition primitive + the type `REGISTRY`. |
| `src/scan/verifyTokenChain.ts` | Off-chain chain validator + per-event checker (`verifyTokenChain`, `verifyEvent`). |

> Naming note: the `SimpleMultiBOLT` **class** currently lives in `tokens/MultiBOLT.ts`.
> Resolving that file/class name mismatch is tracked in the ROADMAP.

The full public API is the named exports of [`src/index.ts`](src/index.ts).

## Regenerating the contracts (maintainers only)

The compiled artifacts + template suffixes are produced once from the BOLT `sx` toolchain:

```
npm run build:contract     # build-time only; consumers never need this
```

The `scripts/` folder holds these regeneration tools. They are **not** part of `npm run build`
(`tsconfig` excludes them) and are **not** published (the tarball ships only `dist/`). They
require the `sx` compiler to be present at a sibling `../sx` path — that toolchain is **not**
vendored in this repo, so `build:contract` only runs in a checkout where `../sx` exists.

Consumers never need any of this — the package ships the pre-compiled templates.

## License

Open BSV License Version 5 — see [`LICENSE.txt`](LICENSE.txt).
