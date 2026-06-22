# b017

Standalone TypeScript library for **SimpleMultiBolt** — the optimised fungible BOLT layer-1 token
(16-byte balance; mint / transfer / split / merge / melt). The `.sx` contract is **pre-compiled**;
there is **no sx compiler at runtime**. Runtime deps: `@bsv/sdk` and `@elas_co/ts` only.

## Install / build

```
npm install
npm run build      # -> dist/ (JS + .d.ts)
```

## Usage

```ts
import { SimpleMultiBOLT } from "b017";
import { PrivateKey } from "@bsv/sdk";

const issuer = PrivateKey.fromRandom();
const token = await new SimpleMultiBOLT().mint(issuer, fundingTx, "", balance16);  // 16-byte LE balance
await token.transfer(recipientKey);                 // commit + settle
const [main, piece] = await token.split(keyA, keyB, amount16, fundingSource);
const merged = await main.merge(piece, keyC, fundingSource);
await merged.melt();
```

Every operation builds a real, script-valid Bitcoin transaction (verified by both the `@bsv/sdk`
Spend engine and the `@elas_co/ts` Interp). Broadcasting is the caller's responsibility.

## What's inside

- `src/SimpleMultiBolt.ts` — the token class.
- `src/multi/SimpleMultiBolt.sx.template.ts` — runtime lock/unlock/melt assembler (compiled ASM
  suffix embedded; 11 lock args, 198 unlock args).
- `src/multi/boltLibSMB.ts` — SimpleMultiBolt ancestor reconstruction.
- `src/boltLib.ts` — layout-agnostic helpers (verifyTx, verifyTx2, buildOutpoint, buildChangeOutput,
  createSignature, splitCtx).
- `src/contracts/SimpleMultiBolt.sx.json` — the shipped compiled contract artifact.

## Regenerating the contract (maintainers only)

The compiled artifact + template suffix are produced once from `sx/tests/bolt/multi/SimpleMultiBolt.sx`:

```
npm run build:contract     # uses the sibling sx/ toolchain (build-time only)
```

Consumers never need this — the package ships the compiled output.
