# Token library refactor — learnings (how the pieces actually work)

Companion to `refactor-plan.md`. Captures the non-obvious facts the port relies on.

## ESM conversion (A1)
- `package.json`: `type: "module"` + `exports` map; `main`/`module`/`types` → `dist/index.*`.
- `tsconfig`: `module: NodeNext`, `moduleResolution: NodeNext`. NodeNext **requires explicit `.js`** on
  every relative import (TS2835 otherwise) — even though the source is `.ts`. The build patches them all.
  Watch single-quote imports (a double-quote-only regex misses `from '../x'`).
- The one `.sx.json` import uses an import attribute: `import x from "./x.json" with { type: "json" }`
  (needs `resolveJsonModule` + NodeNext). vitest (esbuild) resolves `.js`→`.ts` and the json attribute fine.
- Test runner is **vitest** (ESM-native), not jest. In an ESM test, `__dirname` is not defined —
  use `dirname(fileURLToPath(import.meta.url))`.

## De-elas (A1)
- `boltLib.ts`: deleted `verifyTx2` (elas `Interp`) + the `@elas_co/ts` import. `verifyTx` (@bsv/sdk
  `Spend`) is the sole verifier.
- `SimpleMultiBolt.ts`: dropped the `verifier === 'elas'` branch + the `Tx` import; `VerifierType` → `'bsv'`.

## Releasable (A2)
- `@bsv/sdk` as a **peerDependency** (`^1.8.11 || ^2.0.0`) + a devDependency (`file:../ts-sdk`). The peer
  makes the consumer provide ONE shared `@bsv/sdk` instance — this is what removes the demo's CJS bridge
  and the dual-instance trap. A `file:` spec in `dependencies` is unpublishable; in `devDependencies` it's
  fine. ts-sdk is the **vendored published `@bsv/sdk@1.8.11`** (standard README, real npm version), not a
  fork — so the peer range targets the public package.

## Templates from pre-compiled artifacts (Lane B)
- The artifact `sx/bolt/production/artifacts/<Token>.json` IS the sx compiler output. Its
  `lockingRecombinants` (and `unlockingRecombinants`) are mostly **numbers** (arg placeholders) with the
  **last string entry** being the **static contract bytes in HEX**. That hex IS the golden for lock
  byte-fidelity — no sx runner needed for the lock.
- Template lock = `writeBin(<each dynamic arg>)` chunks + `Script.fromASM(toASM(suffixHex))` chunks.
  `writeBin([0x00])` emits a 1-byte push (not OP_0). The build script (`scripts/build-min-simple-bolt.mjs`)
  reads the artifact, `Script.fromHex(suffixHex).toASM()`, and patches `LOCK_SCRIPT_SUFFIX` into the template
  (same pattern as `scripts/build-contract.mjs` for SimpleMultiBolt).
- MinSimpleBolt lock layout: `pubKeyHash[20] · pubKeyHashCommitment[20] · txoType[1] · parentOutpoint[36]
  · grandparentOutpoint[36] · issuerPubKey[33]` (issuerPubKey always last). Genesis defaults:
  commitment=zeros[20], txoType=[0x00], parent/grandparent=zeros[36].

## The crucial subtlety: a mint does NOT execute the bolt lock
- A mint's inputs are P2PKH **funding** — `verifyTx` on a mint only validates the funding spend, **not**
  the bolt contract. The contract is exercised only when the bolt is **spent** (a transfer commit/settle).
- So the lock template + a mint proves byte-fidelity + well-formedness, but the **spend/unlock** (the 37-arg
  ancestor-reconstruction + ctx path — see `SimpleMultiBolt.sx.template.ts` `unlock()`) is what actually
  proves the contract works. That's the hard part, and it lands with B2 (the discount coupon's commit/settle).

## Generating an sx golden (full-tx byte target)
- `node --import tsx spv-demo-wapps/libs/bolt/src/sx-runner.mjs` is a stdin→stdout JSON child process:
  request `{ contract, simPlan, seedFundTxHex? }` → result `{ txs: [{ idx, hex, txid }] }`. It imports
  `sx/src` + elas internally and routes console noise to stderr (stdout stays pure JSON).
- simPlans come from `spv-demo-wapps/libs/bolt/src/sim-json.builder.ts`: `buildGenesisMint`
  (identity → `[mint]`), `buildTransferLifecycle` (`[mint, commit, settle]`), `buildCouponRoundTrip`
  (`[mint, c1, s1, c2, s2, c3, s3]`). Contract source map is in `sx-runner.mjs` `CONTRACT_SRC`.
- Full-tx byte-equality additionally requires matching sx's synthetic funding (TESTING=true fake funding) —
  that's the funding-match work the SimpleMultiBolt port already solved (`seedFundTx` hook).

## Lane B — token LOCK templates (B1–B4)
- Each NFT template (MinSimpleBolt / Discount / Balance) = `writeBin(<dynamic args>)` chunks +
  `Script.fromASM(LOCK_SCRIPT_SUFFIX)`, patched from the production artifact's last-string recombinant by
  `scripts/build-min-simple-*.mjs`. Layouts: identity `[20,20,1,36,36,33]`, discount
  `[1,20,20,1,36,36,33]` (discount FIRST = discount-before-amount), balance `[16,20,20,1,36,36,33]`.
  issuerPubKey is ALWAYS the last 33-byte push.
- B-lane test pattern (the safety net): parse the sx golden's mint vout0, extract its OWN data-push args,
  rebuild via the template, assert `rebuilt.toHex() === goldLock.toHex()` AND the static suffix === the
  artifact recombinant. Byte-fidelity to the actual sx output, no sx runner at test time.
- `MinimumSimpleBalanceBolt` (sx source name) and `MinSimpleBalanceBolt.json` (artifact) are the SAME
  contract — verified by suffix byte-equality (1127 B). The general golden generator is
  `spv-demo-wapps/libs/bolt/src/gen-nft-golden.ts <sxContract> <valueArg|-> <valueHex|-> <out>`.
- B4 fingerprint = `{ pushLengths, suffixHash = sha256(staticCode) }`. `recognizeType(lock)` requires BOTH
  the leading-push layout AND the suffix hash to match → a tampered body or a non-token is rejected.

## Lane C — the scanner (verifyTokenChain)
- txoType conventions DIFFER: NFT settle = `00` (post-commit resting state), commit = `21`;
  SimpleMultiBolt settle = `20`. So the UNIVERSAL settle signal is the **parentOutpoint link** (settle
  token's parentOutpoint → the commit token's outpoint), not the txoType.
- Outpoint bytes = 32-byte txid in internal order (reverse for the display txid) + 4-byte vout LE.
- Output classes: token (recognizeType) · p2pb = `b017 OP_EQUALVERIFY` + standard P2PKH (7 chunks) ·
  p2pkh = standard 5-chunk · else "other". C4 rejects any "other" (the "nothing uninspected" rule) and
  asserts the per-role shape (mint/commit/settle) across EVERY input and output.
- FIELDS (per-type push indices) live in verifyTokenChain.ts: parent/grandparent/issuer are the last 3
  pushes for every type; the txoType index varies (Min* = dataPushCount−4; SMB = 6, outputIndexN at 7).
- The scanner READS txs — it does NOT need the spend/unlock builder (that's why Lane C shipped before B2b).
  Genuine-chain fixtures = the sx goldens; SPV/BEEF on-chain presence is a composable leg the caller supplies.

## Lane B2b — NFT spend/unlock (SOLVED for simple transfer; ancestor path = B2b-2)
- **DONE:** `src/templates/nftSpend.ts` + `unlock()` on all 3 NFT templates build VALID mint->commit->settle
  spends on the @bsv/sdk Spend engine — verified live in `test/min-nft-spend.test.ts` (identity / discount /
  balance, 3/3). Two bugs fixed:
  1. **Truncated `UNLOCK_SCRIPT_SUFFIX`** — the suffix was pasted by hand and lost 6 ops in the repetitive
     `OP_SWAP OP_CAT` / `OP_1 OP_SPLIT` chain (337 vs 343 chunks), which corrupted the optimal-sighash
     s-computation while leaving the preimage assembly intact (hence it reached the final checksig and failed
     only there). FIX: patch the suffix from the artifact's `unlockingRecombinants` via the build scripts
     (`build-min-simple-*.mjs` now patch BOTH lock and unlock suffixes). NOTE: `Script.fromHex(hex).toASM()`
     round-trips faithfully here (343->343); the breakage was purely the manual paste.
  2. **Tx version must be >= 2** — the contract asserts `version >= 2` from the preimage (`OP_9 OP_PICK OP_2
     OP_GREATERTHANOREQUAL OP_VERIFY` at lock PC ~383). `new Transaction()` defaults to v1; set `tx.version = 2`.
- The investigation below is retained because the *diagnostics* are reusable; the "deterministic blocker"
  framing was superseded once the suffix truncation was found.

### B2b-2 — ancestor reconstruction (DONE)
- A settle reaching back over a chain ≥4 txs (a coupon's 2nd hop: settleTx2 at txIdx 4) carries the 26
  ancestor pieces [0..25] reconstructing the commit **two hops back** (`prevTxs[txIdx-3]`), where the current
  owner received the token. `src/templates/nftAncestor.ts` `nftAncestorPieces(ancestorTx, leadingValuePushes)`
  extracts them: ver/locktime/sequences; the ancestor's in[0] bolt-spend args (fund/change/beneficiary/sig/
  pubkey/ctxHeader/ctxFooter via the 37-arg unlock chunks 26–31,35); the ancestor's **spent-lock** fields
  (pkh/commit/txoType/parent/gp) by `Script.fromBinary(unlock.chunks[34])` then skipping `leadingValuePushes`;
  the ancestor's **output token** fields from `outputs[0]` chunks; in[1] funding outpoint/script/seq; and the
  change `outputs[2]`. `leadingValuePushes` = 0 identity / 1 discount+balance.
- Only the back-reaching SETTLE carries the block; the intervening COMMIT (txIdx odd) is empty (verified
  against the golden). The settle has **3 inputs**: [bolt, p2pb-proof, funding] — the p2pb proof (the commit's
  vout1 the owner received 2 hops back) is spent with `[sig, pubkey, push(b017)]` by that owner.
- Golden truth = the canonical `sx/tests/bolt/simple/zeroData/MinSimpleDiscountBolt.sim.json` (its `settleTx2`
  IS the ancestor case); derive fixtures from it via `spv-demo-wapps/libs/bolt/src/gen-sx-golden.ts`. The
  coupon's **3rd hop** (commit3, txIdx 5) is a known sx WIP (vinIdx out-of-range) — bucket "repurchase" stays WIP.

### Investigation trail (the deterministic blocker — root-caused)
- The 3 NFT contracts (MinSimpleBolt/Discount/Balance) share an **identical 37-arg unlock layout** (M-I/M-H
  stripped: no mintData/issuerPubKey/genesisOutpoint/miscData). For the simple mint→commit→settle lifecycle
  the **first 26 args (the ancestor block) are empty** (verified from the golden); the ancestor-reconstruction
  path only fires for chains ≥4 txs (coupon round-trips). `src/templates/nftSpend.ts` implements the simple
  path: 26 empty + fundOutpoint + changeOutput + beneficiaryPubKeyHash + sig + pubKey + 6 ctx pieces from
  `splitCtx(ctx,2)`, OCS subscript = `OP_CHECKSIGVERIFY OP_ENDIF` + lock (the combined `ad68` tail, like SMB;
  golden confirms `ctxCodeUnlockScriptCode = ad68`). One issuer key drives the whole lifecycle (the recipient
  pkh is just committed data; spender pkh = current owner = issuer for both commit and settle).
- The unlock **executes the ENTIRE contract** (every output + lineage reconstruction passes; reaches the final
  introspection checksig at PC 372) and fails ONLY there. Findings, in order of certainty:
  - The contract's final checksig is an **OP_PUSH_TX optimal-sighash r-puzzle**: fixed `r = 79be667e…`
    (= x(G), k=1), fixed pubkey `038ff8…`, assembling `s = sighash + 1` — **C = s − z = 1**, confirmed by
    recovering C from the genuine golden (`s_golden = z_golden + 1` exactly).
  - **The 6 ctx pieces are byte-identical to the golden's** (verified: `splitCtx(format(ad68+lock),2)` ==
    the golden's pushed chunks 31..36). **The preimage the contract assembles is byte-identical to the engine
    preimage** — proven by *simulating the unlock-suffix assembly opcodes* (`OP_5 PICK/ROLL … CAT …`) on my
    real pushed args and getting the exact 1441 B `OP_HASH256` input == `format(subscript = ad68+lock)`. So the
    preimage/pieces are **NOT** the bug; `HASH256` yields the correct sighash.
  - Yet the contract's assembled `s` ≠ `sighash + 1` for my tx (it comes out a deterministic ~1-byte rotation),
    so the engine rejects it. The divergence is therefore inside the contract's **`s`-value
    serialization** (the `00 OP_CAT OP_BIN2NUM OP_1 OP_ADD` → `OP_0NOTEQUAL OP_SPLIT ×32` → reverse → DER
    framing), responding to my specific sighash bytes. **Not low-S** (`requireLowSSignatures = false`),
    **not findAndDelete** (pre==post subscript len), **not nLockTime-grindable** (2000 tries fail), and **the sx
    builder does NOT grind** (no retry/massage loop in `boltLib.tsx`/`tx-builder.ts`/`simulator.js`).
  - **Decisive lever for next time:** the `no-elas` SMB lifecycle builds txs LIVE (not goldens) and passes the
    SAME optimal-sighash magic on the same bsv engine — so this is **NFT-specific**, not a universal "must
    grind". The remaining work is to find what the SMB live path does that the NFT path doesn't. Concrete next
    step (the proven SMB-port method): build the identical mint→commit→settle via `SxSimulator` with the SAME
    keys/funding, confirm the sx-built commit passes bsv `Spend`, then **byte-diff its input[0] unlock against
    mine arg-by-arg** (`sim.simTxs` technique). The first differing byte in a structural arg is the bug.
- Status: `nftSpend.ts` + the wired `unlock()` are correct in LAYOUT, ctx pieces, and assembled preimage;
  the lifecycle test `test/min-nft-spend.test.ts` is **`it.skip`** (executable spec). Do NOT wire into Lane D
  until green. Reusable diagnostics that nailed the localization: instrument the vendored `Spend.ts` OP_CHECKSIG
  to log `{ctx, fSuccess, preLen, bufSig, bufPubkey}` (vitest loads `ts-sdk/dist/esm`, NOT src — patch dist or
  src+rebuild); recover C from the golden; simulate the suffix assembly opcodes in JS to capture the HASH256 input.

## Engine dependency caveat (PR #195 / the peer range)
- The vendored `ts-sdk/src/script/Spend.ts` is **NOT pristine `@bsv/sdk@1.8.11`** — it carries a hand-rolled
  patch (~L798–805) so that, in `UnlockingScript` context, the CHECKSIG subscript = post-OP_CODESEPARATOR
  unlock chunks **concat the full locking script**. This is what makes BOLT's OP_PUSH_TX introspection pass.
  Upstream **PR #195** (bsv-blockchain/ts-stack) is the canonical fix for the same thing (lands at ~L1216 with
  the standard `slice(lastCodeSeparator===null?0:+1)` + a `Spend.codeseparator.test.ts`). The vendored copy is
  functionally equivalent for the BOLT happy path but is an earlier, differently-structured variant.
- **Consequence for A2's "releasable" claim:** the peerDependency `@bsv/sdk ^1.8.11 || ^2.0.0` targets the
  *public* package, which has neither the hand-patch nor (in 1.8.11) PR #195 — so BOLT **spends** would fail on
  a stock install. The peer range must be pinned to the first published release that contains PR #195 before
  the spend path can be called releasable. (Lock byte-fidelity + the scanner are unaffected — they don't spend.)
