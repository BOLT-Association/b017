# Token library refactor — drop elas_ts, release simplemultibolt (templates + shared scanner)
# TDD backlog for ralph-loop execution (one task / iteration: RED → GREEN → commit)

## Progress (updated 2026-06-21, branch `bolt-integration`)
- **A1 ✓** `2376d0b` — simplemultibolt → ESM (NodeNext) + vitest; dropped `@elas_co/ts`; `verifyTx`
  (`@bsv/sdk` `Spend`) is the sole verifier. ESM kills the demo's CJS `smb-bridge` + dual-instance trap.
- **A2 ✓** `88cf012` — publishable: `@bsv/sdk` is a peerDependency (`^1.8.11 || ^2.0.0`) + dev
  `file:../ts-sdk`; no `file:` runtime dep; `npm pack` clean. ts-sdk = vendored published `@bsv/sdk@1.8.11`.
- **B1 ✓** `f6b5e3e` — MinSimpleBolt LOCK template + `scripts/build-min-simple-bolt.mjs`; static suffix
  byte-identical to the production artifact (the sx-compiled contract); mint verifyTx-green. Suite 10/10.
- **A3 deferred** (plan-sanctioned optional) — ts-bolt is a dev workspace (no package name/version, like
  sx); its elas `verifyTx2` stays as a dev cross-check vs bsv `Spend`. 9-file footprint if ever wanted.
- **B2a ✓** `aeacf8e` — MinSimpleDiscountBolt LOCK (discount-first); rebuilt lock byte-equals the sx golden mint.
- **B3 ✓** `72aa879` — MinSimpleBalanceBolt LOCK (balance[16] first); `MinimumSimpleBalanceBolt` ≡ the artifact.
- **B4 ✓** `511778a` — `src/scan/fingerprints.ts`: per-type `{pushLengths, suffixHash}` for all 4 types;
  `recognizeType` + `issuerPubKeyOf`. **Lane B complete.**
- **Lane C ✓** `8c323c1` / `f667ef0` / `0821f15` — `verifyTokenChain`: C2 issuer + C3 commit/settle lineage +
  C4 full every-input/output arrangement + C5 parity. **The shared scanner is done; full suite 33/33.**
- **B2b ✓ (simple transfer)** — the 37-arg NFT spend/unlock. `src/templates/nftSpend.ts` + `unlock()` on all
  3 NFT templates build VALID mint→commit→settle spends on the @bsv/sdk Spend engine (live test
  `test/min-nft-spend.test.ts`, 3/3). Two fixes: the `UNLOCK_SCRIPT_SUFFIX` was hand-paste-truncated (337 vs
  343 ops → corrupted the optimal-sighash s-computation) — now patched from the artifact by the build scripts
  (they patch BOTH lock+unlock); and the spending tx must be **version >= 2** (contract assertion). See
  `refactor-learnings.md` → B2b.
- **B2b-2 ✓ (ancestor reconstruction)** — `src/templates/nftAncestor.ts` reconstructs the 26 ancestor pieces
  for a settle reaching back over a chain ≥4 txs (coupon 2nd hop); `nftSpend` populates them. Validated two
  ways: `nftAncestorPieces` reproduces the canonical sx golden's settleTx2 block byte-for-byte
  (`test/nft-ancestor.test.ts`), and a live coupon mint→c1→s1→c2→s2 passes `verifyTx`
  (`test/min-nft-coupon.test.ts`). Golden truth = `sx/tests/bolt/simple/zeroData/MinSimpleDiscountBolt.sim.json`
  (its settleTx2 is the ancestor case); the fixture derives from it via `spv-demo-wapps/.../gen-sx-golden.ts`.
  NOTE: the coupon's **3rd hop** (commit3) is a known sx WIP, so the bucket "repurchase" leg stays WIP.
- **Engine caveat (PR #195):** vendored `ts-sdk` is patched at `Spend.ts` (unlock-context CHECKSIG concats the
  locking script) — NOT pristine `@bsv/sdk@1.8.11`. The A2 peer range must be pinned to the first published
  release carrying PR #195 before the **spend** path is releasable (lock + scanner unaffected).
- **Next** — Lane D (rewire the wapps + A′ off sx onto the templates + `verifyTokenChain`; fix the bundle
  Dockerfile). **Lanes A+B+C + B2b + B2b-2 = the released library (lock templates + scanner + NFT transfer &
  ancestor spend) is feature-complete and green (38 tests).** See `refactor-learnings.md` for the how.

## Context
The BOLT demo's wapps run the **sx simulator + elas_ts at runtime** for the NFT/coupon/EventTrigger flows,
and `simplemultibolt` still carries an optional `@elas_co/ts` fallback verifier. We are consolidating the
token layer onto **one runtime stack: `@bsv/sdk` (ts-sdk) primitives + TS templates spliced from
pre-compiled `.sx.json`** — for every token. `sx` + `elas_ts` become **build-time-only** (the compiler that
emits `.sx.json`; not released; elas_ts stays inside sx). `simplemultibolt` becomes the **released library**:
the token templates **and** the shared token-tx-chain scanner / payment-processor every wapp uses.
`simpleMultiBOLT` is the flagship and already proves the pattern (pre-compiled `SimpleMultiBolt.sx.json` +
TS template + `@bsv/sdk`, zero sx at runtime). The SimpleBalanceBolt fee-coupon (£3.33 price-gate) is
deferred.

## Target architecture
- Runtime: `@bsv/sdk` + `simplemultibolt` (templates + scanner). No elas_ts, no sx child-process.
- **simplemultibolt is ESM** (NodeNext) — kills the demo's CJS `smb-bridge.cjs` + the dual
  `@bsv/sdk`-instance trap (the ESM demo imports it directly); modern shape for a released lib. Tests on
  **vitest** (ESM-native), not jest. `.sx.json` via `with { type: 'json' }`; relative imports gain `.js`.
- Build-time only: `sx` (compiler) + `elas_ts` (its engine) → emit `.sx.json` artifacts.
- `verifyTx` (`@bsv/sdk` `Spend`) is the verifier; `verifyTx2` (elas `Interp`) is deleted.

## Ralph-loop rules
- One backlog task per iteration. **RED first** (write the failing test), then **GREEN** (minimal impl to
  pass), then **commit**. Never green a task whose test isn't actually passing.
- Respect the dependency graph below — pick the lowest-numbered unblocked task whose deps are all done.
- Completion promise `SMB-LIB-REFACTOR-DONE` only when **every** task A1→D6 is committed and its test green.

## Dependency graph (the Gantt)
```
A1 → A2                         (simplemultibolt de-elas + releasable)            [no deps]
        └─► B1, B2, B3 ─► B4    (token templates ‖, then fingerprints)            [dep: A1]
                            └─► C1 → C2 → C3 → C4 → C5   (the scanner)            [dep: B1–B4]
                                                    └─► D1, D2, D3, D4 ─► D5 ─► D6  (rewire demo)  [dep: B*, C*]
A3 (ts-bolt de-elas) runs any time after A1, parallel to B/C.                     [dep: A1]
```
Lane A first (unblocks everything); B templates can go in parallel; C is mostly sequential (C5 ties it
together); D wapps in parallel, D6 (bundle) last.

## Backlog

### Lane A — simplemultibolt de-elas + releasable
- **A1** RED `test/no-elas.test.ts`: SMB mint→transfer→split→merge→melt verifies on `@bsv/sdk` `verifyTx`,
  no `@elas_co/ts` in src. GREEN: delete `verifyTx2` + the elas import; @bsv/sdk Spend is the sole verifier.
- **A2** RED `test/releasable.test.ts`: no `@elas_co/ts`; `npm pack` clean; `@bsv/sdk` is a peer dep.
- **A3** (optional, deferred) mirror the de-elas in ts-bolt (dev workspace; not release-critical).

### Lane B — token templates from pre-compiled contracts  [dep: A1]
Pattern: copy `src/multi/SimpleMultiBolt.sx.template.ts` (data-push chunks + `Script.fromASM(LOCK_SUFFIX)`);
inputs are `sx/bolt/production/artifacts/{MinSimpleBolt,MinSimpleDiscountBolt,MinSimpleBalanceBolt}.json`.
- **B1** MinSimpleBolt LOCK template — lock byte-faithful to the artifact; mint verifyTx-green. **DONE.**
- **B2** MinSimpleDiscountBolt — mint + commit + settle (1-byte discount) incl. the spend/unlock; byte-equals sx.
- **B3** MinSimpleBalanceBolt — same with the 16-byte balance.
- **B4** `src/scan/fingerprints.ts` — per type `{ pushLengths, suffixHash=sha256(staticScriptCode) }`;
  issuerPubKey is the last 33-byte push.

### Lane C — shared full off-chain BOLT validator (the scanner)  [dep: B1–B4]
`verifyTokenChain(beefOrTxs, { expectedType, trustedIssuerPubKey })`. C1 fingerprint recognition;
C2 issuerPubKey; C3 commit+settle lineage; C4 full arrangement (every input AND output classified
uniformly, txType×type shape; discount-before-amount); C5 accept/reject parity vs the on-chain contract.

### Lane D — rewire the demo off the sx simulator  [dep: B*, C*]
D1–D4 per wapp (catpicz/bwanq/tackle/bucket): e2e green with sx OFF, using templates + `verifyTokenChain`.
D5 the A′ EventTrigger flow via ts-bolt templates (no sx). D6 the bundle wapps image builds with only
`ts-sdk` + `simplemultibolt` vendored; clickable B1→B7 walk.

## Scanner spec (security properties for Lane C — all must hold)
1. Type recognition: `[pushLengths] + sha256(staticScriptCode)` == registry → genuine BOLT token of type X.
2. issuerPubKey (last 33-byte push) == trusted issuer.
3. Lineage: bolt present in **both** commit and settle; parent/grandparent + pubKeyHashCommitment chain valid.
4. Full arrangement: **every** input and output inspected/classified uniformly (none skipped) and matching
   the `txType` × token-type input/output shape the contract enforces on-chain.
5. SPV/BEEF on-chain presence.
Parity target: accept/reject set == the on-chain BOLT contract (EventListener is the minimum bar).

## Notes
- **Golden byte-equality (B1–B3) is the safety net**: templates must reproduce the sx-simulator txs
  byte-for-byte before Lane D swaps them in, so on-chain acceptance is unchanged.
- Deferred — **SimpleBalanceBolt fee-coupon**: NFT+16B balance redeemable against bucketshop fees,
  redemption unlocked once the % discount is listed at **£3.33** (price-gate). Plan after D6.
- Orthogonal to the shipped chain work (custom teranode/arcade: Genesis@1 + Japanese genesis + A′ fire green).
