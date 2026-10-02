// b017 — optimised BOLT layer-1 token templates + off-chain scanner.
// Pre-compiled contract (no sx compiler at runtime); only @bsv/sdk.
export { SimpleMultiBOLT } from "./tokens/MultiBOLT.js";
export type { VerifierType } from "./tokens/MultiBOLT.js";
export { default as SimpleMultiTemplate } from "./tokens/templates/SimpleMulti.sx.template.js";
export { BOLT } from "./tokens/BOLT.js";
export { verifyTx, buildOutpoint } from "./lib/boltLib.js";

// Token LOCK templates (mint/build the contract output for each type).
export { default as MinSimpleTemplate } from "./tokens/templates/MinSimple.sx.template.js";
export { default as AuthBoltTemplate, AUTH_DATA_MAX_BYTES } from "./tokens/templates/AuthBolt.sx.template.js";
export { default as Pay2ProofTemplate } from "./tokens/templates/pay2Proof.js";

// Token recognition — the scanner's fingerprint primitive.
export { REGISTRY, recognizeType, recognizeP2P, issuerPubKeyOf, sha256Hex } from "./lib/scanner/fingerprints.js";
export type { TokenType, TypeSpec } from "./lib/scanner/fingerprints.js";

// The shared off-chain BOLT event validator (the scanner): a batch verifier + the per-event checker.
export { verifyEvents, verifyEvent } from "./lib/scanner/verifyEvents.js";
export type { ScanResult, ScanOpts, EventResult, EventKind, SourceTx, TxInput } from "./lib/scanner/verifyEvents.js";

// The off-chain data package: Atomic BEEF (BRC-95) over BEEF V2 (BRC-96); V1 is refused.
export { toAtomicBeef, fromBeef, isBeef } from "./lib/scanner/beef.js";
