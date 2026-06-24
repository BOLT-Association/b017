// b017 — optimised BOLT layer-1 token templates + off-chain scanner.
// Pre-compiled contract (no sx compiler at runtime); only @bsv/sdk.
export { SimpleMultiBOLT } from "./tokens/MultiBOLT.js";
export type { VerifierType } from "./tokens/MultiBOLT.js";
export { default as SimpleMultiTemplate } from "./tokens/templates/SimpleMulti.sx.template.js";
export { BOLT } from "./tokens/BOLT.js";
export { verifyTx, buildOutpoint } from "./lib/boltLib.js";

// Token LOCK templates (mint/build the contract output for each type).
export { default as MinSimpleTemplate } from "./tokens/templates/MinSimple.sx.template.js";
export { default as MinSimpleDiscountTemplate } from "./tokens/templates/MinSimpleDiscount.sx.template.js";
export { default as MinSimpleBalanceTemplate } from "./tokens/templates/MinSimpleBalance.sx.template.js";
export { default as Pay2ProofTemplate } from "./tokens/templates/pay2Proof.js";

// Token recognition — the scanner's fingerprint primitive.
export { REGISTRY, recognizeType, recognizeP2P, issuerPubKeyOf, sha256Hex } from "./lib/scanner/fingerprints.js";
export type { TokenType, TypeSpec } from "./lib/scanner/fingerprints.js";

// The shared off-chain BOLT event validator (the scanner): a batch verifier + the per-event checker.
export { verifyEvents, verifyEvent } from "./lib/scanner/verifyEvents.js";
export type { ScanResult, ScanOpts, EventResult, EventKind } from "./lib/scanner/verifyEvents.js";
