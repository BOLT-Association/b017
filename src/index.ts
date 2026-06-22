// b017 — optimised BOLT layer-1 token templates + off-chain scanner.
// Pre-compiled contract (no sx compiler at runtime); only @bsv/sdk.
export { SimpleMultiBOLT } from "./SimpleMultiBolt.js";
export type { VerifierType } from "./SimpleMultiBolt.js";
export { default as SimpleMultiTemplate } from "./multi/SimpleMultiBolt.sx.template.js";
export { BOLT } from "./boltToken.js";
export { verifyTx, buildOutpoint } from "./boltLib.js";

// Token LOCK templates (mint/build the contract output for each type).
export { default as MinSimpleTemplate } from "./templates/MinSimpleBolt.sx.template.js";
export { default as MinSimpleDiscountTemplate } from "./templates/MinSimpleDiscountBolt.sx.template.js";
export { default as MinSimpleBalanceTemplate } from "./templates/MinSimpleBalanceBolt.sx.template.js";

// Token recognition — the scanner's fingerprint primitive.
export { REGISTRY, recognizeType, issuerPubKeyOf, sha256Hex } from "./scan/fingerprints.js";
export type { TokenType, TypeSpec } from "./scan/fingerprints.js";

// The shared off-chain BOLT token-chain validator (the scanner).
export { verifyTokenChain } from "./scan/verifyTokenChain.js";
export type { ScanResult, ScanOpts } from "./scan/verifyTokenChain.js";

// The compiled contract artifact is shipped for reference (consumers never run sx).
import contractJson from "./contracts/SimpleMultiBolt.sx.json" with { type: "json" };
export const SimpleMultiBOLTContract = contractJson;
