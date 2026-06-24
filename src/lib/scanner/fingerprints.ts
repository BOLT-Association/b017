// fingerprints.ts — per-type recognition primitive for the BOLT token scanner.
// A genuine BOLT token's locking script = [N leading dynamic data pushes] + [static contract code].
// A type's fingerprint is { pushLengths (the data-push byte layout) , suffixHash = sha256(static code) }.
// issuerPubKey is always the LAST dynamic push (33 bytes); it identifies the issuer, not the type.
//
// The same golden-hash idea also fingerprints the p2Proof output (the b017 marker proof carried by
// commit txs and consumed by settle txs): its only dynamic field is the 20-byte beneficiary pkh, so
// recognizeP2P hashes the static skeleton (incl. the b017 marker bytes) and checks the pkh length.
import { Hash, Script, Utils } from "@bsv/sdk";
import MinSimpleTemplate from "../../tokens/templates/MinSimple.sx.template.js";
import MinSimpleDiscountTemplate from "../../tokens/templates/MinSimpleDiscount.sx.template.js";
import MinSimpleBalanceTemplate from "../../tokens/templates/MinSimpleBalance.sx.template.js";
import SimpleMultiTemplate from "../../tokens/templates/SimpleMulti.sx.template.js";
import Pay2ProofTemplate from "../../tokens/templates/pay2Proof.js";

export type TokenType =
  | "MinSimpleBOLT"
  | "MinSimpleDiscountBOLT"
  | "MinSimpleBalanceBOLT"
  | "SimpleMultiBOLT";

export interface TypeSpec {
  type: TokenType;
  dataPushCount: number;
  pushLengths: number[];
  suffixHashHex: string;
}

// Leading dynamic-push byte lengths per type (issuerPubKey is always the last, 33 bytes).
const LAYOUTS: Record<TokenType, readonly number[]> = Object.freeze({
  MinSimpleBOLT: [20, 20, 1, 36, 36, 33],
  MinSimpleDiscountBOLT: [1, 20, 20, 1, 36, 36, 33],
  MinSimpleBalanceBOLT: [16, 20, 20, 1, 36, 36, 33],
  SimpleMultiBOLT: [16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33],
});
const SUFFIX: Record<TokenType, Script> = {
  MinSimpleBOLT: new MinSimpleTemplate().staticSuffix(),
  MinSimpleDiscountBOLT: new MinSimpleDiscountTemplate().staticSuffix(),
  MinSimpleBalanceBOLT: new MinSimpleBalanceTemplate().staticSuffix(),
  SimpleMultiBOLT: new SimpleMultiTemplate().staticSuffix(),
};

export const sha256Hex = (bin: number[]): string => Utils.toHex(Hash.sha256(bin));

export const REGISTRY: Record<TokenType, TypeSpec> = Object.freeze(
  Object.fromEntries(
    (Object.keys(LAYOUTS) as TokenType[]).map((type) => [
      type,
      Object.freeze({
        type,
        dataPushCount: LAYOUTS[type].length,
        pushLengths: Object.freeze([...LAYOUTS[type]]),
        suffixHashHex: sha256Hex(SUFFIX[type].toBinary()),
      }),
    ]),
  ),
) as Record<TokenType, TypeSpec>;

/**
 * Recognise a locking script as a genuine BOLT token of a known type (or null).
 * Requires BOTH the leading-push layout AND the static-code hash to match a registered type —
 * so a tampered contract body or a non-token script is rejected.
 */
export function recognizeType(lock: Script | null | undefined, expected?: TokenType): TokenType | null {
  if (!lock || !Array.isArray(lock.chunks)) return null;
  for (const spec of Object.values(REGISTRY)) {
    if (expected && spec.type !== expected) continue;
    const n = spec.dataPushCount;
    if (lock.chunks.length <= n) continue;
    const lens = lock.chunks.slice(0, n).map((c) => c.data?.length ?? 0);
    if (!lens.every((l, i) => l === spec.pushLengths[i])) continue;
    const suffix = new Script(lock.chunks.slice(n));
    if (sha256Hex(suffix.toBinary()) !== spec.suffixHashHex) continue;
    return spec.type;
  }
  return null;
}

/** The issuerPubKey is always the last dynamic data push of a recognised token. */
export function issuerPubKeyOf(lock: Script, type: TokenType): number[] {
  return (lock.chunks[REGISTRY[type].dataPushCount - 1]?.data as number[]) ?? [];
}

// ---- p2Proof golden fingerprint --------------------------------------------------------------
// The b017 proof output has exactly ONE dynamic field — the 20-byte beneficiary pkh at index
// P2P_PKH_IDX. Everything else (the b017 marker bytes + the surrounding opcodes) is static, so a
// genuine p2Proof is fingerprinted by sha256(static skeleton) + the pkh push length, derived from
// Pay2ProofTemplate so there is a single source of truth.
const P2P_PKH_IDX = 4;
const P2P_REF = new Pay2ProofTemplate().lock(new Array(20).fill(0));
const P2P_LEN = P2P_REF.chunks.length;

/** Serialise a script with its single dynamic push zeroed so only static structure is hashed. */
function p2pSkeleton(lock: Script): number[] {
  const chunks = lock.chunks.map((c, i) =>
    /* v8 ignore next -- recognizeP2P guarantees chunk[P2P_PKH_IDX] carries 20 bytes before this runs */
    i === P2P_PKH_IDX ? { op: c.op, data: new Array(c.data?.length ?? 0).fill(0) } : c);
  return new Script(chunks).toBinary();
}
const P2P_SKELETON_HASH = sha256Hex(p2pSkeleton(P2P_REF));

/**
 * Recognise a locking script as a genuine p2Proof (the b017 marker proof) output, golden-strict:
 * the static skeleton hash (incl. the b017 marker) must match Pay2ProofTemplate AND the single
 * dynamic field must be a 20-byte pkh. Used to fingerprint commit proof outputs and settle proof
 * inputs. Returns false for anything else (token, plain p2pkh, tampered marker/opcodes).
 */
export function recognizeP2P(lock: Script | null | undefined): boolean {
  if (!lock || !Array.isArray(lock.chunks) || lock.chunks.length !== P2P_LEN) return false;
  const pkh = lock.chunks[P2P_PKH_IDX]?.data;
  if (!pkh || pkh.length !== 20) return false;
  return sha256Hex(p2pSkeleton(lock)) === P2P_SKELETON_HASH;
}
