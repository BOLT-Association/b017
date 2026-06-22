// fingerprints.ts — per-type recognition primitive for the BOLT token scanner.
// A genuine BOLT token's locking script = [N leading dynamic data pushes] + [static contract code].
// A type's fingerprint is { pushLengths (the data-push byte layout) , suffixHash = sha256(static code) }.
// issuerPubKey is always the LAST dynamic push (33 bytes); it identifies the issuer, not the type.
import { Hash, Script, Utils } from "@bsv/sdk";
import MinSimpleTemplate from "../templates/MinSimpleBolt.sx.template.js";
import MinSimpleDiscountTemplate from "../templates/MinSimpleDiscountBolt.sx.template.js";
import MinSimpleBalanceTemplate from "../templates/MinSimpleBalanceBolt.sx.template.js";
import SimpleMultiTemplate from "../multi/SimpleMultiBolt.sx.template.js";

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
const LAYOUTS: Record<TokenType, number[]> = {
  MinSimpleBOLT: [20, 20, 1, 36, 36, 33],
  MinSimpleDiscountBOLT: [1, 20, 20, 1, 36, 36, 33],
  MinSimpleBalanceBOLT: [16, 20, 20, 1, 36, 36, 33],
  SimpleMultiBOLT: [16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33],
};
const SUFFIX: Record<TokenType, Script> = {
  MinSimpleBOLT: new MinSimpleTemplate().staticSuffix(),
  MinSimpleDiscountBOLT: new MinSimpleDiscountTemplate().staticSuffix(),
  MinSimpleBalanceBOLT: new MinSimpleBalanceTemplate().staticSuffix(),
  SimpleMultiBOLT: new SimpleMultiTemplate().staticSuffix(),
};

export const sha256Hex = (bin: number[]): string => Utils.toHex(Hash.sha256(bin));

export const REGISTRY: Record<TokenType, TypeSpec> = Object.fromEntries(
  (Object.keys(LAYOUTS) as TokenType[]).map((type) => [
    type,
    {
      type,
      dataPushCount: LAYOUTS[type].length,
      pushLengths: LAYOUTS[type],
      suffixHashHex: sha256Hex(SUFFIX[type].toBinary()),
    },
  ]),
) as Record<TokenType, TypeSpec>;

/**
 * Recognise a locking script as a genuine BOLT token of a known type (or null).
 * Requires BOTH the leading-push layout AND the static-code hash to match a registered type —
 * so a tampered contract body or a non-token script is rejected.
 */
export function recognizeType(lock: Script, expected?: TokenType): TokenType | null {
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
  return (lock.chunks[REGISTRY[type].dataPushCount - 1].data as number[]) ?? [];
}
