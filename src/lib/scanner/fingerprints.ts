// fingerprints.ts — per-type recognition primitive for the BOLT token scanner.
// A genuine BOLT token's locking script = [N leading dynamic data pushes] + [static contract code].
// A type's fingerprint is { pushLengths (the data-push byte layout) , suffixHash = sha256(static code) }.
// issuerPubKey is always the LAST dynamic push (33 bytes); it identifies the issuer, not the type.
//
// The genesis family (FixedBOLT, OpenBOLT, SerialBOLT) leads with two more pushes: a 36-byte outpoint field and the
// issuer's mintData, which is variable on the MINT and empty (OP_0) on every later output. So each has TWO specs:
//   mint      field 0 = 36 zero bytes (null), mintData 0..255 bytes;
//   postMint  field 0 = 36 bytes, not all zero,  mintData exactly 0 bytes.
// Every other push is exact-length in both. A non-empty mintData after the mint is therefore unrecognised.
//
// The same golden-hash idea also fingerprints the p2Proof output (the b017 marker proof carried by
// commit txs and consumed by settle txs): its only dynamic field is the 20-byte beneficiary pkh, so
// recognizeP2P hashes the static skeleton (incl. the b017 marker bytes) and checks the pkh length.
import { Hash, Script, Utils } from "@bsv/sdk";
import MinSimpleTemplate from "../../tokens/templates/MinSimple.sx.template.js";
import AuthBoltTemplate from "../../tokens/templates/AuthBolt.sx.template.js";
import SimpleMultiTemplate from "../../tokens/templates/SimpleMulti.sx.template.js";
import FixedMultiTemplate from "../../tokens/templates/FixedMulti.sx.template.js";
import OpenMultiTemplate from "../../tokens/templates/OpenMulti.sx.template.js";
import SerialBoltTemplate from "../../tokens/templates/SerialBolt.sx.template.js";
import Pay2ProofTemplate from "../../tokens/templates/pay2Proof.js";

export type TokenType =
  | "MinSimpleBOLT"
  | "AuthBOLT"
  | "SimpleMultiBOLT"
  | "FixedBOLT"
  | "OpenBOLT"
  | "SerialBOLT";

/** Genesis-family recognition phase: the mint (null field, any mintData) or any later output. */
export type TokenPhase = "mint" | "postMint";

export interface TypeSpec {
  type: TokenType;
  dataPushCount: number;
  /** Exact push lengths (for the genesis family: the postMint spec; the mint spec relaxes pushes 0-1). */
  pushLengths: number[];
  suffixHashHex: string;
  /** Genesis family: leads with the 36-byte genesis / LMG field and the mintData push. */
  genesis: boolean;
}

// Leading dynamic-push byte lengths per type (issuerPubKey is always the last, 33 bytes).
const LAYOUTS: Record<TokenType, readonly number[]> = Object.freeze({
  MinSimpleBOLT: [20, 20, 1, 36, 36, 33],
  AuthBOLT: [20, 20, 1, 36, 36, 33], // same lock layout as MinSimpleBOLT: told apart by the suffix hash alone
  SimpleMultiBOLT: [16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33],
  FixedBOLT: [36, 0, 16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33],
  OpenBOLT: [36, 0, 16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33],
  SerialBOLT: [36, 0, 20, 20, 1, 36, 36, 33],
});
const GENESIS: ReadonlySet<TokenType> = new Set<TokenType>(["FixedBOLT", "OpenBOLT", "SerialBOLT"]);
/** mintData is pushed with at most PUSHDATA1. */
const MINT_DATA_MAX = 255;
const SUFFIX: Record<TokenType, Script> = {
  MinSimpleBOLT: new MinSimpleTemplate().staticSuffix(),
  AuthBOLT: new AuthBoltTemplate().staticSuffix(),
  SimpleMultiBOLT: new SimpleMultiTemplate().staticSuffix(),
  FixedBOLT: new FixedMultiTemplate().staticSuffix(),
  OpenBOLT: new OpenMultiTemplate().staticSuffix(),
  SerialBOLT: new SerialBoltTemplate().staticSuffix(),
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
        genesis: GENESIS.has(type),
      }),
    ]),
  ),
) as Record<TokenType, TypeSpec>;

/** The leading pushes match a spec: exact lengths, except the genesis family's mint / postMint pair (see top). */
function pushesMatch(lock: Script, spec: TypeSpec): TokenPhase | "exact" | null {
  const n = spec.dataPushCount;
  const lens = lock.chunks.slice(0, n).map((c) => c.data?.length ?? 0);
  if (!spec.genesis) return lens.every((l, i) => l === spec.pushLengths[i]) ? "exact" : null;
  if (!lens.every((l, i) => i < 2 || l === spec.pushLengths[i]) || lens[0] !== 36) return null;
  const nullField = (lock.chunks[0].data as number[]).every((b) => b === 0);
  if (nullField) return lens[1] <= MINT_DATA_MAX ? "mint" : null;
  return lens[1] === 0 ? "postMint" : null;
}

/**
 * Recognise a locking script as a genuine BOLT token of a known type, with its genesis-family phase (or null).
 * Requires BOTH the leading-push layout AND the static-code hash to match a registered type —
 * so a tampered contract body or a non-token script is rejected.
 */
export function recognizeToken(
  lock: Script | null | undefined, expected?: TokenType,
): { type: TokenType; phase?: TokenPhase } | null {
  if (!lock || !Array.isArray(lock.chunks)) return null;
  for (const spec of Object.values(REGISTRY)) {
    if (expected && spec.type !== expected) continue;
    const n = spec.dataPushCount;
    if (lock.chunks.length <= n) continue;
    const m = pushesMatch(lock, spec);
    if (!m) continue;
    const suffix = new Script(lock.chunks.slice(n));
    if (sha256Hex(suffix.toBinary()) !== spec.suffixHashHex) continue;
    return m === "exact" ? { type: spec.type } : { type: spec.type, phase: m };
  }
  return null;
}

/** Recognise a locking script as a genuine BOLT token of a known type (or null). See recognizeToken. */
export function recognizeType(lock: Script | null | undefined, expected?: TokenType): TokenType | null {
  return recognizeToken(lock, expected)?.type ?? null;
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
