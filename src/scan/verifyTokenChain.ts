// verifyTokenChain.ts — the shared off-chain BOLT token-chain validator (the scanner).
// Builds on the B4 fingerprint registry. Validates, over a set of lineage txs:
//   C2 issuer       — issuerPubKey consistent across every token output, and == trustedIssuerPubKey
//   C3 lineage      — the bolt appears in BOTH a commit (txoType 21) AND a settle (txoType 20),
//                     linked by parentOutpoint (settle.parent -> commit token outpoint)
// C4 (full input/output arrangement) and C5 (parity) build on this in the next steps.
import { OP, Transaction, Script, Utils } from "@bsv/sdk";
import { recognizeType, issuerPubKeyOf, type TokenType } from "./fingerprints.js";

// Field push-indices per type (parent/grandparent/issuer are the last 3 pushes; txoType varies).
type FieldName = "pubKeyHash" | "commitment" | "txoType" | "parent" | "grandparent";
const FIELDS: Record<TokenType, Record<FieldName, number>> = {
  MinSimpleBOLT: { pubKeyHash: 0, commitment: 1, txoType: 2, parent: 3, grandparent: 4 },
  MinSimpleDiscountBOLT: { pubKeyHash: 1, commitment: 2, txoType: 3, parent: 4, grandparent: 5 },
  MinSimpleBalanceBOLT: { pubKeyHash: 1, commitment: 2, txoType: 3, parent: 4, grandparent: 5 },
  SimpleMultiBOLT: { pubKeyHash: 2, commitment: 3, txoType: 6, parent: 8, grandparent: 9 },
};
const field = (lock: Script, type: TokenType, f: FieldName): number[] =>
  (lock.chunks[FIELDS[type][f]]?.data as number[]) ?? [];
const fieldHex = (lock: Script, type: TokenType, f: FieldName): string => Utils.toHex(field(lock, type, f));

// A 36-byte outpoint is txid (32, internal byte order) + vout (4, LE). The display txid is reversed.
function parseOutpoint(op: number[]): { txidHex: string; vout: number } {
  const txidHex = Utils.toHex([...op.slice(0, 32)].reverse());
  const v = op.slice(32, 36);
  const vout = ((v[0] ?? 0) | ((v[1] ?? 0) << 8) | ((v[2] ?? 0) << 16) | ((v[3] ?? 0) << 24)) >>> 0;
  return { txidHex, vout };
}

export interface ScanOpts {
  expectedType?: TokenType;
  trustedIssuerPubKey?: number[] | string;
}
export interface ScanResult {
  ok: boolean;
  reason?: string;
  type?: TokenType;
  issuerPubKeyHex?: string;
  chain?: { txid: string; vout: number; txoType: string }[];
}

const toTx = (t: Transaction | string): Transaction => (typeof t === "string" ? Transaction.fromHex(t) : t);
const optHex = (b?: number[] | string): string | undefined =>
  b == null ? undefined : typeof b === "string" ? b.toLowerCase() : Utils.toHex(b);

export function verifyTokenChain(txsIn: (Transaction | string)[], opts: ScanOpts = {}): ScanResult {
  const txs = txsIn.map(toTx);
  if (txs.length === 0) return { ok: false, reason: "empty chain" };

  // Find every recognised token output across the chain.
  type TokenRef = { txid: string; vout: number; type: TokenType; lock: Script };
  const tokens: TokenRef[] = [];
  for (const tx of txs) {
    const txid = tx.id("hex");
    tx.outputs.forEach((o, vout) => {
      const type = recognizeType(o.lockingScript, opts.expectedType);
      if (type) tokens.push({ txid, vout, type, lock: o.lockingScript });
    });
  }
  if (tokens.length === 0) return { ok: false, reason: "no BOLT token output recognised" };

  const type = tokens[0].type;
  if (tokens.some((t) => t.type !== type)) return { ok: false, reason: "mixed token types in chain" };
  if (opts.expectedType && type !== opts.expectedType)
    return { ok: false, reason: `expected ${opts.expectedType}, got ${type}` };

  // C2 — issuerPubKey consistent across all token outputs, and == trusted issuer (if supplied).
  const issuers = new Set(tokens.map((t) => Utils.toHex(issuerPubKeyOf(t.lock, type))));
  if (issuers.size !== 1) return { ok: false, reason: "inconsistent issuerPubKey across chain" };
  const issuerPubKeyHex = [...issuers][0];
  const trusted = optHex(opts.trustedIssuerPubKey);
  if (trusted && trusted !== issuerPubKeyHex) return { ok: false, reason: "issuerPubKey != trusted issuer" };

  // C3 — lineage: the bolt must appear in a commit (txoType 21) AND a settle that links back to it.
  // The settle's own txoType is the post-commit resting state (00 for the NFTs, 20 for
  // SimpleMultiBolt), so the universal signal is the parentOutpoint: settle.parent -> commit token.
  const commits = tokens.filter((t) => fieldHex(t.lock, type, "txoType") === "21");
  if (commits.length === 0) return { ok: false, reason: "no commit token (txoType 21) in chain" };
  const settle = tokens.find((s) => {
    const p = parseOutpoint(field(s.lock, type, "parent"));
    return commits.some((c) => c.txid === p.txidHex && c.vout === p.vout);
  });
  if (!settle) return { ok: false, reason: "no settle token linking back to a commit (parentOutpoint)" };

  // C4 — full arrangement: classify EVERY input and output of each lineage tx; nothing may be left
  // unclassified ("other"), and the shape must match the tx's role (mint / commit / settle).
  type Cls = "token" | "p2p" | "p2pkh" | "external" | "other";
  const classifyOut = (lock: Script): Cls => {
    if (recognizeType(lock, type)) return "token";
    const c = lock.chunks;
    if (
      c.length === 7 && c[0].data?.length === 2 && c[0].data[0] === 0xb0 && c[0].data[1] === 0x17 &&
      c[1].op === OP.OP_EQUALVERIFY && c[2].op === OP.OP_DUP && c[3].op === OP.OP_HASH160 &&
      c[4].data?.length === 20 && c[5].op === OP.OP_EQUALVERIFY && c[6].op === OP.OP_CHECKSIG
    ) return "p2p";
    if (
      c.length === 5 && c[0].op === OP.OP_DUP && c[1].op === OP.OP_HASH160 && c[2].data?.length === 20 &&
      c[3].op === OP.OP_EQUALVERIFY && c[4].op === OP.OP_CHECKSIG
    ) return "p2pkh";
    return "other";
  };
  const byId = new Map(txs.map((t) => [t.id("hex"), t]));
  const classifyIn = (inp: { sourceTXID?: string; sourceOutputIndex: number }): Cls => {
    const src = inp.sourceTXID ? byId.get(inp.sourceTXID) : undefined;
    if (!src) return "external"; // funding from outside the supplied chain
    return classifyOut(src.outputs[inp.sourceOutputIndex].lockingScript);
  };
  const tailOk = (got: Cls[], head: Cls[], tail: Cls[]): boolean =>
    got.length >= head.length && head.every((h, i) => got[i] === h) &&
    got.slice(head.length).every((g) => tail.includes(g));

  for (const tx of txs) {
    const tokenIdx = tx.outputs.findIndex((o) => recognizeType(o.lockingScript, type));
    if (tokenIdx < 0) continue; // non-lineage tx (none in the BOLT goldens)
    const id = tx.id("hex").slice(0, 8);
    const outs = tx.outputs.map((o) => classifyOut(o.lockingScript));
    const ins = tx.inputs.map((i) => classifyIn(i as any));
    if (outs.includes("other")) return { ok: false, reason: `uninspected output in ${id} [${outs}]` };
    if (ins.includes("other")) return { ok: false, reason: `uninspected input in ${id} [${ins}]` };

    const lock = tx.outputs[tokenIdx].lockingScript;
    const tt = fieldHex(lock, type, "txoType");
    const parentZero = field(lock, type, "parent").every((b) => b === 0);
    const role = tt === "21" ? "commit" : parentZero ? "mint" : "settle";

    if (role === "mint") {
      if (!tailOk(outs, ["token"], ["p2pkh"])) return { ok: false, reason: `mint ${id} outputs [${outs}]` };
      if (!ins.every((c) => c === "external" || c === "p2pkh")) return { ok: false, reason: `mint ${id} inputs [${ins}]` };
    } else if (role === "commit") {
      if (!tailOk(outs, ["token", "p2p"], ["p2pkh"])) return { ok: false, reason: `commit ${id} outputs [${outs}]` };
      if (ins[0] !== "token" || !ins.slice(1).every((c) => c === "p2pkh" || c === "external"))
        return { ok: false, reason: `commit ${id} inputs [${ins}]` };
    } else {
      if (!tailOk(outs, ["token"], ["p2pkh"])) return { ok: false, reason: `settle ${id} outputs [${outs}]` };
      if (ins[0] !== "token" || !ins.slice(1).every((c) => c === "p2pkh" || c === "external" || c === "p2p"))
        return { ok: false, reason: `settle ${id} inputs [${ins}]` };
    }
  }

  return {
    ok: true,
    type,
    issuerPubKeyHex,
    chain: tokens.map((t) => ({ txid: t.txid, vout: t.vout, txoType: fieldHex(t.lock, type, "txoType") })),
  };
}
