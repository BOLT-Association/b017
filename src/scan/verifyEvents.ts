// verifyEvents.ts — the shared off-chain BOLT validator (the scanner).
//
// The protocol is a stream of TRANSACTIONAL EVENTS. A transfer/split/merge event is a
// commit -> settle PAIR of txs; a mint is a single genesis tx; a melt is a single terminal tx.
// Because most events are two txs, events can be collected into a BATCH, transmitted together,
// and parsed for authenticity by a multistep inspection.
//
//   verifyEvent(txs)   — validate ONE event: categorise its tx(s) by the token's txoType action
//                        byte, fingerprint EVERY interface (strict golden recognition for all token
//                        inputs/outputs — including split's 2 token outputs and merge's 2 token
//                        inputs; loose shape for the p2p proof / change / funding), and check the
//                        commit<->settle linkage.
//   verifyEvents(txs)  — validate a BATCH of events: recognise the type, pin the issuer across the
//                        whole batch, fingerprint every tx's arrangement, then pair the events —
//                        every commit must be matched by a settle (and vice-versa) via parentOutpoint.
//                        A lone mint or melt is a valid single-tx event.
//
// NOTE — a commit and its settle are bound TWO independent ways:
//   (1) TOKEN LINEAGE  — the settle's token parentOutpoint references the commit's token output.
//                        This is the binding verifyEvents/verifyEvent assert.
//   (2) FUNDING CHAIN  — in general the settle's funding input spends the commit's CHANGE output (the
//                        commit's last, change=true output). So the pair is also chained at the
//                        satoshi/funding level. This is a CONSTRUCTION property — a caller-supplied
//                        fundOverride can fund the settle from elsewhere — so it is NOT asserted here.
//
// Strict = golden byte fingerprint (recognizeType: leading-push layout + sha256(static code)).
// Loose  = shape only (a P2PKH change output / external funding input may carry any pkh + value).
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
export type EventKind = "mint" | "transfer" | "split" | "merge" | "melt";
export interface ScanResult {
  ok: boolean;
  reason?: string;
  type?: TokenType;
  issuerPubKeyHex?: string;
  events?: { kind: EventKind; txids: string[] }[];
}
export interface EventResult {
  ok: boolean;
  reason?: string;
  type?: TokenType;
  kind?: EventKind;
}

const toTx = (t: Transaction | string): Transaction => (typeof t === "string" ? Transaction.fromHex(t) : t);
const optHex = (b?: number[] | string): string | undefined =>
  b == null ? undefined : typeof b === "string" ? b.toLowerCase() : Utils.toHex(b);

// ---- interface fingerprinting: classify every input / output ----
type Cls = "token" | "p2p" | "p2pkh" | "external" | "other";
type ById = Map<string, Transaction>;

/** Classify an output's locking script. token = strict golden fingerprint; p2p = the b017 marker
 *  proof output; p2pkh = a plain pay-to-pubkey-hash (change); else "other". */
function classifyOut(lock: Script, type: TokenType): Cls {
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
}

/** Classify an input by fingerprinting the output it spends (via the attached source tx, else a
 *  source tx supplied in the batch); "external" when the source is outside the supplied set. */
function classifyIn(input: any, type: TokenType, byId: ById): Cls {
  const src: Transaction | undefined =
    input.sourceTransaction ?? (input.sourceTXID ? byId.get(input.sourceTXID) : undefined);
  if (!src) return "external";
  return classifyOut(src.outputs[input.sourceOutputIndex].lockingScript, type);
}

// ---- action categorisation: the token's txoType byte -> the event shape ----
// tokenIn / tokenOut / proofOut are EXACT (strict, golden); proof inputs + change + funding are loose.
interface Shape { kind: "mint" | "commit" | "settle" | "melt"; tokenIn: number; tokenOut: number; proofOut: number }

function categorise(tx: Transaction, type: TokenType, byId: ById): { shape: Shape; tokenOutIdx: number } | null {
  const tokenOutIdx = tx.outputs.findIndex((o) => recognizeType(o.lockingScript, type));
  if (tokenOutIdx >= 0) {
    const lock = tx.outputs[tokenOutIdx].lockingScript;
    const parentZero = field(lock, type, "parent").every((b) => b === 0);
    if (parentZero) return { shape: { kind: "mint", tokenIn: 0, tokenOut: 1, proofOut: 0 }, tokenOutIdx };
    const S = (kind: Shape["kind"], tokenIn: number, tokenOut: number, proofOut: number) =>
      ({ shape: { kind, tokenIn, tokenOut, proofOut }, tokenOutIdx });
    switch (fieldHex(lock, type, "txoType")) {
      case "21": return S("commit", 1, 1, 1); // transfer commit
      case "23": return S("commit", 1, 1, 2); // split commit  -> 2 p2p proofs
      case "25": return S("commit", 2, 1, 1); // merge commit  -> 2 token inputs
      case "22": return S("settle", 1, 2, 0); // split settle  -> 2 token outputs
      case "24": return S("settle", 1, 1, 0); // merge settle
      default:   return S("settle", 1, 1, 0); // transfer settle (txoType 20 / 00) + any resting state
    }
  }
  // No token output — a melt (spends a token, no token output)?
  if (tx.inputs.some((i) => classifyIn(i, type, byId) === "token"))
    return { shape: { kind: "melt", tokenIn: 1, tokenOut: 0, proofOut: 0 }, tokenOutIdx: -1 };
  return null;
}

const actionKind = (txoTypeHex: string): EventKind =>
  txoTypeHex === "23" ? "split" : txoTypeHex === "25" ? "merge" : "transfer";

/** Fingerprint every interface of a token tx and check it matches its action's golden shape:
 *  the leading token in/out are strictly recognised; the p2p proof outputs are exact in count;
 *  trailing change (p2pkh) + funding/proof inputs are loose; nothing may be "other". */
function checkArrangement(tx: Transaction, type: TokenType, shape: Shape, byId: ById): string | null {
  const id = tx.id("hex").slice(0, 8);
  const outs = tx.outputs.map((o) => classifyOut(o.lockingScript, type));
  const ins = tx.inputs.map((i) => classifyIn(i, type, byId));
  if (outs.includes("other")) return `uninspected output in ${id} [${outs}]`;
  if (ins.includes("other")) return `uninspected input in ${id} [${ins}]`;
  // outputs: [token × tokenOut] then [p2p × proofOut] then [p2pkh change × rest]
  for (let k = 0; k < shape.tokenOut; k++)
    if (outs[k] !== "token") return `${shape.kind} ${id}: token output @${k} (got ${outs[k] ?? "none"}) [${outs}]`;
  for (let k = 0; k < shape.proofOut; k++)
    if (outs[shape.tokenOut + k] !== "p2p") return `${shape.kind} ${id}: p2p output @${shape.tokenOut + k} [${outs}]`;
  for (let k = shape.tokenOut + shape.proofOut; k < outs.length; k++)
    if (outs[k] !== "p2pkh") return `${shape.kind} ${id}: change p2pkh @${k} (got ${outs[k]}) [${outs}]`;
  // inputs: [token × tokenIn] then [p2p | external | p2pkh × rest]  (proofs + funding, loose)
  for (let k = 0; k < shape.tokenIn; k++)
    if (ins[k] !== "token") return `${shape.kind} ${id}: token input @${k} (got ${ins[k] ?? "none"}) [${ins}]`;
  for (let k = shape.tokenIn; k < ins.length; k++)
    if (!(ins[k] === "p2p" || ins[k] === "external" || ins[k] === "p2pkh"))
      return `${shape.kind} ${id}: unexpected input @${k}: ${ins[k]} [${ins}]`;
  return null;
}

/** Resolve the token type of an event from its first recognised token interface (output, then a
 *  token input's source for a melt). */
function eventType(txs: Transaction[], byId: ById, expected?: TokenType): TokenType | undefined {
  for (const tx of txs) {
    const i = tx.outputs.findIndex((o) => recognizeType(o.lockingScript, expected));
    if (i >= 0) return recognizeType(tx.outputs[i].lockingScript, expected)!;
  }
  for (const tx of txs)
    for (const inp of tx.inputs) {
      const s: Transaction | undefined = inp.sourceTransaction ?? (inp.sourceTXID ? byId.get(inp.sourceTXID) : undefined);
      if (s) {
        const t = recognizeType(s.outputs[inp.sourceOutputIndex].lockingScript, expected);
        if (t) return t;
      }
    }
  return undefined;
}

/**
 * Verify ONE token event — a mint, a commit->settle pair, or a melt. Categorises each tx by its
 * token's txoType action, fingerprints EVERY interface against the action's golden shape, and (for
 * a commit+settle pair) checks the settle links back to the commit via parentOutpoint.
 */
export function verifyEvent(eventTxs: (Transaction | string)[], opts: ScanOpts = {}): EventResult {
  const txs = eventTxs.map(toTx);
  if (txs.length === 0) return { ok: false, reason: "empty event" };
  const byId: ById = new Map(txs.map((t) => [t.id("hex"), t]));

  const type = eventType(txs, byId, opts.expectedType);
  if (!type) return { ok: false, reason: "no BOLT token recognised in event" };
  if (opts.expectedType && type !== opts.expectedType)
    return { ok: false, reason: `expected ${opts.expectedType}, got ${type}`, type };

  for (const tx of txs) {
    const cat = categorise(tx, type, byId);
    if (!cat) return { ok: false, reason: `tx ${tx.id("hex").slice(0, 8)} is not a token tx`, type };
    const reason = checkArrangement(tx, type, cat.shape, byId);
    if (reason) return { ok: false, reason, type, kind: cat.shape.kind as EventKind };
  }

  const commitTx = txs.find((t) => categorise(t, type, byId)?.shape.kind === "commit");
  const settleTx = txs.find((t) => categorise(t, type, byId)?.shape.kind === "settle");
  if (commitTx && settleTx) {
    const cIdx = commitTx.outputs.findIndex((o) => recognizeType(o.lockingScript, type));
    const sIdx = settleTx.outputs.findIndex((o) => recognizeType(o.lockingScript, type));
    const p = parseOutpoint(field(settleTx.outputs[sIdx].lockingScript, type, "parent"));
    if (!(p.txidHex === commitTx.id("hex") && p.vout === cIdx))
      return { ok: false, reason: "settle.parent does not link to the commit token", type };
    return { ok: true, type, kind: actionKind(fieldHex(commitTx.outputs[cIdx].lockingScript, type, "txoType")) };
  }
  const lone = categorise(txs[txs.length - 1], type, byId);
  return { ok: true, type, kind: lone?.shape.kind === "melt" ? "melt" : "mint" };
}

/**
 * Verify a BATCH of transactional events end to end. The multistep inspection: recognise the type,
 * pin the issuer across every token output in the batch, fingerprint every tx's interface
 * arrangement, then pair the events — every commit (txoType 21/23/25) must be matched by a settle
 * that links back via parentOutpoint, and every settle must link to a commit in the batch. A lone
 * mint (genesis) or melt (terminal) is a valid single-tx event.
 */
export function verifyEvents(txsIn: (Transaction | string)[], opts: ScanOpts = {}): ScanResult {
  const txs = txsIn.map(toTx);
  if (txs.length === 0) return { ok: false, reason: "empty batch" };
  const byId: ById = new Map(txs.map((t) => [t.id("hex"), t]));

  // Every recognised token output across the batch.
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
  if (tokens.some((t) => t.type !== type)) return { ok: false, reason: "mixed token types in batch" };
  if (opts.expectedType && type !== opts.expectedType)
    return { ok: false, reason: `expected ${opts.expectedType}, got ${type}` };

  // Issuer consistent across all token outputs, and == the trusted issuer (if supplied).
  const issuers = new Set(tokens.map((t) => Utils.toHex(issuerPubKeyOf(t.lock, type))));
  if (issuers.size !== 1) return { ok: false, reason: "inconsistent issuerPubKey across batch" };
  const issuerPubKeyHex = [...issuers][0];
  const trusted = optHex(opts.trustedIssuerPubKey);
  if (trusted && trusted !== issuerPubKeyHex) return { ok: false, reason: "issuerPubKey != trusted issuer" };

  // Categorise every tx — each must be a well-formed BOLT event tx (mint / commit / settle / melt).
  const cats = txs.map((tx) => ({ tx, cat: categorise(tx, type, byId) }));
  for (const { tx, cat } of cats)
    if (!cat) return { ok: false, reason: `tx ${tx.id("hex").slice(0, 8)} is not a BOLT token tx`, type };

  // Pair the events: every settle links back to a commit in the batch, and every commit is settled.
  // (Checked before the per-interface arrangement so a structurally-incomplete batch reports the
  // missing-pair reason, not an orphaned-input one.)
  const key = (txid: string, vout: number) => `${txid}:${vout}`;
  const commits = cats.filter((c) => c.cat!.shape.kind === "commit");
  const settled = new Set<string>();
  const events: { kind: EventKind; txids: string[] }[] = [];

  for (const s of cats.filter((c) => c.cat!.shape.kind === "settle")) {
    const sLock = s.tx.outputs[s.cat!.tokenOutIdx].lockingScript;
    const p = parseOutpoint(field(sLock, type, "parent"));
    const commit = commits.find((c) => c.tx.id("hex") === p.txidHex && c.cat!.tokenOutIdx === p.vout);
    if (!commit)
      return { ok: false, reason: `settle ${s.tx.id("hex").slice(0, 8)} links to no commit in the batch (orphan settle)`, type };
    settled.add(key(commit.tx.id("hex"), commit.cat!.tokenOutIdx));
    const cLock = commit.tx.outputs[commit.cat!.tokenOutIdx].lockingScript;
    events.push({ kind: actionKind(fieldHex(cLock, type, "txoType")), txids: [commit.tx.id("hex"), s.tx.id("hex")] });
  }
  for (const c of commits)
    if (!settled.has(key(c.tx.id("hex"), c.cat!.tokenOutIdx)))
      return { ok: false, reason: `commit ${c.tx.id("hex").slice(0, 8)} has no settle in the batch (unsettled commit)`, type };

  // Per-interface arrangement: categorise + fingerprint every tx.
  for (const { tx, cat } of cats) {
    const reason = checkArrangement(tx, type, cat!.shape, byId);
    if (reason) return { ok: false, reason, type };
  }

  // Standalone single-tx events (genesis mints, terminal melts).
  for (const { tx, cat } of cats)
    if (cat!.shape.kind === "mint" || cat!.shape.kind === "melt")
      events.push({ kind: cat!.shape.kind as EventKind, txids: [tx.id("hex")] });

  return { ok: true, type, issuerPubKeyHex, events };
}
