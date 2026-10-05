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
//                        commit<->settle linkage. Its VERDICT comes from the same scan as verifyEvents (so a
//                        lone commit, an orphan settle or a forged history behind the event is refused), and
//                        the txs must hold exactly one action (its anchor and its mint may ride along).
//   verifyEvents(txs)  — validate a BATCH of events: recognise the type, pin the issuer across the
//                        whole batch, fingerprint every tx's arrangement, then pair the events —
//                        every commit must be matched by a settle (and vice-versa) via parentOutpoint.
//                        A lone melt is a valid single-tx event. A MINT is not: a mint only NAMES an issuerPubKey
//                        (anyone can mint an output naming anybody's key), and the issuer guard runs when the
//                        genesis is first SPENT, so a mint is accepted only with a COMMIT in the same event/batch
//                        that spends it. Otherwise the verdict is `unauthenticated: true` (not a signature failure).
//                        The scanner also EXECUTES every input whose source tx is supplied (the covenants, the
//                        signatures): structure alone cannot tell a forged commit from a real one, and off-chain
//                        (SPV / zero-funding) txs have not been validated by any node. EVERY input's source tx must
//                        be supplied (attached, in the batch, or inside a BEEF - Atomic BEEF over V2, see beef.ts),
//                        else the verdict is a failure.
//                        THE ANCHOR: the token tx a batch stands on - the settle BEFORE the batch's first commit
//                        (settle N-1), or the mint when the batch starts at genesis. What travels p2p is
//                        [mint, c1, s1] or [sN-1, cN, sN]. The anchor is validated FIRST and like any event tx:
//                        structure, golden fingerprint, issuer, and script execution (so ITS sources must be
//                        supplied too). An anchor settle is the one settle allowed without its commit in the batch.
//                        An anchor only attached as a `sourceTransaction` (or inside a BEEF) is pulled into the batch.
//                        The result names the anchors; the CALLER broadcasts them (verifyAndBroadcast), so the
//                        network is seen to accept (or already know) the tx the batch is built on. Local execution
//                        reaches the anchor's own inputs only; the ancestry behind it is what the broadcast proves.
//                        An anchor must be a tx the network has seen and will therefore mine. An UNFUNDED anchor
//                        pays no fee, so being seen proves nothing: it is refused unless it carries a merkle path
//                        into a block header the caller knows (ScanOpts.isKnownBlockRoot, or a chainTracker given
//                        to verifyAndBroadcast). The events standing on the anchor may be unfunded and stay off chain.
//                        A HEADER-PROVEN anchor (funded or not) is not re-executed and needs no sources of its own:
//                        consensus validated it, and a BEEF stops at proven txs. So an anchor is one of: proven
//                        by its merkle tree into a known chain header, or seen on the network (broadcast), or mined.
//                        VALUE CONSERVATION is checked: an ANCHOR whose outputs exceed its inputs is refused; an EVENT
//                        tx that does so is only reported (`offChainOnly`), since a commit / settle that is never
//                        broadcast is still valid off chain. `requireBroadcastable` turns the report into a refusal.
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
import { OP, Spend, Transaction, Script, Utils } from "@bsv/sdk";
import { recognizeType, recognizeP2P, issuerPubKeyOf, type TokenType } from "./fingerprints.js";
import { fromBeef, isBeef } from "./beef.js";

// Field push-indices per type (parent/grandparent/issuer are the last 3 pushes; txoType varies).
type FieldName = "pubKeyHash" | "commitment" | "txoType" | "parent" | "grandparent";
const FIELDS: Record<TokenType, Record<FieldName, number>> = {
  MinSimpleBOLT: { pubKeyHash: 0, commitment: 1, txoType: 2, parent: 3, grandparent: 4 },
  AuthBOLT: { pubKeyHash: 0, commitment: 1, txoType: 2, parent: 3, grandparent: 4 },
  SimpleMultiBOLT: { pubKeyHash: 2, commitment: 3, txoType: 6, parent: 8, grandparent: 9 },
};
const field = (lock: Script, type: TokenType, f: FieldName): number[] =>
  (lock.chunks[FIELDS[type][f]]?.data as number[]) ?? [];
const fieldHex = (lock: Script, type: TokenType, f: FieldName): string => Utils.toHex(field(lock, type, f));

// A 36-byte outpoint is txid (32, internal byte order) + vout (4, LE). The display txid is reversed.
// A short/empty buffer (a tampered or absent field) yields a txid that cannot match any real tx, so
// the linkage check fails closed rather than throwing.
function parseOutpoint(op: number[]): { txidHex: string; vout: number } {
  const bytes = Array.isArray(op) ? op : [];
  const txidHex = Utils.toHex([...bytes.slice(0, 32)].reverse());
  const v = new Uint8Array(4);
  v.set(bytes.slice(32, 36)); // missing bytes stay 0 — a short/absent field can't match a real outpoint
  const vout = (v[0] | (v[1] << 8) | (v[2] << 16) | (v[3] << 24)) >>> 0;
  return { txidHex, vout };
}

export interface ScanOpts {
  expectedType?: TokenType;
  trustedIssuerPubKey?: number[] | string;
  /** Your block headers: is `merkleRoot` the merkle root of the block at `height`? An anchor whose merkle path
   *  proves it into a header you know is HEADER-PROVEN: consensus already validated it, so its own inputs are not
   *  re-executed and its sources need not be supplied (a BEEF stops at proven txs). An UNFUNDED anchor is refused
   *  unless it is header-proven. */
  isKnownBlockRoot?: (merkleRoot: string, height: number) => boolean;
  /** Refuse a batch holding an event tx whose outputs exceed its inputs (see ScanResult.offChainOnly). Default
   *  false: such a tx is valid OFF chain (a never-broadcast commit / settle certifying auth data) and is only
   *  reported. Set true when the events are meant to be broadcast as they are. */
  requireBroadcastable?: boolean;
}
/** An event tx whose outputs exceed its inputs: its scripts are valid, but no node will accept it as built. */
export interface OffChainOnlyTx { txid: string; inputSats: number; outputSats: number }
/** An async source of block headers (the `@bsv/sdk` ChainTracker shape), usable with verifyAndBroadcast. */
export interface HeaderSource { isValidRootForHeight(root: string, height: number): Promise<boolean> }
/** A tx an event spends that is not itself part of the event; `proven` = it carries a BUMP (merkle path). */
export interface SourceTx { txid: string; proven: boolean }
export type EventKind = "mint" | "transfer" | "split" | "merge" | "melt";
/** What the network said about a broadcast anchor. "already-seen" = the node already knows the tx (mempool or mined). */
export type AnchorStatus = "accepted" | "already-seen" | "rejected";
/** An anchor: the token tx a batch stands on (the settle before its first commit, or the mint). The caller must
 *  broadcast it; `status` / `detail` are filled in by verifyAndBroadcast. */
export interface AnchorRef {
  txid: string;
  kind: "mint" | "settle";
  status?: AnchorStatus;
  detail?: string;
}
export interface AnchorBroadcastResult { status: AnchorStatus; detail?: string }
/** The caller's broadcaster: send ONE anchor tx (its unproven ancestors are attached through `sourceTransaction`)
 *  and report whether the network accepted it, already knew it, or rejected it. */
export type AnchorBroadcaster = (anchor: Transaction) => Promise<AnchorBroadcastResult>;
export interface ScanResult {
  ok: boolean;
  reason?: string;
  type?: TokenType;
  issuerPubKeyHex?: string;
  /** The txs the event txs spend that are not themselves event txs (parents / funding), with whether each carries a BUMP.
   *  A `proven` source is NOT checked against a block header here: verify its merkle path with your ChainTracker.
   *  (Only an ANCHOR's merkle path is checked, against `isKnownBlockRoot`.) */
  sources?: SourceTx[];
  /** true when the batch holds a mint that no commit in it spends (the mint alone proves nothing about the issuer key). */
  unauthenticated?: boolean;
  events?: { kind: EventKind; txids: string[] }[];
  /** The anchors the batch stands on (see AnchorRef). `ok: true` from verifyEvents is only FINAL once the network has
   *  accepted (or already seen) every one of them: broadcast them, or call verifyAndBroadcast. */
  anchors?: AnchorRef[];
  /** VALUE CONSERVATION, reported not refused: the event txs whose outputs exceed their inputs. They are valid off
   *  chain (the scripts execute) but cannot be broadcast as built; fund them first. Absent when every event tx
   *  conserves value. An ANCHOR that creates value is refused instead: the network would never accept it. */
  offChainOnly?: OffChainOnlyTx[];
}
export interface EventResult {
  ok: boolean;
  reason?: string;
  type?: TokenType;
  kind?: EventKind;
  /** See ScanResult.sources. */
  sources?: SourceTx[];
  /** true when the event is a mint that no commit in it spends (see ScanResult.unauthenticated). */
  unauthenticated?: boolean;
  /** See ScanResult.anchors. */
  anchors?: AnchorRef[];
  /** See ScanResult.offChainOnly. */
  offChainOnly?: OffChainOnlyTx[];
}

/** Thrown when an input tx (string) cannot be parsed; caught at the verify entry points and turned
 *  into an `ok: false` result so a malformed batch never escapes as an exception. */
class ParseError extends Error {}
/** The first line of whatever was thrown (an Error's message, else the value itself). */
const errText = (e: unknown): string => String((e as any)?.message ?? e).split(String.fromCharCode(10))[0];
/** The scanner never throws. A Transaction OBJECT handed in by the caller can still be broken in ways parsing
 *  cannot be (an input with no source reference or no unlocking script, an output with no locking script), and
 *  the SDK throws when such a tx is serialised. Anything a verifier body throws becomes a refusal. */
const failClosed = <T extends { ok: boolean; reason?: string }>(run: () => T): T => {
  try {
    return run();
  } catch (e) {
    return { ok: false, reason: `unverifiable input: ${errText(e)}` } as T;
  }
};
/** An event tx: a Transaction, raw tx hex, or BEEF (hex / bytes: Atomic BEEF over BEEF V2) whose subject is the tx. */
export type TxInput = Transaction | string | Uint8Array;
/** Parse one event tx. Throws ParseError and nothing else, so the entry points can report `e.message` as is. */
const toTx = (t: TxInput): Transaction => {
  if (t instanceof Transaction) return t;
  if (typeof t !== "string" && !(t instanceof Uint8Array) && !Array.isArray(t))
    throw new ParseError("not a transaction: expected a Transaction, raw tx hex, or BEEF hex / bytes");
  if (isBeef(t)) {
    try {
      return fromBeef(t);
    } catch (e) {
      throw new ParseError(`invalid BEEF: ${errText(e)}`);
    }
  }
  try {
    return typeof t === "string" ? Transaction.fromHex(t) : Transaction.fromBinary(Array.from(t));
  } catch (e) {
    throw new ParseError(`malformed transaction hex: ${errText(e)}`);
  }
};
const optHex = (b?: number[] | string): string | undefined =>
  b == null ? undefined : typeof b === "string" ? b.toLowerCase() : Utils.toHex(b);

// ---- interface fingerprinting: classify every input / output ----
type Cls = "token" | "p2p" | "p2pkh" | "external" | "other";
type ById = Map<string, Transaction>;
/** The tx an input spends: its attached source, else the tx of the batch its outpoint names. */
const sourceOf = (input: any, byId: ById): Transaction | undefined =>
  input.sourceTransaction ?? (input.sourceTXID ? byId.get(input.sourceTXID) : undefined);
/** The txid an input spends: the outpoint's, else the attached source's. */
const spentTxid = (input: any): string | undefined => input.sourceTXID ?? input.sourceTransaction?.id("hex");

/** Classify an output's locking script. token = strict golden fingerprint; p2p = the b017 marker
 *  proof output; p2pkh = a plain pay-to-pubkey-hash (change); else "other". */
function classifyOut(lock: Script, type: TokenType): Cls {
  if (recognizeType(lock, type)) return "token";
  if (recognizeP2P(lock)) return "p2p"; // golden p2Proof fingerprint (b017 marker + static skeleton)
  const c = lock?.chunks ?? [];
  if (
    c.length === 5 && c[0].op === OP.OP_DUP && c[1].op === OP.OP_HASH160 && c[2].data?.length === 20 &&
    c[3].op === OP.OP_EQUALVERIFY && c[4].op === OP.OP_CHECKSIG
  ) return "p2pkh";
  return "other";
}

/** Classify an input by fingerprinting the output it spends (via the attached source tx, else a
 *  source tx supplied in the batch); "external" when the source is outside the supplied set. */
function classifyIn(input: any, type: TokenType, byId: ById): Cls {
  const spent = sourceOf(input, byId)?.outputs?.[input.sourceOutputIndex]?.lockingScript;
  if (!spent) return "external"; // source not in the supplied set (or out-of-range vout)
  return classifyOut(spent, type);
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

/** The first MINT in `txs` that no COMMIT in `txs` spends, or null. A mint is just an output naming an issuerPubKey;
 *  the issuer guard only runs when the genesis token is first SPENT, so a mint is authenticated only by a commit that
 *  spends its token output (funded or not). */
function unauthenticatedMint(txs: Transaction[], type: TokenType, byId: ById): Transaction | null {
  const cats = txs.map((tx) => ({ tx, cat: categorise(tx, type, byId) }));
  const commits = cats.filter((c) => c.cat?.shape.kind === "commit").map((c) => c.tx);
  for (const { tx, cat } of cats) {
    if (cat?.shape.kind !== "mint") continue;
    const txid = tx.id("hex");
    const spent = commits.some((c) =>
      c.inputs.some((i: any) => spentTxid(i) === txid && i.sourceOutputIndex === cat.tokenOutIdx));
    if (!spent) return tx;
  }
  return null;
}
/**
 * EXECUTE every input of every tx (event txs and anchors) on the @bsv/sdk Spend engine. The structural checks say a
 * tx HAS the right shape; only execution shows its scripts are VALID. That matters for off-chain (SPV /
 * zero-funding) packages, which no node has validated: a forged commit (signed by a stranger, refused by the
 * covenant's issuer guard) is structurally perfect. requireSources runs first and refuses any input whose source tx
 * was not supplied, so no input is skipped here. Returns the first failure.
 */
function executeInputs(txs: Transaction[], byId: ById): string | undefined {
  const outpointRef = (i: any) => ({
    sourceTXID: spentTxid(i) as string,
    sourceOutputIndex: i.sourceOutputIndex as number,
    sequence: (i.sequence ?? 0xffffffff) as number,
  });
  for (const tx of txs) {
    const id = tx.id("hex").slice(0, 8);
    for (let vin = 0; vin < tx.inputs.length; vin++) {
      const input: any = tx.inputs[vin];
      const out = sourceOf(input, byId)?.outputs?.[input.sourceOutputIndex];
      /* v8 ignore next 2 -- requireSources runs before executeInputs and refuses a missing source; if that order ever changes this fails closed instead of skipping the input */
      if (!out) return `script execution failed: tx ${id} input ${vin}: its source tx was not supplied`;
      let failure: string | undefined;
      try {
        if (!input.unlockingScript) failure = "no unlocking script";
        else if (
          !new Spend({
            sourceTXID: outpointRef(input).sourceTXID,
            sourceOutputIndex: input.sourceOutputIndex,
            lockingScript: out.lockingScript,
            sourceSatoshis: out.satoshis ?? 0,
            transactionVersion: tx.version,
            otherInputs: tx.inputs.filter((_: any, k: number) => k !== vin).map(outpointRef),
            unlockingScript: input.unlockingScript,
            inputSequence: input.sequence ?? 0xffffffff,
            inputIndex: vin,
            outputs: tx.outputs,
            lockTime: tx.lockTime,
          }).validate()
        ) failure = "the script evaluated false";
      } catch (e: any) {
        failure = errText(e);
      }
      if (failure) return `script execution failed: tx ${id} input ${vin}: ${failure}`;
    }
  }
  return undefined;
}
/**
 * Every input of every event tx must have its source tx SUPPLIED (attached, or another event tx): without it the
 * input's script cannot be executed, so the event cannot be authenticated. Returns the first missing source as a
 * failure reason, else the non-event source txs (with whether each carries a BUMP).
 */
function requireSources(txs: Transaction[], byId: ById): { failure?: string; sources: SourceTx[] } {
  const sources = new Map<string, SourceTx>();
  for (const tx of txs) {
    const id = tx.id("hex").slice(0, 8);
    for (let vin = 0; vin < tx.inputs.length; vin++) {
      const input: any = tx.inputs[vin];
      const src = sourceOf(input, byId);
      if (!src || !src.outputs?.[input.sourceOutputIndex])
        return { failure: `source tx ${String(input.sourceTXID ?? "?").slice(0, 8)} of tx ${id} input ${vin} was not supplied (send the package as BEEF)`, sources: [] };
      const sid = src.id("hex");
      // An attached source must BE the tx the input names: the outpoint is what the signature commits to.
      if (input.sourceTXID && input.sourceTXID !== sid)
        return { failure: `attached source ${sid.slice(0, 8)} of tx ${id} input ${vin} is not the tx its outpoint names (${String(input.sourceTXID).slice(0, 8)})`, sources: [] };
      if (!byId.has(sid) && !sources.has(sid)) sources.set(sid, { txid: sid, proven: !!src.merklePath });
    }
  }
  return { sources: [...sources.values()] };
}
/**
 * Is `tx` HEADER-PROVEN: does it carry a merkle path that proves it into a block header the caller knows? If so
 * consensus has already validated it. `why` says what is missing when it is not.
 */
function headerProof(tx: Transaction, opts: ScanOpts): { proven: boolean; why: string } {
  const path = tx.merklePath;
  if (!path) return { proven: false, why: "it is accepted only with an SPV proof (a merkle path) to a known block header" };
  if (typeof opts.isKnownBlockRoot !== "function")
    return { proven: false, why: "it carries a merkle path, but no block headers were supplied to check it against (isKnownBlockRoot)" };
  let root: string;
  try {
    root = path.computeRoot(tx.id("hex"));
  } catch (e: any) {
    return { proven: false, why: `its merkle path does not prove it (${errText(e)})` };
  }
  let known = false;
  try {
    known = opts.isKnownBlockRoot(root, path.blockHeight) === true;
  } catch { /* a throwing header lookup is not a known header */ }
  return known ? { proven: true, why: "" } : { proven: false, why: `its merkle root is not a known block header at height ${path.blockHeight}` };
}

/**
 * An anchor is proven into a known block header, or it is a tx the network has seen and will therefore mine. An
 * UNFUNDED anchor (no funding input) gives the network no reason to mine it, so being seen proves nothing. It can
 * still be mined (a friendly miner), so it is accepted only once it has been, i.e. when it is header-proven.
 * Called for anchors that are NOT header-proven; returns the refusal reason, if any.
 */
function anchorNotMinable(tx: Transaction, type: TokenType, byId: ById, why: string): string | undefined {
  const id = tx.id("hex").slice(0, 8);
  // An anchor whose outputs exceed its inputs CREATES value: no node accepts that, funded or not.
  const { inputSats, outputSats } = valueOf(tx, byId);
  if (outputSats > inputSats)
    return `anchor ${id} creates value (inputs ${inputSats} sat, outputs ${outputSats} sat): the network will never accept it; ${why}`;
  const funded = tx.inputs.some((i) => {
    const cls = classifyIn(i, type, byId);
    return cls === "p2pkh" || cls === "external";
  });
  if (!funded) return `unfunded anchor ${id}: ${tx.merklePath ? "" : "it pays no fee, so the network will not mine it on sight; "}${why}`;
  return undefined;
}
/** The satoshis a tx spends and creates (its sources must be supplied: requireSources has run). */
function valueOf(tx: Transaction, byId: ById): { inputSats: number; outputSats: number } {
  let inputSats = 0;
  for (const input of tx.inputs as any[]) {
    inputSats += sourceOf(input, byId)?.outputs?.[input.sourceOutputIndex]?.satoshis ?? 0;
  }
  let outputSats = 0;
  for (const out of tx.outputs) outputSats += out.satoshis ?? 0;
  return { inputSats, outputSats };
}
const unauthenticatedReason = (tx: Transaction) =>
  `unauthenticated mint ${tx.id("hex").slice(0, 8)}: no commit in the event spends it, so nothing shows the sender holds the issuer key`;

const actionKind = (txoTypeHex: string): EventKind =>
  txoTypeHex === "23" ? "split" : txoTypeHex === "25" ? "merge" : "transfer";

/** Fingerprint every interface of a token tx and check it matches its action's golden shape:
 *  the leading token in/out are strictly recognised; the p2p proof outputs are exact in count;
 *  trailing change (p2pkh) + funding/proof inputs are loose; nothing may be "other". */
function checkArrangement(tx: Transaction, type: TokenType, shape: Shape, byId: ById, outputsOnly = false): string | null {
  const id = tx.id("hex").slice(0, 8);
  const outs = tx.outputs.map((o) => classifyOut(o.lockingScript, type));
  const ins = tx.inputs.map((i) => classifyIn(i, type, byId));
  if (outs.includes("other")) return `uninspected output in ${id} [${outs}]`;
  if (!outputsOnly && ins.includes("other")) return `uninspected input in ${id} [${ins}]`;
  // outputs: [token × tokenOut] then [p2p × proofOut] then [p2pkh change × rest]
  for (let k = 0; k < shape.tokenOut; k++)
    if (outs[k] !== "token") return `${shape.kind} ${id}: token output @${k} (got ${outs[k] ?? "none"}) [${outs}]`;
  for (let k = 0; k < shape.proofOut; k++)
    if (outs[shape.tokenOut + k] !== "p2p") return `${shape.kind} ${id}: p2p output @${shape.tokenOut + k} [${outs}]`;
  for (let k = shape.tokenOut + shape.proofOut; k < outs.length; k++)
    if (outs[k] !== "p2pkh") return `${shape.kind} ${id}: change p2pkh @${k} (got ${outs[k]}) [${outs}]`;
  // A header-proven anchor: consensus validated its inputs, and their sources need not be supplied.
  if (outputsOnly) return null;
  // inputs: [token × tokenIn] then [p2p proof × any (settle only, contiguous)] then [funding: external | p2pkh].
  // A p2Proof input (consuming a commit's proof output) is STRICTLY fingerprinted (classifyIn ->
  // recognizeP2P) and is only legitimate on a settle, immediately after the token input(s); a proof
  // input on any other tx kind, or after the funding region, is rejected.
  for (let k = 0; k < shape.tokenIn; k++)
    if (ins[k] !== "token") return `${shape.kind} ${id}: token input @${k} (got ${ins[k] ?? "none"}) [${ins}]`;
  let k = shape.tokenIn;
  if (shape.kind === "settle") while (ins[k] === "p2p") k++; // strict, contiguous proof inputs
  for (; k < ins.length; k++)
    if (!(ins[k] === "external" || ins[k] === "p2pkh"))
      return `${shape.kind} ${id}: unexpected input @${k}: ${ins[k]} (a p2Proof input is only valid on a settle, immediately after the token input) [${ins}]`;
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
      const s = sourceOf(inp, byId);
      if (s) {
        const lock = s.outputs?.[inp.sourceOutputIndex]?.lockingScript; // an out-of-range vout is not a token
        const t = lock ? recognizeType(lock, expected) : undefined;
        if (t) return t;
      }
    }
  return undefined;
}

/**
 * Verify ONE token event - a commit->settle pair or a melt (a mint is accepted only with the commit that spends
 * it). Categorises each tx by its token's txoType action, fingerprints EVERY interface against the action's
 * golden shape, checks the settle links back to the commit, then takes its verdict from the same scan as
 * verifyEvents: the anchor step, pairing, sources and script execution all apply, and `anchors` names what the
 * caller must broadcast. A lone commit or a lone settle is NOT an event.
 */
export function verifyEvent(eventTxs: TxInput[], opts: ScanOpts = {}): EventResult {
  return failClosed(() => verifyOneEvent(eventTxs, opts));
}
function verifyOneEvent(eventTxs: TxInput[], opts: ScanOpts): EventResult {
  if (!Array.isArray(eventTxs)) return { ok: false, reason: "event must be an array of transactions" };
  let txs: Transaction[];
  try {
    txs = eventTxs.map(toTx);
  } catch (e) {
    return { ok: false, reason: (e as ParseError).message }; // toTx throws ParseError only
  }
  if (txs.length === 0) return { ok: false, reason: "empty event" };
  const byId: ById = new Map(txs.map((t) => [t.id("hex"), t]));

  const type = eventType(txs, byId, opts.expectedType);
  if (!type) return { ok: false, reason: "no BOLT token recognised in event" };
  /* v8 ignore next 2 -- eventType() already filtered by expectedType, so this is unreachable; kept as defense-in-depth */
  if (opts.expectedType && type !== opts.expectedType)
    return { ok: false, reason: `expected ${opts.expectedType}, got ${type}`, type };

  for (const tx of txs) {
    const cat = categorise(tx, type, byId);
    if (!cat) return { ok: false, reason: `tx ${tx.id("hex").slice(0, 8)} is not a token tx`, type };
    const reason = checkArrangement(tx, type, cat.shape, byId);
    if (reason) return { ok: false, reason, type, kind: cat.shape.kind as EventKind };
  }

  const stray = unauthenticatedMint(txs, type, byId);
  if (stray) return { ok: false, reason: unauthenticatedReason(stray), type, kind: "mint", unauthenticated: true };
  const need = requireSources(txs, byId);
  if (need.failure) return { ok: false, reason: need.failure, type };

  // The event's commit must be settled by a settle of the event (an ANCHOR settle may ride along; it links elsewhere).
  const commitTx = txs.find((t) => categorise(t, type, byId)?.shape.kind === "commit");
  const settleTxs = txs.filter((t) => categorise(t, type, byId)?.shape.kind === "settle");
  if (commitTx && settleTxs.length > 0) {
    const cIdx = commitTx.outputs.findIndex((o) => recognizeType(o.lockingScript, type));
    const linked = settleTxs.some((settleTx) => {
      const sIdx = settleTx.outputs.findIndex((o) => recognizeType(o.lockingScript, type));
      const p = parseOutpoint(field(settleTx.outputs[sIdx].lockingScript, type, "parent"));
      return p.txidHex === commitTx.id("hex") && p.vout === cIdx;
    });
    if (!linked) return { ok: false, reason: "settle.parent does not link to the commit token", type };
  }
  // The verdict itself comes from the SAME scan as verifyEvents (anchor step, pairing, sources, script execution), so
  // the two entry points cannot disagree: a lone commit, an orphan settle or a forged history behind the event is
  // refused here exactly as it is there. On top of that, an event is exactly ONE action (a mint riding with the
  // commit that authenticates it is not counted).
  const r = scan(txs, opts);
  if (!r.ok)
    return {
      ok: false, reason: r.reason, type,
      ...(r.unauthenticated ? { unauthenticated: true } : {}), ...(r.offChainOnly ? { offChainOnly: r.offChainOnly } : {}),
    };
  const actions = r.events!.filter((e) => e.kind !== "mint");
  if (actions.length !== 1)
    return { ok: false, reason: `expected exactly one event, got ${actions.length} (use verifyEvents for a batch)`, type };
  return {
    ok: true, type, kind: actions[0].kind, sources: r.sources, anchors: r.anchors,
    ...(r.offChainOnly ? { offChainOnly: r.offChainOnly } : {}),
  };
}

/**
 * Verify a BATCH of transactional events end to end. The multistep inspection: recognise the type,
 * pin the issuer across every token output in the batch, fingerprint every tx's interface
 * arrangement, then pair the events — every commit (txoType 21/23/25) must be matched by a settle
 * that links back via parentOutpoint, and every settle must link to a commit in the batch. A lone
 * melt (terminal) is a valid single-tx event; a MINT must be spent by a commit in the batch, else the
 * result is `unauthenticated: true` (a mint alone does not prove the sender holds the issuer key).
 * The batch's ANCHORS (settle N-1 / the mint) are validated with it and named in `anchors`; this function is offline,
 * so the caller still has to broadcast them (verifyAndBroadcast does both).
 */
export function verifyEvents(txsIn: TxInput[], opts: ScanOpts = {}): ScanResult {
  return scan(txsIn, opts);
}

/**
 * verifyEvents, then BROADCAST every anchor through the caller's broadcaster. The batch is accepted only when the
 * offline verdict is ok AND the network accepted (or had already seen) each anchor: that shows the tx the batch
 * stands on exists and that a node accepted its scripts and its ancestry. Nothing is broadcast when the offline
 * verdict fails. A rejected anchor, a throwing broadcaster or an unknown status all fail closed.
 */
export async function verifyAndBroadcast(
  txsIn: TxInput[], broadcastAnchor: AnchorBroadcaster, opts: ScanOpts & { chainTracker?: HeaderSource } = {},
): Promise<ScanResult> {
  if (typeof broadcastAnchor !== "function") return { ok: false, reason: "an anchor broadcaster is required" };
  const anchorTxs: Transaction[] = [];
  // With an async chainTracker (and no sync isKnownBlockRoot): a first pass collects the merkle roots the anchors
  // offer, the tracker answers for each, and the real scan then runs against those answers. Nothing is broadcast
  // before that.
  let scanOpts: ScanOpts = opts;
  const tracker = opts.isKnownBlockRoot ? undefined : opts.chainTracker;
  if (tracker) {
    const offered = new Map<string, { root: string; height: number }>();
    scan(txsIn, { ...opts, isKnownBlockRoot: (root, height) => { offered.set(`${height}:${root}`, { root, height }); return false; } });
    const known = new Set<string>();
    for (const [key, { root, height }] of offered) {
      try {
        if ((await tracker.isValidRootForHeight(root, height)) === true) known.add(key);
      } catch { /* a failing tracker is not a known header */ }
    }
    scanOpts = { ...opts, isKnownBlockRoot: (root, height) => known.has(`${height}:${root}`) };
  }
  const result = scan(txsIn, scanOpts, anchorTxs);
  if (!result.ok) return result;
  const anchors: AnchorRef[] = [];
  for (let k = 0; k < anchorTxs.length; k++) {
    const ref = result.anchors![k];
    let sent: AnchorBroadcastResult;
    try {
      sent = await broadcastAnchor(anchorTxs[k]);
    } catch (e: any) {
      sent = { status: "rejected", detail: `broadcast failed: ${errText(e)}` };
    }
    const known = sent?.status === "accepted" || sent?.status === "already-seen";
    const detail = sent?.detail ?? (known || sent?.status === "rejected" ? undefined : `unknown broadcast status ${String(sent?.status)}`);
    anchors.push({ ...ref, status: known ? sent.status : "rejected", ...(detail === undefined ? {} : { detail }) });
    if (!known) {
      const reason = `anchor ${ref.kind} ${ref.txid.slice(0, 8)} was not accepted by the network${detail ? `: ${detail}` : ""}`;
      return { ok: false, reason, type: result.type, issuerPubKeyHex: result.issuerPubKeyHex, anchors };
    }
  }
  return { ...result, anchors };
}

/** The offline scan behind verifyEvents. `anchorTxsOut` receives the anchor Transactions, in `anchors` order. */
function scan(txsIn: TxInput[], opts: ScanOpts, anchorTxsOut?: Transaction[]): ScanResult {
  return failClosed(() => scanBatch(txsIn, opts, anchorTxsOut));
}
function scanBatch(txsIn: TxInput[], opts: ScanOpts, anchorTxsOut?: Transaction[]): ScanResult {
  if (!Array.isArray(txsIn)) return { ok: false, reason: "batch must be an array of transactions" };
  let txs: Transaction[];
  try {
    txs = txsIn.map(toTx);
  } catch (e) {
    return { ok: false, reason: (e as ParseError).message }; // toTx throws ParseError only
  }
  if (txs.length === 0) return { ok: false, reason: "empty batch" };
  const byId: ById = new Map(txs.map((t) => [t.id("hex"), t]));

  // Every recognised token output across the batch.
  type TokenRef = { txid: string; vout: number; type: TokenType; lock: Script };
  const tokensOf = (list: Transaction[]): TokenRef[] => {
    const found: TokenRef[] = [];
    for (const tx of list) {
      const txid = tx.id("hex");
      tx.outputs.forEach((o, vout) => {
        const type = recognizeType(o.lockingScript, opts.expectedType);
        if (type) found.push({ txid, vout, type, lock: o.lockingScript });
      });
    }
    return found;
  };
  let tokens = tokensOf(txs);
  // A batch of melts only has no token OUTPUT: read the type off the token a melt spends (its attached anchor).
  let type: TokenType | undefined = tokens[0]?.type;
  for (const tx of txs) {
    if (type) break;
    for (const input of tx.inputs as any[]) {
      const lock = input.sourceTransaction?.outputs?.[input.sourceOutputIndex]?.lockingScript;
      type = (lock && recognizeType(lock, opts.expectedType)) || undefined;
      if (type) break;
    }
  }
  if (!type) return { ok: false, reason: "no BOLT token output recognised" };

  // THE ANCHOR STEP. The anchor is the settle N-1 (or the mint) whose token output is SPENT BY a commit or a melt of
  // the batch. The anchor itself is never a melt: a melt has no token output. When it was supplied only as an
  // attached source (or inside a BEEF), pull it INTO the batch so it gets every check an event tx gets: golden
  // fingerprint, issuer pin, arrangement, sources, script execution.
  const promoted = new Set<string>();
  for (const tx of [...txs]) {
    const kind = categorise(tx, type, byId)?.shape.kind;
    if (kind !== "commit" && kind !== "melt") continue;
    for (const input of tx.inputs as any[]) {
      const src: Transaction | undefined = input.sourceTransaction;
      if (!src || classifyIn(input, type, byId) !== "token") continue;
      const sid = src.id("hex");
      if (byId.has(sid)) continue;
      byId.set(sid, src);
      promoted.add(sid);
      txs.unshift(src);
    }
  }
  if (promoted.size > 0) tokens = tokensOf(txs);
  if (tokens.some((t) => t.type !== type)) return { ok: false, reason: "mixed token types in batch" };
  /* v8 ignore next 2 -- recognizeType() already filtered by expectedType, so this is unreachable; kept as defense-in-depth */
  if (opts.expectedType && type !== opts.expectedType)
    return { ok: false, reason: `expected ${opts.expectedType}, got ${type}` };

  // Issuer consistent across all token outputs, and == the trusted issuer (if supplied).
  const issuers = new Set(tokens.map((t) => Utils.toHex(issuerPubKeyOf(t.lock, type))));
  if (issuers.size !== 1) return { ok: false, reason: "inconsistent issuerPubKey across batch" };
  const issuerPubKeyHex = [...issuers][0];
  /* v8 ignore next 2 -- a recognised token's last push is exactly 33 bytes (the registry layout), so this never fires; kept as defense-in-depth */
  if (issuerPubKeyHex.length !== 66) // a compressed secp256k1 pubkey is exactly 33 bytes
    return { ok: false, reason: "issuerPubKey is not a 33-byte compressed public key", type };
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
  const anchors: AnchorRef[] = [];
  const anchorTxs: Transaction[] = [];
  const addAnchor = (tx: Transaction, kind: AnchorRef["kind"]) => {
    anchors.push({ txid: tx.id("hex"), kind });
    anchorTxs.push(tx);
  };
  // A token output of `t` is spent by a commit / melt of the batch: `t` is what that spend stands on.
  const spentAsToken = (t: Transaction): boolean => {
    const id = t.id("hex");
    return cats.some((c) =>
      (c.cat!.shape.kind === "commit" || c.cat!.shape.kind === "melt") &&
      c.tx.inputs.some((i: any) => {
        const lock = t.outputs[i.sourceOutputIndex]?.lockingScript;
        return spentTxid(i) === id && !!lock && !!recognizeType(lock, type);
      }));
  };
  // An anchor must be a SETTLED token (or a mint): a token still in a commit state is not something to build on.
  for (const { tx, cat } of cats)
    if (promoted.has(tx.id("hex")) && cat!.shape.kind !== "settle" && cat!.shape.kind !== "mint")
      return { ok: false, reason: `anchor ${tx.id("hex").slice(0, 8)} is not a settled token or a mint (it is a ${cat!.shape.kind})`, type };

  for (const s of cats.filter((c) => c.cat!.shape.kind === "settle")) {
    const sLock = s.tx.outputs[s.cat!.tokenOutIdx].lockingScript;
    const p = parseOutpoint(field(sLock, type, "parent"));
    const commit = commits.find((c) => c.tx.id("hex") === p.txidHex && c.cat!.tokenOutIdx === p.vout);
    if (!commit) {
      // The one settle allowed without its commit: the ANCHOR (settle N-1), which a commit / melt of the batch spends.
      if (spentAsToken(s.tx)) {
        addAnchor(s.tx, "settle");
        continue;
      }
      return { ok: false, reason: `settle ${s.tx.id("hex").slice(0, 8)} links to no commit in the batch (orphan settle)`, type };
    }
    settled.add(key(commit.tx.id("hex"), commit.cat!.tokenOutIdx));
    const cLock = commit.tx.outputs[commit.cat!.tokenOutIdx].lockingScript;
    events.push({ kind: actionKind(fieldHex(cLock, type, "txoType")), txids: [commit.tx.id("hex"), s.tx.id("hex")] });
  }
  for (const c of commits)
    if (!settled.has(key(c.tx.id("hex"), c.cat!.tokenOutIdx)))
      return { ok: false, reason: `commit ${c.tx.id("hex").slice(0, 8)} has no settle in the batch (unsettled commit)`, type };

  // Which anchors are HEADER-PROVEN (a merkle path into a known block header)? Consensus validated those, so their
  // inputs are not re-examined and their sources need not be supplied. Every anchor is asked, up front.
  const proofs = new Map<Transaction, { proven: boolean; why: string }>();
  for (const { tx, cat } of cats)
    if (cat!.shape.kind === "mint" || anchorTxs.includes(tx)) proofs.set(tx, headerProof(tx, opts));
  const headerProven = (tx: Transaction) => proofs.get(tx)?.proven === true;
  const toExecute = txs.filter((tx) => !headerProven(tx));

  // Per-interface arrangement: categorise + fingerprint every tx.
  for (const { tx, cat } of cats) {
    const reason = checkArrangement(tx, type, cat!.shape, byId, headerProven(tx));
    if (reason) return { ok: false, reason, type };
  }

  // Every mint must be spent by a commit in the batch (a mint alone does not authenticate the issuer key).
  const stray = unauthenticatedMint(txs, type, byId);
  if (stray) return { ok: false, reason: unauthenticatedReason(stray), type, issuerPubKeyHex, unauthenticated: true };

  // Every input's source tx must be supplied (so its script can be executed), else the batch cannot be authenticated.
  const need = requireSources(toExecute, byId);
  if (need.failure) return { ok: false, reason: need.failure, type, issuerPubKeyHex };

  // Standalone single-tx events (genesis mints - each already shown to be spent by a commit - and terminal melts).
  // A mint is also an ANCHOR (the batch starts at genesis); one pulled in from a source is an anchor but not an event.
  for (const { tx, cat } of cats) {
    if (cat!.shape.kind === "mint") addAnchor(tx, "mint");
    if ((cat!.shape.kind === "mint" || cat!.shape.kind === "melt") && !promoted.has(tx.id("hex")))
      events.push({ kind: cat!.shape.kind as EventKind, txids: [tx.id("hex")] });
  }

  // Execute every supplied input: structure alone does not show the scripts (signatures, covenants) are valid.
  const failure = executeInputs(toExecute, byId);
  if (failure) return { ok: false, reason: failure, type, issuerPubKeyHex };

  // An anchor that is not header-proven must be one the network will mine on sight (see anchorNotMinable).
  for (const anchor of anchorTxs) {
    if (headerProven(anchor)) continue;
    const refused = anchorNotMinable(anchor, type, byId, proofs.get(anchor)!.why);
    if (refused) return { ok: false, reason: refused, type, issuerPubKeyHex };
  }

  // VALUE CONSERVATION for the event txs: checked and REPORTED, refused only on request. A tx whose outputs exceed
  // its inputs executes fine off chain (a never-broadcast commit / settle certifying auth data) but no node would
  // accept it as built. (Anchors were checked above; a header-proven anchor was validated by consensus.)
  const offChainOnly: OffChainOnlyTx[] = [];
  for (const tx of toExecute) {
    if (anchorTxs.includes(tx)) continue;
    const { inputSats, outputSats } = valueOf(tx, byId);
    if (outputSats > inputSats) offChainOnly.push({ txid: tx.id("hex"), inputSats, outputSats });
  }
  if (opts.requireBroadcastable && offChainOnly.length > 0) {
    const t = offChainOnly[0];
    return {
      ok: false, type, issuerPubKeyHex, offChainOnly,
      reason: `tx ${t.txid.slice(0, 8)} creates value (inputs ${t.inputSats} sat, outputs ${t.outputSats} sat): it cannot be broadcast as built`,
    };
  }

  anchorTxsOut?.push(...anchorTxs);
  return {
    ok: true, type, issuerPubKeyHex, events, sources: need.sources, anchors,
    ...(offChainOnly.length > 0 ? { offChainOnly } : {}),
  };
}
