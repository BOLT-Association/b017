// beef.ts - the data package for an off-chain (SPV) token transfer: Atomic BEEF (BRC-95) over BEEF V2 (BRC-96).
//
// A commit or settle received by SPV is only verifiable if the txs it spends travel with it, back to txs a block
// has proven. BEEF carries exactly that: the subject tx, every unproven ancestor, and a BUMP (merkle path) for the
// proven ones. b017 uses the CURRENT format only: BEEF V2, wrapped as Atomic BEEF so the package names ONE subject.
// BEEF V1 (BRC-62) is refused. The scanner checks the package is SELF-CONTAINED (every tx is proven by a BUMP or has
// all its inputs in the BEEF) but fromBeef does NOT check a BUMP's merkle root against a block header; do that with
// `Beef.verify(chainTracker)` / `tx.merklePath.verify(txid, chainTracker)`, which needs a header source. The one
// BUMP verifyEvents checks itself is an ANCHOR's, against the headers the caller supplies (isKnownBlockRoot).
import { Beef, Transaction, Utils } from "@bsv/sdk";

const BEEF_V2 = 4022206466; // 0200BEEF (LE)
const MAGIC_V1 = "0100beef";
const MAGIC_V2 = "0200beef";
const MAGIC_ATOMIC = "01010101";

/** True when the hex string / bytes begin with a BEEF magic (V1, V2 or Atomic). */
export function isBeef(x: string | Uint8Array | number[]): boolean {
  const head = typeof x === "string" ? x.slice(0, 8).toLowerCase() : Utils.toHex(Array.from(x).slice(0, 4));
  return head === MAGIC_V1 || head === MAGIC_V2 || head === MAGIC_ATOMIC;
}

/** The SDK orders a BEEF by each input's `sourceTXID`; an in-memory tx often carries only `sourceTransaction`, which
 *  would make every tx look input-less and lose the dependency order. Fill it in across the attached graph. */
function fillSourceTxids(tx: Transaction, seen = new Set<Transaction>()): void {
  if (seen.has(tx)) return;
  seen.add(tx);
  for (const input of tx.inputs) {
    if (!input.sourceTransaction) continue;
    if (input.sourceTXID === undefined) input.sourceTXID = input.sourceTransaction.id("hex");
    fillSourceTxids(input.sourceTransaction, seen);
  }
}

/** Serialise `tx` and every attached source tx (with merkle paths where known) as Atomic BEEF over BEEF V2. */
export function toAtomicBeef(tx: Transaction): number[] {
  fillSourceTxids(tx);
  const beef = new Beef(BEEF_V2);
  beef.mergeTransaction(tx);
  return beef.toBinaryAtomic(tx.id("hex"));
}

/**
 * Parse BEEF V2 (plain or Atomic) into its subject transaction, with every ancestor wired in through
 * `sourceTransaction` (and `merklePath` on proven ones). Throws on BEEF V1, on a BEEF that is not self-contained
 * (a tx neither proven by a BUMP nor having all its inputs in the BEEF, or txid-only entries), or on no subject.
 */
export function fromBeef(input: string | Uint8Array | number[]): Transaction {
  const bytes = typeof input === "string" ? Utils.toArray(input, "hex") : Array.from(input);
  const beef = Beef.fromBinary(bytes);
  if (beef.version !== BEEF_V2) throw new Error("BEEF V1 (BRC-62) is not accepted; use BEEF V2 (BRC-96) / Atomic BEEF (BRC-95)");
  if (!beef.isValid(false))
    throw new Error("BEEF is not self-contained: a tx is neither proven by a BUMP nor has all its inputs in the BEEF");
  // The SDK counts a tx with no inputs and no BUMP as vacuously valid. A real tx always spends something, so an
  // unproven tx with no inputs is a fabricated root: refuse it.
  for (const t of beef.txs)
    if (t.tx && t.bumpIndex === undefined && t.tx.inputs.length === 0)
      throw new Error(`BEEF is not self-contained: tx ${t.txid.slice(0, 8)} has no inputs and no BUMP`);
  const subject = beef.atomicTxid ?? [...beef.txs].reverse().find((t) => t.tx)?.txid;
  const tx = subject ? beef.findAtomicTransaction(subject) : undefined;
  if (!tx) throw new Error("BEEF has no subject transaction");
  return tx;
}
