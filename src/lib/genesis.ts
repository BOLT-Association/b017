// genesis.ts
// The two leading lock pushes of the genesis family (FixedBolt, OpenBolt, SerialBolt; genesis layout v3):
//
//   field 0  genesisOutpoint (FixedBolt, SerialBolt) | lastMergeOrGenesisOutpoint (OpenBolt), 36 bytes
//            - the MINT output carries a null (36 zero bytes) field;
//            - the GENESIS SPEND (the first spend of the mint) writes the mint outpoint it spends;
//            - OpenBolt only: a MERGE COMMIT re-roots it to vin0's token outpoint (which is also the merge
//              output's parentOutpoint);
//            - every other hop copies it unchanged.
//   field 1  mintData: the issuer's bytes (0..255) on the MINT only; OP_0 on every later output.
//
// The covenant enforces each rule; this computes the values a builder must write (the same rules the
// sibling toolchain's simulator stamps onto its reference chains).
import { Transaction, Utils } from "@bsv/sdk";

export const NULL_OUTPOINT: readonly number[] = Object.freeze(new Array(36).fill(0x00));
/** mintData is pushed with at most PUSHDATA1 (the covenant's canonical skip is capped there). */
export const MINT_DATA_MAX_BYTES = 255;

/** The 36-byte outpoint txid(LE) || vout(LE32). */
export const outpointOf = (tx: Transaction, vout: number): number[] => {
  const w = new Utils.Writer();
  w.write(tx.hash() as number[]);
  w.writeUInt32LE(vout);
  return w.toArray();
};

const isNull = (b: readonly number[] | undefined): boolean => !b || b.length === 0 || b.every((x) => x === 0);

export interface GenesisFieldInput {
  /** The token tx this output's vin0 spends, or undefined for a mint. */
  prevTx?: Transaction;
  /** Which output of prevTx is that token. */
  prevVoutIdx?: number;
  /** Lock chunk index of parentOutpoint in this contract (FixedBolt/OpenBolt 10, SerialBolt 5). */
  parentIdx: number;
  /** OpenBolt merge commit: re-root to vin0's token outpoint. */
  reroot?: boolean;
}

/** Field 0 (genesis / LMG) for a new token output. */
export function genesisFieldFor({ prevTx, prevVoutIdx = 0, parentIdx, reroot = false }: GenesisFieldInput): number[] {
  if (!prevTx) return [...NULL_OUTPOINT]; // the mint
  const prevLock = prevTx.outputs[prevVoutIdx].lockingScript;
  const prevParent = prevLock.chunks[parentIdx]?.data as number[] | undefined;
  if (isNull(prevParent)) return outpointOf(prevTx, prevVoutIdx); // genesis spend: the mint outpoint it spends
  if (reroot) return outpointOf(prevTx, prevVoutIdx);            // OpenBolt merge commit: vin0's token outpoint
  return [...(prevLock.chunks[0].data as number[])]; // copied (a genesis-family token always carries the 36-byte field)
}

/** Field 1 (mintData) for a new token output: the issuer's bytes on the mint, empty (OP_0) after. */
export function mintDataFor(isMint: boolean, mintData: number[] = []): number[] {
  if (!isMint) return [];
  if (mintData.length > MINT_DATA_MAX_BYTES) throw new Error(`mintData is ${mintData.length} bytes; at most ${MINT_DATA_MAX_BYTES} (PUSHDATA1)`);
  return [...mintData];
}
