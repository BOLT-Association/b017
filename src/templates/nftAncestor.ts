// NFT ancestor reconstruction (Lane B2b-2) — the 26 ancestor-piece unlock args [0..25] a settle
// must carry when it reaches back over a chain of >= 4 txs (e.g. a coupon round-trip's 2nd hop: the
// settle s2 reconstructs the commit c1 where the current owner received the token). These bytes let
// the contract rebuild + hash the ancestor commit to verify the lineage binding.
//
// The ancestor is a COMMIT tx with the shape: in[0]=bolt (spends the prior token), in[1]=funding;
// out[0]=token, out[1]=p2pb(beneficiary), out[2]=change. We extract from it (and its in[0] unlock,
// which carries the same 37-arg layout). `leadingValuePushes` = number of immutable value pushes at
// the front of the lock (0 = MinSimpleBolt identity, 1 = Discount/Balance) so the token-data fields
// (pubKeyHash/commitment/txoType/parent/grandparent) are read at the right chunk offset.
import { Transaction, Script, Utils } from "@bsv/sdk";
import { buildOutpoint } from "../boltLib.js";

const le32 = (n: number): number[] => { const w = new Utils.Writer(); w.writeUInt32LE(n); return w.toArray(); };
const le64 = (n: number): number[] => { const w = new Utils.Writer(); w.writeUInt64LE(n); return w.toArray(); };
const chunkData = (s: Script, i: number): number[] => (s.chunks[i]?.data as number[]) ?? [];
const outpointOfInput = (tx: Transaction, vin: number): number[] => {
  const inp = tx.inputs[vin];
  if (!inp.sourceTransaction) throw new Error(`ancestor in[${vin}] missing sourceTransaction`);
  return buildOutpoint(inp.sourceTransaction, inp.sourceOutputIndex);
};

/**
 * Extract the 26 ancestor pieces (in unlockArgs order [0..25]) from an ancestor commit tx.
 * The ancestor's in[0] must have its sourceTransaction attached (to read the spent-lock fields).
 */
export function nftAncestorPieces(ancestorTx: Transaction, leadingValuePushes: number): number[][] {
  const in0 = ancestorTx.inputs[0];
  const in1 = ancestorTx.inputs[1];
  const u = in0.unlockingScript!; // ancestor's bolt-spend unlock (37-arg layout)
  // The ancestor's SPENT lock (its in[0] CTX scriptCode = arg34) → the prior token's data fields.
  const spentLock = Script.fromBinary((u.chunks[34]?.data as number[]) ?? []);
  const sd = (i: number) => chunkData(spentLock, leadingValuePushes + i); // skip leading value push(es)
  // The ancestor's OUTPUT token (vout0) data fields.
  const outLock = ancestorTx.outputs[0].lockingScript;
  const od = (i: number) => chunkData(outLock, leadingValuePushes + i);
  const changeOut = ancestorTx.outputs[2];

  return [
    le32(ancestorTx.version),                              // [0]  ancestorVer
    outpointOfInput(ancestorTx, 0),                        // [1]  ancestorVin1Outpoint
    chunkData(u, 26),                                      // [2]  ancestorVin1FundOutpoint
    chunkData(u, 27),                                      // [3]  ancestorVin1ChangeOutput
    chunkData(u, 28),                                      // [4]  ancestorVin1BeneficiaryPubKeyHash
    chunkData(u, 29),                                      // [5]  ancestorVin1Sig
    chunkData(u, 30),                                      // [6]  ancestorVin1PubKey
    chunkData(u, 31),                                      // [7]  ancestorVin1CTXHeader
    sd(0),                                                 // [8]  ancestorVin1CTXScriptCodePubKeyHash
    sd(1),                                                 // [9]  ancestorVin1CTXScriptCodePubKeyHashCommitment
    sd(2),                                                 // [10] ancestorVin1CTXScriptCodeTxoType
    sd(3),                                                 // [11] ancestorVin1CTXScriptCodeParentOutpoint
    sd(4),                                                 // [12] ancestorVin1CTXScriptCodeGrandparentOutpoint
    chunkData(u, 35),                                      // [13] ancestorVin1CTXFooter
    le32((in0.sequence as number) ?? 0xffffffff),          // [14] ancestorVin1NSequence
    outpointOfInput(ancestorTx, 1),                        // [15] ancestorVin2Outpoint
    in1.unlockingScript!.toBinary(),                       // [16] ancestorVin2Script
    le32((in1.sequence as number) ?? 0xffffffff),          // [17] ancestorVin2NSequence
    od(0),                                                 // [18] ancestorVout1PubKeyHash
    od(1),                                                 // [19] ancestorVout1PubKeyHashCommitment
    od(2),                                                 // [20] ancestorVout1TxoType
    od(3),                                                 // [21] ancestorVout1ParentOutpoint
    od(4),                                                 // [22] ancestorVout1GrandparentOutpoint
    le64(changeOut.satoshis as number),                    // [23] ancestorChangeValue
    changeOut.lockingScript.toBinary(),                    // [24] ancestorChangeScript
    le32(ancestorTx.lockTime),                             // [25] ancestorNLockTime
  ];
}
