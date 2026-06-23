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
//
// Mirrors the SimpleMultiBolt ancestor idiom (multiBoltLib): a PIECE_NAMES list + an
// ancestorPiece(name, tx) switch — common naming + shape across both token streams.
import { Transaction, Script } from "@bsv/sdk";
import { le32, le64, scriptChunk, spentOutpoint } from "./boltLib.js";

/** The 26 NFT ancestor-piece names, in unlockArgs order [0..25]. */
export const PIECE_NAMES = [
  "Version",
  "Vin1Outpoint", "Vin1FundOutpoint", "Vin1ChangeOutput", "Vin1BeneficiaryPubKeyHash",
  "Vin1Sig", "Vin1PubKey", "Vin1CTXHeader",
  "Vin1CTXScriptCodePubKeyHash", "Vin1CTXScriptCodePubKeyHashCommitment", "Vin1CTXScriptCodeTxoType",
  "Vin1CTXScriptCodeParentOutpoint", "Vin1CTXScriptCodeGrandparentOutpoint",
  "Vin1CTXFooter", "Vin1NSequence",
  "Vin2Outpoint", "Vin2Script", "Vin2NSequence",
  "Vout1PubKeyHash", "Vout1PubKeyHashCommitment", "Vout1TxoType", "Vout1ParentOutpoint", "Vout1GrandparentOutpoint",
  "ChangeValue", "ChangeScript", "NLockTime",
];

/** Extract one named NFT ancestor piece from an ancestor commit tx (its in[0] must have its
 *  sourceTransaction attached). `leadingValuePushes`: 0 = identity, 1 = discount/balance. */
export function ancestorPiece(name: string, ancestorTx: Transaction, leadingValuePushes: number): number[] {
  const in0 = ancestorTx.inputs[0];
  const in1 = ancestorTx.inputs[1];
  const u = in0.unlockingScript!;                       // ancestor's bolt-spend unlock (37-arg layout)
  const spentLock = Script.fromBinary((u.chunks[34]?.data as number[]) ?? []); // its in[0] CTX scriptCode
  const sd = (i: number) => scriptChunk(spentLock, leadingValuePushes + i);     // prior token's data fields
  const outLock = ancestorTx.outputs[0].lockingScript;  // ancestor's OUTPUT token (vout0)
  const od = (i: number) => scriptChunk(outLock, leadingValuePushes + i);
  const changeOut = ancestorTx.outputs[2];
  switch (name) {
    case "Version": return le32(ancestorTx.version);
    case "Vin1Outpoint": return spentOutpoint(ancestorTx, 0);
    case "Vin1FundOutpoint": return scriptChunk(u, 26);
    case "Vin1ChangeOutput": return scriptChunk(u, 27);
    case "Vin1BeneficiaryPubKeyHash": return scriptChunk(u, 28);
    case "Vin1Sig": return scriptChunk(u, 29);
    case "Vin1PubKey": return scriptChunk(u, 30);
    case "Vin1CTXHeader": return scriptChunk(u, 31);
    case "Vin1CTXScriptCodePubKeyHash": return sd(0);
    case "Vin1CTXScriptCodePubKeyHashCommitment": return sd(1);
    case "Vin1CTXScriptCodeTxoType": return sd(2);
    case "Vin1CTXScriptCodeParentOutpoint": return sd(3);
    case "Vin1CTXScriptCodeGrandparentOutpoint": return sd(4);
    case "Vin1CTXFooter": return scriptChunk(u, 35);
    case "Vin1NSequence": return le32((in0.sequence as number) ?? 0xffffffff);
    case "Vin2Outpoint": return spentOutpoint(ancestorTx, 1);
    case "Vin2Script": return in1.unlockingScript!.toBinary();
    case "Vin2NSequence": return le32((in1.sequence as number) ?? 0xffffffff);
    case "Vout1PubKeyHash": return od(0);
    case "Vout1PubKeyHashCommitment": return od(1);
    case "Vout1TxoType": return od(2);
    case "Vout1ParentOutpoint": return od(3);
    case "Vout1GrandparentOutpoint": return od(4);
    case "ChangeValue": return le64(changeOut.satoshis as number);
    case "ChangeScript": return changeOut.lockingScript.toBinary();
    case "NLockTime": return le32(ancestorTx.lockTime);
    default: return [];
  }
}

/** All 26 ancestor pieces in unlockArgs order — PIECE_NAMES mapped through ancestorPiece. */
export function nftAncestorPieces(ancestorTx: Transaction, leadingValuePushes: number): number[][] {
  return PIECE_NAMES.map((name) => ancestorPiece(name, ancestorTx, leadingValuePushes));
}
