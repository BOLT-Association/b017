// multiBoltLib.ts
// SimpleMultiBolt-specific ancestor reconstruction + CTX helpers.
//
// SimpleMultiBolt is the optimised fungible contract: 16-byte balance, mandatory change/funding.
//   - 11 lock data chunks.
//   - 198 unlock args; 89 ancestor pieces per ancestor.
//
// Layout constants:
//   - ctxHeader sits at unlock chunk index 192   -> ARGS2CTX_SMB = 192
//   - lock data-push count                       -> PUSHDATAS_SMB = 11
//   - live section start in a token unlock script -> SKIP_SMB = 178
//   - txoType lock chunk index                   -> TXOTYPE_IDX_SMB = 6
//
// Self-contained: depends only on @bsv/sdk (no sx tooling at runtime).

import { Script, Transaction, Utils } from "@bsv/sdk";
import {
  txVersion, txLockTime, spentOutpoint, vinChunk, vinSequence, vinScript,
  voutChunk, outputValue, outputScript, scriptChunksFromBin,
} from "../boltLib.js";
const { Reader, Writer } = Utils;

const ARGS2CTX_SMB = 192;
const PUSHDATAS_SMB = 11;
const SKIP_SMB = 178;
const TXOTYPE_IDX_SMB = 6;

// ---- CTX reconstruction from a prior token tx's vin unlocking script ----
// ctxHeader is at ARGS2CTX_SMB; ctxCodeLockScriptCode/footer/lockLen at +3/+4/+5.

// piece 0 = ctxHeader (104 bytes); piece 2 = ctxFooter (the bytes after the scriptCode).
const getVinCTXPieceSMB = (tx: Transaction, vinIndex: number, piece: number): number[] => {
  const w = new Utils.Writer();
  const inputScript = tx.inputs[vinIndex]?.unlockingScript;
  if (!inputScript?.chunks?.[ARGS2CTX_SMB]) return [];
  const ctxHeader = inputScript.chunks[ARGS2CTX_SMB].data;
  const ctxCodeLockScriptCode = inputScript.chunks[ARGS2CTX_SMB + 3]?.data;
  const ctxFooter = inputScript.chunks[ARGS2CTX_SMB + 4]?.data;
  const ctxCodeLockLen = inputScript.chunks[ARGS2CTX_SMB + 5]?.data;

  const ctx = (ctxHeader || [])
    .concat(ctxCodeLockLen || [])
    .concat(ctxCodeLockScriptCode || [])
    .concat(ctxFooter || []);
  const tmpScript = new Script();
  tmpScript.writeBin(ctx);
  const scriptBin = tmpScript.toBinary();
  const headerLen = scriptBin.length - ctx.length;
  const scriptCodeStart = 104 + headerLen;
  const reader = new Utils.Reader(scriptBin.slice(scriptCodeStart));
  const scriptCodeLen = reader.readVarIntNum();
  if (piece === 0) w.write(ctx.slice(0, 104));
  else w.write(scriptBin.slice(scriptCodeStart + scriptCodeLen + reader.pos)); // piece 2: footer
  return w.toArray();
};

// Extract a single committed lock-data arg out of the reconstructed CTX scriptCode.
// argIdx indexes the 11 SMB lock data chunks (balance=0 ... issuerPubKey=10).
const getVinCTXDataArgSMB = (tx: Transaction, vinIndex: number, argIdx: number): number[] => {
  const inputScript = tx.inputs[vinIndex]?.unlockingScript;
  if (!inputScript?.chunks?.[ARGS2CTX_SMB]) return [];
  const ctxHeader = inputScript.chunks[ARGS2CTX_SMB].data;
  const ctxCodeLockScriptCode = inputScript.chunks[ARGS2CTX_SMB + 3]?.data;
  const ctxFooter = inputScript.chunks[ARGS2CTX_SMB + 4]?.data;
  const ctxCodeLockLen = inputScript.chunks[ARGS2CTX_SMB + 5]?.data;

  const ctx = (ctxHeader || [])
    .concat(ctxCodeLockLen || [])
    .concat(ctxCodeLockScriptCode || [])
    .concat(ctxFooter || []);
  const tmpScript = new Script();
  tmpScript.writeBin(ctx);
  const scriptBin = tmpScript.toBinary();
  const headerLen = scriptBin.length - ctx.length;
  const scriptCodeStart = 104 + headerLen;
  const scriptCodeBuf = scriptBin.slice(scriptCodeStart);
  const reader = new Utils.Reader(scriptCodeBuf);
  const scriptCodeLen = reader.readVarIntNum();
  const scriptCode = Script.fromBinary(scriptCodeBuf.slice(reader.pos, reader.pos + scriptCodeLen));
  const chunk = scriptCode.chunks[argIdx];
  if (chunk && chunk.op === 0) return [];
  return (chunk?.data as number[]) ?? [];
};

// SimpleMultiBolt action bytes (no swap): 20 transferSettle, 21 transferCommit,
// 22 splitSettle, 23 splitCommit, 24 mergeSettle, 25 mergeCommit.
const determineTxTypeSMB = (tx: Transaction): string => {
  const firstToken = tx.outputs[0];
  const txoType = firstToken.lockingScript.chunks[TXOTYPE_IDX_SMB];
  const typeByte = txoType?.data?.[0] || -1;
  return typeByte.toString(16);
};

// The 89 SimpleMultiBolt ancestor piece names per ancestor.
export const PIECE_NAMES = [
  "Version",
  "Vin1Outpoint",
  "Vin1GrandparentProofVoutIdx", "Vin1InteropProofVoutIdx",
  "Vin1InteropPubKeyHash", "Vin1InteropOutpoint", "Vin1InteropParentOutpoint",
  "Vin1FundOutpoint", "Vin1ChangeOutput",
  "Vin1PubKeyHash1", "Vin1PubKeyHash2", "Vin1NextBalanceCommit", "Vin1NextTxoType", "Vin1InputIndexN",
  "Vin1Sig", "Vin1PubKey",
  "Vin1CTXHeader", "Vin1CTXBalance", "Vin1CTXBalanceCommit",
  "Vin1CTXPubKeyHash", "Vin1CTXPubKeyHashCommit", "Vin1CTXPubKeyHashCommit2",
  "Vin1CTXOtherGrandparentOutpoint",
  "Vin1CTXTxoType", "Vin1CTXOutputIndexN",
  "Vin1CTXParentOutpoint", "Vin1CTXGrandparentOutpoint", "Vin1CTXIssuerPubKey",
  "Vin1CTXFooter", "Vin1NSequence",
  "Vin2Outpoint",
  "Vin2GrandparentProofVoutIdx", "Vin2InteropProofVoutIdx",
  "Vin2InteropPubKeyHash", "Vin2InteropOutpoint", "Vin2InteropParentOutpoint",
  "Vin2FundOutpoint", "Vin2ChangeOutput",
  "Vin2PubKeyHash1", "Vin2PubKeyHash2", "Vin2NextBalanceCommit", "Vin2NextTxoType", "Vin2InputIndexN",
  "Vin2Sig", "Vin2PubKey",
  "Vin2CTXHeader", "Vin2CTXBalance", "Vin2CTXBalanceCommit",
  "Vin2CTXPubKeyHash", "Vin2CTXPubKeyHashCommit", "Vin2CTXPubKeyHashCommit2",
  "Vin2CTXOtherGrandparentOutpoint",
  "Vin2CTXTxoType", "Vin2CTXOutputIndexN",
  "Vin2CTXParentOutpoint", "Vin2CTXGrandparentOutpoint", "Vin2CTXIssuerPubKey",
  "Vin2CTXFooter", "Vin2NSequence",
  "VinFundOutpoint", "VinFundScript", "VinFundNSequence",
  "Vout1Balance", "Vout1BalanceCommit",
  "Vout1PubKeyHash", "Vout1PubKeyHashCommit", "Vout1PubKeyHashCommit2",
  "Vout1OtherGrandparentOutpoint",
  "Vout1TxoType", "Vout1OutputIndexN",
  "Vout1ParentOutpoint", "Vout1GrandparentOutpoint", "Vout1IssuerPubKey",
  "Vout2Balance", "Vout2BalanceCommit",
  "Vout2PubKeyHash", "Vout2PubKeyHashCommit", "Vout2PubKeyHashCommit2",
  "Vout2OtherGrandparentOutpoint",
  "Vout2TxoType", "Vout2OutputIndexN",
  "Vout2ParentOutpoint", "Vout2GrandparentOutpoint", "Vout2IssuerPubKey",
  "ProofPubKeyHash1", "ProofPubKeyHash2",
  "ChangeValue", "ChangeScript", "NLockTime",
];

// Extract one named ancestor piece from a SimpleMultiBolt transaction.
export const ancestorPiece = (name: string, tx: Transaction): number[] => {
  let res: number[] = [];
  const ancestorTx = tx;
  const txType = determineTxTypeSMB(ancestorTx);
  const hasTwoTokenInputs = txType === "25"; // mergeCommit (swap removed)
  const hasTwoBolts = txType === "23";        // splitCommit
  const fundVinIdx = ancestorTx.inputs.length - 1;
  const changeVoutIdx = ancestorTx.outputs.length - 1;
  const lastOutput = ancestorTx.outputs[changeVoutIdx];
  const hasChange = lastOutput?.lockingScript?.chunks?.length === 5;
  const hasFunding = ancestorTx.inputs.length > (hasTwoTokenInputs ? 2 : 1);

  switch (name) {
    case "Version": res = txVersion(ancestorTx); break;
    // ---- Vin1 (token, always present) ----
    case "Vin1Outpoint": res = spentOutpoint(ancestorTx, 0); break;
    case "Vin1GrandparentProofVoutIdx": res = vinChunk(ancestorTx, 0, SKIP_SMB + 0); break;
    case "Vin1InteropProofVoutIdx": res = vinChunk(ancestorTx, 0, SKIP_SMB + 1); break;
    case "Vin1InteropPubKeyHash": res = vinChunk(ancestorTx, 0, SKIP_SMB + 2); break;
    case "Vin1InteropOutpoint": res = vinChunk(ancestorTx, 0, SKIP_SMB + 3); break;
    case "Vin1InteropParentOutpoint": res = vinChunk(ancestorTx, 0, SKIP_SMB + 4); break;
    case "Vin1FundOutpoint": res = vinChunk(ancestorTx, 0, SKIP_SMB + 5); break;
    case "Vin1ChangeOutput": res = vinChunk(ancestorTx, 0, SKIP_SMB + 6); break;
    case "Vin1PubKeyHash1": res = vinChunk(ancestorTx, 0, SKIP_SMB + 7); break;
    case "Vin1PubKeyHash2": res = vinChunk(ancestorTx, 0, SKIP_SMB + 8); break;
    case "Vin1NextBalanceCommit": res = vinChunk(ancestorTx, 0, SKIP_SMB + 9); break;
    case "Vin1NextTxoType": res = vinChunk(ancestorTx, 0, SKIP_SMB + 10); break;
    case "Vin1InputIndexN": res = vinChunk(ancestorTx, 0, SKIP_SMB + 11); break;
    case "Vin1Sig": res = vinChunk(ancestorTx, 0, SKIP_SMB + 12); break;
    case "Vin1PubKey": res = vinChunk(ancestorTx, 0, SKIP_SMB + 13); break;
    case "Vin1CTXHeader": res = getVinCTXPieceSMB(ancestorTx, 0, 0); break;
    case "Vin1CTXBalance": res = getVinCTXDataArgSMB(ancestorTx, 0, 0); break;
    case "Vin1CTXBalanceCommit": res = getVinCTXDataArgSMB(ancestorTx, 0, 1); break;
    case "Vin1CTXPubKeyHash": res = getVinCTXDataArgSMB(ancestorTx, 0, 2); break;
    case "Vin1CTXPubKeyHashCommit": res = getVinCTXDataArgSMB(ancestorTx, 0, 3); break;
    case "Vin1CTXPubKeyHashCommit2": res = getVinCTXDataArgSMB(ancestorTx, 0, 4); break;
    case "Vin1CTXOtherGrandparentOutpoint": res = getVinCTXDataArgSMB(ancestorTx, 0, 5); break;
    case "Vin1CTXTxoType": res = getVinCTXDataArgSMB(ancestorTx, 0, 6); break;
    case "Vin1CTXOutputIndexN": res = getVinCTXDataArgSMB(ancestorTx, 0, 7); break;
    case "Vin1CTXParentOutpoint": res = getVinCTXDataArgSMB(ancestorTx, 0, 8); break;
    case "Vin1CTXGrandparentOutpoint": res = getVinCTXDataArgSMB(ancestorTx, 0, 9); break;
    case "Vin1CTXIssuerPubKey": res = getVinCTXDataArgSMB(ancestorTx, 0, 10); break;
    case "Vin1CTXFooter": res = getVinCTXPieceSMB(ancestorTx, 0, 2); break;
    case "Vin1NSequence": res = vinSequence(ancestorTx, 0); break;
    // ---- Vin2 (token, only mergeCommit) ----
    case "Vin2Outpoint": if (hasTwoTokenInputs) res = spentOutpoint(ancestorTx, 1); break;
    case "Vin2GrandparentProofVoutIdx": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 0); break;
    case "Vin2InteropProofVoutIdx": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 1); break;
    case "Vin2InteropPubKeyHash": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 2); break;
    case "Vin2InteropOutpoint": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 3); break;
    case "Vin2InteropParentOutpoint": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 4); break;
    case "Vin2FundOutpoint": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 5); break;
    case "Vin2ChangeOutput": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 6); break;
    case "Vin2PubKeyHash1": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 7); break;
    case "Vin2PubKeyHash2": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 8); break;
    case "Vin2NextBalanceCommit": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 9); break;
    case "Vin2NextTxoType": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 10); break;
    case "Vin2InputIndexN": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 11); break;
    case "Vin2Sig": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 12); break;
    case "Vin2PubKey": if (hasTwoTokenInputs) res = vinChunk(ancestorTx, 1, SKIP_SMB + 13); break;
    case "Vin2CTXHeader": if (hasTwoTokenInputs) res = getVinCTXPieceSMB(ancestorTx, 1, 0); break;
    case "Vin2CTXBalance": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 0); break;
    case "Vin2CTXBalanceCommit": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 1); break;
    case "Vin2CTXPubKeyHash": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 2); break;
    case "Vin2CTXPubKeyHashCommit": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 3); break;
    case "Vin2CTXPubKeyHashCommit2": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 4); break;
    case "Vin2CTXOtherGrandparentOutpoint": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 5); break;
    case "Vin2CTXTxoType": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 6); break;
    case "Vin2CTXOutputIndexN": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 7); break;
    case "Vin2CTXParentOutpoint": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 8); break;
    case "Vin2CTXGrandparentOutpoint": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 9); break;
    case "Vin2CTXIssuerPubKey": if (hasTwoTokenInputs) res = getVinCTXDataArgSMB(ancestorTx, 1, 10); break;
    case "Vin2CTXFooter": if (hasTwoTokenInputs) res = getVinCTXPieceSMB(ancestorTx, 1, 2); break;
    case "Vin2NSequence": if (hasTwoTokenInputs) res = vinSequence(ancestorTx, 1); break;
    // ---- Funding vin (always last input) ----
    case "VinFundOutpoint": if (hasFunding) res = spentOutpoint(ancestorTx, fundVinIdx); break;
    case "VinFundScript": if (hasFunding) res = vinScript(ancestorTx, fundVinIdx); break;
    case "VinFundNSequence": if (hasFunding) res = vinSequence(ancestorTx, fundVinIdx); break;
    // ---- Vout1 (first token output, always present) ----
    case "Vout1Balance": res = voutChunk(ancestorTx, 0, 0); break;
    case "Vout1BalanceCommit": res = voutChunk(ancestorTx, 0, 1); break;
    case "Vout1PubKeyHash": res = voutChunk(ancestorTx, 0, 2); break;
    case "Vout1PubKeyHashCommit": res = voutChunk(ancestorTx, 0, 3); break;
    case "Vout1PubKeyHashCommit2": res = voutChunk(ancestorTx, 0, 4); break;
    case "Vout1OtherGrandparentOutpoint": res = voutChunk(ancestorTx, 0, 5); break;
    case "Vout1TxoType": res = voutChunk(ancestorTx, 0, 6); break;
    case "Vout1OutputIndexN": res = voutChunk(ancestorTx, 0, 7); break;
    case "Vout1ParentOutpoint": res = voutChunk(ancestorTx, 0, 8); break;
    case "Vout1GrandparentOutpoint": res = voutChunk(ancestorTx, 0, 9); break;
    case "Vout1IssuerPubKey": res = voutChunk(ancestorTx, 0, 10); break;
    // ---- Vout2 (second token output, only splitSettle) ----
    case "Vout2Balance": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 0); break;
    case "Vout2BalanceCommit": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 1); break;
    case "Vout2PubKeyHash": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 2); break;
    case "Vout2PubKeyHashCommit": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 3); break;
    case "Vout2PubKeyHashCommit2": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 4); break;
    case "Vout2OtherGrandparentOutpoint": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 5); break;
    case "Vout2TxoType": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 6); break;
    case "Vout2OutputIndexN": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 7); break;
    case "Vout2ParentOutpoint": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 8); break;
    case "Vout2GrandparentOutpoint": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 9); break;
    case "Vout2IssuerPubKey": if (hasTwoBolts) res = voutChunk(ancestorTx, 1, 10); break;
    // ---- Bolt (pay2Bolt) outputs ----
    case "ProofPubKeyHash1":
      // 1 token output always -> bolt1 at vout 1
      res = voutChunk(ancestorTx, 1, 4);
      break;
    case "ProofPubKeyHash2":
      // splitCommit emits a 2nd bolt commitment at vout 2
      if (hasTwoBolts) res = voutChunk(ancestorTx, 2, 4);
      break;
    // ---- Change + locktime ----
    case "ChangeValue": if (hasChange) res = outputValue(ancestorTx, changeVoutIdx); break;
    case "ChangeScript": if (hasChange) res = outputScript(ancestorTx, changeVoutIdx); break;
    case "NLockTime": res = txLockTime(ancestorTx); break;
  }
  return res;
};

// 89 ancestorA + 89 ancestorB = 178 empty chunks (no leading miscData) for melt.
export const createEmptyFungibleAncestorChunksSMB = (): any[] => {
  const emptyChunks: any[] = [];
  for (let i = 0; i < SKIP_SMB; i++) {
    emptyChunks.push(...scriptChunksFromBin([]));
  }
  return emptyChunks;
};
