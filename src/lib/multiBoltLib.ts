// multiBoltLib.ts
// SimpleMultiBolt-specific ancestor reconstruction + CTX helpers.
//
// SimpleMultiBolt is the optimised fungible contract (16-byte balance, mandatory
// change/funding, swap unused) whose lock/unlock layout differs from canonical MultiBolt:
//   - 11 lock data chunks (vs 16): mintData / otherParentOutpoint / otherGenesisOutpoint /
//     otherIssuerPubKey / genesisOutpoint all removed.
//   - 198 unlock args (vs MultiBolt's ~253): no leading miscData; 89 ancestor pieces per
//     ancestor (vs 115); interopGenesisOutpoint + interopIssuerPubKey removed from the tail.
//
// Derived constants (see ts-bolt/src/sxFiles/SimpleMultiBolt.sx.json):
//   - ctxHeader sits at unlock chunk index 192  -> ARGS2CTX_SMB = 192   (MultiBolt: 247)
//   - lock data-push count                       -> PUSHDATAS_SMB = 11  (MultiBolt: 16)
//   - live section start in a token unlock script -> SKIP_SMB = 178      (MultiBolt: 231)
//   - txoType lock chunk index                   -> TXOTYPE_IDX_SMB = 6 (MultiBolt: 10)
//
// Self-contained: only depends on @bsv/sdk so the standalone package needs no sx tooling.

import { Script, Transaction, Utils } from "@bsv/sdk";
const { Reader, Writer } = Utils;

const ARGS2CTX_SMB = 192;
const PUSHDATAS_SMB = 11;
const SKIP_SMB = 178;
const TXOTYPE_IDX_SMB = 6;

// ---- layout-agnostic primitives (mirrors of boltLib.ts) ----

const getVersion = (tx: Transaction): number[] => {
  const w = new Utils.Writer();
  w.writeUInt32LE(tx.version);
  return w.toArray();
};

const getVinOutpoint = (tx: Transaction, vinIndex: number): number[] => {
  const w = new Utils.Writer();
  const input = tx.inputs[vinIndex];
  if (!input) return [];
  const txid = (input.sourceTransaction?.hash() as number[]) ||
    Utils.toArray(input.sourceTXID || "", "hex").reverse();
  if (!txid || txid.length === 0) return [];
  w.write(txid);
  w.writeUInt32LE(input.sourceOutputIndex);
  return w.toArray();
};

const getVinChunk = (tx: Transaction, vinIndex: number, chunkIdx: number): number[] => {
  const w = new Utils.Writer();
  const inputScript = tx.inputs[vinIndex].unlockingScript;
  const chunk = inputScript?.chunks?.[chunkIdx];
  w.write(chunk?.data || []);
  return w.toArray();
};

const getVinNSequence = (tx: Transaction, vinIndex: number): number[] => {
  const w = new Utils.Writer();
  const input = tx.inputs[vinIndex];
  if (!input) return [];
  w.writeUInt32LE(input.sequence || 0xffffffff);
  return w.toArray();
};

const getVinScript = (tx: Transaction, vinIndex: number): number[] => {
  const input = tx.inputs[vinIndex];
  if (!input) return [];
  return input?.unlockingScript?.toBinary() || [];
};

const getVoutDataArg = (tx: Transaction, voutIndex: number, chunkIdx: number): number[] => {
  const outputScript = tx.outputs[voutIndex].lockingScript;
  return (outputScript.chunks[chunkIdx]?.data as number[]) || [];
};

const getVoutChunk = (tx: Transaction, voutIndex: number, chunkIdx: number): number[] => {
  const outputScript = tx.outputs[voutIndex].lockingScript;
  return (outputScript.chunks[chunkIdx]?.data as number[]) || [];
};

const getChangeValue = (tx: Transaction, index: number): number[] => {
  const w = new Utils.Writer();
  const output = tx.outputs[index];
  if (!output) return [];
  w.writeUInt64LE(output.satoshis || 0);
  return w.toArray();
};

const getChangeScript = (tx: Transaction, index: number): number[] => {
  const w = new Utils.Writer();
  const output = tx.outputs[index];
  if (!output) return [];
  w.write(output.lockingScript.toBinary());
  return w.toArray();
};

const getTxNLockTime = (tx: Transaction): number[] => {
  const w = new Utils.Writer();
  w.writeUInt32LE(tx.lockTime);
  return w.toArray();
};

export const scriptChunksFromBin = (data: number[]): any[] => {
  return new Script().writeBin(data).chunks;
};

// ---- CTX reconstruction from a prior token tx's vin unlocking script ----
// ctxHeader is at ARGS2CTX_SMB; ctxCodeLockScriptCode/footer/lockLen at +3/+4/+5.

const getVinCTXPieceSMB = (
  tx: Transaction,
  vinIndex: number,
  piece: number,
  includeNSequence: boolean = false
): number[] => {
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
  tmpScript.writeBin(ctx || []);
  const scriptBin = tmpScript.toBinary();
  const headerLen = scriptBin.length - (ctx?.length || 0);
  const scriptCodeStart = 104 + headerLen;
  const scriptCodeBuf = scriptBin?.slice(scriptCodeStart);
  const reader = new Utils.Reader(scriptCodeBuf);
  const scriptCodeLen = reader.readVarIntNum();
  switch (piece) {
    case 0:
      w.write(ctx?.slice(0, 104) || []);
      break;
    case 1: {
      const scriptCode = Script.fromBinary(
        scriptCodeBuf?.slice(reader.pos, reader.pos + scriptCodeLen || 0)
      );
      const scriptData = new Script();
      for (let i = 0; i < PUSHDATAS_SMB; i++) {
        scriptData.chunks.push(scriptCode.chunks[i]);
      }
      w.write(scriptData.toBinary() || []);
      break;
    }
    case 2: {
      const remainingCtx = scriptBin.slice(scriptCodeStart + scriptCodeLen + reader.pos);
      w.write(remainingCtx || []);
      if (includeNSequence) {
        const input = tx.inputs[vinIndex];
        w.writeUInt32LE(input.sequence || 0xffffffff);
      }
      break;
    }
  }
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
  tmpScript.writeBin(ctx || []);
  const scriptBin = tmpScript.toBinary();
  const headerLen = scriptBin.length - (ctx?.length || 0);
  const scriptCodeStart = 104 + headerLen;
  const scriptCodeBuf = scriptBin?.slice(scriptCodeStart);
  const reader = new Utils.Reader(scriptCodeBuf);
  const scriptCodeLen = reader.readVarIntNum();
  const scriptCode = Script.fromBinary(
    scriptCodeBuf?.slice(reader.pos, reader.pos + scriptCodeLen || 0)
  );
  const chunk = scriptCode.chunks[argIdx];
  if (!!chunk && chunk.op === 0) return [];
  return (scriptCode.chunks[argIdx]?.data as number[]) || [];
};

// SimpleMultiBolt action bytes (no swap): 20 transferSettle, 21 transferCommit,
// 22 splitSettle, 23 splitCommit, 24 mergeSettle, 25 mergeCommit.
const determineTxTypeSMB = (tx: Transaction): string => {
  const firstToken = tx.outputs[0];
  const txoType = firstToken.lockingScript.chunks[TXOTYPE_IDX_SMB];
  const typeByte = txoType?.data?.[0] || -1;
  return typeByte.toString(16);
};

// All 89 SimpleMultiBolt ancestor piece names per ancestor (A or B).
export const ANCESTOR_PIECES_SMB = [
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
export const getAncestorPieceFungibleSMB = (piece: string, tx: Transaction): number[] => {
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

  switch (piece) {
    case "Version": res = getVersion(ancestorTx); break;
    // ---- Vin1 (token, always present) ----
    case "Vin1Outpoint": res = getVinOutpoint(ancestorTx, 0); break;
    case "Vin1GrandparentProofVoutIdx": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 0); break;
    case "Vin1InteropProofVoutIdx": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 1); break;
    case "Vin1InteropPubKeyHash": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 2); break;
    case "Vin1InteropOutpoint": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 3); break;
    case "Vin1InteropParentOutpoint": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 4); break;
    case "Vin1FundOutpoint": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 5); break;
    case "Vin1ChangeOutput": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 6); break;
    case "Vin1PubKeyHash1": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 7); break;
    case "Vin1PubKeyHash2": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 8); break;
    case "Vin1NextBalanceCommit": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 9); break;
    case "Vin1NextTxoType": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 10); break;
    case "Vin1InputIndexN": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 11); break;
    case "Vin1Sig": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 12); break;
    case "Vin1PubKey": res = getVinChunk(ancestorTx, 0, SKIP_SMB + 13); break;
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
    case "Vin1CTXFooter": res = getVinCTXPieceSMB(ancestorTx, 0, 2, false); break;
    case "Vin1NSequence": res = getVinNSequence(ancestorTx, 0); break;
    // ---- Vin2 (token, only mergeCommit) ----
    case "Vin2Outpoint": if (hasTwoTokenInputs) res = getVinOutpoint(ancestorTx, 1); break;
    case "Vin2GrandparentProofVoutIdx": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 0); break;
    case "Vin2InteropProofVoutIdx": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 1); break;
    case "Vin2InteropPubKeyHash": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 2); break;
    case "Vin2InteropOutpoint": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 3); break;
    case "Vin2InteropParentOutpoint": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 4); break;
    case "Vin2FundOutpoint": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 5); break;
    case "Vin2ChangeOutput": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 6); break;
    case "Vin2PubKeyHash1": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 7); break;
    case "Vin2PubKeyHash2": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 8); break;
    case "Vin2NextBalanceCommit": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 9); break;
    case "Vin2NextTxoType": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 10); break;
    case "Vin2InputIndexN": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 11); break;
    case "Vin2Sig": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 12); break;
    case "Vin2PubKey": if (hasTwoTokenInputs) res = getVinChunk(ancestorTx, 1, SKIP_SMB + 13); break;
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
    case "Vin2CTXFooter": if (hasTwoTokenInputs) res = getVinCTXPieceSMB(ancestorTx, 1, 2, false); break;
    case "Vin2NSequence": if (hasTwoTokenInputs) res = getVinNSequence(ancestorTx, 1); break;
    // ---- Funding vin (always last input) ----
    case "VinFundOutpoint": if (hasFunding) res = getVinOutpoint(ancestorTx, fundVinIdx); break;
    case "VinFundScript": if (hasFunding) res = getVinScript(ancestorTx, fundVinIdx); break;
    case "VinFundNSequence": if (hasFunding) res = getVinNSequence(ancestorTx, fundVinIdx); break;
    // ---- Vout1 (first token output, always present) ----
    case "Vout1Balance": res = getVoutDataArg(ancestorTx, 0, 0); break;
    case "Vout1BalanceCommit": res = getVoutDataArg(ancestorTx, 0, 1); break;
    case "Vout1PubKeyHash": res = getVoutDataArg(ancestorTx, 0, 2); break;
    case "Vout1PubKeyHashCommit": res = getVoutDataArg(ancestorTx, 0, 3); break;
    case "Vout1PubKeyHashCommit2": res = getVoutDataArg(ancestorTx, 0, 4); break;
    case "Vout1OtherGrandparentOutpoint": res = getVoutDataArg(ancestorTx, 0, 5); break;
    case "Vout1TxoType": res = getVoutDataArg(ancestorTx, 0, 6); break;
    case "Vout1OutputIndexN": res = getVoutDataArg(ancestorTx, 0, 7); break;
    case "Vout1ParentOutpoint": res = getVoutDataArg(ancestorTx, 0, 8); break;
    case "Vout1GrandparentOutpoint": res = getVoutDataArg(ancestorTx, 0, 9); break;
    case "Vout1IssuerPubKey": res = getVoutDataArg(ancestorTx, 0, 10); break;
    // ---- Vout2 (second token output, only splitSettle) ----
    case "Vout2Balance": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 0); break;
    case "Vout2BalanceCommit": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 1); break;
    case "Vout2PubKeyHash": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 2); break;
    case "Vout2PubKeyHashCommit": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 3); break;
    case "Vout2PubKeyHashCommit2": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 4); break;
    case "Vout2OtherGrandparentOutpoint": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 5); break;
    case "Vout2TxoType": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 6); break;
    case "Vout2OutputIndexN": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 7); break;
    case "Vout2ParentOutpoint": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 8); break;
    case "Vout2GrandparentOutpoint": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 9); break;
    case "Vout2IssuerPubKey": if (hasTwoBolts) res = getVoutDataArg(ancestorTx, 1, 10); break;
    // ---- Bolt (pay2Bolt) outputs ----
    case "ProofPubKeyHash1":
      // 1 token output always -> bolt1 at vout 1
      res = getVoutChunk(ancestorTx, 1, 4);
      break;
    case "ProofPubKeyHash2":
      // splitCommit emits a 2nd bolt commitment at vout 2
      if (hasTwoBolts) res = getVoutChunk(ancestorTx, 2, 4);
      break;
    // ---- Change + locktime ----
    case "ChangeValue": if (hasChange) res = getChangeValue(ancestorTx, changeVoutIdx); break;
    case "ChangeScript": if (hasChange) res = getChangeScript(ancestorTx, changeVoutIdx); break;
    case "NLockTime": res = getTxNLockTime(ancestorTx); break;
  }
  return res || [];
};

// 89 ancestorA + 89 ancestorB = 178 empty chunks (no leading miscData) for melt.
export const createEmptyFungibleAncestorChunksSMB = (): any[] => {
  const emptyChunks: any[] = [];
  for (let i = 0; i < SKIP_SMB; i++) {
    emptyChunks.push(...scriptChunksFromBin([]));
  }
  return emptyChunks;
};
