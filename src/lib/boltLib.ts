// boltLib.ts — layout-agnostic helpers shared by both token streams:
// verifyTx (bsv Spend), buildOutpoint, buildChangeOutput, createSignature, splitCtx,
// and the tx-field primitives (le32/le64, spentOutpoint, vin*/vout*, …).

import { Script, Spend, Transaction, Utils, PrivateKey, TransactionSignature, Hash } from "@bsv/sdk";
const { Reader, Writer } = Utils;

// Verify every input of a tx with the @bsv/sdk Spend engine.
export const verifyTx = (
  tx: Transaction,
  skipOutputCheck: boolean = false
): { valid: boolean; scriptExecutions: { spend: Spend; valid: boolean }[] } => {
  let inputTotal = 0;
  const txid = tx.id("hex");
  const scriptExecutions: { spend: Spend; valid: boolean }[] = [];
  for (let i = 0; i < tx.inputs.length; i++) {
    const input = tx.inputs[i];
    if (typeof input.sourceTransaction !== "object") {
      throw new Error(`Verification failed: input ${i} of ${txid} is missing its source transaction.`);
    }
    if (typeof input.unlockingScript !== "object") {
      throw new Error(`Verification failed: input ${i} of ${txid} is missing its unlocking script.`);
    }
    const sourceOutput = input.sourceTransaction.outputs[input.sourceOutputIndex];
    inputTotal += sourceOutput.satoshis || 0;
    const sourceTxid = input.sourceTransaction.id("hex");
    const otherInputs = tx.inputs.filter((_, idx) => idx !== i);
    if (typeof input.sourceTXID === "undefined") input.sourceTXID = sourceTxid;
    const spend = new Spend({
      sourceTXID: input.sourceTXID,
      sourceOutputIndex: input.sourceOutputIndex,
      lockingScript: sourceOutput.lockingScript,
      sourceSatoshis: sourceOutput.satoshis || 0,
      transactionVersion: tx.version,
      otherInputs,
      unlockingScript: input.unlockingScript,
      inputSequence: input.sequence || 0xffffffff,
      inputIndex: i,
      outputs: tx.outputs,
      lockTime: tx.lockTime,
    });
    const valid = spend.validate();
    scriptExecutions.push({ spend, valid });
    if (!valid) return { valid: false, scriptExecutions };
  }
  let outputTotal = 0;
  for (const out of tx.outputs) {
    if (typeof out.satoshis !== "number") throw new Error("Every output must have a defined amount during verification.");
    outputTotal += out.satoshis;
  }
  if (!skipOutputCheck && outputTotal > inputTotal) throw new Error("Output total greater than input total");
  return { valid: true, scriptExecutions };
};

// 36-byte outpoint (txid LE + 4-byte vout).
export const buildOutpoint = (tx: Transaction, outputIndex: number): number[] => {
  const writer = new Utils.Writer();
  writer.write(tx.hash() as number[]);
  writer.writeUInt32LE(outputIndex);
  return writer.toArray();
};

// Serialised change output: 8-byte value + varint scriptLen + script.
export const buildChangeOutput = (tx: Transaction, outputIndex: number): number[] => {
  const writer = new Utils.Writer();
  const output = tx.outputs[outputIndex];
  if (!output) return [];
  writer.writeUInt64LE(output.satoshis as number);
  const scriptBin = output.lockingScript.toBinary();
  writer.writeVarIntNum(scriptBin.length);
  writer.write(scriptBin);
  return writer.toArray();
};

// Sign a preimage (signs sha256(preimage); the engine double-hashes) -> checksig-format sig + pubkey.
export const createSignature = (
  privateKey: PrivateKey,
  preimage: number[],
  signatureScope: number
): { sigForScript: number[]; pubkeyForScript: number[] } => {
  const rawSignature = privateKey.sign(Hash.sha256(preimage));
  const sig = new TransactionSignature(rawSignature.r, rawSignature.s, signatureScope);
  const sigForScript = sig.toChecksigFormat();
  const pubkeyForScript = privateKey.toPublicKey().encode(true) as number[];
  return { sigForScript, pubkeyForScript };
};

// Split a BIP143 preimage into header(104) + scriptCodeLen + unlockScriptCode + lockScriptCode +
// footer(52) + lockLen. unlockBytesLen = bytes of unlock-script-code prefix (2 for SimpleMultiBolt).
export const splitCtx = (ctx: number[], unlockBytesLen: number = 0) => {
  const ctxHeader = ctx.slice(0, 104);
  let offset = 104;
  let reader = new Reader(ctx, offset);
  const firstByte = reader.readUInt8();
  let scriptLenSize = 1;
  if (firstByte === 0xfd) scriptLenSize = 3;
  else if (firstByte === 0xfe) scriptLenSize = 5;
  /* v8 ignore next -- 0xff (>4GB scriptCode) is unreachable for any real BIP143 preimage */
  else if (firstByte === 0xff) scriptLenSize = 9;
  const ctxCodeLen = ctx.slice(offset, offset + scriptLenSize);
  offset += scriptLenSize;
  let actualScriptLen = firstByte;
  reader = new Reader(ctx, 104 + 1);
  if (firstByte === 0xfd) actualScriptLen = reader.readUInt16LE();
  else if (firstByte === 0xfe) actualScriptLen = reader.readUInt32LE();
  /* v8 ignore next -- 0xff (>4GB scriptCode) is unreachable for any real BIP143 preimage */
  else if (firstByte === 0xff) actualScriptLen = Number(reader.readUInt64LEBn());
  const ctxCode = ctx.slice(offset, offset + actualScriptLen);
  offset += actualScriptLen;
  const ctxCodeUnlockScriptCode = ctxCode.slice(0, unlockBytesLen);
  const ctxCodeLockScriptCode = ctxCode.slice(unlockBytesLen);
  const ctxFooter = ctx.slice(offset, offset + 52);
  const writer = new Writer();
  const ctxCodeLockLen = writer.writeVarIntNum(ctxCodeLockScriptCode.length).toArray();
  return { ctxHeader, ctxCodeUnlockScriptCode, ctxCodeLen, ctxFooter, ctxCodeLockScriptCode, ctxCodeLockLen };
};

// ---- layout-agnostic tx-field primitives (one vocabulary, shared by both token streams) ----
// These replace the duplicated "mirrors" block in multiBoltLib + the inline le32/le64/chunkData/
// outpointOfInput in the nft helpers. Byte-faithful to those originals.

/** 4-byte little-endian. */
export const le32 = (n: number): number[] => { const w = new Writer(); w.writeUInt32LE(n); return w.toArray(); };
/** 8-byte little-endian. */
export const le64 = (n: number): number[] => { const w = new Writer(); w.writeUInt64LE(n); return w.toArray(); };

/** bin -> Script chunks (one pushdata; OP_0 for empty). */
export const scriptChunksFromBin = (data: number[]): any[] => new Script().writeBin(data).chunks;
/** Data of a script's chunk `i` (or []). */
export const scriptChunk = (s: Script, i: number): number[] => (s.chunks[i]?.data as number[]) ?? [];

/** tx version as 4-byte LE. */
export const txVersion = (tx: Transaction): number[] => le32(tx.version);
/** tx lockTime as 4-byte LE. */
export const txLockTime = (tx: Transaction): number[] => le32(tx.lockTime);

/** The 36-byte outpoint input `vin` spends — from the attached source tx, else the sourceTXID
 *  (reversed) fallback; [] if neither is available. */
export const spentOutpoint = (tx: Transaction, vin: number): number[] => {
  const input = tx.inputs[vin];
  if (!input) return [];
  const txid = (input.sourceTransaction?.hash() as number[]) ||
    Utils.toArray(input.sourceTXID || "", "hex").reverse();
  if (!txid || txid.length === 0) return [];
  const w = new Writer();
  w.write(txid);
  w.writeUInt32LE(input.sourceOutputIndex);
  return w.toArray();
};
/** Data of input `vin`'s unlocking-script chunk `chunkIdx` (or []). */
export const vinChunk = (tx: Transaction, vin: number, chunkIdx: number): number[] => {
  const w = new Writer();
  w.write(tx.inputs[vin]?.unlockingScript?.chunks?.[chunkIdx]?.data || []);
  return w.toArray();
};
/** Input `vin`'s 4-byte LE nSequence (or []). */
export const vinSequence = (tx: Transaction, vin: number): number[] => {
  const input = tx.inputs[vin];
  if (!input) return [];
  return le32((input.sequence ?? 0xffffffff) as number);
};
/** Input `vin`'s full unlocking-script bytes (or []). */
export const vinScript = (tx: Transaction, vin: number): number[] =>
  tx.inputs[vin]?.unlockingScript?.toBinary() || [];
/** Data of output `vout`'s locking-script chunk `chunkIdx` (or []). */
export const voutChunk = (tx: Transaction, vout: number, chunkIdx: number): number[] =>
  scriptChunk(tx.outputs[vout].lockingScript, chunkIdx);
/** Output `idx`'s 8-byte LE value (or []). */
export const outputValue = (tx: Transaction, idx: number): number[] => {
  const output = tx.outputs[idx];
  if (!output) return [];
  return le64(output.satoshis || 0);
};
/** Output `idx`'s locking-script bytes (or []). */
export const outputScript = (tx: Transaction, idx: number): number[] => {
  const output = tx.outputs[idx];
  if (!output) return [];
  const w = new Writer();
  w.write(output.lockingScript.toBinary());
  return w.toArray();
};
