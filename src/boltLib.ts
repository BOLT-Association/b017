// boltLib.ts (SimpleMultiBolt standalone package)
// Trimmed to the layout-agnostic helpers SimpleMultiBolt needs:
// verifyTx (bsv Spend), buildOutpoint, buildChangeOutput,
// createSignature, splitCtx. No SimpleBolt/MultiBolt dependencies.

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
  else if (firstByte === 0xff) scriptLenSize = 9;
  const ctxCodeLen = ctx.slice(offset, offset + scriptLenSize);
  offset += scriptLenSize;
  let actualScriptLen = firstByte;
  reader = new Reader(ctx, 104 + 1);
  if (firstByte === 0xfd) actualScriptLen = reader.readUInt16LE();
  else if (firstByte === 0xfe) actualScriptLen = reader.readUInt32LE();
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
