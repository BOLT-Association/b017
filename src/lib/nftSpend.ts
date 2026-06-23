// Shared spend/unlock assembler for the NFT-family BOLT templates (MinSimpleBolt / Discount / Balance).
//
// Produces VALID spends on the @bsv/sdk Spend engine for the simple transfer (mint -> commit -> settle):
// verified live across all three contracts (test/min-nft-spend.test.ts) and byte-identical to the genuine
// sx golden (modulo the signature's low-S variant). Two caller requirements:
//   • the spending tx MUST be version >= 2 (the contract asserts it from the preimage);
//   • the template's UNLOCK_SCRIPT_SUFFIX must be the full compiled unlock (patched from the artifact by
//     the build scripts) — a truncated suffix corrupts the optimal-sighash s-computation.
// The ancestor-reconstruction path (a settle reaching back over chains >= 4 txs, e.g. a coupon's 2nd
// hop) is implemented via nftAncestorPieces (B2b-2), validated against the canonical sx golden.
//
// All three compile to an IDENTICAL 37-arg unlock layout (the M-I/M-H stripped contract: no
// mintData / issuerPubKey / genesisOutpoint / miscData in the ancestor reconstruction):
//
//   [0..25]  ancestor pieces (26)  — EMPTY for the simple transfer (mint->commit->settle); populated
//            by nftAncestorPieces when a settle reaches back over a chain >= 4 txs (coupon 2nd hop).
//   [26]     fundOutpoint           — the funding input's outpoint (36B)
//   [27]     changeOutput           — serialised change output (value + varint len + script)
//   [28]     beneficiaryPubKeyHash  — the next owner's 20-byte pkh
//   [29]     sig                    — checksig-format signature over the lock-only preimage
//   [30]     pubKey                 — signer's 33-byte compressed pubkey
//   [31..36] ctxHeader, ctxCodeLen, ctxCodeUnlockScriptCode, ctxCodeLockScriptCode, ctxFooter,
//            ctxCodeLockLen  — the 6 BIP143 preimage pieces from splitCtx(ctx, 2)
//
// OCS subscript = `OP_CHECKSIGVERIFY OP_ENDIF` + lockingScript (the combined-checksig tail, 2-byte
// unlock-script-code prefix `ad68`), exactly as SimpleMultiBolt. splitCtx(ctx, 2) accordingly.
import {
  Script,
  UnlockingScript,
  Transaction,
  TransactionSignature,
  PrivateKey,
  Hash,
} from "@bsv/sdk";
import { splitCtx, buildOutpoint, buildChangeOutput, createSignature, scriptChunksFromBin } from "./boltLib.js";
import { nftAncestorPieces } from "./nftAncestor.js";

/** Number of leading ancestor-reconstruction args in the NFT unlock layout. */
export const NFT_ANCESTOR_ARG_COUNT = 26;

const SIGNATURE_SCOPE = TransactionSignature.SIGHASH_FORKID | TransactionSignature.SIGHASH_ALL;

/** 26 empty ancestor pushes — the simple-transfer (and melt) case. */
export const emptyNftAncestorChunks = (): any[] => {
  const out: any[] = [];
  for (let i = 0; i < NFT_ANCESTOR_ARG_COUNT; i++) out.push(...scriptChunksFromBin([]));
  return out;
};

export interface NftUnlockParams {
  privateKey: PrivateKey;
  /** The next owner's 20-byte pubKeyHash (commit + settle both commit-to the recipient). */
  beneficiaryPubKeyHash: number[];
  /** UNLOCK_SCRIPT_SUFFIX ASM for the specific contract (patched from its artifact). */
  unlockScriptSuffixASM: string;
  forceNoChange?: boolean;
  forceNoFund?: boolean;
  /** Prior txs in the lineage (mint, commit, ...). Used to detect a back-reaching settle. */
  prevTxs?: Transaction[];
  /** Optional overrides when the input's sourceTransaction isn't attached. */
  sourceSatoshis?: number;
  lockingScript?: Script;
  /** Leading immutable value pushes in the lock (0 = identity, 1 = discount/balance). Needed to read
   *  the ancestor's token-data fields at the right chunk offset during back-reaching reconstruction. */
  leadingValuePushes?: number;
}

/**
 * Build a ScriptTemplate-compatible unlocker for an NFT-family bolt spend (transfer commit/settle, and
 * a back-reaching settle that reconstructs its ancestor commit). Requires tx version >= 2.
 */
export function nftSpendUnlock(params: NftUnlockParams): {
  sign: (tx: Transaction, inputIndex: number) => Promise<UnlockingScript>;
  estimateLength: () => Promise<number>;
} {
  const { privateKey, beneficiaryPubKeyHash, unlockScriptSuffixASM, forceNoChange, forceNoFund, prevTxs } = params;
  return {
    sign: async (tx: Transaction, inputIndex: number) => {
      const input = tx.inputs[inputIndex];
      const sourceTXID = input.sourceTXID || input.sourceTransaction?.id("hex");
      if (!sourceTXID) throw new Error("input sourceTXID or sourceTransaction required for signing");
      const sourceSatoshis =
        params.sourceSatoshis ?? input.sourceTransaction?.outputs[input.sourceOutputIndex].satoshis;
      if (sourceSatoshis === undefined) throw new Error("sourceSatoshis or input sourceTransaction required");
      const lockingScript =
        params.lockingScript ?? input.sourceTransaction?.outputs[input.sourceOutputIndex].lockingScript;
      if (!lockingScript) throw new Error("lockingScript or input sourceTransaction required");

      // Detect a settle that reaches back to a prior token (needs the ancestor block). The simple
      // mint->commit->settle lifecycle never does (txIdx <= 2): prevTxs at settle = [mint, commit].
      // A back-reaching settle (e.g. a coupon's 2nd hop settleTx2 at txIdx 4) reconstructs the commit
      // two hops back (prevTxs[txIdx-3]) where the current owner received the token (B2b-2).
      const txIdx = (prevTxs?.length ?? 0);
      const ancestorIdx = txIdx - 3;
      const hasAncestor = ancestorIdx >= 1 && txIdx >= 4 && txIdx % 2 === 0;
      const ancestorChunks = hasAncestor
        ? nftAncestorPieces(prevTxs![ancestorIdx], params.leadingValuePushes ?? 0).flatMap((p) =>
            scriptChunksFromBin(p),
          )
        : emptyNftAncestorChunks();

      const otherInputs = tx.inputs.filter((_: any, i: number) => i !== inputIndex);
      const ocsSubScript = new Script(
        Script.fromASM("OP_CHECKSIGVERIFY OP_ENDIF").chunks.concat(lockingScript.chunks),
      );
      const ctx = TransactionSignature.format({
        sourceTXID,
        sourceOutputIndex: input.sourceOutputIndex,
        sourceSatoshis,
        transactionVersion: tx.version,
        otherInputs,
        inputIndex,
        outputs: tx.outputs,
        inputSequence: input.sequence as number,
        subscript: ocsSubScript,
        lockTime: tx.lockTime,
        scope: SIGNATURE_SCOPE,
      });

      const { ctxHeader, ctxCodeLen, ctxCodeUnlockScriptCode, ctxCodeLockScriptCode, ctxFooter, ctxCodeLockLen } =
        splitCtx(ctx, 2);
      const ctxForSig = ctxHeader.concat(...[ctxCodeLockLen, ctxCodeLockScriptCode, ctxFooter]);
      const { sigForScript, pubkeyForScript } = createSignature(privateKey, ctxForSig, SIGNATURE_SCOPE);

      const fundInput = tx.inputs[tx.inputs.length - 1];
      const fundOutpoint = forceNoFund
        ? []
        : buildOutpoint(fundInput.sourceTransaction!, fundInput.sourceOutputIndex);
      const changeOutput = forceNoChange ? [] : buildChangeOutput(tx, tx.outputs.length - 1);

      return new UnlockingScript([
        ...ancestorChunks, // [0..25]
        ...scriptChunksFromBin(fundOutpoint), // [26]
        ...scriptChunksFromBin(changeOutput), // [27]
        ...scriptChunksFromBin(beneficiaryPubKeyHash), // [28]
        ...scriptChunksFromBin(sigForScript), // [29]
        ...scriptChunksFromBin(pubkeyForScript), // [30]
        ...scriptChunksFromBin(ctxHeader), // [31]
        ...scriptChunksFromBin(ctxCodeLen), // [32]
        ...scriptChunksFromBin(ctxCodeUnlockScriptCode), // [33]
        ...scriptChunksFromBin(ctxCodeLockScriptCode), // [34]
        ...scriptChunksFromBin(ctxFooter), // [35]
        ...scriptChunksFromBin(ctxCodeLockLen), // [36]
        ...Script.fromASM(unlockScriptSuffixASM).chunks,
      ]);
    },
    estimateLength: async () => 2000,
  };
}

export { Hash };
