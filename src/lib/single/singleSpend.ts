// Shared spend/unlock assembler for the NFT-family BOLT templates (MinSimpleBolt / Discount / Balance).
//
// Produces VALID spends on the @bsv/sdk Spend engine for the simple transfer (mint -> commit -> settle):
// verified live across all three contracts (test/lib/singleSpend.test.ts) and byte-identical to the
// genuine sx golden (modulo the signature's low-S variant). Two caller requirements:
//   • the spending tx MUST be version >= 2 (the contract asserts it from the preimage);
//   • the template's UNLOCK_SCRIPT_SUFFIX must be the full compiled unlock (patched from the artifact by
//     the build scripts) — a truncated suffix corrupts the optimal-sighash s-computation.
// The ancestor-reconstruction path (a settle reaching back over chains >= 4 txs, e.g. a coupon's 2nd
// hop) is implemented via singleAncestorPieces, validated against the canonical sx golden.
//
// MinSimpleBolt compiles to a 37-arg unlock layout; AuthBolt to 39 (a leading authOrMiscData + a 27th ancestor
// piece, `Vin1AuthOrMiscData`; see SingleLayout in singleAncestor.ts). The indices below are MinSimple's.
// All three (Min/Discount/Balance) shared an IDENTICAL 37-arg unlock layout (no mintData / issuerPubKey /
// genesisOutpoint / miscData in the ancestor reconstruction):
//
//   [0..25]  ancestor pieces (26)  — EMPTY for the simple transfer (mint->commit->settle); populated
//            by singleAncestorPieces when a settle reaches back over a chain >= 4 txs (coupon 2nd hop).
//   [26]     fundOutpoint           — the funding input's outpoint (36B); OP_0 when UNFUNDED (zero-funding)
//   [27]     changeOutput           — serialised change output (value + varint len + script); OP_0 when change-less
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
import { splitCtx, buildOutpoint, buildChangeOutput, createSignature, scriptChunksFromBin, type Signer } from "../boltLib.js";
import { singleAncestorPieces, MIN_SIMPLE_LAYOUT, type SingleLayout } from "./singleAncestor.js";

/** Number of leading ancestor-reconstruction args in the NFT unlock layout. */
export const SINGLE_ANCESTOR_ARG_COUNT = 26;

/** The p2pb proof lock leads with the 2-byte b017 marker push (b0 17). */
const isProofLock = (s?: Script): boolean => {
  const d = s?.chunks[0]?.data;
  return !!d && d.length === 2 && d[0] === 0xb0 && d[1] === 0x17;
};

const SIGNATURE_SCOPE = TransactionSignature.SIGHASH_FORKID | TransactionSignature.SIGHASH_ALL;

/** Empty ancestor pushes (26 for MinSimple, 27 for AuthBolt) — the simple-transfer (and melt) case. */
export const emptySingleAncestorChunks = (count: number = SINGLE_ANCESTOR_ARG_COUNT): any[] => {
  const out: any[] = [];
  for (let i = 0; i < count; i++) out.push(...scriptChunksFromBin([]));
  return out;
};

export interface SingleUnlockParams {
  privateKey: PrivateKey | Signer;
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
  /** The contract's unlock-arg layout (default MinSimple: 26 ancestor pieces; AuthBolt adds a leading auth arg + a 27th piece). */
  layout?: SingleLayout;
  /** AuthBolt only: the owner-supplied/transaction negotiated/challenge based authOrMiscData (<= 75 B), the FIRST unlock arg. Omitted / [] = OP_0. */
  authOrMiscData?: number[];
  /** MELT: burn the token. Every arg is OP_0 (a null CTX takes the lock's melt branch) except the owner's
   *  signature and pubKey; the tx has no token output. */
  melt?: boolean;
}

/**
 * Build a ScriptTemplate-compatible unlocker for an NFT-family bolt spend (transfer commit/settle, and
 * a back-reaching settle that reconstructs its ancestor commit). Requires tx version >= 2.
 */
export function singleSpendUnlock(params: SingleUnlockParams): {
  sign: (tx: Transaction, inputIndex: number) => Promise<UnlockingScript>;
  estimateLength: () => Promise<number>;
} {
  const { privateKey, beneficiaryPubKeyHash, unlockScriptSuffixASM, forceNoChange, forceNoFund, prevTxs } = params;
  const layout = params.layout ?? MIN_SIMPLE_LAYOUT;
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
      // two hops back (prevTxs[txIdx-3]) where the current owner received the token.
      const txIdx = (prevTxs?.length ?? 0);
      const ancestorIdx = txIdx - 3;
      const hasAncestor = ancestorIdx >= 1 && txIdx >= 4 && txIdx % 2 === 0;
      const ancestorChunks = hasAncestor
        ? singleAncestorPieces(prevTxs![ancestorIdx], params.leadingValuePushes ?? 0, layout).flatMap((p) =>
            scriptChunksFromBin(p),
          )
        : emptySingleAncestorChunks(layout.pieceNames.length);

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
      const { sigForScript, pubkeyForScript } = await createSignature(privateKey, ctxForSig, SIGNATURE_SCOPE);

      // Melt: a null CTX (every CTX piece OP_0) takes the lock's melt branch, which checks only the owner's
      // signature and pubKey (plus the issuer guard on a genesis / 2nd-tx token). No ancestor, fund or change args.
      if (params.melt) {
        const empty = () => scriptChunksFromBin([]);
        return new UnlockingScript([
          ...(layout.hasAuth ? empty() : []),
          ...emptySingleAncestorChunks(layout.pieceNames.length),
          ...empty(), ...empty(), ...empty(), // fundOutpoint, changeOutput, beneficiaryPubKeyHash
          ...scriptChunksFromBin(sigForScript),
          ...scriptChunksFromBin(pubkeyForScript),
          ...empty(), ...empty(), ...empty(), ...empty(), ...empty(), ...empty(), // the six CTX pieces
          ...Script.fromASM(unlockScriptSuffixASM).chunks,
        ]);
      }

      // Zero-funding: the funding input and the change output are each OPTIONAL (null -> OP_0). Inputs are
      // [token, proof?, funding?] and outputs [token, p2pb?, change?]: a settle that reaches back (hop >= 2)
      // carries the p2pb proof as input 1; a commit carries the p2pb as output 1. Detect them from the tx
      // itself so an unfunded or change-less spend is described correctly (forceNo* still force-omit).
      const nextIn = tx.inputs[inputIndex + 1];
      const nextLock = nextIn?.sourceTransaction?.outputs[nextIn.sourceOutputIndex]?.lockingScript;
      const hasProof = nextIn !== undefined && (nextLock ? isProofLock(nextLock) : hasAncestor);
      const fundInput = forceNoFund ? undefined : tx.inputs[inputIndex + 1 + (hasProof ? 1 : 0)];
      const changeIdx = isProofLock(tx.outputs[1]?.lockingScript) ? 2 : 1; // commit: [token, p2pb, change]
      const hasChange = !forceNoChange && tx.outputs.length > changeIdx;
      if (hasChange && !fundInput) throw new Error("an unfunded spend has no change to return (change needs a funding input)");
      const fundOutpoint = fundInput ? buildOutpoint(fundInput.sourceTransaction!, fundInput.sourceOutputIndex) : [];
      const changeOutput = hasChange ? buildChangeOutput(tx, changeIdx) : [];

      return new UnlockingScript([
        ...(layout.hasAuth ? scriptChunksFromBin(params.authOrMiscData ?? []) : []), // AuthBolt: [0] authOrMiscData
        ...ancestorChunks, // MinSimple [0..25]; AuthBolt [1..27]
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
