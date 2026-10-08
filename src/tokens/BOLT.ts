import {
  Transaction,
  PrivateKey
} from "@bsv/sdk";
import type { Signer, Recipient } from "../lib/boltLib.js";

// Base BOLT Protocol Token class
export abstract class BOLT {
  tx?: Transaction;
  voutIdx?: number;
  prevTxs: Transaction[] = []; // prior txs in the token's lineage
  pubKey: number[] = [];
  issuerPubKey: number[] = [];
  genesisOutpoint: number[] = [];
  // Current-owner Signer the builder feeds to the unlock templates (tpl.unlock(signer) -> { sign });
  // rotates on each settle. A Signer is { publicKey, sign(msg) } — a PrivateKey is one, but so is a
  // wallet that never exposes its key, so the class no longer has to hold the secret.
  signer!: Signer;
  // Helpful test duplicates (stored on-chain otherwise)
  mintData?: number[];
  pubKeyHash?: number[];

  constructor() { }
  abstract mint(
    owner: PrivateKey | Signer,
    sourceTransaction: Transaction,
    mintData?: string
  ): any;
  abstract commit(to: Recipient): any;
  abstract settle(to: Recipient): any;
  abstract transfer(to: Recipient): any;
}
