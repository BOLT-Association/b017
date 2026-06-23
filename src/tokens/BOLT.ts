import {
  Transaction,
  PrivateKey
} from "@bsv/sdk";

// Base BOLT Protocol Token class
export abstract class BOLT {
  tx?: Transaction;
  voutIdx?: number;
  prevTxs: Transaction[] = []; // We only need to store a maximum of two previous txs (e.g. B2G solved)
  pubKey: number[] = [];
  issuerPubKey: number[] = [];
  genesisOutpoint: number[] = [];
  // Current-owner key the builder feeds to the @bsv/sdk unlock-template signers (tpl.unlock(key)
  // -> { sign }); rotates on each settle. The signing itself is the SDK's injection; this is just
  // the stateful builder caching the owner key. (Roadmap: take a per-op signer so the class need
  // not hold the secret — see docs/ROADMAP.md.)
  privKey!: PrivateKey;
  // Helpful test duplicates (stored on-chain otherwise)
  mintData?: number[];
  pubKeyHash?: number[];

  constructor() { }
  abstract mint(
    privKey: PrivateKey,
    sourceTransaction: Transaction,
    mintData?: string
  ): any;
  abstract commit(toPrivKey: PrivateKey): any;
  abstract settle(toPrivKey: PrivateKey): any;
  abstract transfer(toPrivKey: PrivateKey): any;
}

