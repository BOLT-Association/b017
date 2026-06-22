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
  privKey!: PrivateKey; // FOR TESTING ONLY NOT PRODUCTION !!!
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

