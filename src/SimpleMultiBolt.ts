import {
  Transaction,
  PrivateKey,
  P2PKH,
  Hash,
  Utils,
  TransactionOutput,
  TransactionInput
} from "@bsv/sdk";
import SimpleMultiTemplate from "./multi/SimpleMultiBolt.sx.template.js";
import Pay2ProofTemplate from "./templates/pay2Proof.js";
import { verifyTx, buildOutpoint } from "./boltLib.js";
import { BOLT } from "./boltToken.js";

export type VerifierType = 'bsv';

// SimpleMultiBolt: optimised fungible token (swap removed, 16-byte balance,
// mandatory change + funding). Ported from MultiBolt.ts. See
// ts-bolt/src/multi/SimpleMultiBolt.sx.template.ts for the runtime assembler.
export class SimpleMultiBOLT extends BOLT {
  skipVerify: boolean = false;
  verifier: VerifierType = (process.env.BOLT_VERIFIER as VerifierType) || 'bsv';
  balance: number[] = [];
  balanceCommit: number[] = new Array(16).fill(0x00);
  outputIndexN: number[] = [0x00];

  async mint(
    privKey: PrivateKey,
    sourceTransaction: Transaction,
    _mintData: string = "",
    balance: number[] = [0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
  ) {
    const pubKey = privKey.toPublicKey().encode(true);
    const pubKeyHashStr = Utils.toHex(Hash.hash160(pubKey as number[]));
    const version = 2;
    let sourceOutputIndex = -1;
    const findPKHVoutIdx = (sourceTransaction: Transaction) => {
      for (let idx = 0; idx < sourceTransaction.outputs.length; idx++) {
        const output = sourceTransaction.outputs[idx];
        const lockingScript = output.lockingScript;
        const pKHChunkStr = Utils.toHex(lockingScript.chunks[2].data as number[]);
        if (pKHChunkStr === pubKeyHashStr) {
          sourceOutputIndex = idx;
          break;
        }
      }
    };
    findPKHVoutIdx(sourceTransaction);
    const input = {
      sourceTransaction,
      sourceOutputIndex,
      unlockingScriptTemplate: new P2PKH().unlock(privKey),
      sequence: 0xffffffff,
    };
    this.pubKeyHash = Hash.hash160(pubKey);
    this.balance = balance;

    const tokenLocking = new SimpleMultiTemplate().lock(
      pubKey as number[],
      this.prevTxs,
      this.balance,
      new Array(16).fill(0x00), // balanceCommit = zeros
      new Array(20).fill(0x00), // pubKeyHashCommit
      new Array(20).fill(0x00), // pubKeyHashCommit2
      new Array(36).fill(0x00), // otherGrandparentOutpoint
      [0x20], // txoType = settle (genesis)
      [0x00], // outputIndexN
    );
    const tokenOut = {
      lockingScript: tokenLocking,
      satoshis: 1,
      change: false,
    };
    const mintTx = new Transaction(
      version,
      [input],
      [
        tokenOut,
        {
          change: true,
          lockingScript: new P2PKH().lock(this.pubKeyHash),
        },
      ]
    );
    await mintTx.fee(0);
    await mintTx.sign();

    let { valid } = verifyTx(mintTx);
    if (!valid) throw new Error("Mint tx not valid");
    this.tx = mintTx;
    this.voutIdx = 0;
    this.prevTxs.push(this.tx);
    this.pubKey = pubKey as number[];
    this.issuerPubKey = pubKey as number[];
    this.genesisOutpoint = buildOutpoint(mintTx, 0);
    this.privKey = privKey;
    return this;
  }

  createTransferInputs = (
    toPrivKey: PrivateKey,
    _miscData: string,
    isCommitTx: boolean = true,
    forceNoChange: boolean = false,
    fundOverride: TransactionInput | undefined = undefined,
    forceNoFund: boolean = false
  ) => {
    // Determine ancestor proof vout for settles
    const hasAncestor = !isCommitTx && this.prevTxs.length >= 3;
    let proofVout = 1;
    if (hasAncestor) {
      const ancestorTx = this.prevTxs[this.prevTxs.length - 3];
      proofVout = ancestorTx.outputs.length >= 5 ? 2 : 1;
    }

    const input = {
      sourceTransaction: this.tx,
      sourceOutputIndex: this.voutIdx as number,
      unlockingScriptTemplate: new SimpleMultiTemplate().unlock(
        this.privKey,
        toPrivKey.toPublicKey().encode(true) as number[],
        this.prevTxs as Transaction[],
        forceNoChange,
        forceNoFund,
        [], // nextBalanceCommit empty for transfer (sim sets none); not 16 zeros
        isCommitTx ? [0x21] : [0x20], // nextTxoType
        [0x00], // inputIndexN
        [],     // pubKeyHash2
        hasAncestor ? this.voutLE(proofVout) : [], // grandparentProofVoutIdx
      ),
      sequence: 0xffffffff,
    };
    const funding = fundOverride || {
      sourceTransaction: this.tx,
      sourceOutputIndex: this.tx?.outputs ? this.tx?.outputs.length - 1 : 0,
      unlockingScriptTemplate: new P2PKH().unlock(this.privKey),
      sequence: 0xffffffff,
    };
    if (hasAncestor) {
      const ancestorTx = this.prevTxs[this.prevTxs.length - 3];
      const proof = {
        sourceTransaction: ancestorTx,
        sourceOutputIndex: proofVout,
        unlockingScriptTemplate: new Pay2ProofTemplate().unlock(this.privKey),
        sequence: 0xffffffff,
      };
      return forceNoFund ? [input, proof] : [input, proof, funding];
    }
    return forceNoFund ? [input] : [input, funding];
  };

  createTransferOutputs = (toPrivKey: PrivateKey, isCommitTx = true, forceNoChange = false, customChangeScript?: any): TransactionOutput[] => {
    const toPubKeyHash = Hash.hash160(toPrivKey.toPublicKey().encode(true));
    const pubKeyHashCommit = isCommitTx
      ? toPubKeyHash
      : new Array(20).fill(0x00);
    const tokenLocking = new SimpleMultiTemplate().lock(
      isCommitTx
        ? this.pubKey
        : (toPrivKey.toPublicKey().encode(true) as number[]),
      this.prevTxs,
      this.balance,
      this.balanceCommit,
      pubKeyHashCommit,
      new Array(20).fill(0x00), // pubKeyHashCommit2
      new Array(36).fill(0x00), // otherGrandparentOutpoint
      isCommitTx ? [0x21] : [0x20], // txoType
      [0x00], // outputIndexN
      isCommitTx ? (this.voutIdx || 0) : 0, // prevVoutIdx: commit reads from current token vout, settle reads from commit vout 0
    );
    const tokenOut = { lockingScript: tokenLocking, satoshis: 1 };
    const proofOut = {
      lockingScript: new Pay2ProofTemplate().lock(pubKeyHashCommit),
      satoshis: 1,
      change: false,
    };
    const changeOut = {
      change: true,
      lockingScript: customChangeScript || new P2PKH().lock(
        isCommitTx ? (this.pubKeyHash as number[]) : toPubKeyHash
      ),
    };
    if (!isCommitTx) return (forceNoChange ? [tokenOut] : [tokenOut, changeOut]);
    return (forceNoChange ? [tokenOut, proofOut] : [tokenOut, proofOut, changeOut]);
  };

  async commit(
    toPrivKey: PrivateKey,
    commitTxMiscData: string = "Bolt Protocol Transfer Commit Transaction Miscellaneous Data",
    forceNoChange: boolean = false,
    fundOverride: TransactionInput | undefined = undefined,
    forceNoFund: boolean = false,
    customChangeScript?: any,
  ) {
    const version = 2;
    const inputs = this.createTransferInputs(toPrivKey, commitTxMiscData, true, forceNoChange, fundOverride, forceNoFund);
    const outputs = this.createTransferOutputs(toPrivKey, true, forceNoChange, customChangeScript);
    const commitTx = new Transaction(version, inputs, outputs);

    if (!forceNoChange)
      await commitTx.fee(0);

    await commitTx.sign();

    const signedHex = commitTx.toHex();
    this.tx = Transaction.fromHex(signedHex);
    commitTx.inputs.forEach((input, i) => {
      this.tx!.inputs[i].sourceTransaction = input.sourceTransaction;
    });

    this.verifyAndLogTransaction(this.tx, 'COMMIT TX', fundOverride?.sourceTransaction);
    this.voutIdx = 0; // commit always places token at vout 0
    this.prevTxs?.push(this.tx);
    return this;
  }

  async settle(
    toPrivKey: PrivateKey,
    settleTxMiscData: string = "Bolt Protocol Transfer Settle Transaction Miscellaneous Data",
    forceNoChange: boolean = false,
    fundOverride: TransactionInput | undefined = undefined,
    forceNoFund: boolean = false,
    customChangeScript?: any,
  ) {
    const version = 2;
    const settleOutputs = this.createTransferOutputs(toPrivKey, false, forceNoChange, customChangeScript);
    const settleInputs = this.createTransferInputs(
      toPrivKey, settleTxMiscData, false, forceNoChange, fundOverride, forceNoFund
    );
    const settleTx = new Transaction(version, settleInputs, settleOutputs);
    if (!forceNoChange)
      await settleTx.fee(0);

    await settleTx.sign();

    const signedHex = settleTx.toHex();
    this.tx = Transaction.fromHex(signedHex);
    settleTx.inputs.forEach((input, i) => {
      this.tx!.inputs[i].sourceTransaction = input.sourceTransaction;
    });

    this.verifyAndLogTransaction(this.tx, 'SETTLE TX', fundOverride?.sourceTransaction);
    this.prevTxs?.push(this.tx);

    this.privKey = toPrivKey;
    this.pubKey = toPrivKey.toPublicKey().encode(true) as number[];
    this.pubKeyHash = Hash.hash160(this.pubKey);

    return this;
  }

  async transfer(
    toPrivKey: PrivateKey,
    commitTxMiscData: string = "Bolt Protocol Transfer Commit Transaction Miscellaneous Data",
    settleTxMiscData: string = "Bolt Protocol Transfer Settle Transaction Miscellaneous Data",
    skipSettle = false,
    forceNoChange = false,
    fundOverride: TransactionInput | undefined = undefined,
    forceNoFund = false,
    customChangeScript?: any,
  ) {
    await this.commit(toPrivKey, commitTxMiscData, forceNoChange, fundOverride, forceNoFund, customChangeScript);
    if (!skipSettle) {
      await this.settle(toPrivKey, settleTxMiscData, forceNoChange, fundOverride, forceNoFund, customChangeScript);
    }
    return this;
  }

  // Read 16 LE bytes into a BigInt as low + (high << 64) (Buffer has no 128-bit read)
  private balanceToBigInt(b: number[]): bigint {
    const buf = Buffer.from(b.slice(0, 16));
    const low = buf.readBigUInt64LE(0);
    const high = buf.readBigUInt64LE(8);
    return low + (high << BigInt(64));
  }

  // Write a BigInt back to 16 LE bytes (wrap to 128 bits)
  private bigIntToBalance(v: bigint): number[] {
    const mask64 = (BigInt(1) << BigInt(64)) - BigInt(1);
    const x = v & ((BigInt(1) << BigInt(128)) - BigInt(1));
    const buf = Buffer.alloc(16);
    buf.writeBigUInt64LE(x & mask64, 0);
    buf.writeBigUInt64LE((x >> BigInt(64)) & mask64, 8);
    return Array.from(buf);
  }

  // Add two 16-byte LE balance values
  private addBalances(a: number[], b: number[]): number[] {
    return this.bigIntToBalance(this.balanceToBigInt(a) + this.balanceToBigInt(b));
  }

  // Subtract two 16-byte LE balance values (a - b)
  private subtractBalances(a: number[], b: number[]): number[] {
    return this.bigIntToBalance(this.balanceToBigInt(a) - this.balanceToBigInt(b));
  }

  // Find proof vout that matches a key's pubKeyHash in an ancestor commit tx
  private findProofVout(ancestorTx: Transaction, key: PrivateKey): number {
    const pkh = Utils.toHex(Hash.hash160(key.toPublicKey().encode(true)));
    const startIdx = ancestorTx.outputs.length >= 5 ? 2 : 1;
    for (let i = startIdx; i < ancestorTx.outputs.length - 1; i++) {
      const proofChunks = ancestorTx.outputs[i].lockingScript.chunks;
      if (proofChunks.length >= 5 && Utils.toHex(proofChunks[4]?.data || []) === pkh) return i;
    }
    return startIdx;
  }

  // 4-byte LE uint32 for vout indices used in outpoint construction
  private voutLE(n: number): number[] {
    const buf = new ArrayBuffer(4);
    new DataView(buf).setUint32(0, n, true);
    return Array.from(new Uint8Array(buf));
  }

  private signAndClean = async (tx: Transaction, skipFee = false): Promise<Transaction> => {
    if (!skipFee) await tx.fee(0);
    await tx.sign();
    const cleanTx = Transaction.fromHex(tx.toHex());
    tx.inputs.forEach((input, i) => {
      cleanTx.inputs[i].sourceTransaction = input.sourceTransaction;
    });
    return cleanTx;
  }

  // Get the parent outpoint from a token's locking script (SMB lock chunk 8)
  private getParentOutpoint(): number[] {
    return this.tx!.outputs[this.voutIdx!].lockingScript.chunks[8].data as number[];
  }

  // Merge: absorb other token into this one
  async merge(
    other: SimpleMultiBOLT,
    toKey: PrivateKey,
    fundingSource?: { tx: Transaction, vout: number, key: PrivateKey },
  ): Promise<SimpleMultiBOLT> {
    const tpl = new SimpleMultiTemplate();
    const proofTpl = new Pay2ProofTemplate();
    const version = 2;
    const toPubKeyHash = Hash.hash160(toKey.toPublicKey().encode(true));

    // Default funding: use the last output of whichever token's tx has a change output we can unlock
    const fundTx = fundingSource?.tx || this.tx!;
    const fundVout = fundingSource?.vout ?? (this.tx!.outputs.length - 1);
    const fundKey = fundingSource?.key || this.privKey;

    // ── Merge Commit ──
    const thisInput = {
      sourceTransaction: this.tx,
      sourceOutputIndex: this.voutIdx as number,
      unlockingScriptTemplate: tpl.unlock(
        this.privKey,
        toKey.toPublicKey().encode(true) as number[],
        this.prevTxs,
        false, false,
        other.balance,                // nextBalanceCommit = other's balance
        [0x25],                       // merge commit
        [0x00],
        [],                           // pubKeyHash2
        [], [],                       // no proof vout idx for commit
        [],                           // interopPubKeyHash
        buildOutpoint(other.tx!, other.voutIdx!),
        other.getParentOutpoint(),
      ),
      sequence: 0xffffffff,
    };

    const otherInput = {
      sourceTransaction: other.tx,
      sourceOutputIndex: other.voutIdx as number,
      unlockingScriptTemplate: tpl.unlock(
        other.privKey,
        toKey.toPublicKey().encode(true) as number[],
        other.prevTxs,
        false, false,
        this.balance,
        [0x25],
        [0x01],
        [], [], [],
        Hash.hash160(this.pubKey),
        buildOutpoint(this.tx!, this.voutIdx!),
        this.getParentOutpoint(),
      ),
      sequence: 0xffffffff,
    };

    const fundInput = {
      sourceTransaction: fundTx,
      sourceOutputIndex: fundVout,
      unlockingScriptTemplate: new P2PKH().unlock(fundKey),
      sequence: 0xffffffff,
    };

    // Merged token output (commit)
    const tokenOut = tpl.lock(
      this.pubKey,
      this.prevTxs,
      this.balance,
      other.balance,
      toPubKeyHash,
      new Array(20).fill(0x00),
      other.getParentOutpoint(),     // otherGrandparentOutpoint = other token's parentOutpoint
      [0x25],
      [0x00],
      this.voutIdx,
    );

    const proofOut = { lockingScript: proofTpl.lock(toPubKeyHash), satoshis: 1, change: false };
    const changeOut = { change: true, lockingScript: new P2PKH().lock(this.pubKeyHash as number[]) };

    const commitTx = await this.signAndClean(new Transaction(version,
      [thisInput, otherInput, fundInput],
      [{ lockingScript: tokenOut, satoshis: 1 }, proofOut, changeOut]
    ));

    this.verifyAndLogTransaction(commitTx, 'MERGE COMMIT TX', fundingSource?.tx, other.prevTxs);
    this.prevTxs.push(commitTx);
    other.prevTxs.push(commitTx);

    // ── Merge Settle ──
    // Ancestor commits at prevTxs[txIdx - 3] for each lineage
    const thisAncestorCommit = this.prevTxs[this.prevTxs.length - 3];
    const otherAncestorCommit = other.prevTxs[other.prevTxs.length - 3];

    const thisProofVout = this.findProofVout(thisAncestorCommit, this.privKey);
    const otherProofVout = this.findProofVout(otherAncestorCommit, other.privKey);

    const settleInput = {
      sourceTransaction: commitTx,
      sourceOutputIndex: 0,
      unlockingScriptTemplate: tpl.unlock(
        this.privKey,
        toKey.toPublicKey().encode(true) as number[],
        this.prevTxs,
        false, false,
        new Array(16).fill(0x00),
        [0x24],                       // merge settle
        [0x00],
        [],
        this.voutLE(thisProofVout),    // grandparentProofVoutIdx
        this.voutLE(otherProofVout),   // interopProofVoutIdx
        [], [], [],
        otherAncestorCommit,          // ancestorTxBRef
      ),
      sequence: 0xffffffff,
    };

    const proof0 = {
      sourceTransaction: thisAncestorCommit,
      sourceOutputIndex: thisProofVout,
      unlockingScriptTemplate: proofTpl.unlock(this.privKey),
      sequence: 0xffffffff,
    };

    const proof1 = {
      sourceTransaction: otherAncestorCommit,
      sourceOutputIndex: otherProofVout,
      unlockingScriptTemplate: proofTpl.unlock(other.privKey),
      sequence: 0xffffffff,
    };

    const settleFundInput = {
      sourceTransaction: commitTx,
      sourceOutputIndex: commitTx.outputs.length - 1,
      unlockingScriptTemplate: new P2PKH().unlock(this.privKey),
      sequence: 0xffffffff,
    };

    // Merged balance = sum of both tokens' balances (16-byte LE addition)
    const mergedBalance = this.addBalances(this.balance, other.balance);
    const settleTokenOut = tpl.lock(
      toKey.toPublicKey().encode(true) as number[],
      this.prevTxs,
      mergedBalance,
      new Array(16).fill(0x00),
      new Array(20).fill(0x00),
      new Array(20).fill(0x00),
      new Array(36).fill(0x00),
      [0x24],
      [0x00],
      0,
    );

    // Lock change to the new owner's key so the merged token can fund subsequent operations
    const mergeSettleChangePKH = Hash.hash160(toKey.toPublicKey().encode(true));
    const settleChangeOut = { change: true, lockingScript: new P2PKH().lock(mergeSettleChangePKH) };

    const settleTx = await this.signAndClean(new Transaction(version,
      [settleInput, proof0, proof1, settleFundInput],
      [{ lockingScript: settleTokenOut, satoshis: 1 }, settleChangeOut]
    ));

    this.verifyAndLogTransaction(settleTx, 'MERGE SETTLE TX', undefined, other.prevTxs);

    this.tx = settleTx;
    this.voutIdx = 0;
    this.prevTxs.push(settleTx);
    this.privKey = toKey;
    this.pubKey = toKey.toPublicKey().encode(true) as number[];
    this.pubKeyHash = Hash.hash160(this.pubKey);
    this.balance = mergedBalance;
    this.balanceCommit = new Array(16).fill(0x00);

    return this;
  }

  // Split: divide this token into two with specified balances
  // Returns [tokenA, tokenB]
  async split(
    toKeyA: PrivateKey,
    toKeyB: PrivateKey,
    splitBalanceCommit: number[],
    fundingSource?: { tx: Transaction, vout: number, key: PrivateKey },
  ): Promise<[SimpleMultiBOLT, SimpleMultiBOLT]> {
    const tpl = new SimpleMultiTemplate();
    const proofTpl = new Pay2ProofTemplate();
    const version = 2;
    const toPubKeyHashA = Hash.hash160(toKeyA.toPublicKey().encode(true));
    const toPubKeyHashB = Hash.hash160(toKeyB.toPublicKey().encode(true));

    const fundTx = fundingSource?.tx || this.tx!;
    const fundVout = fundingSource?.vout ?? (this.tx!.outputs.length - 1);
    const fundKey = fundingSource?.key || this.privKey;

    // ── Split Commit ──
    const tokenInput = {
      sourceTransaction: this.tx,
      sourceOutputIndex: this.voutIdx as number,
      unlockingScriptTemplate: tpl.unlock(
        this.privKey,
        toKeyA.toPublicKey().encode(true) as number[],
        this.prevTxs,
        false, false,
        splitBalanceCommit,           // nextBalanceCommit = second split's balance
        [0x23],                       // split commit
        [0x00],
        toPubKeyHashB,                // pubKeyHash2 (second split recipient)
      ),
      sequence: 0xffffffff,
    };

    const fundInput = {
      sourceTransaction: fundTx,
      sourceOutputIndex: fundVout,
      unlockingScriptTemplate: new P2PKH().unlock(fundKey),
      sequence: 0xffffffff,
    };

    const tokenOut = tpl.lock(
      this.pubKey,
      this.prevTxs,
      this.balance,
      splitBalanceCommit,
      toPubKeyHashA,
      toPubKeyHashB,
      new Array(36).fill(0x00),
      [0x23],
      [0x00],
      this.voutIdx,
    );

    const proofOut0 = { lockingScript: proofTpl.lock(toPubKeyHashA), satoshis: 1, change: false };
    const proofOut1 = { lockingScript: proofTpl.lock(toPubKeyHashB), satoshis: 1, change: false };
    const changeOut = { change: true, lockingScript: new P2PKH().lock(this.pubKeyHash as number[]) };

    const commitTx = await this.signAndClean(new Transaction(version,
      [tokenInput, fundInput],
      [{ lockingScript: tokenOut, satoshis: 1 }, proofOut0, proofOut1, changeOut]
    ));

    this.verifyAndLogTransaction(commitTx, 'SPLIT COMMIT TX', fundingSource?.tx);
    this.prevTxs.push(commitTx);

    // ── Split Settle ──
    const ancestorCommit = this.prevTxs[this.prevTxs.length - 3]; // the commit before the split commit
    const ancestorProofVout = ancestorCommit.outputs.length >= 5 ? 2 : 1;

    const settleInput = {
      sourceTransaction: commitTx,
      sourceOutputIndex: 0,
      unlockingScriptTemplate: tpl.unlock(
        this.privKey,
        [],                           // toPubKey empty -> pubKeyHash1 empty (recipients from commitments)
        this.prevTxs,
        false, false,
        [],                           // nextBalanceCommit empty for split settle
        [0x22],                       // split settle
        [0x00],
        [],
        this.voutLE(ancestorProofVout), // grandparentProofVoutIdx
      ),
      sequence: 0xffffffff,
    };

    const proofInput = {
      sourceTransaction: ancestorCommit,
      sourceOutputIndex: ancestorProofVout,
      unlockingScriptTemplate: proofTpl.unlock(this.privKey),
      sequence: 0xffffffff,
    };

    const settleFundInput = {
      sourceTransaction: commitTx,
      sourceOutputIndex: commitTx.outputs.length - 1,
      unlockingScriptTemplate: new P2PKH().unlock(this.privKey),
      sequence: 0xffffffff,
    };

    // Two settled token outputs — first gets balance - balanceCommit, second gets balanceCommit
    const mainBalance = this.subtractBalances(this.balance, splitBalanceCommit);
    const settleTokenOut0 = tpl.lock(
      toKeyA.toPublicKey().encode(true) as number[],
      this.prevTxs,
      mainBalance,
      new Array(16).fill(0x00),
      new Array(20).fill(0x00),
      new Array(20).fill(0x00),
      new Array(36).fill(0x00),
      [0x22],
      [0x00],
      0,
    );

    const settleTokenOut1 = tpl.lock(
      toKeyB.toPublicKey().encode(true) as number[],
      this.prevTxs,
      splitBalanceCommit,
      new Array(16).fill(0x00),
      new Array(20).fill(0x00),
      new Array(20).fill(0x00),
      new Array(36).fill(0x00),
      [0x22],
      [0x01],
      0,
    );

    // Lock change to first split recipient so the token can fund subsequent operations
    const splitSettleChangePKH = Hash.hash160(toKeyA.toPublicKey().encode(true));
    const settleChangeOut = { change: true, lockingScript: new P2PKH().lock(splitSettleChangePKH) };

    const settleTx = await this.signAndClean(new Transaction(version,
      [settleInput, proofInput, settleFundInput],
      [{ lockingScript: settleTokenOut0, satoshis: 1 }, { lockingScript: settleTokenOut1, satoshis: 1 }, settleChangeOut]
    ));

    this.verifyAndLogTransaction(settleTx, 'SPLIT SETTLE TX');

    // Update this token to be the first split
    this.tx = settleTx;
    this.voutIdx = 0;
    this.prevTxs.push(settleTx);
    this.privKey = toKeyA;
    this.pubKey = toKeyA.toPublicKey().encode(true) as number[];
    this.pubKeyHash = Hash.hash160(this.pubKey);
    this.balance = mainBalance;

    // Create second split token
    const tokenB = new SimpleMultiBOLT();
    tokenB.tx = settleTx;
    tokenB.voutIdx = 1;
    tokenB.prevTxs = [...this.prevTxs]; // share lineage
    tokenB.privKey = toKeyB;
    tokenB.pubKey = toKeyB.toPublicKey().encode(true) as number[];
    tokenB.pubKeyHash = Hash.hash160(tokenB.pubKey);
    tokenB.issuerPubKey = this.issuerPubKey;
    tokenB.genesisOutpoint = this.genesisOutpoint;
    tokenB.balance = splitBalanceCommit;
    tokenB.skipVerify = this.skipVerify;
    tokenB.verifier = this.verifier;

    return [this, tokenB];
  }

  async melt(meltPubKeyHash?: number[]) {
    const input = {
      sourceTransaction: this.tx,
      sourceOutputIndex: this.voutIdx as number,
      unlockingScriptTemplate: new SimpleMultiTemplate().melt(this.privKey),
      sequence: 0xffffffff,
    };
    const funding = {
      sourceTransaction: this.tx,
      sourceOutputIndex: this.tx?.outputs ? this.tx?.outputs.length - 1 : 0,
      unlockingScriptTemplate: new P2PKH().unlock(this.privKey),
      sequence: 0xffffffff,
    };

    const version = 2;
    const meltTx = new Transaction(
      version,
      [input, funding],
      [
        {
          change: true,
          lockingScript: new P2PKH().lock(meltPubKeyHash || this.pubKeyHash as number[]),
        },
      ]
    );

    await meltTx.fee(0);
    await meltTx.sign();

    const signedHex = meltTx.toHex();
    this.tx = Transaction.fromHex(signedHex);
    meltTx.inputs.forEach((input, i) => {
      this.tx!.inputs[i].sourceTransaction = input.sourceTransaction;
    });

    this.verifyAndLogTransaction(this.tx, 'MELT TX');
    return this;
  }

  private verifyAndLogTransaction(tx: Transaction, txType: string, fundOverrideTx: Transaction | undefined = undefined, extraHistory: Transaction[] = []): void {
    if (this.skipVerify) return;

    // Ensure all inputs have sourceTXID set
    tx.inputs.forEach(input => {
      if (!input.sourceTXID && input.sourceTransaction) {
        input.sourceTXID = input.sourceTransaction.id('hex');
      }
    });

    const { valid, scriptExecutions } = verifyTx(tx, true); // skipOutputCheck: zero-funding txs may have output > input
    if (!valid) {
      const failedIdx = scriptExecutions.findIndex(e => !e.valid);
      console.log(`\n========== SCRIPT FAILURE [bsv] (${txType}) - INPUT ${failedIdx} ==========`);
      throw new Error(`${txType} tx not valid [bsv]`);
    }
  }
}
