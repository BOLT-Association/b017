import { PrivateKey, Transaction, Utils } from "@bsv/sdk";
import { SimpleMultiBOLT } from "./MultiBOLT.js";
import SimpleMultiTemplate from "./templates/SimpleMulti.sx.template.js";
import FixedMultiTemplate from "./templates/FixedMulti.sx.template.js";
import OpenMultiTemplate from "./templates/OpenMulti.sx.template.js";

// The genesis family of fungible tokens. Both lead their lock with two pushes before the SimpleMultiBolt
// fields: a 36-byte outpoint field and the issuer's mintData (on the mint only). Every operation of
// SimpleMultiBOLT (mint, commit, settle, transfer, split, merge, melt) works unchanged on top of their
// templates; the covenants add the rules below, and these classes refuse a merge the covenant would refuse
// before building it (so a caller gets a clear error, not an invalid transaction).

type Funding = { tx: Transaction; vout: number; key: PrivateKey };

const leadingField = (t: SimpleMultiBOLT): string =>
  Utils.toHex(t.tx!.outputs[t.voutIdx!].lockingScript.chunks[0].data as number[]);
const issuerOf = (t: SimpleMultiBOLT): string =>
  Utils.toHex(t.tx!.outputs[t.voutIdx!].lockingScript.chunks[12].data as number[]);

function assertSameIssuer(a: SimpleMultiBOLT, b: SimpleMultiBOLT, type: string): void {
  if (issuerOf(a) !== issuerOf(b)) throw new Error(`${type}: cannot merge tokens of different issuers`);
}

/**
 * FixedBOLT: one genesis per asset. `genesisOutpoint` is null on the mint, the mint outpoint from the genesis
 * spend on, and copied forever: it is the asset id. Only tokens of ONE genesis merge (a cross-genesis or a
 * cross-issuer merge is refused by the covenant at the merge commit).
 */
export class FixedBOLT extends SimpleMultiBOLT {
  protected readonly leading: number = 2;
  protected template(): SimpleMultiTemplate {
    return new FixedMultiTemplate(this.mintData);
  }

  async merge(other: SimpleMultiBOLT, toKey: PrivateKey, fundingSource?: Funding): Promise<SimpleMultiBOLT> {
    assertSameIssuer(this, other, "FixedBOLT");
    if (leadingField(this) !== leadingField(other))
      throw new Error("FixedBOLT: cannot merge tokens of different genesis outpoints (different assets)");
    return super.merge(other, toKey, fundingSource);
  }
}

/**
 * OpenBOLT: many mints under one issuer. `lastMergeOrGenesisOutpoint` (LMG) starts like FixedBOLT's
 * genesisOutpoint, but tokens of different genesis roots may merge: the merge commit re-roots the merged
 * token's LMG to vin0's token outpoint. A cross-issuer merge is refused by the covenant.
 */
export class OpenBOLT extends SimpleMultiBOLT {
  protected readonly leading: number = 2;
  protected template(): SimpleMultiTemplate {
    return new OpenMultiTemplate(this.mintData);
  }

  async merge(other: SimpleMultiBOLT, toKey: PrivateKey, fundingSource?: Funding): Promise<SimpleMultiBOLT> {
    assertSameIssuer(this, other, "OpenBOLT");
    return super.merge(other, toKey, fundingSource);
  }
}
