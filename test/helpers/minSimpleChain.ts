// Shared chain harness for the MinSimpleBOLT family (MinSimple zero-funding, AuthBolt): builds
// mint -> commit1 -> settle1 -> commit2 -> settle2 (settle2 rebuilds commit1 and spends its proof) from
// the library templates and verifies every tx on the @bsv/sdk Spend engine. Port of the simulator-level harness
// the contract-level suite (the sim there; real txs here).
//
// Lineage: issuer(0) -> user(1) -> bucket(2). Every funding UTXO and change output belongs to the issuer
// key (the covenant never constrains who signs the funding input or who the change pays).
import {
  Hash, MerklePath, P2PKH, PrivateKey, Script, Transaction, TransactionSignature, UnlockingScript,
} from '@bsv/sdk'
import { verifyTx, buildOutpoint, createSignature, scriptChunksFromBin } from '../../src/lib/boltLib.js'

const SCOPE = TransactionSignature.SIGHASH_FORKID | TransactionSignature.SIGHASH_ALL
export const issuerKey = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
export const userKey = PrivateKey.fromString('a1b2c3d4e5f60718293a4b5c6d7e8f90112233445566778899aabbccddeeff00', 'hex')
export const bucketKey = PrivateKey.fromString('5566778899aabbccddeeff00112233445566778899aabbccddeeff0011223344', 'hex')
export const attackerKey = PrivateKey.fromString('0f1e2d3c4b5a69788796a5b4c3d2e1f00112233445566778899aabbccddeeff1', 'hex')
export const pub = (k: PrivateKey) => k.toPublicKey().encode(true) as number[]
export const pkh = (k: PrivateKey) => Hash.hash160(pub(k))
export const issuerPub = pub(issuerKey)
export const [iPkh, uPkh, bPkh, aPkh] = [pkh(issuerKey), pkh(userKey), pkh(bucketKey), pkh(attackerKey)]
export const ZERO20 = new Array(20).fill(0)
export const ZERO36 = new Array(36).fill(0)
export const fromHex = (h: string): number[] => (h === '' ? [] : Array.from(Buffer.from(h, 'hex')))
export const toHex = (a: number[]) => Buffer.from(a).toString('hex')
export const p2pb = (h: number[]) => Script.fromHex('02b0178876a914' + toHex(h) + '88ac')

/** A token family under test: its lock builder, its spend unlocker and its unlock-arg layout. */
export interface Family {
  name: string
  lock(owner: number[], commitment: number[], txoType: number[], parent: number[], gp: number[]): Script
  /** `auth` is only meaningful for AuthBolt (omitted / [] = OP_0). */
  unlock(key: PrivateKey, beneficiary: number[], prevTxs: Transaction[], auth?: number[]): any
  /** The melt (burn) unlocker: an owner spend with a null CTX. */
  melt(key: PrivateKey): any
  /** Ancestor piece names in unlock order, and the unlock index of the first one. */
  pieceNames: readonly string[]
  ancestorStart: number
}

// A spend of a funding p2pkh / the p2pb proof.
const p2pkhUnlock = (key: PrivateKey) => new P2PKH().unlock(key)
const p2pbUnlock = (key: PrivateKey) => ({
  sign: async (tx: Transaction, i: number) => {
    const inp = tx.inputs[i]
    const src = inp.sourceTransaction!.outputs[inp.sourceOutputIndex]
    const preimage = TransactionSignature.format({
      sourceTXID: inp.sourceTransaction!.id('hex'), sourceOutputIndex: inp.sourceOutputIndex,
      sourceSatoshis: src.satoshis as number, transactionVersion: tx.version,
      otherInputs: tx.inputs.filter((_, j) => j !== i), inputIndex: i, outputs: tx.outputs,
      inputSequence: inp.sequence as number, subscript: src.lockingScript, lockTime: tx.lockTime, scope: SCOPE,
    })
    const { sigForScript, pubkeyForScript } = createSignature(key, preimage, SCOPE)
    return new UnlockingScript([
      ...scriptChunksFromBin(sigForScript), ...scriptChunksFromBin(pubkeyForScript), ...scriptChunksFromBin([0xb0, 0x17]),
    ])
  },
  estimateLength: async () => 120,
})

export interface Src { tx: number; vout: number }
/** One hop's shape: fund = the funding UTXO (null = unfunded), change = emit a change output. */
export interface Hop { fund: Src | null; change: boolean; auth?: number[] }
export type HopName = 'commit1' | 'settle1' | 'commit2' | 'settle2'
export type ChainSpec = Partial<Record<HopName, Partial<Hop>>>

export const UNFUNDED: Partial<Hop> = { fund: null, change: false }
export const FUNDED_NO_CHANGE = (tx: number, vout: number): Partial<Hop> => ({ fund: { tx, vout }, change: false })

/** Give a synthetic root tx a (fake) single-tx-block merkle path, as a mined funding tx would carry in a BEEF.
 *  The scanner checks a BEEF is self-contained, not that the BUMP's root is a real block header. */
export const proven = <T extends Transaction>(tx: T): T => {
  tx.merklePath = new MerklePath(1, [[{ offset: 0, hash: tx.id('hex'), txid: true }]])
  return tx
}

/** Low-level: one token spend (input 0 = the token; then the optional proof; then the optional funding). */
export interface SpendOpts {
  fam: Family
  txs: Transaction[]            // everything built so far (also the prevTxs handed to the unlocker)
  from: Src                     // the token output being spent
  actor: PrivateKey
  beneficiary: number[]
  outputs: Script[]             // token (+ p2pb on a commit), in order
  fund?: Src | null
  change?: boolean              // append a change output (needs fund)
  proof?: { src: Src; key: PrivateKey }
  /** Key that signs the funding input (default: the issuer, who owns every funding UTXO in buildChain). */
  fundKey?: PrivateKey
  auth?: number[]
  /** Replace the prevTxs handed to the unlocker (default = all txs so far). */
  prevTxs?: Transaction[]
}

export async function spendToken(o: SpendOpts): Promise<Transaction> {
  if (o.change && !o.fund) throw new Error('an unfunded spend has no change to return (change needs fund)')
  const tx = new Transaction()
  tx.version = 2
  tx.addInput({
    sourceTransaction: o.txs[o.from.tx], sourceOutputIndex: o.from.vout,
    unlockingScriptTemplate: o.fam.unlock(o.actor, o.beneficiary, o.prevTxs ?? o.txs, o.auth), sequence: 0xffffffff,
  })
  if (o.proof) {
    tx.addInput({
      sourceTransaction: o.txs[o.proof.src.tx], sourceOutputIndex: o.proof.src.vout,
      unlockingScriptTemplate: p2pbUnlock(o.proof.key), sequence: 0xffffffff,
    })
  }
  if (o.fund) {
    tx.addInput({
      sourceTransaction: o.txs[o.fund.tx], sourceOutputIndex: o.fund.vout,
      unlockingScriptTemplate: p2pkhUnlock(o.fundKey ?? issuerKey), sequence: 0xffffffff,
    })
  }
  for (const lockingScript of o.outputs) tx.addOutput({ satoshis: 1, lockingScript })
  if (o.change) {
    const fundSats = o.txs[o.fund!.tx].outputs[o.fund!.vout].satoshis as number
    tx.addOutput({ satoshis: fundSats - 10, lockingScript: new P2PKH().lock(iPkh) })
  }
  await tx.sign()
  return tx
}

/** MELT the token at `from`: input 0 = the token, then the optional funding; ONE p2pkh output, no token output. */
export async function meltToken(o: {
  fam: Family; txs: Transaction[]; from: Src; actor: PrivateKey; fund?: Src | null; fundKey?: PrivateKey; payTo?: number[]
}): Promise<Transaction> {
  const tx = new Transaction()
  tx.version = 2
  tx.addInput({ sourceTransaction: o.txs[o.from.tx], sourceOutputIndex: o.from.vout, unlockingScriptTemplate: o.fam.melt(o.actor), sequence: 0xffffffff })
  let sats = o.txs[o.from.tx].outputs[o.from.vout].satoshis as number
  if (o.fund) {
    tx.addInput({
      sourceTransaction: o.txs[o.fund.tx], sourceOutputIndex: o.fund.vout,
      unlockingScriptTemplate: p2pkhUnlock(o.fundKey ?? issuerKey), sequence: 0xffffffff,
    })
    sats += (o.txs[o.fund.tx].outputs[o.fund.vout].satoshis as number) - 10
  }
  tx.addOutput({ satoshis: sats, lockingScript: new P2PKH().lock(o.payTo ?? pkh(o.actor)) })
  await tx.sign()
  return tx
}

/** mint: a 5000-sat funding -> token(issuer) + two 1000-sat issuer fundings (vout1, vout2). */
export async function mintToken(fam: Family): Promise<Transaction[]> {
  const funding = proven(new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(iPkh) }]))
  const mint = new Transaction(); mint.version = 2
  mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: p2pkhUnlock(issuerKey), sequence: 0xffffffff })
  mint.addOutput({ satoshis: 1, lockingScript: fam.lock(iPkh, ZERO20, [0x00], ZERO36, ZERO36) })
  mint.addOutput({ satoshis: 1000, lockingScript: new P2PKH().lock(iPkh) })
  mint.addOutput({ satoshis: 1000, lockingScript: new P2PKH().lock(iPkh) })
  await mint.sign()
  return [mint]
}

/**
 * mint -> commit1 -> settle1 -> commit2 -> settle2, built up to `upTo` txs (default all 5).
 * Defaults mirror the simulator chain(): every hop funded with change, each funded from the previous hop's change.
 */
export async function buildChain(fam: Family, f: ChainSpec = {}, upTo = 5): Promise<Transaction[]> {
  const hop = (k: HopName, d: Hop): Hop => ({ ...d, ...(f[k] || {}) })
  const txs = await mintToken(fam)
  const op = (t: number, v: number) => buildOutpoint(txs[t], v)

  const c1 = hop('commit1', { fund: { tx: 0, vout: 1 }, change: true })
  txs.push(await spendToken({
    fam, txs, from: { tx: 0, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: c1.fund, change: c1.change, auth: c1.auth,
    outputs: [fam.lock(iPkh, uPkh, [0x21], op(0, 0), ZERO36), p2pb(uPkh)],
  }))
  if (upTo <= 2) return txs.slice(0, upTo)

  const s1 = hop('settle1', { fund: c1.fund && c1.change ? { tx: 1, vout: 2 } : { tx: 0, vout: 2 }, change: true })
  txs.push(await spendToken({
    fam, txs, from: { tx: 1, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: s1.fund, change: s1.change, auth: s1.auth,
    outputs: [fam.lock(uPkh, ZERO20, [0x00], op(1, 0), op(0, 0))],
  }))
  if (upTo <= 3) return txs.slice(0, upTo)

  const s1Change: Src | null = s1.fund && s1.change ? { tx: 2, vout: 1 } : null
  const c2 = hop('commit2', { fund: s1Change, change: !!s1Change })
  txs.push(await spendToken({
    fam, txs, from: { tx: 2, vout: 0 }, actor: userKey, beneficiary: bPkh, fund: c2.fund, change: c2.change, auth: c2.auth,
    outputs: [fam.lock(uPkh, bPkh, [0x21], op(2, 0), op(1, 0)), p2pb(bPkh)],
  }))
  if (upTo <= 4) return txs.slice(0, upTo)

  const c2Change: Src | null = c2.fund && c2.change ? { tx: 3, vout: 2 } : null
  const s2 = hop('settle2', { fund: c2Change, change: !!c2Change })
  txs.push(await spendToken({
    fam, txs, from: { tx: 3, vout: 0 }, actor: userKey, beneficiary: bPkh, fund: s2.fund, change: s2.change, auth: s2.auth,
    proof: { src: { tx: 1, vout: 1 }, key: userKey },
    outputs: [fam.lock(bPkh, ZERO20, [0x00], op(3, 0), op(2, 0))],
  }))
  return txs
}

export interface RunResult { ok: boolean; failedTx?: number; message?: string; pc?: number }

/** Verify every tx in order; stops at the first failing tx (input 0 = the token unless noted). */
export function verifyChain(txs: Transaction[]): RunResult {
  for (let i = 0; i < txs.length; i++) {
    const tx = txs[i]
    tx.inputs.forEach((inp: any) => { if (!inp.sourceTXID && inp.sourceTransaction) inp.sourceTXID = inp.sourceTransaction.id('hex') })
    try {
      const { valid } = verifyTx(tx, true)
      if (!valid) return { ok: false, failedTx: i }
    } catch (e: any) {
      return { ok: false, failedTx: i, message: String(e?.message ?? e), pc: e?.programCounter }
    }
  }
  return { ok: true }
}

/** Replace named ancestor pieces (hex, '' = OP_0) in a tx's input-0 unlock. Re-assigns a fresh
 *  UnlockingScript because Script caches its serialisation. */
export function tamper(fam: Family, tx: Transaction, pieces: Record<string, string>, inputIdx = 0): void {
  const chunks = [...tx.inputs[inputIdx].unlockingScript!.chunks]
  for (const [name, hex] of Object.entries(pieces)) {
    const i = fam.pieceNames.indexOf(name)
    if (i < 0) throw new Error(`unknown ancestor piece ${name}`)
    chunks[fam.ancestorStart + i] = scriptChunksFromBin(fromHex(hex))[0]
  }
  tx.inputs[inputIdx].unlockingScript = new UnlockingScript(chunks)
}

/** Lock-script chunk index of the grandparent txid check `hash256 dup <gp> pick 32 split drop equalVerify`:
 *  the first OP_EQUALVERIFY after the OP_HASH256 OP_DUP pair. */
export function grandparentCheckPc(lock: Script): number {
  const ops = lock.chunks.map((c) => c.op)
  const h = ops.findIndex((op, k) => op === 0xaa && ops[k + 1] === 0x76)
  return ops.indexOf(0x88, h)
}
