// Builders for the fungible spends that used to give a token an index byte other than its output position, shared
// by the Lean vector exporter (lean/vectors/export.test.ts, the `smb_probe_idx_*` vectors) and the regression suite
// (test/lib/indexByte.test.ts). Until the outputIndexN removal the script wrote a token's index byte (lock chunk 7,
// `outputIndexN`) from the spender's `inputIndexN` argument, or from the `i2` interop slot for a split settle's
// second token, and never read it back (lean/README.md, Finding 6). The byte is gone: the lock has 10 data pushes
// and chunk 7 is the parent outpoint. The shapes stay, because `inputIndexN`, `i2` and `pkh1` still exist and a
// spend that sets them must still leave a spendable token: with `pkh1` set a split settle's two tokens come out
// swapped. Each helper builds one shape with the honest builders around it, so a refusal would be the covenant's own.
import { Hash, LockingScript, P2PKH, PrivateKey, Script, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

export const zeros = (n: number): number[] => new Array(n).fill(0x00)
export const pubOf = (k: PrivateKey): number[] => k.toPublicKey().encode(true) as number[]

/** Re-parse a signed transaction and reattach its source transactions, as the builders' `signAndClean` does. */
export const cleanTx = (tx: Transaction): Transaction => {
  const c = Transaction.fromHex(tx.toHex())
  tx.inputs.forEach((inp, i) => { c.inputs[i].sourceTransaction = inp.sourceTransaction })
  return c
}

/** A lock with some of its data pushes replaced. */
export const patchLock = (lock: Script, patches: Record<number, number[]>): LockingScript =>
  new LockingScript(lock.chunks.map((c, i) => (patches[i] ? { op: patches[i].length, data: patches[i] } : c)))

/** A fresh 1000-satoshi P2PKH source for `key`. */
export const sourceFor = (key: PrivateKey): Transaction =>
  new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(pubOf(key))) }])

/** A P2PKH funding input for `key` from a fresh source: a split settle's change belongs to the first recipient, so
 *  the second token's owner needs their own. */
export const fundFor = (key: PrivateKey) => ({
  sourceTransaction: sourceFor(key), sourceOutputIndex: 0, sequence: 0xffffffff,
  unlockingScriptTemplate: new P2PKH().unlock(key),
})

/** The number of data pushes in front of the static suffix of the token at output `vout` (10 for SimpleMultiBOLT:
 *  balance, balanceCommit, pubKeyHash, pubKeyHashCommit, pubKeyHashCommit2, otherGrandparentOutpoint, txoType,
 *  parentOutpoint, grandparentOutpoint, issuerPubKey; 11 while it carried the index byte). */
export const lockDataPushes = (tx: Transaction, vout: number): number =>
  tx.outputs[vout].lockingScript.chunks.length - new SimpleMultiTemplate().staticSuffix().chunks.length

/** The parent outpoint the token at output `vout` carries (lock chunk 7 since the index byte went). */
export const parentOutpointAt = (tx: Transaction, vout: number): number[] =>
  (tx.outputs[vout].lockingScript.chunks[7].data as number[] | undefined) ?? []

/** The token at output `vout` of `tx`, owned by `key`, as a builder object with its lineage. */
export const tokenAt = (tx: Transaction, vout: number, key: PrivateKey, balance: number[], prevTxs: Transaction[],
  like: SimpleMultiBOLT): SimpleMultiBOLT => {
  const tok = new SimpleMultiBOLT()
  tok.tx = tx
  tok.voutIdx = vout
  tok.prevTxs = [...prevTxs]
  tok.signer = key as any
  tok.pubKey = pubOf(key)
  tok.pubKeyHash = Hash.hash160(tok.pubKey)
  tok.issuerPubKey = like.issuerPubKey
  tok.genesisOutpoint = like.genesisOutpoint
  tok.mintData = like.mintData
  tok.balance = balance
  tok.balanceCommit = zeros(16)
  tok.skipVerify = true
  return tok
}

/** A transfer commit or settle built as the honest one but with `inputIndexN` = 1. It used to make the covenant write
 *  index byte 1 into the new token at output 0; with the byte gone the new token is the honest one, so the output is
 *  left exactly as `createTransferOutputs` builds it. The token object advances as `commit()`/`settle()` would. */
export const spendIdx1 = async (tok: SimpleMultiBOLT, to: PrivateKey, isCommit: boolean): Promise<Transaction> => {
  const tpl = new SimpleMultiTemplate()
  const inputs = (tok as any).createTransferInputs(to, '', isCommit, false, undefined, false) as any[]
  const hasAnc = !isCommit && tok.prevTxs.length >= 3
  const proofVout = hasAnc ? ((tok as any).findProofVout(tok.prevTxs[tok.prevTxs.length - 3], tok.signer) as number) : 1
  inputs[0].unlockingScriptTemplate = tpl.unlock(tok.signer, pubOf(to), tok.prevTxs, false, false, [],
    isCommit ? [0x21] : [0x20], [0x01], [], hasAnc ? (tok as any).voutLE(proofVout) : [])
  const outputs = (tok as any).createTransferOutputs(to, isCommit, false) as any[]
  const tx = new Transaction(2, inputs, outputs)
  await tx.fee(0)
  await tx.sign()
  const c = cleanTx(tx)
  tok.tx = c
  tok.voutIdx = 0
  tok.prevTxs.push(c)
  if (!isCommit) { tok.signer = to as any; tok.pubKey = pubOf(to); tok.pubKeyHash = Hash.hash160(tok.pubKey) }
  return c
}

/** The last two transactions a builder object produced: a commit and its settle. */
export const last2 = (tok: SimpleMultiBOLT): [Transaction, Transaction] =>
  [tok.prevTxs[tok.prevTxs.length - 2], tok.prevTxs[tok.prevTxs.length - 1]]

/** A melt of the token at output `vout` of `tx` by `key`, funded from a fresh source. */
export const meltOf = async (tx: Transaction, vout: number, key: PrivateKey): Promise<Transaction> => {
  const tpl = new SimpleMultiTemplate()
  const meltTx = new Transaction(2, [
    { sourceTransaction: tx, sourceOutputIndex: vout, sequence: 0xffffffff, unlockingScriptTemplate: tpl.melt(key) },
    fundFor(key),
  ], [{ change: true, lockingScript: new P2PKH().lock(Hash.hash160(pubOf(key))) }])
  await meltTx.fee(0)
  await meltTx.sign()
  return cleanTx(meltTx)
}

/**
 * The settle of an honest split, rebuilt by hand with the given flags. `main` is the first split token the honest
 * `split()` returned, so its lineage ends with the honest settle, which is replaced; `owner` signed the split,
 * `keyA`/`keyB` are the two recipients, `total` and `piece` the balances. `swapped` sets `pkh1` (the covenant then
 * expects the two tokens in the other order); `i2` sets the interop-outpoint slot (which used to set the second
 * token's index byte to 0). Returns the settle, the lineage up to it, and where each token sits.
 */
export async function splitSettleWithFlags(main: SimpleMultiBOLT, owner: PrivateKey, keyA: PrivateKey, keyB: PrivateKey,
  total: number[], piece: number[], swapped: boolean, i2: boolean) {
  const tpl = new SimpleMultiTemplate()
  const proofTpl = new Pay2ProofTemplate()
  const txs = main.prevTxs.slice(0, main.prevTxs.length - 1)
  const commit = txs[txs.length - 1]
  const anc = txs[txs.length - 3]
  const ancProof = (main as any).findProofVout(anc, owner) as number
  const mainBal = (main as any).subtractBalances(total, piece) as number[]
  const outA = tpl.lock(pubOf(keyA), txs, mainBal, zeros(16), zeros(20), zeros(20), zeros(36), [0x22], 0)
  const outB = tpl.lock(pubOf(keyB), txs, piece, zeros(16), zeros(20), zeros(20), zeros(36), [0x22], 0)
  const settleTx = new Transaction(2, [
    { sourceTransaction: commit, sourceOutputIndex: 0, sequence: 0xffffffff,
      unlockingScriptTemplate: tpl.unlock(owner, swapped ? pubOf(keyA) : [], txs, false, false, [], [0x22], [0x00], [],
        (main as any).voutLE(ancProof), [], [], i2 ? buildOutpoint(anc, 0) : []) },
    { sourceTransaction: anc, sourceOutputIndex: ancProof, sequence: 0xffffffff, unlockingScriptTemplate: proofTpl.unlock(owner) },
    { sourceTransaction: commit, sourceOutputIndex: commit.outputs.length - 1, sequence: 0xffffffff, unlockingScriptTemplate: new P2PKH().unlock(owner) },
  ], [
    { satoshis: 1, lockingScript: swapped ? outB : outA },
    { satoshis: 1, lockingScript: swapped ? outA : outB },
    { change: true, lockingScript: new P2PKH().lock(Hash.hash160(pubOf(keyA))) },
  ])
  await settleTx.fee(0)
  await settleTx.sign()
  const settle = cleanTx(settleTx)
  return { settle, lineage: [...txs, settle], mainBal, aVout: swapped ? 1 : 0, bVout: swapped ? 0 : 1 }
}
