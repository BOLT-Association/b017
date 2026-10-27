// The MinSimpleBOLT attack builders shared by the red-team suite (test/lib/minSimpleAttack.test.ts) and the
// Lean vector exporter (lean/vectors/export.test.ts). Every builder is INTERNALLY CONSISTENT: an unlock arg
// never moves without the declared outputs moving with it, so a rejection is a covenant guard firing.
import { P2PKH, Transaction } from '@bsv/sdk'
import { spendToken, mintToken, p2pb, issuerKey, attackerKey, issuerPub, iPkh, uPkh, aPkh, ZERO20, ZERO36 } from './minSimpleChain.js'
import { minSimple as fam } from './minSimpleFamily.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const tpl = new MinSimpleTemplate()
const op = (txs: Transaction[], t: number, v: number) => buildOutpoint(txs[t], v)

// -- B1: the F3-shape orphan ----------------------------------------------------------------------
//   tx0 attacker funding: [4000 p2pkh, 1-sat p2pb proof slot] (no covenant runs)
//   tx1 fabricate the resting token: victim issuer, attacker owner, parent != 0, gp = 0
//   tx2 commit it ('21')   -> escapes the issuer guard + the ancestor rebuild
//   tx3 settle it ('00')   -> must rebuild tx1 as a genuine commit -> refused
export async function fabricate(o: { txoType?: number; parent?: boolean } = {}): Promise<Transaction[]> {
  const txoType = o.txoType ?? 0x00
  const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }])
  const tx0 = new Transaction(); tx0.version = 2
  tx0.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  tx0.addOutput({ satoshis: 4000, lockingScript: new P2PKH().lock(aPkh) })
  tx0.addOutput({ satoshis: 1, lockingScript: p2pb(aPkh) }) // vout1: a non-zero outpoint the attacker controls + proof slot
  await tx0.sign()
  const txs = [tx0]
  const parent = o.parent === false ? ZERO36 : buildOutpoint(tx0, 1)
  const tx1 = new Transaction(); tx1.version = 2
  tx1.addInput({ sourceTransaction: tx0, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  tx1.addOutput({ satoshis: 1, lockingScript: tpl.lock(aPkh, issuerPub, ZERO20, [txoType], parent, ZERO36) }) // victim issuer
  tx1.addOutput({ satoshis: 3800, lockingScript: new P2PKH().lock(aPkh) }) // funds the commit
  await tx1.sign()
  txs.push(tx1)
  return txs
}

export const commitFabricated = async (txs: Transaction[]) => {
  const fabParent = (txs[1].outputs[0].lockingScript.chunks[3].data as number[])
  txs.push(await spendToken({
    fam, txs, from: { tx: 1, vout: 0 }, actor: attackerKey, beneficiary: aPkh, fund: { tx: 1, vout: 1 }, change: true,
    fundKey: attackerKey,
    outputs: [fam.lock(aPkh, aPkh, [0x21], op(txs, 1, 0), fabParent), p2pb(aPkh)],
  }))
  return txs
}

export const settleFabricated = async (txs: Transaction[]) => {
  txs.push(await spendToken({
    fam, txs, from: { tx: 2, vout: 0 }, actor: attackerKey, beneficiary: aPkh, fund: { tx: 2, vout: 2 }, change: true,
    proof: { src: { tx: 0, vout: 1 }, key: attackerKey }, // the grandparent co-spend placeholder
    prevTxs: [txs[0], txs[1], txs[0], txs[2]],             // ancestor slot (len-3) = the fabricating tx1
    outputs: [fam.lock(aPkh, ZERO20, [0x00], op(txs, 2, 0), op(txs, 1, 0))],
  }))
  return txs
}


// -- B4: a commit of the genesis forced to emit an arbitrary txoType byte ------------------------------
export const commitWith = async (txoType: number) => {
  const txs = await mintToken(fam)
  txs.push(await spendToken({
    fam, txs, from: { tx: 0, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 0, vout: 1 }, change: true,
    outputs: [fam.lock(iPkh, uPkh, [txoType], op(txs, 0, 0), ZERO36), p2pb(uPkh)],
  }))
  return txs
}

