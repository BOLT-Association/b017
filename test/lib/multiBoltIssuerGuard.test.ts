// The issuer guard, executed on the shipped bytecode of every contract that carries it (real txs, Spend engine):
// the fungible SimpleMultiBOLT and its genesis family (FixedBOLT, OpenBOLT), and the NFT carriers MinSimpleBOLT,
// AuthBOLT and SerialBOLT.
//
// Both families open their lock with "the issuer must sign this spend":
//   NFT      needsIssuer    = isGenesis || (grandparent == 0 && txoType != 0)      <- the `is2ndTx` flag
//   fungible needsIssuerKey = isGenesis || (grandparent == 0)                      <- the F3 fix, 2026-09-07
// The fungible rule is a superset of the NFT one, so `is2ndTx` is neither present nor needed there. The genesis
// contracts (FixedBOLT, OpenBOLT, SerialBOLT) run their family's guard after the opcodes that handle their two
// leading pushes (genesis outpoint, mintData). This suite pins all of that on the bytes: see docs/issuer-guard.md
// for the history and why the two keep being conflated. minSimpleAttack.test.ts attacks MinSimpleBOLT more widely.
//
// Method (as minSimpleAttack.test.ts): every attack asserts WHICH opcode refuses (the guard's OP_EQUALVERIFY,
// not something downstream), and ships a positive control built the same way that is ACCEPTED.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, LockingScript, Script } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { FixedBOLT, OpenBOLT } from '../../src/tokens/GenesisMultiBOLT.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import FixedMultiTemplate from '../../src/tokens/templates/FixedMulti.sx.template.js'
import OpenMultiTemplate from '../../src/tokens/templates/OpenMulti.sx.template.js'
import { verifyTx, buildOutpoint, toSigner } from '../../src/lib/boltLib.js'
import * as nft from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt, tpl as authTpl } from '../helpers/authBoltFamily.js'
import { serialBolt, tpl as serialTpl } from '../helpers/serialBoltFamily.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'

const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const attackerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000002', 'hex')
const userKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000003', 'hex')
const issuerPub = issuerKey.toPublicKey().encode(true) as number[]
const attackerPub = attackerKey.toPublicKey().encode(true) as number[]
const aPkh = Hash.hash160(attackerPub)
const zeros = (n: number) => new Array(n).fill(0x00)
const push = (d: number[]) => new Script().writeBin(d).chunks

const MASK64 = (BigInt(1) << BigInt(64)) - BigInt(1)
function bal(amount: bigint): number[] {
  const buf = Buffer.alloc(16)
  buf.writeBigUInt64LE(amount & MASK64, 0)
  buf.writeBigUInt64LE((amount >> BigInt(64)) & MASK64, 8)
  return Array.from(buf)
}
const INVENTED = bal(BigInt(1) << BigInt(100)) // 2^100: the balance of the fabricated-hop repro

const freshSource = (key: PrivateKey) =>
  new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(key.toPublicKey().encode(true) as number[])) }])

type Run = { ok: boolean; message?: string; pc?: number; context?: string }
function run(tx: Transaction): Run {
  tx.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
  try { return { ok: verifyTx(tx, true).valid } }
  catch (e: any) { return { ok: false, message: String(e?.message ?? e), pc: e?.programCounter, context: e?.context } }
}

/** Lock-chunk index of the issuer guard's OP_EQUALVERIFY, found from the guard's own flag rather than by position:
 *  the first OP_BOOLOR followed by OP_IF (fungible: OP_BOOLOR OP_TUCK OP_IF OP_13 OP_PICK; NFT: OP_BOOLOR OP_IF OP_3
 *  OP_PICK OP_10 OP_PICK), then its OP_EQUALVERIFY. Searching by position would pick the genesis family's earlier
 *  mintData check (OP_DUP OP_0 OP_EQUALVERIFY), so a refusal there is the guard, not a check before it. */
function issuerGuardPc(lock: Script): number {
  const ops = lock.chunks.map((c) => c.op)
  const flag = ops.findIndex((op, k) => op === 0x9b && (ops[k + 1] === 0x63 || (ops[k + 1] === 0x7d && ops[k + 2] === 0x63)))
  expect(flag).toBeGreaterThan(0)
  const pc = ops.indexOf(0x88, flag)
  // between the flag and the check: only OP_TUCK, OP_IF, small-number pushes and the OP_PICKs that fetch the two keys
  expect(ops.slice(flag + 1, pc).every((op) => op === 0x7d || op === 0x63 || op === 0x79 || (op >= 0x51 && op <= 0x60))).toBe(true)
  return pc
}

// -- the fungible family: SimpleMultiBOLT and the genesis family built on it ------------------------------------
interface Fungible { name: string; make: () => SimpleMultiBOLT; tpl: SimpleMultiTemplate; leading: number }
const FUNGIBLE: Fungible[] = [
  { name: 'SimpleMultiBOLT', make: () => new SimpleMultiBOLT(), tpl: new SimpleMultiTemplate(), leading: 0 },
  { name: 'FixedBOLT', make: () => new FixedBOLT(), tpl: new FixedMultiTemplate(), leading: 2 },
  { name: 'OpenBOLT', make: () => new OpenBOLT(), tpl: new OpenMultiTemplate(), leading: 2 },
]

/** A token-shaped output the attacker funds from their own P2PKH: owner = attacker, parent = a REAL outpoint
 *  (non-zero, so isGenesis is false), grandparent = zeros, issuerPubKey = whoever we say, balance = 2^100.
 *  A commit-typed token (21) carries the committed recipient; a settled one (20) carries zeros. The genesis family
 *  leads with the genesis outpoint (the mint outpoint it names as parent, as the first commit's output carries) and
 *  an empty mintData (the mint alone carries one). */
function fabricatedLock(fam: Fungible, txoType: number, parent: number[], issuer: number[]): LockingScript {
  const pkhCommit = txoType === 0x21 ? aPkh : zeros(20)
  return new LockingScript([
    ...(fam.leading ? [...push(parent), ...push([])] : []),
    ...push(INVENTED), ...push(zeros(16)), ...push(aPkh), ...push(pkhCommit), ...push(zeros(20)), ...push(zeros(36)),
    ...push([txoType]), ...push([0x00]), ...push(parent), ...push(zeros(36)), ...push(issuer),
    ...fam.tpl.staticSuffix().chunks,
  ])
}
async function fabricate(fam: Fungible, txoType: number, parent: number[], issuer: number[]): Promise<Transaction> {
  const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }])
  const f = new Transaction(); f.version = 2
  f.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  f.addOutput({ satoshis: 1, lockingScript: fabricatedLock(fam, txoType, parent, issuer) })
  f.addOutput({ satoshis: 4000, change: true, lockingScript: new P2PKH().lock(aPkh) }) // the builder funds from the last output
  await f.sign()
  return f
}
/** The attacker spends a fabricated token through the ordinary builder, so the unlock is well-formed and the only
 *  thing wrong with the spend is who signs it. */
async function attackerSpends(fam: Fungible, f: Transaction, prevTxs: Transaction[], isCommit: boolean, issuer: number[]): Promise<Transaction> {
  const t = fam.make()
  t.skipVerify = true
  t.tx = f; t.voutIdx = 0; t.prevTxs = prevTxs
  t.pubKey = attackerPub; t.pubKeyHash = aPkh; t.issuerPubKey = issuer; t.signer = toSigner(attackerKey)
  t.balance = INVENTED; t.balanceCommit = zeros(16)
  await (isCommit ? t.commit(attackerKey) : t.settle(attackerKey))
  return t.tx!
}
const victimMint = (fam: Fungible) => fam.make().mint(issuerKey, freshSource(issuerKey), '', bal(BigInt(1000)))

describe.each(FUNGIBLE.map((f) => [f.name, f] as const))('%s: the zero-grandparent issuer guard refuses the F3 shape and the settle-typed orphan', (_name, fam) => {
  it('control: the honest first settle (the issuer spends commit1, whose grandparent is zero) is ACCEPTED', async () => {
    const tok = await victimMint(fam)
    await tok.commit(userKey)
    expect(tok.tx!.outputs[0].lockingScript.chunks[9 + fam.leading].data).toEqual(zeros(36)) // grandparent == 0 at the first commit
    await tok.settle(userKey)
    expect(run(tok.tx!).ok).toBe(true)
  })

  it('the F3 / is2ndTx shape (txoType 21, no grandparent, non-issuer owner, victim issuer): the SETTLE is REFUSED at the guard', async () => {
    const victim = await victimMint(fam)
    const f = await fabricate(fam, 0x21, buildOutpoint(victim.tx!, 0), issuerPub)
    const r = run(await attackerSpends(fam, f, [victim.tx!, f], false, issuerPub))
    expect(r.ok).toBe(false)
    expect(r.context).toBe('LockingScript')
    expect(r.pc).toBe(issuerGuardPc(f.outputs[0].lockingScript))
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
  })

  it('the settle-typed orphan (txoType 20, no grandparent, non-issuer owner, victim issuer): the COMMIT is REFUSED at the same guard', async () => {
    // Only the fungible rule refuses this at the commit. The NFT family's is2ndTx lets the analogous 00 token through
    // (minSimpleAttack B1.0, and SerialBOLT below) and relies on the settle. F3 itself was the 21 shape above, which
    // both rules refuse.
    const victim = await victimMint(fam)
    const f = await fabricate(fam, 0x20, buildOutpoint(victim.tx!, 0), issuerPub)
    const r = run(await attackerSpends(fam, f, [f], true, issuerPub))
    expect(r.ok).toBe(false)
    expect(r.context).toBe('LockingScript')
    expect(r.pc).toBe(issuerGuardPc(f.outputs[0].lockingScript))
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
  })

  it('isolation: the SAME is2ndTx-shaped bytes naming the attacker as issuer are ACCEPTED (only the guard refuses)', async () => {
    const victim = await victimMint(fam)
    const f = await fabricate(fam, 0x21, buildOutpoint(victim.tx!, 0), attackerPub)
    const r = run(await attackerSpends(fam, f, [victim.tx!, f], false, attackerPub))
    expect(r.message, r.message).toBeUndefined()
    expect(r.ok).toBe(true)
  })
})

// -- the NFT family: MinSimpleBOLT, AuthBOLT and SerialBOLT (is2ndTx) ------------------------------------------
// Built on the NFT chain harness, with the harness's own keys. Outputs are built with each template directly so the
// issuer key (and SerialBOLT's genesis field) are explicit; the family adapter supplies the mint and the unlocker.
const minSimpleTpl = new MinSimpleTemplate()
interface Nft {
  name: string
  fam: nft.Family
  /** owner, issuer, commitment, txoType, parent, grandparent; `root` is SerialBOLT's genesis field. */
  lock: (owner: number[], issuer: number[], commitment: number[], txoType: number, parent: number[], gp: number[], root: number[]) => Script
}
const NFTS: Nft[] = [
  { name: 'MinSimpleBOLT', fam: minSimple, lock: (o, i, c, t, p, g) => minSimpleTpl.lock(o, i, c, [t], p, g) },
  { name: 'AuthBOLT', fam: authBolt, lock: (o, i, c, t, p, g) => authTpl.lock(o, i, c, [t], p, g) },
  { name: 'SerialBOLT', fam: serialBolt, lock: (o, i, c, t, p, g, root) => serialTpl.lock(o, i, c, [t], p, g, root, []) },
]

/** An NFT-shaped output the attacker funds from their own P2PKH, its parent the victim's real mint outpoint and its
 *  grandparent zero (SerialBOLT carries that outpoint as its genesis field, as the first commit's output does). */
async function fabricateNft(n: Nft, txoType: number, issuer: number[]): Promise<{ txs: Transaction[]; parent: number[] }> {
  const [victim] = await nft.mintToken(n.fam)
  const parent = buildOutpoint(victim, 0)
  const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(nft.aPkh) }])
  const f = new Transaction(); f.version = 2
  f.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(nft.attackerKey), sequence: 0xffffffff })
  const commitment = txoType === 0x21 ? nft.aPkh : nft.ZERO20
  f.addOutput({ satoshis: 1, lockingScript: n.lock(nft.aPkh, issuer, commitment, txoType, parent, nft.ZERO36, parent) })
  f.addOutput({ satoshis: 4000, lockingScript: new P2PKH().lock(nft.aPkh) })
  await f.sign()
  return { txs: [victim, f], parent }
}
/** The attacker spends the fabrication at txs[1]: a commit (spending 00) emits a 21 token and its proof; a settle
 *  (spending 21) emits the 00 token paid to the committed owner. No grandparent, so nothing is rebuilt. */
const attackerSpendsNft = (n: Nft, txs: Transaction[], parent: number[], issuer: number[], isCommit: boolean) =>
  nft.spendToken({
    fam: n.fam, txs, from: { tx: 1, vout: 0 }, actor: nft.attackerKey, beneficiary: nft.aPkh,
    fund: { tx: 1, vout: 1 }, change: true, fundKey: nft.attackerKey,
    outputs: isCommit
      ? [n.lock(nft.aPkh, issuer, nft.aPkh, 0x21, buildOutpoint(txs[1], 0), parent, parent), nft.p2pb(nft.aPkh)]
      : [n.lock(nft.aPkh, issuer, nft.ZERO20, 0x00, buildOutpoint(txs[1], 0), parent, parent)],
  })

describe.each(NFTS.map((n) => [n.name, n] as const))('%s: the NFT issuer guard (is2ndTx)', (_name, n) => {
  it('control: the honest lifecycle (mint -> commit -> settle) is ACCEPTED', async () => {
    expect(nft.verifyChain(await nft.buildChain(n.fam, {}, 3)).ok).toBe(true)
  })

  it('the is2ndTx shape (txoType 21, no grandparent, non-issuer owner, victim issuer): the SETTLE is REFUSED at the guard', async () => {
    const { txs, parent } = await fabricateNft(n, 0x21, nft.issuerPub)
    const r = run(await attackerSpendsNft(n, txs, parent, nft.issuerPub, false))
    expect(r.ok).toBe(false)
    expect(r.context).toBe('LockingScript')
    expect(r.pc).toBe(issuerGuardPc(txs[1].outputs[0].lockingScript))
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
  })

  it('isolation: the SAME is2ndTx-shaped bytes naming the attacker as issuer are ACCEPTED (only the guard refuses)', async () => {
    const { txs, parent } = await fabricateNft(n, 0x21, nft.pub(nft.attackerKey))
    const r = run(await attackerSpendsNft(n, txs, parent, nft.pub(nft.attackerKey), false))
    expect(r.message, r.message).toBeUndefined()
    expect(r.ok).toBe(true)
  })

  it('the narrower NFT rule: a resting 00 orphan with no grandparent is COMMITTED without the issuer (as minSimpleAttack B1.0)', async () => {
    // is2ndTx is false for a 00 token, so the guard does not fire and the lone commit is accepted; the settle after
    // it must rebuild the fabrication and cannot. Aligning the NFT rule with the fungible one (docs/ROADMAP.md) flips this.
    const { txs, parent } = await fabricateNft(n, 0x00, nft.issuerPub)
    const r = run(await attackerSpendsNft(n, txs, parent, nft.issuerPub, true))
    expect(r.message, r.message).toBeUndefined()
    expect(r.ok).toBe(true)
  })
})
