// The fungible issuer guard, executed on the shipped SimpleMultiBOLT bytecode (real txs, Spend engine).
//
// Both families open their lock with "the issuer must sign this spend":
//   NFT      needsIssuer    = isGenesis || (grandparent == 0 && txoType != 0)      <- the `is2ndTx` flag
//   fungible needsIssuerKey = isGenesis || (grandparent == 0)                      <- the F3 fix, 2026-09-07
// The fungible rule is a superset of the NFT one, so `is2ndTx` is neither present nor needed here. This suite
// pins that on the bytes: see docs/issuer-guard.md for the history and why the two keep being conflated.
//
// Method (as minSimpleAttack.test.ts): every attack asserts WHICH opcode refuses (the guard's OP_EQUALVERIFY,
// not something downstream), and ships a positive control built the same way that is ACCEPTED.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, LockingScript, Script } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import { verifyTx, buildOutpoint, toSigner } from '../../src/lib/boltLib.js'

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

/** Lock-chunk index of the issuer guard: the first OP_EQUALVERIFY after the 11 data pushes, which must be the
 *  `OP_IF OP_13 OP_PICK OP_EQUALVERIFY` of the prologue (so a refusal there is the guard, not a later check). */
function issuerGuardPc(lock: Script): number {
  const ops = lock.chunks.map((c) => c.op)
  const pc = ops.findIndex((op, k) => k >= 11 && op === 0x88)
  expect(ops.slice(pc - 3, pc + 1)).toEqual([0x63, 0x5d, 0x79, 0x88]) // OP_IF OP_13 OP_PICK OP_EQUALVERIFY
  return pc
}

const tpl = new SimpleMultiTemplate()

/** A token-shaped output the attacker funds from their own P2PKH: owner = attacker, parent = a REAL outpoint
 *  (non-zero, so isGenesis is false), grandparent = zeros, issuerPubKey = whoever we say, balance = 2^100.
 *  A commit-typed token (21) carries the committed recipient; a settled one (20) carries zeros. */
function fabricatedLock(txoType: number, parent: number[], issuer: number[]): LockingScript {
  const pkhCommit = txoType === 0x21 ? aPkh : zeros(20)
  return new LockingScript([
    ...push(INVENTED), ...push(zeros(16)), ...push(aPkh), ...push(pkhCommit), ...push(zeros(20)), ...push(zeros(36)),
    ...push([txoType]), ...push([0x00]), ...push(parent), ...push(zeros(36)), ...push(issuer),
    ...tpl.staticSuffix().chunks,
  ])
}
async function fabricate(txoType: number, parent: number[], issuer: number[]): Promise<Transaction> {
  const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }])
  const f = new Transaction(); f.version = 2
  f.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  f.addOutput({ satoshis: 1, lockingScript: fabricatedLock(txoType, parent, issuer) })
  f.addOutput({ satoshis: 4000, change: true, lockingScript: new P2PKH().lock(aPkh) }) // the builder funds from the last output
  await f.sign()
  return f
}
/** The attacker spends a fabricated token through the ordinary builder, so the unlock is well-formed and the only
 *  thing wrong with the spend is who signs it. */
async function attackerSpends(f: Transaction, prevTxs: Transaction[], isCommit: boolean, issuer: number[]): Promise<Transaction> {
  const t = new SimpleMultiBOLT()
  t.skipVerify = true
  t.tx = f; t.voutIdx = 0; t.prevTxs = prevTxs
  t.pubKey = attackerPub; t.pubKeyHash = aPkh; t.issuerPubKey = issuer; t.signer = toSigner(attackerKey)
  t.balance = INVENTED; t.balanceCommit = zeros(16)
  await (isCommit ? t.commit(attackerKey) : t.settle(attackerKey))
  return t.tx!
}
const victimMint = () => new SimpleMultiBOLT().mint(issuerKey, freshSource(issuerKey), '', bal(BigInt(1000)))

describe('SimpleMultiBOLT: the zero-grandparent issuer guard covers both is2ndTx shapes', () => {
  it('control: the honest first settle (the issuer spends commit1, whose grandparent is zero) is ACCEPTED', async () => {
    const tok = await victimMint()
    await tok.commit(userKey)
    expect(tok.tx!.outputs[0].lockingScript.chunks[9].data).toEqual(zeros(36)) // grandparent == 0 at the first commit
    await tok.settle(userKey)
    expect(run(tok.tx!).ok).toBe(true)
  })

  it('the is2ndTx shape (txoType 21, no grandparent, non-issuer owner, victim issuer): the SETTLE is REFUSED at the guard', async () => {
    const victim = await victimMint()
    const f = await fabricate(0x21, buildOutpoint(victim.tx!, 0), issuerPub)
    const r = run(await attackerSpends(f, [victim.tx!, f], false, issuerPub))
    expect(r.ok).toBe(false)
    expect(r.context).toBe('LockingScript')
    expect(r.pc).toBe(issuerGuardPc(f.outputs[0].lockingScript))
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
  })

  it('the F3 shape (txoType 20, no grandparent, non-issuer owner, victim issuer): the COMMIT is REFUSED at the same guard', async () => {
    // The NFT family tolerates this shape at the commit (minSimpleAttack B1.0) because an NFT has no balance to
    // inflate and its settle is refused anyway. A fungible token cannot afford the one hop.
    const victim = await victimMint()
    const f = await fabricate(0x20, buildOutpoint(victim.tx!, 0), issuerPub)
    const r = run(await attackerSpends(f, [f], true, issuerPub))
    expect(r.ok).toBe(false)
    expect(r.context).toBe('LockingScript')
    expect(r.pc).toBe(issuerGuardPc(f.outputs[0].lockingScript))
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
  })

  it('isolation: the SAME is2ndTx-shaped bytes naming the attacker as issuer are ACCEPTED (only the guard refuses)', async () => {
    const victim = await victimMint()
    const f = await fabricate(0x21, buildOutpoint(victim.tx!, 0), attackerPub)
    const r = run(await attackerSpends(f, [victim.tx!, f], false, attackerPub))
    expect(r.message, r.message).toBeUndefined()
    expect(r.ok).toBe(true)
  })
})
