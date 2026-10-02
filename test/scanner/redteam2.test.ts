// redteam2 — off-chain READER red-team for the b017 scanner (verifyEvents + fingerprints).
//
// The covenant is sound and node-verified; these tests attack what the OFF-CHAIN reader wrongly
// ACCEPTS. Every input is built live from the SimpleMultiBOLT token class, then tampered at the
// script/interface level. Each assertion documents what the reader returns and whether that is a
// MISREAD (accepted something a correct reader should reject) or CORRECT / BY-DESIGN.
//
// Chunk layout of a SimpleMultiBOLT token lock (LAYOUTS in fingerprints.ts / SMB_CHUNK in
// spv-demo-wapps smbToken.ts):
//   0 balance(16) 1 balanceCommit(16) 2 pubKeyHash(20) 3 pkhCommit(20) 4 pkhCommit2(20)
//   5 otherGrandparent(36) 6 txoType(1) 7 outputIndexN(1) 8 parent(36) 9 grandparent(36) 10 issuer(33)
// verifyEvents FIELDS only ever reads {pubKeyHash,commitment,txoType,parent,grandparent} — never
// balance/balanceCommit — so the scanner does NO arithmetic.
import { describe, it, expect } from 'vitest'
import { OP, Hash, P2PKH, PrivateKey, Script, LockingScript, UnlockingScript, Transaction, Utils } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { verifyEvents } from '../../src/lib/scanner/verifyEvents.js'
import { recognizeType, issuerPubKeyOf } from '../../src/lib/scanner/fingerprints.js'
import { appendOutput, assertOutputAdded } from '../helpers/counterfeit.js'

const T = 'SimpleMultiBOLT' as const
const MASK64 = (1n << 64n) - 1n
const bal = (amount: bigint): number[] => {
  const x = amount & ((1n << 128n) - 1n)
  const b = Buffer.alloc(16)
  b.writeBigUInt64LE(x & MASK64, 0)
  b.writeBigUInt64LE((x >> 64n) & MASK64, 8)
  return Array.from(b)
}
const SIM = BigInt('0x1ffffffffffffe')
const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const issuerPubHex = Utils.toHex(issuerKey.toPublicKey().encode(true) as number[])
const child = (n: string) => issuerKey.deriveChild(issuerKey.toPublicKey(), n)
const freshSource = () =>
  new Transaction(1, [], [{
    satoshis: 1000, change: true,
    lockingScript: new P2PKH().lock(Hash.hash160(issuerKey.toPublicKey().encode(true) as number[])),
  }])

/** A live mint->commit->settle transfer. prevTxs = [mint, commit, settle]. */
async function mkTransfer(amount: number[] = bal(SIM)) {
  const t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', amount)
  await t.transfer(child('1'))
  return t
}

/** Patch selected chunks (by index) of a locking script, preserving push lengths. */
const patchLock = (lock: Script, patches: Record<number, number[]>): LockingScript =>
  new LockingScript(lock.chunks.map((c, i) =>
    patches[i] ? { op: patches[i].length, data: patches[i] } : c))

/** Assemble a raw tx from explicit inputs/outputs (no signing — the scanner never runs scripts),
 *  round-trip through hex to canonicalise, then re-attach the given source txs by input index. */
function assemble(
  inputs: { sourceTXID: string; sourceOutputIndex: number; sourceTransaction?: Transaction }[],
  outputs: { satoshis: number; lockingScript: Script }[],
  sources: Record<number, Transaction | undefined>,
): Transaction {
  const tx = new Transaction()
  tx.version = 2
  for (const i of inputs)
    tx.addInput({ sourceTXID: i.sourceTXID, sourceOutputIndex: i.sourceOutputIndex, unlockingScript: new UnlockingScript([]), sequence: 0xffffffff })
  for (const o of outputs) tx.addOutput({ satoshis: o.satoshis, lockingScript: o.lockingScript })
  const parsed = Transaction.fromHex(tx.toHex())
  for (const [idx, src] of Object.entries(sources)) if (src) parsed.inputs[+idx].sourceTransaction = src
  return parsed
}

describe('redteam2 — b017 scanner off-chain reader', () => {
  // ── C1: double-settle. One commit, TWO distinct settles citing it (same parentOutpoint). ──
  it('C1 double-settle: a hand-patched second settle is now refused on EXECUTION (two validly signed settles remain a node-only double-spend)', async () => {
    const t = await mkTransfer()
    const [, commit, settle] = t.prevTxs // [mint, commit, settle]

    // A second, byte-distinct settle: same token output @vout0 (same parent -> same commit), one
    // extra p2pkh change output appended so its txid differs. This is a real double-spend of the
    // commit's token output; a node rejects it, the scanner cannot see it.
    const p2pkhHex = '76a914' + '11'.repeat(20) + '88ac'
    const settle2Hex = appendOutput(settle.toHex(), p2pkhHex, 0)
    assertOutputAdded(settle.toHex(), settle2Hex)
    const settle2 = Transaction.fromHex(settle2Hex)
    settle.inputs.forEach((inp, i) => { settle2.inputs[i].sourceTransaction = inp.sourceTransaction })

    expect(settle.id('hex')).not.toBe(settle2.id('hex')) // genuinely two different settles

    // Positive control: the honest single settle is accepted.
    const honest = verifyEvents([commit, settle], { expectedType: T })
    expect(honest.ok, honest.reason).toBe(true)

    // The structure alone would pass (completeness, not uniqueness), but the patched copy's signature no longer
    // covers its outputs, so the scanner's script execution refuses it. (A SECOND, validly signed settle of the same
    // commit is a genuine double spend; only a node can see that - the scanner cannot.)
    const r = verifyEvents([commit, settle, settle2], { expectedType: T })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/script execution failed/)
  })

  // ── C2: caller-controlled classification. A second token input, its source WITHHELD, is read as
  //         "external" funding and waved through. classifyIn -> "external" when the source tx is not
  //         in the caller-supplied batch, and the caller controls the batch. ──
  it('C2 hidden token input: a withheld-source 2nd token passes the structure but is refused on execution', async () => {
    const t = await mkTransfer()
    const [, commit, settle] = t.prevTxs
    const other = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM)) // a 2nd token
    const otherMint = other.tx as Transaction

    const tokenOut = settle.outputs[0] // recognised settle token, parent -> commit
    const changeOut = settle.outputs[1] // p2pkh change

    // settle-shaped tx: [ tokenInput(source=commit), smuggledTokenInput(source of otherMint) ]
    const build = (attachSmuggledSource: boolean) => {
      const tx = assemble(
        [
          { sourceTXID: commit.id('hex'), sourceOutputIndex: 0 },
          { sourceTXID: otherMint.id('hex'), sourceOutputIndex: 0 },
        ],
        [
          { satoshis: 1, lockingScript: tokenOut.lockingScript },
          { satoshis: (changeOut.satoshis as number) ?? 1, lockingScript: changeOut.lockingScript },
        ],
        { 0: commit, 1: attachSmuggledSource ? otherMint : undefined },
      )
      return tx
    }

    // Source withheld -> classifyIn returns "external" -> the 2nd token input lands in the funding region and the
    // STRUCTURE passes; but every input's source tx must be supplied, so the withheld source is refused outright.
    const smuggled = verifyEvents([commit, build(false)], { expectedType: T })
    expect(smuggled.ok).toBe(false)
    expect(smuggled.reason).toMatch(/was not supplied/)

    // CORRECT control: attach the smuggled input's source -> it classifies as "token" at position 1
    // and the arrangement rejects it.
    const exposed = verifyEvents([commit, build(true)], { expectedType: T })
    expect(exposed.ok).toBe(false)
    expect(exposed.reason).toMatch(/unexpected input @1: token/)
  })

  // ── C3: unknown txoType byte. categorise() switches on the 1-byte txoType; any unrecognised byte
  //         falls to `default: settle`. ──
  it('C3 unknown txoType: a novel action byte (0x77) is routed to settle structurally but refused on execution', async () => {
    const t = await mkTransfer()
    const [, commit, settle] = t.prevTxs
    const tokenLock = settle.outputs[0].lockingScript
    const changeOut = settle.outputs[1]
    const funding = freshSource() // the settle's funding source, supplied

    // Control: the genuine settle (txoType 0x20 -> default settle) is accepted.
    const honest = verifyEvents([commit, settle], { expectedType: T })
    expect(honest.ok, honest.reason).toBe(true)

    // Patch chunk 6 (txoType) to a byte defined nowhere in the protocol; parent (chunk 8) still
    // points to the commit so pairing succeeds.
    const novelLock = patchLock(tokenLock, { 6: [0x77] })
    expect(recognizeType(novelLock, T)).toBe(T) // still a recognised token (length + suffix unchanged)
    const novelSettle = assemble(
      [
        { sourceTXID: commit.id('hex'), sourceOutputIndex: 0 },
        { sourceTXID: funding.id('hex'), sourceOutputIndex: 0 }, // funding, source supplied
      ],
      [
        { satoshis: 1, lockingScript: novelLock },
        { satoshis: (changeOut.satoshis as number) ?? 1, lockingScript: changeOut.lockingScript },
      ],
      { 0: commit, 1: funding },
    )

    // The unknown action byte is routed to `settle` structurally, but the covenant refuses the patched token on execution.
    const r = verifyEvents([commit, novelSettle], { expectedType: T })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/script execution failed/)
  })

  // ── C4: forged balance. The scanner reads no balance field, so an inflated settle balance is
  //         invisible. BY DESIGN — the finding is that a scan pass is NOT a balance check. ──
  it('C4 forged balance: an inflated settle balance is refused on execution (the scanner does no arithmetic itself)', async () => {
    const t = await mkTransfer()
    const [, commit, settle] = t.prevTxs
    const tokenLock = settle.outputs[0].lockingScript
    const changeOut = settle.outputs[1]
    const funding = freshSource() // the settle's funding source, supplied

    const commitBal = Utils.toHex(commit.outputs[0].lockingScript.chunks[0].data as number[])
    const inflated = new Array(16).fill(0xff) // ~2^128-1
    const inflatedLock = patchLock(tokenLock, { 0: inflated })
    expect(recognizeType(inflatedLock, T)).toBe(T)

    const inflatedSettle = assemble(
      [
        { sourceTXID: commit.id('hex'), sourceOutputIndex: 0 },
        { sourceTXID: funding.id('hex'), sourceOutputIndex: 0 },
      ],
      [
        { satoshis: 1, lockingScript: inflatedLock },
        { satoshis: (changeOut.satoshis as number) ?? 1, lockingScript: changeOut.lockingScript },
      ],
      { 0: commit, 1: funding },
    )

    const settleBal = Utils.toHex(inflatedSettle.outputs[0].lockingScript.chunks[0].data as number[])
    expect(settleBal).not.toBe(commitBal) // the balance was inflated vs the commit...

    // The scanner does no balance arithmetic itself (FIELDS omits it), but it now EXECUTES the settle, and the
    // covenant refuses an inflated balance - so a forged balance no longer passes a scan.
    const r = verifyEvents([commit, inflatedSettle], { expectedType: T })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/script execution failed/)
  })

  // ── C5: recognizeType look-alike + issuerPubKeyOf returns any 33 bytes unvalidated. ──
  it('C5a recognizeType rejects a one-op-different suffix (recognition works)', async () => {
    const t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
    const lock = t.tx!.outputs[0].lockingScript
    const chunks = lock.chunks.map((c) => ({ ...c }))
    const last = chunks[chunks.length - 1]
    last.op = last.op === OP.OP_NOP ? OP.OP_1 : OP.OP_NOP // flip exactly one suffix opcode
    expect(recognizeType(new Script(chunks), T)).toBeNull() // CORRECT: suffix-hash mismatch rejects
  })

  it('C5b foreign issuer: any 33 bytes are recognised + returned unvalidated; the lone mint is refused as unauthenticated', async () => {
    const t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
    const mintTx = t.tx as Transaction
    const mintLock = mintTx.outputs[0].lockingScript // genesis: parent zeros
    const changeOut = mintTx.outputs[1]

    const foreignIssuer = new Array(33).fill(0xab) // 33 bytes, NOT a valid secp256k1 point
    const foreignLock = patchLock(mintLock, { 10: foreignIssuer })

    // recognizeType still matches (push lengths + suffix hash unchanged) and issuerPubKeyOf hands
    // back the garbage bytes with no curve/identity validation.
    expect(recognizeType(foreignLock, T)).toBe(T)
    expect(issuerPubKeyOf(foreignLock, T)).toEqual(foreignIssuer)

    const foreignMint = assemble(
      [{ sourceTXID: '00'.repeat(32), sourceOutputIndex: 0 }], // funding, external
      [
        { satoshis: 1, lockingScript: foreignLock },
        { satoshis: (changeOut.satoshis as number) ?? 1, lockingScript: changeOut.lockingScript },
      ],
      {},
    )

    // An issuer-agnostic scan (no trustedIssuerPubKey) used to wave a lone foreign/garbage-issuer mint through
    // as valid. A mint alone now proves nothing about the issuer key, so it is refused as UNAUTHENTICATED
    // (still reporting the claimed issuer so the caller sees what it names).
    const agnostic = verifyEvents([foreignMint], { expectedType: T })
    expect(agnostic.ok).toBe(false)
    expect(agnostic.unauthenticated).toBe(true)
    expect(agnostic.issuerPubKeyHex).toBe(Utils.toHex(foreignIssuer))

    // CORRECT control: pin the real issuer and the foreign-issuer token is rejected.
    const pinned = verifyEvents([foreignMint], { expectedType: T, trustedIssuerPubKey: issuerPubHex })
    expect(pinned.ok).toBe(false)
    expect(pinned.reason).toMatch(/trusted issuer/)
  })
})
