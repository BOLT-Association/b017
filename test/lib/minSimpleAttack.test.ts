// Red-team suite for MinSimpleBOLT (the identity NFT) - port of the contract-level suite onto the b017 library (real txs, Spend engine).
//
// Method (as the simulator suite):
//   - every attack is INTERNALLY CONSISTENT: an unlock arg never moves without the declared outputs
//     moving with it, so hashOutputs is satisfiable and a rejection is a guard firing;
//   - every attack asserts WHICH tx rejects (`failedTx`), never merely that something failed;
//   - every attack ships a POSITIVE CONTROL built the same way that is ACCEPTED.
//
// NFT attack surface: (B1) can a non-issuer forge a completed victim-issued event, (B2) non-owner
// spend / owner substitution, (B3) non-issuer genesis, (B4) txoType state-machine skips. Value-neutral
// NFT cloning is tolerated by design and is not treated as a defect.
//   B1 CLEAN  the F3-shape orphan is not a vulnerability: a RESTING '00' token with parent != 0 and
//             grandparent == 0 dodges the issuer guard and the rebuild at its OWN spend, so a lone COMMIT of
//             it is accepted - but a commit is half an event and the SETTLE refuses it (it cannot rebuild
//             the fabricating tx as a genuine commit). The refused settle IS the security model.
//   B2 CLEAN  ownership is covenant-bound: a substituted owner is refused at the creating tx's hashOutputs.
//   B3 CLEAN  a non-issuer cannot spend the genesis token.
//   B4 CLEAN  the txoType state machine is covenant-determined; every skip is refused.
import { describe, it, expect } from 'vitest'
import { P2PKH, Transaction } from '@bsv/sdk'
import {
  buildChain, verifyChain, spendToken, mintToken, p2pb, grandparentCheckPc,
  issuerKey, attackerKey, issuerPub, iPkh, uPkh, aPkh, ZERO20, ZERO36, pub, userKey,
  type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple as fam } from '../helpers/minSimpleFamily.js'
import { fabricate, commitFabricated, settleFabricated, commitWith } from '../helpers/minSimpleAttacks.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const tpl = new MinSimpleTemplate()
const op = (txs: Transaction[], t: number, v: number) => buildOutpoint(txs[t], v)
const rejectedAt = (r: ReturnType<typeof verifyChain>) => (r.ok ? undefined : r.failedTx)

// -- controls ------------------------------------------------------------------------------------
describe('controls - the honest lifecycle verifies under this harness', () => {
  it('full lifecycle (mint -> commit -> settle -> commit -> settle)', async () => {
    expect(verifyChain(await buildChain(fam)).ok).toBe(true)
  })
  it('genesis -> commit -> settle prefix', async () => {
    expect(verifyChain(await buildChain(fam, {}, 3)).ok).toBe(true)
  })
})

// -- B1: the F3-shape orphan ----------------------------------------------------------------------
//   tx0 attacker funding: [4000 p2pkh, 1-sat p2pb proof slot] (no covenant runs)
//   tx1 fabricate the resting token: victim issuer, attacker owner, parent != 0, gp = 0
//   tx2 commit it ('21')   -> escapes the issuer guard + the ancestor rebuild
//   tx3 settle it ('00')   -> must rebuild tx1 as a genuine commit -> refused
describe('B1 - a fabricated orphan cannot complete an event (the refused settle is the model)', () => {
  it('B1.0 a lone commit of the fabrication is accepted - but a commit is not an event', async () => {
    const txs = await commitFabricated(await fabricate())
    expect(verifyChain(txs).ok).toBe(true)
  })

  it('B1.1 THE GUARANTEE: the settle refuses the fabrication, so no valid event forms', async () => {
    const txs = await settleFabricated(await commitFabricated(await fabricate()))
    expect(verifyChain(txs.slice(0, 3)).ok).toBe(true) // the commit alone is accepted (B1.0)
    const r = verifyChain(txs)
    expect(rejectedAt(r)).toBe(3)
    // ... and it dies in the grandparent reconstruction (the txid check), not at hashOutputs
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
    expect(r.pc).toBe(grandparentCheckPc(txs[2].outputs[0].lockingScript))
  })

  it('B1.2 the escape is exact: a GENESIS shape (parent=0) re-arms the issuer guard', async () => {
    const txs = await commitFabricated(await fabricate({ parent: false }))
    expect(rejectedAt(verifyChain(txs))).toBe(2)
  })

  it('B1.3 the escape is exact: ANY non-zero txoType re-arms the issuer guard (is2ndTx)', async () => {
    const txs = await commitFabricated(await fabricate({ txoType: 0x02 }))
    expect(rejectedAt(verifyChain(txs))).toBe(2)
  })
})

// -- B2: ownership is bound to the lineage ----------------------------------------------------------
describe('B2 - ownership is bound to the lineage, not chosen by the spender', () => {
  it('B2.0 control: the honest owner spend is accepted', async () => {
    expect(verifyChain(await buildChain(fam, {}, 3)).ok).toBe(true)
  })

  it('B2.1 SECURITY: substituting the settle-revealed owner is refused at the settle', async () => {
    const txs = await buildChain(fam, {}, 2)
    txs.push(await spendToken({
      fam, txs, from: { tx: 1, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 1, vout: 2 }, change: true,
      outputs: [fam.lock(aPkh, ZERO20, [0x00], op(txs, 1, 0), op(txs, 0, 0))], // covenant computes the commitment (user)
    }))
    expect(rejectedAt(verifyChain(txs))).toBe(2)
  })

  it('B2.2 SECURITY: substituting the commit-carried owner is refused at the commit', async () => {
    const txs = await mintToken(fam)
    txs.push(await spendToken({
      fam, txs, from: { tx: 0, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 0, vout: 1 }, change: true,
      outputs: [fam.lock(aPkh, uPkh, [0x21], op(txs, 0, 0), ZERO36), p2pb(uPkh)], // covenant computes the token's owner (issuer)
    }))
    expect(rejectedAt(verifyChain(txs))).toBe(1)
  })
})

// -- B3: non-issuer genesis ---------------------------------------------------------------------------
describe('B3 - a non-issuer cannot mint (spend the genesis)', () => {
  it('B3.0 control: the issuer mints (issuerPubKey == owner)', async () => {
    expect(verifyChain(await buildChain(fam, {}, 2)).ok).toBe(true)
  })

  it('B3.1 SECURITY: a non-issuer spending the genesis is refused at the mint', async () => {
    // issuerPubKey is someone else's, but the token is owned/spendable by the issuer key, so the only key
    // that satisfies the owner gate is not the issuer.
    const other = pub(userKey)
    const bad: Family = { ...fam, lock: (o, c, t, p, g) => tpl.lock(o, other, c, t, p, g) }
    expect(rejectedAt(verifyChain(await buildChain(bad, {}, 2)))).toBe(1)
  })
})

// -- B4: the txoType state machine ------------------------------------------------------------------------
describe('B4 - the txoType state machine is covenant-determined', () => {
  it('B4.0 control: commit (00->21) then settle (21->00) is accepted', async () => {
    expect(verifyChain(await buildChain(fam, {}, 3)).ok).toBe(true)
  })

  it('B4.1 settle->settle: a 00 token forced to emit a 00 output is refused', async () => {
    expect(rejectedAt(verifyChain(await commitWith(0x00)))).toBe(1) // covenant computes 21
  })

  it('B4.2 commit->commit: a 21 token forced to emit a 21 output is refused', async () => {
    const txs = await buildChain(fam, {}, 2)
    txs.push(await spendToken({
      fam, txs, from: { tx: 1, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: { tx: 1, vout: 2 }, change: true,
      outputs: [fam.lock(uPkh, ZERO20, [0x21], op(txs, 1, 0), op(txs, 0, 0))], // covenant computes 00
    }))
    expect(rejectedAt(verifyChain(txs))).toBe(2)
  })

  it('B4.3 undefined OUTPUT txoType bytes are refused', async () => {
    for (const t of [0x02, 0x20, 0xff]) expect(rejectedAt(verifyChain(await commitWith(t)))).toBe(1)
  })

  it('B4.4 an undefined INPUT txoType byte does NOT enable orphaning - it re-arms the guard', async () => {
    // A fabricated token with txoType 02 (instead of 00) makes is2ndTx true, so the commit demands the
    // issuer key and is refused - the B1 escape needs txoType exactly 00.
    const txs = await commitFabricated(await fabricate({ txoType: 0x02 }))
    expect(rejectedAt(verifyChain(txs))).toBe(2)
  })
})

