// A minted token received by SPV does not prove the sender holds the issuer key: a mint is just an output whose
// lock NAMES an issuerPubKey, and anyone can create one naming anybody's key. The issuer guard only runs when the
// genesis is first SPENT, so the scanner must not accept a mint on its own. A mint is authenticated only by a
// commit that SPENDS it (funded or not) in the same event/batch; without one the verdict is "unauthenticated
// mint" - not a signature failure (the scanner is structural; it does not execute scripts, so the caller still
// verifyTx's the commit).
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, UnlockingScript } from '@bsv/sdk'
import {
  buildChain, verifyChain, spendToken, p2pb, UNFUNDED, issuerPub, aPkh, attackerKey, ZERO20, ZERO36, type Family,
} from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent } from '../../src/lib/scanner/verifyEvents.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

// A STRANGER mints a token naming the victim issuer's key: owner = the stranger, issuerPubKey = the victim's.
async function strangerMint(fam: Family): Promise<Transaction> {
  const funding = new Transaction(1, [], [{ satoshis: 5000, lockingScript: new P2PKH().lock(aPkh) }])
  const mint = new Transaction(); mint.version = 2
  mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(attackerKey), sequence: 0xffffffff })
  mint.addOutput({ satoshis: 1, lockingScript: fam.lock(aPkh, ZERO20, [0x00], ZERO36, ZERO36) }) // names `issuerPub` (the victim's)
  mint.addOutput({ satoshis: 4000, lockingScript: new P2PKH().lock(aPkh) })
  await mint.sign()
  return mint
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: a mint alone is unauthenticated`, () => {
    it("a stranger's lone mint naming the victim's issuer key is recognised as a well-formed token", async () => {
      const mint = await strangerMint(fam)
      // recognised + the issuer is the victim's: nothing about the mint itself shows who holds that key
      expect(Buffer.from(issuerPub).toString('hex')).toBeTruthy()
      const r = verifyEvents([mint], { trustedIssuerPubKey: issuerPub })
      expect(r.type).toBe(type)
      expect(r.issuerPubKeyHex).toBe(Buffer.from(issuerPub).toString('hex'))
    })

    it("verifyEvents REFUSES a lone mint: unauthenticated mint (no commit spends it)", async () => {
      const r = verifyEvents([await strangerMint(fam)], { trustedIssuerPubKey: issuerPub })
      expect(r.ok).toBe(false)
      expect(r.unauthenticated).toBe(true)
      expect(r.reason).toMatch(/unauthenticated mint/)
      expect(r.reason).not.toMatch(/signature/i)
    })

    it('verifyEvent REFUSES a lone mint the same way', async () => {
      const r = verifyEvent([await strangerMint(fam)])
      expect(r.ok).toBe(false)
      expect(r.unauthenticated).toBe(true)
      expect(r.reason).toMatch(/unauthenticated mint/)
    })

    it('a mint WITH the commit + settle that spend it is accepted (funded and unfunded)', async () => {
      for (const spec of [{}, { commit1: UNFUNDED, settle1: UNFUNDED }]) {
        const txs = await buildChain(fam, spec, 3)
        const r = verifyEvents(txs, { trustedIssuerPubKey: issuerPub })
        expect(r.ok).toBe(true)
        expect(r.unauthenticated).toBeUndefined()
        expect(verifyEvent(txs).ok).toBe(true)
      }
    })

    it('in a batch, EVERY mint needs a spending commit: one authenticated + one stray mint is refused', async () => {
      const txs = await buildChain(fam, {}, 3)
      const stray = await strangerMint(fam)
      const r = verifyEvents([...txs, stray])
      expect(r.ok).toBe(false)
      expect(r.unauthenticated).toBe(true)
    })

    it('a commit that does not spend the mint does not authenticate it', async () => {
      const honest = await buildChain(fam, {}, 3) // the issuer's mint + its commit + settle
      // the stranger's mint rides with the honest commit + settle, which spend the HONEST mint, not this one
      const r = verifyEvents([await strangerMint(fam), honest[1], honest[2]])
      expect(r.ok).toBe(false)
      expect(r.unauthenticated).toBe(true)
    })
  })
}

// The scanner must also EXECUTE the commit: a forged commit (the stranger signs it with their own key, since they
// lack the issuer key) spends the mint and is structurally perfect, but the covenant's issuer guard refuses it.
async function forgedPackage(fam: Family): Promise<Transaction[]> {
  const mint = await strangerMint(fam)
  const txs = [mint]
  txs.push(await spendToken({
    fam, txs, from: { tx: 0, vout: 0 }, actor: attackerKey, beneficiary: aPkh, fund: { tx: 0, vout: 1 }, change: true, fundKey: attackerKey,
    outputs: [fam.lock(aPkh, aPkh, [0x21], buildOutpoint(mint, 0), ZERO36), p2pb(aPkh)],
  }))
  txs.push(await spendToken({
    fam, txs, from: { tx: 1, vout: 0 }, actor: attackerKey, beneficiary: aPkh, fund: { tx: 1, vout: 2 }, change: true, fundKey: attackerKey,
    outputs: [fam.lock(aPkh, ZERO20, [0x00], buildOutpoint(txs[1], 0), buildOutpoint(mint, 0))],
  }))
  return txs
}

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`${type}: the scanner executes the commit, so a forged commit does not authenticate the mint`, () => {
    it("a stranger's mint + forged commit + settle is structurally perfect but REFUSED on execution", async () => {
      const txs = await forgedPackage(fam)
      expect(verifyChain(txs).ok).toBe(false) // the covenant (issuer guard) refuses the commit
      expect(verifyChain(txs).failedTx).toBe(1)
      const r = verifyEvents(txs, { trustedIssuerPubKey: issuerPub })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/script execution failed/)
      expect(r.reason).toMatch(/input 0/)
      expect(verifyEvent(txs).ok).toBe(false)
    })

    it('the honest package executes clean (funded and unfunded) and reports nothing unexecuted', async () => {
      for (const spec of [{}, { commit1: UNFUNDED, settle1: UNFUNDED }]) {
        const r = verifyEvents(await buildChain(fam, spec, 3), { trustedIssuerPubKey: issuerPub })
        expect(r.ok, r.reason).toBe(true)
        expect(r.unexecutedInputs).toBeUndefined()
      }
    })

    it('a tampered signed settle is refused on execution (not merely structurally)', async () => {
      const txs = await buildChain(fam, {}, 3)
      const chunks = [...txs[2].inputs[0].unlockingScript!.chunks]
      const i = chunks.findIndex((c) => c.data?.length === 33) // the owner pubkey push
      chunks[i] = { ...chunks[i], data: chunks[i].data!.map((b, k) => (k === 5 ? b ^ 1 : b)) }
      txs[2].inputs[0].unlockingScript = new UnlockingScript(chunks)
      const r = verifyEvents(txs)
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/script execution failed/)
    })

    it('a package missing the commit source is refused (fail-closed): every token input of an accepted event is executed', async () => {
      const txs = await buildChain(fam, {}, 3)
      // as received off the wire: hex only (no attached source txs), the commit WITHOUT the mint it spends
      const r = verifyEvent([txs[1].toHex(), txs[2].toHex()])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/token input @0 \(got external\)/)
    })
  })
}

describe('SimpleMultiBOLT: a mint alone is unauthenticated too', () => {
  const MASK64 = (1n << 64n) - 1n
  const bal = (amount: bigint): number[] => {
    const b = Buffer.alloc(16)
    b.writeBigUInt64LE(amount & MASK64, 0)
    b.writeBigUInt64LE((amount >> 64n) & MASK64, 8)
    return Array.from(b)
  }
  const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const pub = key.toPublicKey().encode(true) as number[]
  const child = (n: string) => key.deriveChild(key.toPublicKey(), n)
  const src = () => new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(pub)) }])

  it('a lone SMB mint is refused as unauthenticated', async () => {
    const t = await new SimpleMultiBOLT().mint(key, src(), '', bal(1000n))
    const r = verifyEvents([t.prevTxs[0]])
    expect(r.ok).toBe(false)
    expect(r.unauthenticated).toBe(true)
  })

  it('an SMB mint with the commit + settle that spend it is accepted', async () => {
    const t = await new SimpleMultiBOLT().mint(key, src(), '', bal(1000n))
    await t.transfer(child('1'))
    expect(verifyEvents(t.prevTxs).ok).toBe(true)
  })
})
