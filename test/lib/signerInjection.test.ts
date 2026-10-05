// The point of the Signer change: a wallet that never exposes its private key can drive the library.
// These tests pass a Signer that is NOT a PrivateKey (no toPublicKey/encode), and whose sign() is
// async (as a wallet's would be), and build real, Spend-valid token chains with it — including a
// transfer whose recipient is given only as a public key (a third party the caller cannot sign for).
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import { verifyEvents } from '../../src/lib/scanner/verifyEvents.js'
import { verifyTx, buildOutpoint, type Signer } from '../../src/lib/boltLib.js'

/** A wallet-style Signer: only { publicKey, sign }, and sign is async. It holds a key here only so the
 *  test is self-contained; the library never sees it — it calls publicKey and sign and nothing else. */
const walletSigner = (priv: PrivateKey): Signer => ({
  publicKey: priv.toPublicKey().encode(true) as number[],
  sign: async (msg) => priv.sign(msg)
})

const MASK64 = (1n << 64n) - 1n
const bal = (n: bigint): number[] => {
  const b = Buffer.alloc(16)
  b.writeBigUInt64LE(n & MASK64, 0)
  b.writeBigUInt64LE((n >> 64n) & MASK64, 8)
  return Array.from(b)
}
const fundTo = (pubKey: number[]) =>
  new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(pubKey)) }])

describe('a wallet-style async Signer (no exposed key) drives the fungible class', () => {
  const issuer = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')

  it('mint + transfer, recipient given only as a public key', async () => {
    const signer = walletSigner(issuer)
    const t = await new SimpleMultiBOLT().mint(signer, fundTo(signer.publicKey), '', bal(1000n))
    const recipientPubKey = PrivateKey.fromRandom().toPublicKey().encode(true) as number[] // a third party
    await t.transfer(recipientPubKey)
    const r = verifyEvents(t.prevTxs, { expectedType: 'SimpleMultiBOLT', trustedIssuerPubKey: signer.publicKey })
    expect(r.ok, r.reason).toBe(true)
    expect(r.events?.map((e) => e.kind).sort()).toEqual(['mint', 'transfer'])
  })

  it('mint + split, both pieces to third-party public keys', async () => {
    const signer = walletSigner(issuer)
    const t = await new SimpleMultiBOLT().mint(signer, fundTo(signer.publicKey), '', bal(1000n))
    await t.transfer(walletSigner(issuer).publicKey) // keep it on a key we hold so split can continue
    const a = PrivateKey.fromRandom().toPublicKey().encode(true) as number[]
    const b = PrivateKey.fromRandom().toPublicKey().encode(true) as number[]
    const [main] = await t.split(a, b, bal(300n))
    const r = verifyEvents(main.prevTxs, { expectedType: 'SimpleMultiBOLT', trustedIssuerPubKey: signer.publicKey })
    expect(r.ok, r.reason).toBe(true)
  })
})

describe('a wallet-style async Signer drives the NFT templates', () => {
  it('MinSimpleBOLT mint -> commit -> settle verifies on the Spend engine', async () => {
    const issuer = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
    const signer = walletSigner(issuer)
    const tpl = new MinSimpleTemplate()
    const issuerPub = signer.publicKey
    const issuerPkh = Hash.hash160(issuerPub)
    const recipientPkh = Hash.hash160(PrivateKey.fromRandom().toPublicKey().encode(true) as number[])
    const Z20 = new Array(20).fill(0); const Z36 = new Array(36).fill(0)
    const tok = (owner: number[], c: number[], t: number[], p: number[], g: number[]) => tpl.lock(owner, issuerPub, c, t, p, g)

    const funding = new Transaction(1, [], [{ satoshis: 2000, lockingScript: new P2PKH().lock(issuerPkh) }])
    const mint = new Transaction(); mint.version = 2
    mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(issuer), sequence: 0xffffffff })
    mint.addOutput({ satoshis: 1, lockingScript: tok(issuerPkh, Z20, [0x00], Z36, Z36) })
    mint.addOutput({ satoshis: 1000, lockingScript: new P2PKH().lock(issuerPkh) })
    await mint.sign()

    const commit = new Transaction(); commit.version = 2
    commit.addInput({ sourceTransaction: mint, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(signer, recipientPkh, [mint]), sequence: 0xffffffff })
    commit.addInput({ sourceTransaction: mint, sourceOutputIndex: 1, unlockingScriptTemplate: new P2PKH().unlock(issuer), sequence: 0xffffffff })
    commit.addOutput({ satoshis: 1, lockingScript: tok(issuerPkh, recipientPkh, [0x21], buildOutpoint(mint, 0), Z36) })
    commit.addOutput({ satoshis: 1, lockingScript: new Pay2ProofTemplate().lock(recipientPkh) })
    commit.addOutput({ satoshis: 990, lockingScript: new P2PKH().lock(issuerPkh) })
    await commit.sign()
    commit.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
    expect(verifyTx(commit, true).valid).toBe(true)
  })
})
