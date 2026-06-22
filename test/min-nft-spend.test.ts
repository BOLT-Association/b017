// B2b — NFT spend/unlock: a live mint -> commit -> settle lifecycle built from the templates, gated
// on verifyTx (the @bsv/sdk Spend engine = the real on-chain validator). Proves the 37-arg unlock
// executes the actual contract and produces VALID spends, across all three NFT-family templates.
// (Golden byte-equality is a scanner / provenance concern, not a spend concern — see scan*.test.ts.)
//
// Two requirements the contract enforces that the builder must honour:
//   1. Tx version >= 2 (asserted from the preimage).
//   2. The UNLOCK_SCRIPT_SUFFIX must be the full 343-op compiled unlock (patched from the artifact by
//      the build scripts) — a truncated suffix corrupts the optimal-sighash (OP_PUSH_TX) s-computation.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Script, Transaction, LockingScript } from '@bsv/sdk'
import { verifyTx, buildOutpoint } from '../src/boltLib.js'
import MinSimpleTemplate from '../src/templates/MinSimpleBolt.sx.template.js'
import MinSimpleDiscountTemplate from '../src/templates/MinSimpleDiscountBolt.sx.template.js'
import MinSimpleBalanceTemplate from '../src/templates/MinSimpleBalanceBolt.sx.template.js'

// Non-degenerate keys: privkey=1 would make pubkey == G (X=79be667e…), colliding with the
// contract's r-puzzle magic-sig constant. Use high-entropy scalars instead.
const issuerKey = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
const recipientKey = PrivateKey.fromString('a1b2c3d4e5f60718293a4b5c6d7e8f90112233445566778899aabbccddeeff00', 'hex')
const issuerPub = issuerKey.toPublicKey().encode(true) as number[]
const issuerPkh = Hash.hash160(issuerPub)
const recipientPkh = Hash.hash160(recipientKey.toPublicKey().encode(true) as number[])
const ZERO20 = new Array(20).fill(0x00)
const ZERO36 = new Array(36).fill(0x00)
const hex = (a: number[]) => Buffer.from(a).toString('hex')
const p2pb = (pkh: number[]) => Script.fromHex('02b0178876a914' + hex(pkh) + '88ac')

function assertValid(label: string, tx: Transaction) {
  tx.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
  const { valid, scriptExecutions } = verifyTx(tx, true)
  if (!valid) console.log(`${label}: input ${scriptExecutions.findIndex((e) => !e.valid)} failed`)
  expect(valid, label).toBe(true)
}

// A NFT template + the per-token lock builder (each contract's lock() leads with its own value field).
type Token = (owner: number[], commitment: number[], txoType: number[], parent: number[], gp: number[]) => LockingScript
interface NftCase { name: string; tpl: any; lock: Token }

const discount = [0x0a]
const balance = [...new Array(15).fill(0x00), 0x07] // 16-byte LE-ish immutable balance
const cases: NftCase[] = [
  {
    name: 'MinSimpleBolt (identity)',
    tpl: new MinSimpleTemplate(),
    lock: (o, c, t, p, g) => new MinSimpleTemplate().lock(o, issuerPub, c, t, p, g),
  },
  {
    name: 'MinSimpleDiscountBolt (1B discount)',
    tpl: new MinSimpleDiscountTemplate(),
    lock: (o, c, t, p, g) => new MinSimpleDiscountTemplate().lock(discount, o, issuerPub, c, t, p, g),
  },
  {
    name: 'MinSimpleBalanceBolt (16B balance)',
    tpl: new MinSimpleBalanceTemplate(),
    lock: (o, c, t, p, g) => new MinSimpleBalanceTemplate().lock(balance, o, issuerPub, c, t, p, g),
  },
]

describe('B2b — NFT mint -> commit -> settle verifies on the bsv Spend engine', () => {
  for (const { name, tpl, lock } of cases) {
    it(`${name}: full lifecycle (commit + settle) passes verifyTx`, async () => {
      const funding = new Transaction(1, [], [{ satoshis: 2000, lockingScript: new P2PKH().lock(issuerPkh) }])

      // MINT (genesis): funding -> token (txoType 00) + change. Bolt not spent here. version >= 2.
      const mint = new Transaction()
      mint.version = 2
      mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
      mint.addOutput({ satoshis: 1, lockingScript: lock(issuerPkh, ZERO20, [0x00], ZERO36, ZERO36) })
      mint.addOutput({ satoshis: 1000, lockingScript: new P2PKH().lock(issuerPkh) })
      await mint.sign()
      assertValid(`${name} mint`, mint)

      // COMMIT: spend mint token -> token(txoType 21, commitment=recipient, parent=mint.0) + p2pb + change.
      const commit = new Transaction()
      commit.version = 2
      commit.addInput({ sourceTransaction: mint, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(issuerKey, recipientPkh, [mint]), sequence: 0xffffffff })
      commit.addInput({ sourceTransaction: mint, sourceOutputIndex: 1, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
      commit.addOutput({ satoshis: 1, lockingScript: lock(issuerPkh, recipientPkh, [0x21], buildOutpoint(mint, 0), ZERO36) })
      commit.addOutput({ satoshis: 1, lockingScript: p2pb(recipientPkh) })
      commit.addOutput({ satoshis: 990, lockingScript: new P2PKH().lock(issuerPkh) })
      await commit.sign()
      assertValid(`${name} commit`, commit)

      // SETTLE: spend commit token -> token(txoType 00, owner=recipient, parent=commit.0, gp=mint.0) + change.
      const settle = new Transaction()
      settle.version = 2
      settle.addInput({ sourceTransaction: commit, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(issuerKey, recipientPkh, [mint, commit]), sequence: 0xffffffff })
      settle.addInput({ sourceTransaction: commit, sourceOutputIndex: 2, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff })
      settle.addOutput({ satoshis: 1, lockingScript: lock(recipientPkh, ZERO20, [0x00], buildOutpoint(commit, 0), buildOutpoint(mint, 0)) })
      settle.addOutput({ satoshis: 980, lockingScript: new P2PKH().lock(recipientPkh) })
      await settle.sign()
      assertValid(`${name} settle`, settle)
    })
  }
})
