// Targeted branch coverage for the exported helpers' defensive paths (the `?? default` / `|| 0`
// guards and the error throws) that the happy-path lifecycle suites don't exercise.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Script, Transaction } from '@bsv/sdk'
import {
  verifyTx, vinSequence, outputValue, outputScript, spentOutpoint, le32, le64, buildOutpoint,
} from '../../src/lib/boltLib.js'
import { ancestorPiece as singleAncestorPiece, singleAncestorPieces } from '../../src/lib/single/singleAncestor.js'
import { singleSpendUnlock } from '../../src/lib/single/singleSpend.js'
import { issuerPubKeyOf } from '../../src/lib/scanner/fingerprints.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'

const key = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
const pkh = Hash.hash160(key.toPublicKey().encode(true))

describe('boltLib — default-value branches', () => {
  it('vinSequence falls back to 0xffffffff when an input has no sequence', () => {
    const tx = new Transaction(1, [{ sourceTXID: '11'.repeat(32), sourceOutputIndex: 0 } as any], [])
    expect(vinSequence(tx, 0)).toEqual(le32(0xffffffff))
  })

  it('outputValue defaults to 0 when satoshis is absent', () => {
    const tx = new Transaction(1, [], [{ lockingScript: new Script([]) } as any])
    expect(outputValue(tx, 0)).toEqual(le64(0))
    expect(outputScript(tx, 0)).toEqual([])
  })

  it('spentOutpoint reads the attached source transaction (hash branch)', () => {
    const funding = new Transaction(1, [], [{ satoshis: 1, lockingScript: new P2PKH().lock(pkh) }])
    const tx = new Transaction(1, [{ sourceTransaction: funding, sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    expect(spentOutpoint(tx, 0).length).toBe(36)
  })

  it('verifyTx throws when outputs exceed inputs and the check is on', async () => {
    const funding = new Transaction(1, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(pkh) }])
    const spend = new Transaction(1,
      [{ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(key), sequence: 0xffffffff }],
      [{ satoshis: 5000, lockingScript: new P2PKH().lock(pkh) }]) // 5000 > 1000
    await spend.sign()
    spend.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
    expect(() => verifyTx(spend)).toThrow(/greater than input/)
  })
})

describe('fingerprints — issuerPubKeyOf guard', () => {
  it('returns [] when the issuer chunk carries no data', () => {
    expect(issuerPubKeyOf(new Script([{ op: 0x51 }]), 'MinSimpleBOLT')).toEqual([])
  })
})

describe('singleAncestor — leadingValuePushes + edge branches', () => {
  // A synthetic ancestor tx: in[0] unlock has < 35 chunks (so chunk[34] is absent), inputs lack a
  // sequence, three outputs present. Exercises the `?? []`, `?? 0xffffffff`, and default branches.
  const synth = new Transaction(1,
    [
      { sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, unlockingScript: new Script([{ op: 0x51 }]) } as any,
      { sourceTXID: '22'.repeat(32), sourceOutputIndex: 0, unlockingScript: new Script([{ op: 0x51 }]) } as any,
    ],
    [
      { satoshis: 1, lockingScript: new Script([]) },
      { satoshis: 1, lockingScript: new Script([]) },
      { satoshis: 1, lockingScript: new Script([]) },
    ])

  it('unknown piece name returns []', () => {
    expect(singleAncestorPiece('NoSuchPiece', synth, 0)).toEqual([])
  })

  it('nSequence pieces fall back to 0xffffffff', () => {
    expect(singleAncestorPiece('Vin1NSequence', synth, 0)).toEqual(le32(0xffffffff))
    expect(singleAncestorPiece('Vin2NSequence', synth, 0)).toEqual(le32(0xffffffff))
  })

  it('a spent-lock script-code field with no chunk yields []', () => {
    expect(singleAncestorPiece('Vin1CTXScriptCodePubKeyHash', synth, 0)).toEqual([])
  })

  it('singleAncestorPieces returns all 26 pieces for both leadingValuePushes values', () => {
    expect(singleAncestorPieces(synth, 0).length).toBe(26)
    expect(singleAncestorPieces(synth, 1).length).toBe(26)
  })
})

describe('singleSpendUnlock — guards + flag branches (direct)', () => {
  const base = { privateKey: key, beneficiaryPubKeyHash: pkh, unlockScriptSuffixASM: 'OP_1' }
  const oneInput = (withSource: boolean, sats?: number) => {
    const funding = new Transaction(1, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(pkh) }])
    const input: any = withSource
      ? { sourceTransaction: funding, sourceOutputIndex: 0, sequence: 0xffffffff }
      : { sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, sequence: 0xffffffff }
    return new Transaction(1, [input], [{ satoshis: sats ?? 1, lockingScript: new P2PKH().lock(pkh) }])
  }

  it('throws when sourceTXID/sourceTransaction is missing', async () => {
    const tx = new Transaction(1, [{ sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    await expect(singleSpendUnlock(base).sign(tx, 0)).rejects.toThrow(/sourceTXID/)
  })

  it('throws when sourceSatoshis is unresolved', async () => {
    await expect(singleSpendUnlock(base).sign(oneInput(false), 0)).rejects.toThrow(/sourceSatoshis/)
  })

  it('throws when lockingScript is unresolved', async () => {
    await expect(singleSpendUnlock({ ...base, sourceSatoshis: 1000 }).sign(oneInput(false), 0)).rejects.toThrow(/lockingScript/)
  })

  it('signs the no-ancestor path (no prevTxs) and honours forceNoFund/forceNoChange', async () => {
    const withFund = await singleSpendUnlock(base).sign(oneInput(true), 0)
    expect(withFund.chunks.length).toBeGreaterThan(0)
    const noFund = await singleSpendUnlock({ ...base, forceNoFund: true, forceNoChange: true }).sign(oneInput(true), 0)
    expect(noFund.chunks.length).toBeGreaterThan(0)
  })

  it('drives the back-reaching ancestor path (hasAncestor) with a real commit in prevTxs', async () => {
    // Build a genuine mint -> commit so prevTxs[1] is a real 37-arg-unlock commit, then sign a settle
    // with a length-4 prevTxs so hasAncestor = true and singleAncestorPieces reconstructs the commit.
    const issuer = key
    const issuerPub = issuer.toPublicKey().encode(true) as number[]
    const issuerPkh = Hash.hash160(issuerPub)
    const tpl = new MinSimpleTemplate()
    const lock = (o: number[], c: number[], t: number[], p: number[], g: number[]) => tpl.lock(o, issuerPub, c, t, p, g)
    const Z20 = new Array(20).fill(0), Z36 = new Array(36).fill(0)

    const funding = new Transaction(1, [], [{ satoshis: 2000, lockingScript: new P2PKH().lock(issuerPkh) }])
    const mint = new Transaction()
    mint.version = 2
    mint.addInput({ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(issuer), sequence: 0xffffffff })
    mint.addOutput({ satoshis: 1, lockingScript: lock(issuerPkh, Z20, [0x00], Z36, Z36) })
    mint.addOutput({ satoshis: 1000, lockingScript: new P2PKH().lock(issuerPkh) })
    await mint.sign()

    const commit = new Transaction()
    commit.version = 2
    commit.addInput({ sourceTransaction: mint, sourceOutputIndex: 0, unlockingScriptTemplate: tpl.unlock(issuer, pkh, [mint]), sequence: 0xffffffff })
    commit.addInput({ sourceTransaction: mint, sourceOutputIndex: 1, unlockingScriptTemplate: new P2PKH().unlock(issuer), sequence: 0xffffffff })
    commit.addOutput({ satoshis: 1, lockingScript: lock(issuerPkh, pkh, [0x21], buildOutpoint(mint, 0), Z36) })
    commit.addOutput({ satoshis: 1, lockingScript: new Pay2ProofTemplate().lock(pkh) })
    commit.addOutput({ satoshis: 990, lockingScript: new P2PKH().lock(issuerPkh) })
    await commit.sign()

    // A settle-shaped spend of the commit token, signed with a length-4 prevTxs -> hasAncestor true.
    const settle = new Transaction()
    settle.version = 2
    settle.addInput({ sourceTransaction: commit, sourceOutputIndex: 0, sequence: 0xffffffff })
    settle.addInput({ sourceTransaction: commit, sourceOutputIndex: 2, sequence: 0xffffffff })
    settle.addOutput({ satoshis: 1, lockingScript: lock(pkh, Z20, [0x00], buildOutpoint(commit, 0), buildOutpoint(mint, 0)) })
    settle.addOutput({ satoshis: 980, lockingScript: new P2PKH().lock(pkh) })

    const us = await singleSpendUnlock({
      ...base, prevTxs: [mint, commit, mint, commit], // leadingValuePushes omitted -> default 0 branch
    }).sign(settle, 0)
    expect(us.chunks.length).toBeGreaterThan(26) // 26 ancestor chunks + the rest
  })
})
