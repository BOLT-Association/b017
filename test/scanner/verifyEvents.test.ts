// C2/C3 — verifyEvents: issuerPubKey verification + commit/settle event pairing.
import { describe, it, expect } from 'vitest'
import { P2PKH, Script, Transaction } from '@bsv/sdk'
import { verifyEvents, verifyEvent } from '../../src/lib/scanner/verifyEvents.js'
import Pay2ProofTemplate from '../../src/tokens/templates/pay2Proof.js'
import { appendOutput, assertOutputAdded } from '../helpers/counterfeit.js'
import { readFixtureJSON } from '../helpers/fixtures.js'

const golden = (name: string): string[] =>
  readFixtureJSON(`${name}.lifecycle.golden.json`).txs.map((t: any) => t.hex)

describe('C2/C3 — verifyEvents: issuer + commit/settle event pairing', () => {
  const discount = golden('MinSimpleDiscountBolt')
  const balance = golden('MinSimpleBalanceBolt')

  it('accepts a genuine discount lifecycle (mint -> commit -> settle)', () => {
    const r = verifyEvents(discount)
    expect(r.ok).toBe(true)
    expect(r.type).toBe('MinSimpleDiscountBOLT')
    expect(r.issuerPubKeyHex).toMatch(/^[0-9a-f]{66}$/)
  })

  it('accepts a genuine balance lifecycle', () => {
    expect(verifyEvents(balance).ok).toBe(true)
  })

  it('accepts a lone genesis mint as a single-tx event', () => {
    const r = verifyEvents([discount[0]])
    expect(r.ok, r.reason).toBe(true)
    expect(r.events).toEqual([{ kind: 'mint', txids: [expect.any(String)] }])
  })

  it('C2: accepts a matching trusted issuer; rejects a wrong one', () => {
    const issuer = verifyEvents(discount).issuerPubKeyHex!
    expect(verifyEvents(discount, { trustedIssuerPubKey: issuer }).ok).toBe(true)
    const r = verifyEvents(discount, { trustedIssuerPubKey: '02' + '00'.repeat(32) })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/trusted/)
  })

  it('C3: rejects a batch with an orphan settle (mint + settle only)', () => {
    const r = verifyEvents([discount[0], discount[2]])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/commit/)
  })

  it('C3: rejects an unsettled commit (mint + commit, no settle)', () => {
    const r = verifyEvents([discount[0], discount[1]])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/unsettled commit/)
  })

  it('rejects a wrong expectedType', () => {
    expect(verifyEvents(discount, { expectedType: 'MinSimpleBalanceBOLT' }).ok).toBe(false)
  })
})

describe('C4 — verifyEvents: full input/output arrangement', () => {
  const discount = golden('MinSimpleDiscountBolt')

  it('accepts the genuine lifecycle (every input + output classified, shapes match)', () => {
    expect(verifyEvents(discount).ok).toBe(true)
  })

  it('rejects an uninspected output — settle tampered with an extra OP_RETURN', () => {
    // The settle is the last tx (unreferenced), so appending an output keeps the lineage link intact
    // (its token vout0 + parentOutpoint are unchanged) but adds an unclassifiable output. Built by raw-hex
    // byte surgery (NOT outputs.push+toHex — @bsv/sdk 2.x drops a mutate-after-parse output).
    const tampered = appendOutput(discount[2], Script.fromASM('OP_RETURN 6e6f').toHex())
    assertOutputAdded(discount[2], tampered)
    const r = verifyEvents([discount[0], discount[1], tampered])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/uninspected output/)
  })

  it('rejects a counterfeit token output appended to the settle (wrong static code, right push shape)', () => {
    // A push-shaped MinSimpleDiscountBolt layout [1,20,20,1,36,36,33] but a bogus 1-op suffix -> not a
    // genuine contract -> classified "other" -> rejected (recognizeType catches what a push-count check can't).
    const push = (n: number) => n.toString(16).padStart(2, '0') + '02'.repeat(n)
    const forgedHex = [1, 20, 20, 1, 36, 36, 33].map(push).join('') + '51' // ...+ OP_1 bogus suffix
    const tampered = appendOutput(discount[2], forgedHex, 1)
    assertOutputAdded(discount[2], tampered)
    const r = verifyEvents([discount[0], discount[1], tampered])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/uninspected output/)
  })

  it('rejects a settle carrying an unexpected p2Proof output in the change region', () => {
    // settle shape is [token, change(p2pkh)]; appending a genuine p2Proof gives [token, p2pkh, p2p],
    // and a p2p where a change p2pkh is expected is rejected.
    const p2pHex = new Pay2ProofTemplate().lock(new Array(20).fill(0x11)).toHex()
    const tampered = appendOutput(discount[2], p2pHex, 1)
    assertOutputAdded(discount[2], tampered)
    const r = verifyEvent([discount[0], discount[1], tampered])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/change p2pkh/)
  })
})

describe('hardening — verifyEvents / verifyEvent fail closed on bad input', () => {
  const discount = golden('MinSimpleDiscountBolt')

  it('rejects a non-array input instead of throwing', () => {
    expect(verifyEvents(undefined as any).ok).toBe(false)
    expect(verifyEvent(null as any).ok).toBe(false)
  })

  it('rejects an empty batch / empty event', () => {
    expect(verifyEvents([]).reason).toMatch(/empty batch/)
    expect(verifyEvent([]).reason).toMatch(/empty event/)
  })

  it('rejects malformed transaction hex with a descriptive reason (no throw)', () => {
    const r = verifyEvents(['not-hex-at-all'])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/malformed transaction hex|unparseable/)
  })

  it('rejects a well-formed tx that carries no BOLT token output', () => {
    const emptyTx = '01000000' + '00' + '00' + '00000000' // version + 0 inputs + 0 outputs + locktime
    const r = verifyEvents([emptyTx])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/no BOLT token output recognised/)
  })

  it('verifyEvent accepts a genuine event and reports its kind', () => {
    const r = verifyEvent(discount)
    expect(r.ok, r.reason).toBe(true)
    expect(r.kind).toBe('transfer')
  })

  it('verifyEvent: empty + unrecognised + expectedType-mismatch all fail closed', () => {
    expect(verifyEvent([]).reason).toMatch(/empty event/)
    expect(verifyEvent(['not-hex']).ok).toBe(false)
    const r = verifyEvent(discount, { expectedType: 'MinSimpleBalanceBOLT' })
    expect(r.ok).toBe(false)
  })

  it('verifyEvent: a lone genesis mint is a valid single-tx event', () => {
    const r = verifyEvent([discount[0]])
    expect(r.ok, r.reason).toBe(true)
    expect(r.kind).toBe('mint')
  })

  it('verifyEvents: rejects a wrong expectedType up front', () => {
    expect(verifyEvents(discount, { expectedType: 'SimpleMultiBOLT' }).ok).toBe(false)
  })

  it('verifyEvents: rejects mixed token types in one batch', () => {
    const balance = golden('MinSimpleBalanceBolt')
    const r = verifyEvents([discount[0], balance[0]])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/mixed token types/)
  })

  it('verifyEvents: accepts a trusted issuer supplied as raw bytes (number[])', () => {
    const hexIssuer = verifyEvents(discount).issuerPubKeyHex!
    const bytes = hexIssuer.match(/../g)!.map((h) => parseInt(h, 16)) // number[] form
    expect(verifyEvents(discount, { trustedIssuerPubKey: bytes }).ok).toBe(true)
  })

  it('verifyEvent / verifyEvents: a non-token tx alongside a token is rejected', () => {
    const emptyTx = '01000000' + '00' + '00' + '00000000'
    expect(verifyEvent([discount[0], emptyTx]).ok).toBe(false)
    const r = verifyEvents([discount[0], emptyTx])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/not a BOLT token tx/)
  })
})

// Synthetic arrangement-failure cases — txs assembled from genuine golden locks but with a
// deliberately wrong interface layout, to drive each checkArrangement rejection branch. (The scanner
// classifies interfaces; it does not run scripts, so unsigned synthetic inputs are fine here.)
describe('verifyEvent — interface arrangement is rejected when malformed', () => {
  const discount = golden('MinSimpleDiscountBolt')
  const mintToken = Transaction.fromHex(discount[0]).outputs[0].lockingScript   // txoType 00 -> mint shape
  const commitToken = Transaction.fromHex(discount[1]).outputs[0].lockingScript // txoType 21 -> commit shape
  const p2pLock = new Pay2ProofTemplate().lock(new Array(20).fill(0x11))
  const p2pkhLock = new P2PKH().lock(new Array(20).fill(0x22))
  const otherLock = Script.fromHex('006a') // OP_0 OP_RETURN -> "other"
  const out = (lock: Script) => ({ satoshis: 1, lockingScript: lock })
  const srcOf = (lock: Script) => new Transaction(1, [], [out(lock)])
  const inp = (src: Transaction): any =>
    ({ sourceTransaction: src, sourceOutputIndex: 0, unlockingScript: new Script([]), sequence: 0xffffffff })

  it('token output not at the expected position', () => {
    const tx = new Transaction(1, [], [out(p2pkhLock), out(mintToken)]) // token at vout1, not vout0
    expect(verifyEvent([tx]).reason).toMatch(/token output @0/)
  })

  it('a commit missing its p2Proof output', () => {
    const tx = new Transaction(1, [inp(srcOf(mintToken))], [out(commitToken), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/p2p output @1/)
  })

  it('a commit whose first input is not a token', () => {
    const tx = new Transaction(1, [inp(srcOf(p2pkhLock))], [out(commitToken), out(p2pLock), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/token input @0/)
  })

  it('a p2Proof input on a commit (proofs are settle-only)', () => {
    const tx = new Transaction(1, [inp(srcOf(mintToken)), inp(srcOf(p2pLock))],
      [out(commitToken), out(p2pLock), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/p2Proof input is only valid on a settle/)
  })

  it('an uninspected ("other") input', () => {
    const tx = new Transaction(1, [inp(srcOf(mintToken)), inp(srcOf(otherLock))],
      [out(commitToken), out(p2pLock), out(p2pkhLock)])
    expect(verifyEvent([tx]).reason).toMatch(/uninspected input/)
  })
})
