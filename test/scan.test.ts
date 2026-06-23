// C2/C3 — verifyEvents: issuerPubKey verification + commit/settle event pairing.
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, resolve } from 'node:path'
import { Transaction, Script } from '@bsv/sdk'
import { verifyEvents } from '../src/scan/verifyEvents.js'
import { appendOutput, assertOutputAdded } from './counterfeit.helper.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const golden = (name: string): string[] =>
  JSON.parse(readFileSync(resolve(__dirname, `fixtures/${name}.lifecycle.golden.json`), 'utf8')).txs.map(
    (t: any) => t.hex,
  )

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
})
