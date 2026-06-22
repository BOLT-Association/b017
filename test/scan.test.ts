// C2/C3 — verifyTokenChain: issuerPubKey verification + commit/settle lineage.
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, resolve } from 'node:path'
import { Transaction, Script } from '@bsv/sdk'
import { verifyTokenChain } from '../src/scan/verifyTokenChain.js'
import { appendOutput, assertOutputAdded } from './counterfeit.helper.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const golden = (name: string): string[] =>
  JSON.parse(readFileSync(resolve(__dirname, `fixtures/${name}.lifecycle.golden.json`), 'utf8')).txs.map(
    (t: any) => t.hex,
  )

describe('C2/C3 — verifyTokenChain: issuer + commit/settle lineage', () => {
  const discount = golden('MinSimpleDiscountBolt')
  const balance = golden('MinSimpleBalanceBolt')

  it('accepts a genuine discount lifecycle (mint -> commit -> settle)', () => {
    const r = verifyTokenChain(discount)
    expect(r.ok).toBe(true)
    expect(r.type).toBe('MinSimpleDiscountBOLT')
    expect(r.issuerPubKeyHex).toMatch(/^[0-9a-f]{66}$/)
  })

  it('accepts a genuine balance lifecycle', () => {
    expect(verifyTokenChain(balance).ok).toBe(true)
  })

  it('C2: accepts a matching trusted issuer; rejects a wrong one', () => {
    const issuer = verifyTokenChain(discount).issuerPubKeyHex!
    expect(verifyTokenChain(discount, { trustedIssuerPubKey: issuer }).ok).toBe(true)
    const r = verifyTokenChain(discount, { trustedIssuerPubKey: '02' + '00'.repeat(32) })
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/trusted/)
  })

  it('C3: rejects a chain missing the commit (mint + settle only)', () => {
    const r = verifyTokenChain([discount[0], discount[2]])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/commit/)
  })

  it('C3: rejects a mint-only chain', () => {
    expect(verifyTokenChain([discount[0]]).ok).toBe(false)
  })

  it('rejects a wrong expectedType', () => {
    expect(verifyTokenChain(discount, { expectedType: 'MinSimpleBalanceBOLT' }).ok).toBe(false)
  })
})

describe('C4 — verifyTokenChain: full input/output arrangement', () => {
  const discount = golden('MinSimpleDiscountBolt')

  it('accepts the genuine lifecycle (every input + output classified, shapes match)', () => {
    expect(verifyTokenChain(discount).ok).toBe(true)
  })

  it('rejects an uninspected output — settle tampered with an extra OP_RETURN', () => {
    // The settle is the last tx (unreferenced), so appending an output keeps the lineage link intact
    // (its token vout0 + parentOutpoint are unchanged) but adds an unclassifiable output. Built by raw-hex
    // byte surgery (NOT outputs.push+toHex — @bsv/sdk 2.x drops a mutate-after-parse output).
    const tampered = appendOutput(discount[2], Script.fromASM('OP_RETURN 6e6f').toHex())
    assertOutputAdded(discount[2], tampered)
    const r = verifyTokenChain([discount[0], discount[1], tampered])
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
    const r = verifyTokenChain([discount[0], discount[1], tampered])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/uninspected output/)
  })
})
