// C5 — parity: the scanner's accept/reject decisions match the on-chain BOLT contract's, over a
// fixture set of genuine lineages (sx-generated + verifyTx-validated) and every counterfeit class.
// (Security bar = the EventListener on-chain scan: fingerprint + issuer + lineage + arrangement.
// SPV/BEEF on-chain presence is a composable leg the caller supplies; this validates the structure.)
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, resolve } from 'node:path'
import { Transaction, Script, P2PKH } from '@bsv/sdk'
import { verifyTokenChain } from '../src/scan/verifyTokenChain.js'
import { appendOutput } from './counterfeit.helper.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
const golden = (name: string): string[] =>
  JSON.parse(readFileSync(resolve(__dirname, `fixtures/${name}.lifecycle.golden.json`), 'utf8')).txs.map(
    (t: any) => t.hex,
  )

describe('C5 — parity: scanner accept/reject == on-chain BOLT contract', () => {
  const discount = golden('MinSimpleDiscountBolt')
  const balance = golden('MinSimpleBalanceBolt')

  // Genuine lineages the on-chain contract accepted (sx-generated, verifyTx-validated).
  const genuine: string[][] = [discount, balance]

  // A settle tampered with an extra OP_RETURN (lineage intact: last tx, token vout0 unchanged). Built by
  // raw-hex byte surgery so the extra output survives serialisation on EVERY @bsv/sdk version (2.x drops
  // an output pushed onto a parsed tx's .outputs array — which silently hid this counterfeit before).
  const tamperedSettle = [discount[0], discount[1], appendOutput(discount[2], Script.fromASM('OP_RETURN 6e6f').toHex())]

  // A settle with an appended COUNTERFEIT token output: the MinSimpleDiscountBolt push layout
  // [1,20,20,1,36,36,33] but a bogus suffix -> recognizeType rejects -> classified "other".
  const push = (n: number) => n.toString(16).padStart(2, '0') + '02'.repeat(n)
  const forgedTokenHex = [1, 20, 20, 1, 36, 36, 33].map(push).join('') + '51'
  const counterfeitToken = [discount[0], discount[1], appendOutput(discount[2], forgedTokenHex, 1)]

  const p2pkhOnly = [
    new Transaction(1, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(new Array(20).fill(0x11)) }]).toHex(),
  ]

  // Counterfeit classes — each must be rejected (== the on-chain contract rejecting it).
  const counterfeits: { name: string; chain: string[]; opts?: any }[] = [
    { name: 'wrong issuer', chain: discount, opts: { trustedIssuerPubKey: '02' + '00'.repeat(32) } },
    { name: 'missing commit', chain: [discount[0], discount[2]] },
    { name: 'mint only', chain: [discount[0]] },
    { name: 'uninspected output (extra OP_RETURN)', chain: tamperedSettle },
    { name: 'counterfeit token output (wrong static code)', chain: counterfeitToken },
    { name: 'plain P2PKH masquerade', chain: p2pkhOnly },
    { name: 'wrong expected type', chain: discount, opts: { expectedType: 'MinSimpleBalanceBOLT' } },
  ]

  it('ACCEPTS every genuine lineage', () => {
    for (const c of genuine) expect(verifyTokenChain(c).ok).toBe(true)
  })

  it('REJECTS every counterfeit class', () => {
    for (const { name, chain, opts } of counterfeits) {
      const r = verifyTokenChain(chain, opts)
      expect(r.ok, `${name} should be rejected (got ok; reason=${r.reason})`).toBe(false)
    }
  })

  it('parity holds: no genuine rejected, no counterfeit accepted', () => {
    expect(genuine.every((c) => verifyTokenChain(c).ok)).toBe(true)
    expect(counterfeits.every((c) => !verifyTokenChain(c.chain, c.opts).ok)).toBe(true)
  })
})
