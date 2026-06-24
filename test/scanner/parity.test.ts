// C5 — parity: the scanner's accept/reject decisions match the on-chain BOLT contract's, over a
// fixture set of genuine lineages (sx-generated + verifyTx-validated) and every counterfeit class.
// (Security bar = the EventListener on-chain scan: fingerprint + issuer + lineage + arrangement.
// SPV/BEEF on-chain presence is a composable leg the caller supplies; this validates the structure.)
import { describe, it, expect } from 'vitest'
import { Transaction, Script, P2PKH } from '@bsv/sdk'
import { verifyEvents } from '../../src/lib/scanner/verifyEvents.js'
import { appendOutput } from '../helpers/counterfeit.js'
import { readFixtureJSON } from '../helpers/fixtures.js'

const golden = (name: string): string[] =>
  readFixtureJSON(`${name}.lifecycle.golden.json`).txs.map((t: any) => t.hex)

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
  // (A lone mint is NOT here: a genesis mint is a valid single-tx event, accepted below.)
  const counterfeits: { name: string; chain: string[]; opts?: any }[] = [
    { name: 'wrong issuer', chain: discount, opts: { trustedIssuerPubKey: '02' + '00'.repeat(32) } },
    { name: 'orphan settle (no commit)', chain: [discount[0], discount[2]] },
    { name: 'unsettled commit (no settle)', chain: [discount[0], discount[1]] },
    { name: 'uninspected output (extra OP_RETURN)', chain: tamperedSettle },
    { name: 'counterfeit token output (wrong static code)', chain: counterfeitToken },
    { name: 'plain P2PKH masquerade', chain: p2pkhOnly },
    { name: 'wrong expected type', chain: discount, opts: { expectedType: 'MinSimpleBalanceBOLT' } },
  ]

  it('ACCEPTS every genuine lineage', () => {
    for (const c of genuine) expect(verifyEvents(c).ok).toBe(true)
  })

  it('ACCEPTS a lone genesis mint as a single-tx event', () => {
    expect(verifyEvents([discount[0]]).ok).toBe(true)
  })

  it('REJECTS every counterfeit class', () => {
    for (const { name, chain, opts } of counterfeits) {
      const r = verifyEvents(chain, opts)
      expect(r.ok, `${name} should be rejected (got ok; reason=${r.reason})`).toBe(false)
    }
  })

  it('parity holds: no genuine rejected, no counterfeit accepted', () => {
    expect(genuine.every((c) => verifyEvents(c).ok)).toBe(true)
    expect(counterfeits.every((c) => !verifyEvents(c.chain, c.opts).ok)).toBe(true)
  })
})
