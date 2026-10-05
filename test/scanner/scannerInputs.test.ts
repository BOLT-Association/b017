// What the scanner does with input that is not a transaction at all, with a broadcaster that throws something
// other than an Error, and with a stray mint that only the shared scan can see. These pin the edges the
// verifyEvents.ts helpers (toTx / errText / the shared scan) are responsible for.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { buildChain } from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { verifyEvents, verifyEvent, verifyAndBroadcast } from '../../src/lib/scanner/verifyEvents.js'

const NOT_A_TX = /not a transaction: expected a Transaction, raw tx hex, or BEEF hex \/ bytes/

describe('an element that is not a transaction is refused, never thrown', () => {
  for (const [label, junk] of [['null', null], ['undefined', undefined], ['a number', 42], ['a plain object', {}], ['a boolean', true]] as const) {
    it(`${label} in the batch`, async () => {
      for (const run of [() => verifyEvents([junk as any]), () => verifyEvent([junk as any])]) {
        let r: { ok: boolean; reason?: string } | undefined
        expect(() => { r = run() }).not.toThrow()
        expect(r!.ok).toBe(false)
        expect(r!.reason).toMatch(NOT_A_TX)
      }
      const sent: unknown[] = []
      const r = await verifyAndBroadcast([junk as any], async (tx) => { sent.push(tx); return { status: 'accepted' } })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(NOT_A_TX)
      expect(sent).toEqual([])
    })
  }

  it('junk next to real txs refuses the whole batch', async () => {
    const txs = await buildChain(minSimple, {}, 3)
    const r = verifyEvents([...txs, null as any])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(NOT_A_TX)
  })

  it('raw bytes that are not a tx are a parse failure, with the parser message on one line', () => {
    const r = verifyEvents([Uint8Array.from([1, 2, 3])])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/^malformed transaction hex: /)
    expect(r.reason).not.toContain('\n')
  })
})

describe('a broadcaster that throws something other than an Error still fails closed', () => {
  for (const [label, thrown, want] of [['a string', 'node unreachable', /broadcast failed: node unreachable/], ['a number', 503, /broadcast failed: 503/], ['undefined', undefined, /broadcast failed: undefined/]] as const) {
    it(`throws ${label}`, async () => {
      const txs = await buildChain(minSimple, {}, 5)
      const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], async () => { throw thrown })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(want)
      expect(r.anchors![0].status).toBe('rejected')
    })
  }

  it('a multi-line error is reported by its first line only', async () => {
    const txs = await buildChain(minSimple, {}, 5)
    const r = await verifyAndBroadcast([txs[2], txs[3], txs[4]], async () => { throw new Error('rejected by policy\nstack frame 1\nstack frame 2') })
    expect(r.reason).toMatch(/broadcast failed: rejected by policy$/)
  })
})

describe('verifyEvent passes on `unauthenticated` when only the shared scan can see the stray mint', () => {
  it('a melt of a bare mint, the mint only attached: verifyEvent itself sees no mint; the scan pulls it in', async () => {
    const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
    const bal = (n: bigint) => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n, 0); return Array.from(b) }
    const src = new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(key.toPublicKey().encode(true) as number[])) }])
    const t = await new SimpleMultiBOLT().mint(key, src, '', bal(1000n))
    const melt = (await t.melt()).tx!
    const r = verifyEvent([melt], { expectedType: 'SimpleMultiBOLT' })
    expect(r.ok).toBe(false)
    expect(r.unauthenticated).toBe(true)
    expect(r.reason).toMatch(/unauthenticated mint/)
  })
})
