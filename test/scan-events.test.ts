// A3 — token events: verifyEvent + verifyTokenChain over REAL SimpleMultiBOLT split / merge / melt
// chains (the first time the scanner sees the fungible lifecycle). Exercises the fingerprint-every-
// interface arrangement for the shapes the old scanner couldn't model: split settle = 2 token
// outputs, split commit = 2 p2p proofs, merge commit = 2 token inputs, merge settle = 2 proof
// inputs, melt = a token input with no token output. Chains are built live (same as no-elas).
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Script, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../src/tokens/MultiBOLT.js'
import { verifyEvent, verifyTokenChain } from '../src/scan/verifyTokenChain.js'

const MASK64 = (1n << 64n) - 1n
const bal = (amount: bigint): number[] => {
  const x = amount & ((1n << 128n) - 1n)
  const b = Buffer.alloc(16)
  b.writeBigUInt64LE(x & MASK64, 0)
  b.writeBigUInt64LE((x >> 64n) & MASK64, 8)
  return Array.from(b)
}
const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const SIM = BigInt('0x1ffffffffffffe')
const freshSource = () =>
  new Transaction(1, [], [{
    satoshis: 1000, change: true,
    lockingScript: new P2PKH().lock(Hash.hash160(issuerKey.toPublicKey().encode(true))),
  }])
const child = (n: string) => issuerKey.deriveChild(issuerKey.toPublicKey(), n)
const T = 'SimpleMultiBOLT' as const

describe('A3 — token events over the SimpleMultiBOLT lifecycle', () => {
  it('split: verifyEvent recognises the split commit/settle (2 token outputs)', async () => {
    let t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
    t = await t.transfer(child('1'))
    const [main] = await t.split(child('10'), child('11'), bal(1n))
    const chain = main.prevTxs                       // mint, c, s, splitC, splitS
    const splitC = chain[chain.length - 2], splitS = chain[chain.length - 1]
    const ev = verifyEvent([splitC, splitS], { expectedType: T })
    expect(ev.ok, ev.reason).toBe(true)
    expect(ev.kind).toBe('split')
    const r = verifyTokenChain(chain, { expectedType: T })
    expect(r.ok, r.reason).toBe(true)
  })

  it('merge: verifyEvent recognises the merge commit/settle (2 token inputs)', async () => {
    let a = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
    let b = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(1n))
    a = await a.transfer(child('1'))
    b = await b.transfer(child('2'))
    const merged = await a.merge(b, child('400'))
    const chain = merged.prevTxs
    const mergeC = chain[chain.length - 2], mergeS = chain[chain.length - 1]
    const ev = verifyEvent([mergeC, mergeS], { expectedType: T })
    expect(ev.ok, ev.reason).toBe(true)
    expect(ev.kind).toBe('merge')

    const melted = await merged.melt()
    const mev = verifyEvent([melted.tx!], { expectedType: T })
    expect(mev.ok, mev.reason).toBe(true)
    expect(mev.kind).toBe('melt')
  })

  it('mint: verifyEvent recognises a genesis mint', async () => {
    const t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
    const ev = verifyEvent([t.tx!], { expectedType: T })
    expect(ev.ok, ev.reason).toBe(true)
    expect(ev.kind).toBe('mint')
  })

  it('rejects a tampered split settle (an unrecognised extra output)', async () => {
    let t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
    t = await t.transfer(child('1'))
    const [main] = await t.split(child('10'), child('11'), bal(1n))
    const chain = main.prevTxs
    const splitC = chain[chain.length - 2], splitS = chain[chain.length - 1]
    const bad = Transaction.fromHex(splitS.toHex())
    bad.inputs.forEach((inp, i) => { inp.sourceTransaction = splitS.inputs[i].sourceTransaction })
    bad.addOutput({ satoshis: 1, lockingScript: Script.fromHex('006a') }) // not token/p2p/p2pkh -> "other"
    const ev = verifyEvent([splitC, bad], { expectedType: T })
    expect(ev.ok).toBe(false)
    expect(ev.reason).toMatch(/uninspected output/)
  })
})
