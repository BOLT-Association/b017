// Scanner over the genesis family (FixedBOLT, OpenBOLT, SerialBOLT): two recognition specs per type (mint: null
// field + any mintData; postMint: set field + empty mintData), the asset-lineage batch rule, and real batches
// built by the library.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Script, Transaction } from '@bsv/sdk'
import fs from 'fs'
import path from 'path'
import { recognizeToken, recognizeType, REGISTRY } from '../../src/lib/scanner/fingerprints.js'
import { verifyEvent, verifyEvents } from '../../src/lib/scanner/verifyEvents.js'
import { FixedBOLT, OpenBOLT } from '../../src/tokens/GenesisMultiBOLT.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { scriptChunksFromBin } from '../../src/lib/boltLib.js'

const FIX = JSON.parse(fs.readFileSync(path.resolve(__dirname, '../fixtures/genesis-chains.json'), 'utf8')) as
  Record<string, { contract: string; txs: string[] }>
const TYPE: Record<string, 'FixedBOLT' | 'OpenBOLT' | 'SerialBOLT'> = { FixedBolt: 'FixedBOLT', OpenBolt: 'OpenBOLT', SerialBolt: 'SerialBOLT' }

const MASK64 = (1n << 64n) - 1n
const bal = (n: bigint): number[] => { const b = Buffer.alloc(16); b.writeBigUInt64LE(n & MASK64, 0); b.writeBigUInt64LE(n >> 64n, 8); return Array.from(b) }
const SIM = BigInt('0x1ffffffffffffe')
const issuer = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const other = PrivateKey.fromString('a1b2c3d4e5f60718293a4b5c6d7e8f90112233445566778899aabbccddeeff00', 'hex')
const child = (k: PrivateKey, n: string) => k.deriveChild(k.toPublicKey(), n)
const source = (k: PrivateKey, sats = 100000) => new Transaction(1, [], [
  { satoshis: sats, change: true, lockingScript: new P2PKH().lock(Hash.hash160(k.toPublicKey().encode(true))) },
])
/** `lock` with push i replaced by `data`. */
const withPush = (lock: Script, i: number, data: number[]) =>
  new Script([...lock.chunks.slice(0, i), scriptChunksFromBin(data)[0], ...lock.chunks.slice(i + 1)])

describe('registry', () => {
  it('registers the three genesis types with distinct suffix hashes; the old types are unchanged in kind', () => {
    for (const t of ['FixedBOLT', 'OpenBOLT', 'SerialBOLT'] as const) expect(REGISTRY[t].genesis).toBe(true)
    for (const t of ['MinSimpleBOLT', 'AuthBOLT', 'SimpleMultiBOLT'] as const) expect(REGISTRY[t].genesis).toBe(false)
    const hashes = Object.values(REGISTRY).map((s) => s.suffixHashHex)
    expect(new Set(hashes).size).toBe(hashes.length)
  })
})

describe('recognition: every token output of the reference chains, with its phase', () => {
  for (const [name, { contract, txs }] of Object.entries(FIX)) {
    it(name, () => {
      let mints = 0, later = 0
      for (const h of txs) {
        const tx = Transaction.fromHex(h)
        tx.outputs.forEach((o) => {
          if (o.lockingScript.chunks.length < 100) return // not a token output
          const r = recognizeToken(o.lockingScript)
          expect(r?.type).toBe(TYPE[contract])
          const nullField = (o.lockingScript.chunks[0].data as number[]).every((b) => b === 0)
          expect(r?.phase).toBe(nullField ? 'mint' : 'postMint')
          nullField ? mints++ : later++
        })
      }
      expect(mints).toBeGreaterThan(0)
      expect(later).toBeGreaterThan(0)
    })
  }
})

describe('recognition boundaries (the two specs)', () => {
  const chain = FIX.FixedBoltMintData.txs.map((h) => Transaction.fromHex(h))
  const mintLock = chain[0].outputs[0].lockingScript   // null field + 48 bytes of mintData
  const laterLock = chain[1].outputs[0].lockingScript  // set field + OP_0
  it('a mint carrying mintData is recognised (mint phase); the same mint with OP_0 mintData too', () => {
    expect(recognizeToken(mintLock)).toEqual({ type: 'FixedBOLT', phase: 'mint' })
    expect(recognizeToken(withPush(mintLock, 1, []))).toEqual({ type: 'FixedBOLT', phase: 'mint' })
  })
  it('a 255-byte mintData is the cap (256, a PUSHDATA2, is not a token); a later output with ANY mintData is not a token', () => {
    expect(recognizeType(withPush(mintLock, 1, new Array(255).fill(1)))).toBe('FixedBOLT')
    expect(recognizeType(withPush(mintLock, 1, new Array(256).fill(1)))).toBeNull()
    expect(recognizeType(withPush(laterLock, 1, [0xab]))).toBeNull()
    expect(recognizeType(withPush(laterLock, 1, new Array(48).fill(0xab)))).toBeNull()
  })
  it('a 35- or 37-byte field, or a mint-shaped field with a tampered suffix, is not a token', () => {
    expect(recognizeType(withPush(laterLock, 0, new Array(35).fill(7)))).toBeNull()
    expect(recognizeType(withPush(laterLock, 0, new Array(37).fill(7)))).toBeNull()
    const tampered = new Script([...laterLock.chunks.slice(0, -1), { op: 0x51 }])
    expect(recognizeType(tampered)).toBeNull()
  })
  it('expectedType filters: a FixedBOLT lock is not an OpenBOLT or SimpleMultiBOLT', () => {
    expect(recognizeType(laterLock, 'OpenBOLT')).toBeNull()
    expect(recognizeType(laterLock, 'SimpleMultiBOLT')).toBeNull()
  })
})

for (const [name, Cls, T] of [['FixedBOLT', FixedBOLT, 'FixedBOLT'], ['OpenBOLT', OpenBOLT, 'OpenBOLT']] as const) {
  describe(`${name} batches`, () => {
    it('a transfer, split and melt lifecycle verifies; the events are typed', async () => {
      const t = await new Cls().mint(issuer, source(issuer), 'issuer bytes', bal(SIM))
      await t.transfer(child(issuer, '1'))
      await t.transfer(child(issuer, '2'))
      const r = verifyEvents(t.prevTxs, { expectedType: T })
      expect(r.ok, r.reason).toBe(true)
      expect(r.type).toBe(T)
      const [a] = await t.split(child(issuer, '10'), child(issuer, '11'), bal(1n))
      const chain = a.prevTxs
      const ev = verifyEvent(chain.slice(-2), { expectedType: T })
      expect(ev.ok, ev.reason).toBe(true)
      expect(ev.kind).toBe('split')
    }, 600000)

    it('a settle whose asset field was rewritten (not its lineage) is refused by the lineage rule', async () => {
      const t = await new Cls().mint(issuer, source(issuer), '', bal(SIM))
      await t.transfer(child(issuer, '1'))
      const [mint, commit, settle] = t.prevTxs
      const forged = Transaction.fromHex(settle.toHex())
      forged.outputs[0].lockingScript = withPush(settle.outputs[0].lockingScript, 0, new Array(36).fill(9)) as any
      forged.inputs.forEach((inp, i) => { inp.sourceTransaction = settle.inputs[i].sourceTransaction })
      const r = verifyEvents([mint, commit, forged], { expectedType: T })
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/asset field does not follow its lineage/)
    }, 600000)
  })
}

describe('merge batches', () => {
  it('OpenBOLT: a re-rooted merge of two separate mints verifies', async () => {
    const a = await new OpenBOLT().mint(issuer, source(issuer, 100000), '', bal(SIM))
    const b = await new OpenBOLT().mint(issuer, source(issuer, 90000), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(issuer, '2'))
    const merged = await a.merge(b, child(issuer, '400'))
    const ev = verifyEvent(merged.prevTxs.slice(-2), { expectedType: 'OpenBOLT' })
    expect(ev.ok, ev.reason).toBe(true)
    expect(ev.kind).toBe('merge')
  }, 600000)

  it('FixedBOLT: a same-genesis merge verifies', async () => {
    const t = await new FixedBOLT().mint(issuer, source(issuer), '', bal(SIM))
    await t.transfer(child(issuer, '1'))
    const [a, b] = await t.split(child(issuer, '10'), child(issuer, '11'), bal(1n))
    await a.transfer(child(issuer, '20'))
    const owner = child(issuer, '11') // piece B's key: B's commit is funded from its own source
    const fund = { sourceTransaction: source(owner, 50000), sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(owner), sequence: 0xffffffff }
    await b.commit(child(issuer, '21'), undefined, false, fund as any)
    await b.settle(child(issuer, '21'))
    const merged = await a.merge(b, child(issuer, '400'))
    const ev = verifyEvent(merged.prevTxs.slice(-2), { expectedType: 'FixedBOLT' })
    expect(ev.ok, ev.reason).toBe(true)
    expect(ev.kind).toBe('merge')
  }, 600000)

  it('FixedBOLT: a cross-genesis merge built anyway (verification off, guard bypassed) is refused by the scanner as different assets', async () => {
    const a = await new FixedBOLT().mint(issuer, source(issuer, 100000), '', bal(SIM))
    const b = await new FixedBOLT().mint(issuer, source(issuer, 90000), '', bal(1n))
    await a.transfer(child(issuer, '1'))
    await b.transfer(child(issuer, '2'))
    a.skipVerify = true; b.skipVerify = true
    const merged = await SimpleMultiBOLT.prototype.merge.call(a, b, child(issuer, '400'))
    const r = verifyEvents([...b.prevTxs.slice(0, -1), ...merged.prevTxs])
    expect(r.ok).toBe(false)
    expect(r.reason).toMatch(/different genesis outpoints/)
  }, 600000)

  it('a cross-issuer batch is refused (inconsistent issuer), for both types', async () => {
    for (const Cls of [FixedBOLT, OpenBOLT]) {
      const a = await new Cls().mint(issuer, source(issuer), '', bal(SIM))
      const b = await new Cls().mint(other, source(other), '', bal(1n))
      await a.transfer(child(issuer, '1'))
      await b.transfer(child(other, '2'))
      const r = verifyEvents([...a.prevTxs, ...b.prevTxs])
      expect(r.ok).toBe(false)
      expect(r.reason).toMatch(/inconsistent issuerPubKey/)
    }
  }, 600000)
})
