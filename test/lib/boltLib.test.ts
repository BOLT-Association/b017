// Direct unit tests for the layout-agnostic boltLib primitives (the shared foundation used by both
// the NFT and fungible streams). These were previously only exercised indirectly via full lifecycles.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, Utils } from '@bsv/sdk'
import {
  verifyTx, buildOutpoint, buildChangeOutput, createSignature, splitCtx,
  le32, le64, scriptChunksFromBin, scriptChunk, txVersion, txLockTime,
  spentOutpoint, outputValue, outputScript, vinChunk, vinSequence, vinScript, voutChunk,
} from '../../src/lib/boltLib.js'
import { Script } from '@bsv/sdk'

const key = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const pkh = Hash.hash160(key.toPublicKey().encode(true))
const sampleTx = () =>
  new Transaction(7, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(pkh) }])

describe('boltLib — little-endian + chunk primitives', () => {
  it('le32 / le64 emit fixed-width little-endian', () => {
    expect(le32(1)).toEqual([1, 0, 0, 0])
    expect(le32(0x01020304)).toEqual([4, 3, 2, 1])
    expect(le64(1)).toEqual([1, 0, 0, 0, 0, 0, 0, 0])
  })

  it('scriptChunksFromBin round-trips through scriptChunk', () => {
    const data = [0xde, 0xad, 0xbe, 0xef]
    const chunks = scriptChunksFromBin(data)
    expect(chunks[0].data).toEqual(data)
  })

  it('txVersion / txLockTime are 4-byte LE', () => {
    const tx = sampleTx()
    expect(txVersion(tx)).toEqual([7, 0, 0, 0])
    expect(txLockTime(tx)).toEqual([0, 0, 0, 0])
  })
})

describe('boltLib — outpoint + output serialisers', () => {
  it('buildOutpoint is 36 bytes: 32-byte txid hash + 4-byte LE vout', () => {
    const tx = sampleTx()
    const op = buildOutpoint(tx, 3)
    expect(op.length).toBe(36)
    expect(op.slice(0, 32)).toEqual(tx.hash())
    expect(op.slice(32)).toEqual([3, 0, 0, 0])
  })

  it('buildChangeOutput = 8-byte value LE + varint len + script; [] for a missing index', () => {
    const tx = sampleTx()
    const ser = buildChangeOutput(tx, 0)
    expect(new Utils.Reader(ser).readUInt64LEBn().toString()).toBe('1000')
    expect(buildChangeOutput(tx, 9)).toEqual([])
  })

  it('outputValue / outputScript fail soft on a missing index', () => {
    const tx = sampleTx()
    expect(outputValue(tx, 0)).toEqual(le64(1000))
    expect(outputValue(tx, 9)).toEqual([])
    expect(outputScript(tx, 0)).toEqual(tx.outputs[0].lockingScript.toBinary())
    expect(outputScript(tx, 9)).toEqual([])
  })

  it('spentOutpoint returns [] when an input has no source', () => {
    expect(spentOutpoint(sampleTx(), 0)).toEqual([])
  })
})

describe('boltLib — createSignature', () => {
  it('returns a checksig-format sig and a 33-byte compressed pubkey', () => {
    const { sigForScript, pubkeyForScript } = createSignature(key, [1, 2, 3, 4], 0x41)
    expect(pubkeyForScript.length).toBe(33)
    expect(sigForScript.length).toBeGreaterThan(8)
    expect(sigForScript[sigForScript.length - 1]).toBe(0x41) // sighash flag tail
  })
})

describe('boltLib — splitCtx (every varint scriptCode length branch)', () => {
  const header = new Array(104).fill(0x01)
  const footer = new Array(52).fill(0x02)

  it('1-byte length (< 0xfd)', () => {
    const code = [0xaa, 0xbb, 0xcc, 0xdd, 0xee]
    const p = splitCtx([...header, code.length, ...code, ...footer], 2)
    expect(p.ctxHeader).toEqual(header)
    expect(p.ctxCodeLen).toEqual([5])
    expect(p.ctxCodeUnlockScriptCode).toEqual([0xaa, 0xbb])
    expect(p.ctxCodeLockScriptCode).toEqual([0xcc, 0xdd, 0xee])
    expect(p.ctxFooter).toEqual(footer)
    expect(p.ctxCodeLockLen).toEqual([3])
  })

  it('0xfd (2-byte) length', () => {
    const len = 300
    const code = new Array(len).fill(0x07)
    const ctx = [...header, 0xfd, len & 0xff, (len >> 8) & 0xff, ...code, ...footer]
    const p = splitCtx(ctx, 0)
    expect(p.ctxCodeLen).toEqual([0xfd, len & 0xff, (len >> 8) & 0xff])
    expect(p.ctxCodeLockScriptCode.length).toBe(len)
    expect(p.ctxFooter).toEqual(footer)
  })

  it('0xfe (4-byte) length', () => {
    const len = 70000
    const code = new Array(len).fill(0x09)
    const ctx = [...header, 0xfe, ...le32(len), ...code, ...footer]
    const p = splitCtx(ctx, 0)
    expect(p.ctxCodeLen).toEqual([0xfe, ...le32(len)])
    expect(p.ctxCodeLockScriptCode.length).toBe(len)
    expect(p.ctxFooter).toEqual(footer)
  })
})

describe('boltLib — vin/vout chunk primitives fail soft on missing input/output', () => {
  it('vinChunk / vinSequence / vinScript return [] for an out-of-range input', () => {
    const tx = sampleTx()
    expect(vinChunk(tx, 5, 0)).toEqual([])
    expect(vinSequence(tx, 5)).toEqual([])
    expect(vinScript(tx, 5)).toEqual([])
  })

  it('voutChunk reads a locking-script chunk', () => {
    const tx = new Transaction(1, [], [{ satoshis: 1, lockingScript: new Script([{ op: 4, data: [1, 2, 3, 4] }]) }])
    expect(voutChunk(tx, 0, 0)).toEqual([1, 2, 3, 4])
  })

  it('spentOutpoint uses the sourceTXID (reversed) fallback when no source tx is attached', () => {
    const txid = '11'.repeat(32)
    const tx = new Transaction(1, [{ sourceTXID: txid, sourceOutputIndex: 2, sequence: 0xffffffff } as any], [])
    const op = spentOutpoint(tx, 0)
    expect(op.length).toBe(36)
    expect(op.slice(32)).toEqual([2, 0, 0, 0])
  })

  it('scriptChunk returns [] for an out-of-range chunk', () => {
    expect(scriptChunk(new Script([]), 3)).toEqual([])
  })
})

describe('boltLib — verifyTx guards', () => {
  it('throws when an input is missing its source transaction', () => {
    const tx = new Transaction(1, [{ sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    expect(() => verifyTx(tx, true)).toThrow(/source/i)
  })

  it('throws when an input is missing its unlocking script', () => {
    const funding = sampleTx()
    const tx = new Transaction(1, [{ sourceTransaction: funding, sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    expect(() => verifyTx(tx, true)).toThrow(/unlocking/i)
  })
})
