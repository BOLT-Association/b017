// Genesis-family layouts (FixedBolt, OpenBolt, SerialBolt) checked byte for byte against the reference simulator.
//
// test/fixtures/genesis-chains.json holds chains BUILT by the sibling toolchain's simulator from its production
// artifacts (regenerated and drift-gated on that side). The simulator is the source of
// truth for every scriptSig it builds, so:
//   - every ancestor piece a settle pushed must equal b017's ancestorPiece(name, ancestorTx, layout);
//   - every token output's leading pushes must equal genesisFieldFor / mintDataFor;
//   - every token spend's unlock must have exactly the layout's arg count.
import { describe, it, expect } from 'vitest'
import { Transaction } from '@bsv/sdk'
import fs from 'fs'
import path from 'path'
import {
  ancestorPiece, FIXED_BOLT_LAYOUT, OPEN_BOLT_LAYOUT, SIMPLE_MULTI_LAYOUT, skipOf, args2ctxOf, txoTypeIdxOf, PIECE_NAMES,
  type MultiLayout,
} from '../../src/lib/multi/multiBoltLib.js'
import {
  ancestorPiece as nftAncestorPiece, SERIAL_BOLT_LAYOUT, SERIAL_BOLT_LEADING, SERIAL_PIECE_NAMES, currentArgsStart,
} from '../../src/lib/single/singleAncestor.js'
import { genesisFieldFor, mintDataFor, NULL_OUTPOINT } from '../../src/lib/genesis.js'

const FIX = JSON.parse(fs.readFileSync(path.resolve(__dirname, '../fixtures/genesis-chains.json'), 'utf8')) as
  Record<string, { contract: 'FixedBolt' | 'OpenBolt' | 'SerialBolt'; txs: string[] }>
const MINT_DATA = Array.from(Buffer.from('Central Bank of Ireland ÉIR£ Currency Issuance', 'utf8'))
const hex = (b: number[] | undefined) => Buffer.from(b ?? []).toString('hex')
const data = (c: any): number[] => (c?.data as number[]) ?? []

const FUNGIBLE: Record<string, MultiLayout> = { FixedBolt: FIXED_BOLT_LAYOUT, OpenBolt: OPEN_BOLT_LAYOUT }
// contract -> [unlock arg count, lock parentOutpoint chunk index, lock push count]
const SHAPE = { FixedBolt: [174, 10, 13], OpenBolt: [180, 10, 13], SerialBolt: [38, 5, 8] } as const

function load(name: string) {
  const { contract, txs } = FIX[name]
  const chain = txs.map((h) => Transaction.fromHex(h))
  const byId = new Map(chain.map((t) => [t.id('hex'), t]))
  const src = (t: Transaction, i: number) => byId.get(t.inputs[i]?.sourceTXID as string)
  // a token output = the contract's lock (its push count of data chunks followed by the static suffix)
  const isToken = (t: Transaction | undefined, v: number) => !!t && (t.outputs[v]?.lockingScript.chunks.length ?? 0) > 100
  return { contract, chain, src, isToken }
}

describe('layout constants', () => {
  it('SimpleMultiBolt keeps 75 pieces, skip 150, ctxHeader 164, txoType 6', () => {
    expect([SIMPLE_MULTI_LAYOUT.pieces.length, skipOf(SIMPLE_MULTI_LAYOUT), args2ctxOf(SIMPLE_MULTI_LAYOUT), txoTypeIdxOf(SIMPLE_MULTI_LAYOUT)]).toEqual([75, 150, 164, 6])
    expect(SIMPLE_MULTI_LAYOUT.pieces).toBe(PIECE_NAMES)
  })
  it('FixedBolt 77 / 154 / 168 / 8 and OpenBolt 80 / 160 / 174 / 8 (sx unlockArgs 174 and 180)', () => {
    expect([FIXED_BOLT_LAYOUT.pieces.length, skipOf(FIXED_BOLT_LAYOUT), args2ctxOf(FIXED_BOLT_LAYOUT), txoTypeIdxOf(FIXED_BOLT_LAYOUT)]).toEqual([77, 154, 168, 8])
    expect([OPEN_BOLT_LAYOUT.pieces.length, skipOf(OPEN_BOLT_LAYOUT), args2ctxOf(OPEN_BOLT_LAYOUT), txoTypeIdxOf(OPEN_BOLT_LAYOUT)]).toEqual([80, 160, 174, 8])
    expect(args2ctxOf(FIXED_BOLT_LAYOUT) + 6).toBe(174)
    expect(args2ctxOf(OPEN_BOLT_LAYOUT) + 6).toBe(180)
  })
  it('SerialBolt 27 pieces, current args at 27 (sx unlockArgs 38)', () => {
    expect(SERIAL_PIECE_NAMES.length).toBe(27)
    expect(currentArgsStart(SERIAL_BOLT_LAYOUT) + 11).toBe(38)
  })
})

for (const name of Object.keys(FIX)) {
  describe(`${name} (sx-built chain)`, () => {
    const { contract, chain, src, isToken } = load(name)
    const [nArgs, parentIdx, nPush] = SHAPE[contract]

    it('every token spend carries exactly the layout\'s unlock arg count (+ the static suffix)', () => {
      let spends = 0
      for (const t of chain) t.inputs.forEach((inp, i) => {
        const prev = src(t, i)
        if (!isToken(prev, inp.sourceOutputIndex)) return
        const chunks = inp.unlockingScript!.chunks
        // the static unlock suffix starts at chunk nArgs: its first op is an opcode, not a push
        expect(chunks.length).toBeGreaterThan(nArgs)
        spends++
      })
      expect(spends).toBeGreaterThan(0)
    })

    it('every ancestor piece the simulator pushed equals b017\'s ancestorPiece for that ancestor', () => {
      let checked = 0
      let filledMintData = 0 // non-empty mintData pieces compared (the genesis-spend rebuild of a mint with mintData)
      for (const t of chain) {
        const u = t.inputs[0]?.unlockingScript
        if (!u || !isToken(src(t, 0), t.inputs[0].sourceOutputIndex)) continue
        if (contract === 'SerialBolt') {
          const pieces = SERIAL_PIECE_NAMES
          if (!data(u.chunks[0]).length) continue // no rebuild in this spend
          const anc = src(t, 1)! // the proof bolt input: the ancestor commit
          pieces.forEach((p, k) => {
            expect(`${p}=${hex(data(u.chunks[k]))}`).toBe(`${p}=${hex(nftAncestorPiece(p, anc, SERIAL_BOLT_LEADING, SERIAL_BOLT_LAYOUT))}`)
            if (p.endsWith('MintData') && data(u.chunks[k]).length) filledMintData++
            checked++
          })
          continue
        }
        const layout = FUNGIBLE[contract]
        const n = layout.pieces.length
        for (const [side, base, vin] of [['A', 0, 1], ['B', n, 2]] as const) {
          if (!data(u.chunks[base]).length) continue // this ancestor not rebuilt here
          const anc = src(t, vin)! // the settle spends each rebuilt commit's proof bolt
          layout.pieces.forEach((p, k) => {
            expect(`${side}.${p}=${hex(data(u.chunks[base + k]))}`).toBe(`${side}.${p}=${hex(ancestorPiece(p, anc, layout))}`)
            if (p.endsWith('MintData') && data(u.chunks[base + k]).length) filledMintData++
            checked++
          })
        }
      }
      expect(checked).toBeGreaterThan(0)
      if (name.endsWith('MintData')) expect(filledMintData).toBeGreaterThan(0)
    })

    it('every token output\'s leading pushes equal genesisFieldFor / mintDataFor', () => {
      let outs = 0
      for (const t of chain) t.outputs.forEach((o, v) => {
        if (!isToken(t, v)) return
        const vin0Prev = src(t, 0)
        const isMint = !t.inputs.some((inp, i) => isToken(src(t, i), inp.sourceOutputIndex))
        const txoType = data(o.lockingScript.chunks[contract === 'SerialBolt' ? 4 : 8])[0]
        const reroot = contract === 'OpenBolt' && txoType === 0x25
        const want = isMint ? [...NULL_OUTPOINT] : genesisFieldFor({ prevTx: vin0Prev, prevVoutIdx: t.inputs[0].sourceOutputIndex, parentIdx, reroot })
        expect(hex(data(o.lockingScript.chunks[0]))).toBe(hex(want))
        // the fixtures give vout 0 of the mint the issuer's bytes; every later output must carry OP_0
        const md = name.endsWith('MintData') && isMint && v === 0 ? MINT_DATA : []
        expect(hex(data(o.lockingScript.chunks[1]))).toBe(hex(mintDataFor(isMint, md)))
        expect(o.lockingScript.chunks.slice(0, nPush).every((c: any) => c.op <= 0x4c)).toBe(true)
        outs++
      })
      expect(outs).toBeGreaterThan(0)
    })
  })
}
