// Genesis-family templates (FixedMulti, OpenMulti, SerialBolt): each static suffix is byte-identical to its
// production artifact (the vendored golden), and each lock leads with the genesis / LMG field and mintData.
import { describe, it, expect } from 'vitest'
import { Script, Transaction, Hash, PrivateKey } from '@bsv/sdk'
import FixedMultiTemplate from '../../src/tokens/templates/FixedMulti.sx.template.js'
import OpenMultiTemplate from '../../src/tokens/templates/OpenMulti.sx.template.js'
import SerialBoltTemplate from '../../src/tokens/templates/SerialBolt.sx.template.js'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import { readFixture } from '../helpers/fixtures.js'

const issuerPub = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex').toPublicKey().encode(true) as number[]
const mintData = Array.from(Buffer.from('issuer bytes', 'utf8'))

for (const [name, Tpl, golden] of [['FixedMulti', FixedMultiTemplate, 'FixedBolt'], ['OpenMulti', OpenMultiTemplate, 'OpenBolt']] as const) {
  describe(`${name} template`, () => {
    const tpl = new Tpl(mintData)
    const lock = tpl.lock(issuerPub, [] as Transaction[])
    it('static suffix is byte-identical to the production artifact', () => {
      expect(tpl.staticSuffix().toHex()).toBe(readFixture(`${golden}.lockSuffix.hex`))
      expect(new Script(lock.chunks.slice(13)).toHex()).toBe(readFixture(`${golden}.lockSuffix.hex`))
    })
    it('a mint leads with a null field and the mintData, then the 11 SimpleMultiBolt pushes', () => {
      expect(lock.chunks.slice(0, 13).map((c) => c.data?.length ?? 0)).toEqual([36, mintData.length, 16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33])
      expect(lock.chunks[0].data).toEqual(new Array(36).fill(0))
      expect(lock.chunks[1].data).toEqual(mintData)
      expect(lock.chunks[12].data).toEqual(issuerPub)
    })
    it('differs from SimpleMultiBolt', () => {
      expect(tpl.staticSuffix().toHex()).not.toBe(new SimpleMultiTemplate().staticSuffix().toHex())
    })
  })
}

describe('SerialBolt template', () => {
  const tpl = new SerialBoltTemplate()
  const pkh = Hash.hash160(issuerPub)
  it('static suffix is byte-identical to the production artifact', () => {
    expect(tpl.staticSuffix().toHex()).toBe(readFixture('SerialBolt.lockSuffix.hex'))
  })
  it('a mint leads [36 null, mintData, 20, 20, 1, 36, 36, 33]; a later output carries OP_0 mintData', () => {
    const mint = tpl.lock(pkh, issuerPub, undefined, undefined, undefined, undefined, undefined, mintData)
    expect(mint.chunks.slice(0, 8).map((c) => c.data?.length ?? 0)).toEqual([36, mintData.length, 20, 20, 1, 36, 36, 33])
    const later = tpl.lock(pkh, issuerPub, new Array(20).fill(0), [0x21], new Array(36).fill(7), new Array(36).fill(0), new Array(36).fill(7), mintData)
    expect(later.chunks[1].op).toBe(0) // mintData is only ever the mint's
    expect(later.chunks[0].data).toEqual(new Array(36).fill(7))
  })
  it('rejects mintData over 255 bytes (PUSHDATA1 cap)', () => {
    expect(() => tpl.lock(pkh, issuerPub, undefined, undefined, undefined, undefined, undefined, new Array(256).fill(1))).toThrow(/at most 255/)
  })
})
