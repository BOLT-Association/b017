// SimpleMulti template — the fungible contract's runtime lock/unlock assembler. A minted token's
// lock must lead with the 11-push fungible layout, the static suffix must agree with the scanner
// registry (single source of truth), and melt must be exposed.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import SimpleMultiTemplate from '../../src/tokens/templates/SimpleMulti.sx.template.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { REGISTRY, recognizeType, sha256Hex } from '../../src/lib/scanner/fingerprints.js'

describe('SimpleMulti template', () => {
  it('staticSuffix hash matches the SimpleMultiBOLT registry entry', () => {
    const suffix = new SimpleMultiTemplate().staticSuffix()
    expect(sha256Hex(suffix.toBinary())).toBe(REGISTRY.SimpleMultiBOLT.suffixHashHex)
  })

  it('exposes lock / unlock / melt', () => {
    const tpl = new SimpleMultiTemplate()
    expect(typeof tpl.lock).toBe('function')
    expect(typeof tpl.unlock).toBe('function')
    expect(typeof tpl.melt).toBe('function')
  })

  it('melt sign throws clear errors when the spent source cannot be resolved', async () => {
    const k = PrivateKey.fromString('e9873d79c6d87dc0fb6a5778633389f4453213303da61f20bd67fc233aa33262', 'hex')
    const tpl = new SimpleMultiTemplate()
    const noSrc = new Transaction(1, [{ sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    await expect(tpl.melt(k).sign(noSrc, 0)).rejects.toThrow(/sourceTXID/)
    const noSats = new Transaction(1, [{ sourceTXID: '11'.repeat(32), sourceOutputIndex: 0, sequence: 0xffffffff } as any], [])
    await expect(tpl.melt(k).sign(noSats, 0)).rejects.toThrow(/sourceSatoshis/)
  })

  it('a minted token lock leads with the 11-push fungible layout and is recognised', async () => {
    const k = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
    const src = new Transaction(1, [], [
      { satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(k.toPublicKey().encode(true))) },
    ])
    const token = await new SimpleMultiBOLT().mint(k, src, '')
    const lock = token.tx!.outputs[0].lockingScript
    const lens = lock.chunks.slice(0, 11).map((c: any) => c.data?.length ?? 0)
    expect(lens).toEqual([16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33])
    expect(recognizeType(lock)).toBe('SimpleMultiBOLT')
  })
})
