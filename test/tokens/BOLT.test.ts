// BOLT abstract base — the shared state contract for token classes. SimpleMultiBOLT must extend it,
// and a minimal subclass must inherit the documented defaults.
import { describe, it, expect } from 'vitest'
import { PrivateKey, Transaction } from '@bsv/sdk'
import { BOLT } from '../../src/tokens/BOLT.js'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'

class StubBOLT extends BOLT {
  mint(_k: PrivateKey, _src: Transaction) { return this }
  commit(_k: PrivateKey) { return this }
  settle(_k: PrivateKey) { return this }
  transfer(_k: PrivateKey) { return this }
}

describe('BOLT abstract base', () => {
  it('a subclass inherits empty default state', () => {
    const t = new StubBOLT()
    expect(t.prevTxs).toEqual([])
    expect(t.pubKey).toEqual([])
    expect(t.issuerPubKey).toEqual([])
    expect(t.genesisOutpoint).toEqual([])
    expect(t.tx).toBeUndefined()
  })

  it('SimpleMultiBOLT is a BOLT', () => {
    expect(new SimpleMultiBOLT()).toBeInstanceOf(BOLT)
  })
})
