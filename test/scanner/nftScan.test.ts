// The off-chain scanner over the NFT family: verifyEvents / verifyEvent recognise MinSimpleBOLT and
// AuthBOLT transfers, including ZERO-FUNDING chains (unfunded / change-less hops are SPV-only txs, so the
// scanner is the only thing that can vouch for them).
import { describe, it, expect } from 'vitest'
import { Hash } from '@bsv/sdk'
import { buildChain, UNFUNDED, FUNDED_NO_CHANGE, issuerPub, ZERO20, ZERO36 } from '../helpers/minSimpleChain.js'
import { minSimple } from '../helpers/minSimpleFamily.js'
import { authBolt } from '../helpers/authBoltFamily.js'
import { verifyEvents, verifyEvent } from '../../src/lib/scanner/verifyEvents.js'
import { recognizeType, REGISTRY, issuerPubKeyOf } from '../../src/lib/scanner/fingerprints.js'

const A20 = new Array(20).fill(0xa5)

for (const [fam, type] of [[minSimple, 'MinSimpleBOLT'], [authBolt, 'AuthBOLT']] as const) {
  describe(`scanner over ${type}`, () => {
    it('verifyEvents accepts the funded lifecycle (transfer x2)', async () => {
      const r = verifyEvents(await buildChain(fam, { commit1: { auth: A20 } }), { expectedType: type })
      expect(r.ok).toBe(true)
      expect(r.type).toBe(type)
    })

    it('verifyEvents accepts a fully UNFUNDED (p2p / SPV) chain', async () => {
      const all = { commit1: UNFUNDED, settle1: UNFUNDED, commit2: UNFUNDED, settle2: UNFUNDED }
      const r = verifyEvents(await buildChain(fam, all), { expectedType: type })
      expect(r.ok).toBe(true)
      expect(r.type).toBe(type)
    })

    it('verifyEvent accepts a funded-no-change commit+settle pair', async () => {
      const txs = await buildChain(fam, { commit1: FUNDED_NO_CHANGE(0, 1) }, 3)
      const r = verifyEvent(txs, { expectedType: type })
      expect(r.ok).toBe(true)
      expect(r.kind).toBe('transfer')
    })

    it('recognises its own lock and issuerPubKeyOf reads the 33-byte issuer', () => {
      const lock = fam.lock(Hash.hash160(issuerPub), ZERO20, [0], ZERO36, ZERO36)
      expect(recognizeType(lock)).toBe(type)
      expect(issuerPubKeyOf(lock, type).length).toBe(33)
    })
  })
}

describe('AuthBOLT is a distinct registered type', () => {
  const lockOf = (fam: typeof minSimple) => fam.lock(Hash.hash160(issuerPub), ZERO20, [0], ZERO36, ZERO36)

  it('shares the 6-push layout but has its own suffix fingerprint', () => {
    expect(REGISTRY.AuthBOLT.suffixHashHex).toBe('378932c162a2fb2344ae7357664268608a05efa2fc07be60b6dbf35984dcf669') // pinned: a change is a BREAKING fingerprint move
    expect(REGISTRY.AuthBOLT.pushLengths).toEqual(REGISTRY.MinSimpleBOLT.pushLengths)
    expect(REGISTRY.AuthBOLT.suffixHashHex).not.toBe(REGISTRY.MinSimpleBOLT.suffixHashHex)
  })

  it('a MinSimple lock is not an AuthBOLT and vice versa (expectedType filters)', () => {
    expect(recognizeType(lockOf(minSimple), 'AuthBOLT')).toBeNull()
    expect(recognizeType(lockOf(authBolt), 'MinSimpleBOLT')).toBeNull()
  })

  it('verifyEvents rejects a chain of the other type when expectedType is set', async () => {
    const txs = await buildChain(authBolt, {}, 3)
    expect(verifyEvents(txs, { expectedType: 'MinSimpleBOLT' }).ok).toBe(false)
  })
})

