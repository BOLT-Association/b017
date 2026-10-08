// AuthBolt template: the lock is byte-faithful to the sx-compiled contract (the production artifact) and a
// genesis mint is well-formed (verifyTx green). Same 6-push lock layout as MinSimpleBolt.
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction, Script } from '@bsv/sdk'
import AuthBoltTemplate from '../../src/tokens/templates/AuthBolt.sx.template.js'
import MinSimpleTemplate from '../../src/tokens/templates/MinSimple.sx.template.js'
import { verifyTx } from '../../src/lib/boltLib.js'
import { readFixture } from '../helpers/fixtures.js'

const lockHexSuffix = readFixture('AuthBolt.lockSuffix.hex')

describe('AuthBolt template', () => {
  const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const issuerPub = issuerKey.toPublicKey().encode(true) as number[]
  const ownerPkh = Hash.hash160(issuerPub)
  const tpl = new AuthBoltTemplate()
  const lock = tpl.lock(ownerPkh, issuerPub)

  it('lock leads with 6 data pushes [20,20,1,36,36,33] (issuerPubKey last)', () => {
    expect(lock.chunks.slice(0, 6).map((c) => c.data?.length ?? 0)).toEqual([20, 20, 1, 36, 36, 33])
    expect(lock.chunks[0].data).toEqual(ownerPkh)
    expect(lock.chunks[5].data).toEqual(issuerPub)
  })

  it('static suffix is byte-identical to the sx-compiled contract (the artifact)', () => {
    expect(new Script(lock.chunks.slice(6)).toHex()).toBe(lockHexSuffix)
    expect(tpl.staticSuffix().toHex()).toBe(lockHexSuffix)
  })

  it('is a different contract from MinSimpleBolt (22 bytes longer: the 75 B guard + auth rebuild)', () => {
    const min = new MinSimpleTemplate().lock(ownerPkh, issuerPub)
    expect(lock.toBinary().length - min.toBinary().length).toBe(22)
    expect(lock.toHex()).not.toBe(min.toHex())
  })

  it('a genesis mint (P2PKH funding -> token + change) is well-formed (verifyTx green)', async () => {
    const funding = new Transaction(1, [], [{ satoshis: 1000, lockingScript: new P2PKH().lock(ownerPkh) }])
    const mint = new Transaction(2,
      [{ sourceTransaction: funding, sourceOutputIndex: 0, unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff }],
      [{ satoshis: 1, lockingScript: lock }, { change: true, lockingScript: new P2PKH().lock(ownerPkh) }])
    await mint.fee(0)
    await mint.sign()
    mint.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
    expect(verifyTx(mint, true).valid).toBe(true)
  })

  it('unlock refuses an authOrMiscData longer than 75 bytes (a direct push) before signing', () => {
    expect(() => tpl.unlock(issuerKey, ownerPkh, [], new Array(76).fill(1))).toThrow(/75/)
    expect(() => tpl.unlock(issuerKey, ownerPkh, [], new Array(75).fill(1))).not.toThrow()
  })

  it('unlock exposes a positive estimateLength', async () => {
    expect(await tpl.unlock(issuerKey, ownerPkh, []).estimateLength()).toBeGreaterThan(0)
  })
})
