// B1 — MinSimpleBolt identity template: the lock is byte-faithful to the sx-compiled
// contract (the production artifact) and a genesis mint is well-formed (verifyTx green).
import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, resolve } from 'node:path'
import { Hash, P2PKH, PrivateKey, Transaction, Script } from '@bsv/sdk'
import MinSimpleTemplate from '../src/templates/MinSimpleBolt.sx.template.js'
import { verifyTx } from '../src/boltLib.js'

const __dirname = dirname(fileURLToPath(import.meta.url))
// Lock-suffix golden, vendored from the sx artifact by scripts/build-min-simple-bolt.mjs, so the
// suite runs WITHOUT the sibling sx/ package (isolation). Still catches hand-edits to the template
// suffix: the template stores hand-editable ASM, this golden is the canonical compiled hex.
const lockHexSuffix = readFileSync(resolve(__dirname, 'fixtures/MinSimpleBolt.lockSuffix.hex'), 'utf8').trim()

describe('B1 — MinSimpleBolt identity template', () => {
  const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
  const issuerPub = issuerKey.toPublicKey().encode(true) as number[]
  const recipientPkh = Hash.hash160(
    issuerKey.deriveChild(issuerKey.toPublicKey(), '1').toPublicKey().encode(true),
  )
  const tpl = new MinSimpleTemplate()
  const lock = tpl.lock(recipientPkh, issuerPub) // genesis defaults (commit zeros, txoType 00, parent/grandparent zeros)

  it('lock leads with 6 data pushes [20,20,1,36,36,33] (issuerPubKey last)', () => {
    const lens = lock.chunks.slice(0, 6).map((c) => c.data?.length ?? 0)
    expect(lens).toEqual([20, 20, 1, 36, 36, 33])
    expect(lock.chunks[0].data).toEqual(recipientPkh)
    expect(lock.chunks[5].data).toEqual(issuerPub)
  })

  it('static suffix is byte-identical to the sx-compiled contract (the artifact)', () => {
    const suffix = new Script(lock.chunks.slice(6))
    expect(suffix.toHex()).toBe(lockHexSuffix)
  })

  it('a genesis mint (P2PKH funding -> token + change) is well-formed (verifyTx green)', async () => {
    const funding = new Transaction(1, [], [
      { satoshis: 1000, lockingScript: new P2PKH().lock(Hash.hash160(issuerPub)) },
    ])
    const mint = new Transaction(
      2,
      [{
        sourceTransaction: funding, sourceOutputIndex: 0,
        unlockingScriptTemplate: new P2PKH().unlock(issuerKey), sequence: 0xffffffff,
      }],
      [
        { satoshis: 1, lockingScript: lock },
        { change: true, lockingScript: new P2PKH().lock(Hash.hash160(issuerPub)) },
      ],
    )
    await mint.fee(0)
    await mint.sign()
    mint.inputs.forEach((i: any) => { if (!i.sourceTXID && i.sourceTransaction) i.sourceTXID = i.sourceTransaction.id('hex') })
    const { valid } = verifyTx(mint, true)
    expect(valid).toBe(true)
  })
})
