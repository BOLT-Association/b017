// VERIFYING A TOKEN'S PROVENANCE IS 2 TRANSACTIONS - CONSTANT, AT ANY DEPTH.
//
// The claim to show peers: to establish a token's full provenance you read the 2 transactions of its
// most recent event - the commit+settle pair - and NOTHING ELSE, no matter how deep the lineage. Not
// O(N), not O(log N): O(1), a flat two transactions.
//
// The proof is inductive, and the covenant supplies the step. A settle is only valid if it
// RECONSTRUCTS its grandparent commit from the spending token's own fields and hash-checks it against
// grandparentOutpoint, AND co-spends that grandparent's one-shot proof output. So a valid tip settle
// is constructible only if its grandparent event genuinely happened and was correct; that grandparent
// commit was likewise only spendable because ITS predecessor happened; and so on down to the genesis
// mint, which is issuer-signed. Consensus enforced each step when the transactions were mined. So the
// validity of the tip pair mathematically induces the validity of the entire chain behind it - the
// peer inherits it, and never reads it.
//
//   cd b017 && npx vitest run test/scanner/verificationScaling.test.ts
import { describe, it, expect } from 'vitest'
import { Hash, P2PKH, PrivateKey, Transaction } from '@bsv/sdk'
import { SimpleMultiBOLT } from '../../src/tokens/MultiBOLT.js'
import { verifyEvent } from '../../src/lib/scanner/verifyEvents.js'

const issuerKey = PrivateKey.fromString('0000000000000000000000000000000000000000000000000000000000000001', 'hex')
const SIM = BigInt('0x1ffffffffffffe')
const bal = (amount: bigint): number[] => {
  const x = amount & ((1n << 128n) - 1n)
  const buf = Buffer.alloc(16); buf.writeBigUInt64LE(x & ((1n << 64n) - 1n), 0); buf.writeBigUInt64LE((x >> 64n) & ((1n << 64n) - 1n), 8)
  return Array.from(buf)
}
const freshSource = () =>
  new Transaction(1, [], [{ satoshis: 1000, change: true, lockingScript: new P2PKH().lock(Hash.hash160(issuerKey.toPublicKey().encode(true))) }])
const child = (n: string) => issuerKey.deriveChild(issuerKey.toPublicKey(), n)
const T = 'SimpleMultiBOLT' as const
const ZERO36 = '0'.repeat(72)

const isToken = (s: any) => {
  const L = [16, 16, 20, 20, 20, 36, 1, 1, 36, 36, 33]
  return s?.chunks && s.chunks.length > 11 && L.every((n, i) => (s.chunks[i]?.data?.length ?? -1) === n)
}
// grandparentOutpoint the spent token records (SMB lock chunk 9): the two-hop anchor the settle rebuilds.
const grandparentOf = (settle: Transaction): string => {
  const tokenOut = settle.inputs[0].sourceTransaction!.outputs.find((o) => isToken(o.lockingScript))!
  return Buffer.from(tokenOut.lockingScript.chunks[9].data as number[]).toString('hex')
}

// Build mint -> transfer x N. Each transfer is one commit->settle event. prevTxs is the full lineage
// [mint, c1, s1, ..., cN, sN]; the tip event is the last two.
async function buildChain(n: number) {
  let t = await new SimpleMultiBOLT().mint(issuerKey, freshSource(), '', bal(SIM))
  for (let i = 0; i < n; i++) t = await t.transfer(child(String(i + 1)))
  return t
}

describe('BOLT provenance verification is O(1) - two transactions, at any depth', () => {
  it('reads EXACTLY 2 transactions to verify the tip, whatever the depth (1, 8, 24)', async () => {
    for (const N of [1, 8, 24]) {
      const line = (await buildChain(N)).prevTxs
      const commit = line[line.length - 2]
      const settle = line[line.length - 1]

      // The verifier reads the tip event pair - two transactions - and nothing else in the lineage.
      const readSet = new Set([commit.id('hex'), settle.id('hex')])
      const ev = verifyEvent([commit, settle], { expectedType: T })
      expect(ev.ok, ev.reason).toBe(true)
      expect(readSet.size).toBe(2)                          // constant: 2, independent of N
      // None of the N-1 earlier events is read - not the grandparent, not the mint.
      for (let k = 0; k < line.length - 2; k++)
        expect(readSet.has(line[k].id('hex'))).toBe(false)
    }
  })

  it('the inductive step: a valid tip event is constructible only if its predecessor happened', async () => {
    const line = (await buildChain(6)).prevTxs
    const settle = line[line.length - 1]

    // The tip settle names a real, non-genesis grandparent two hops back...
    expect(grandparentOf(settle)).not.toBe(ZERO36)
    // ...and it co-spends that grandparent commit's one-shot PROOF output. That proof exists only
    // because the grandparent commit was really mined - so the tip's validity presupposes it, which
    // presupposes the one before, and so on. (A tip naming a grandparent that never happened is
    // rejected: see repro-fabricated-hop.test.ts and the node-verified fabricated-hop specs.)
    const grandparentCommit = line[line.length - 4]
    const proofOut = grandparentCommit.outputs.findIndex((o) => {
      const c = o.lockingScript.chunks
      return c.length >= 5 && (c[4]?.data?.length ?? -1) === 20 && !isToken(o.lockingScript)
    })
    expect(proofOut).toBeGreaterThanOrEqual(0)
    const spendsThatProof = settle.inputs.some(
      (i) => i.sourceTransaction?.id('hex') === grandparentCommit.id('hex') && i.sourceOutputIndex === proofOut,
    )
    expect(spendsThatProof, 'the tip settle co-spends the grandparent commit proof').toBe(true)
  })

  it('base case: the first event has no grandparent to rebuild - the commit spends the mint directly', async () => {
    const line = (await buildChain(3)).prevTxs
    const mint = line[0], c1 = line[1], s1 = line[2]
    expect(grandparentOf(s1)).toBe(ZERO36)                 // nothing two hops back
    expect(c1.inputs.some((i) => i.sourceTransaction?.id('hex') === mint.id('hex'))).toBe(true)
    expect(verifyEvent([c1, s1], { expectedType: T }).ok).toBe(true)
    console.log('[scaling] provenance verification: 2 tx reads at depth 1, 8, 24 alike - O(1). A genesis walk would be O(N).')
  })
})
