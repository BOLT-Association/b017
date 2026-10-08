// MinSimpleBOLT zero-funding (ZF) - port of the contract-level suite
//
// A commit or settle may carry NO funding input (fundOutpoint = OP_0) and change is optional. A 1-sat
// token cannot pay a fee, so an unfunded tx is never worth mining, yet its covenant validates off chain
// (SPV / p2p). Two surfaces:
//   (1) the CURRENT tx: fundOutpoint OP_0 -> hashPrevouts covers only the token (+ proof bolt) input.
//   (2) the ANCESTOR rebuild: a settle re-serialises its grandparent commit; if that commit was unfunded
//       (one input) or had no change, the rebuild must reproduce THAT shape.
// Unfunded + change is IMPOSSIBLE by design (nothing to return): the builder throws, no contract test.
import { describe, it, expect } from 'vitest'
import {
  buildChain, verifyChain, tamper, grandparentCheckPc, spendToken, mintToken,
  UNFUNDED, FUNDED_NO_CHANGE, iPkh, uPkh, ZERO36, issuerKey, p2pb,
  type ChainSpec, type Hop,
} from '../helpers/minSimpleChain.js'
import { minSimple as fam } from '../helpers/minSimpleFamily.js'
import { buildOutpoint } from '../../src/lib/boltLib.js'

const ok = async (spec: ChainSpec, upTo = 5) => verifyChain(await buildChain(fam, spec, upTo))

describe('MinSimpleBOLT null funding (zero-funding)', () => {
  it('control: fully funded chain (every hop funded, with change)', async () => {
    expect((await ok({})).ok).toBe(true)
  })

  // -- (1) current tx: fundOutpoint = OP_0 ------------------------------------------------------
  it('unfunded commit1 (no grandparent, no rebuild)', async () => {
    expect((await ok({ commit1: UNFUNDED }, 2)).ok).toBe(true)
  })
  it('unfunded settle1 (no grandparent, no rebuild)', async () => {
    expect((await ok({ settle1: UNFUNDED }, 3)).ok).toBe(true)
  })
  it('unfunded commit2 (rest-state spend, no rebuild)', async () => {
    expect((await ok({ commit2: UNFUNDED }, 4)).ok).toBe(true)
  })
  it('unfunded settle2 over a FUNDED commit1 (current fundOutpoint OP_0, funded rebuild)', async () => {
    expect((await ok({ settle2: UNFUNDED })).ok).toBe(true)
  })

  // -- (2) ancestor rebuild: the grandparent commit was unfunded / had no change ----------------
  it('funded settle2 over an UNFUNDED commit1 (ancestor fund OP_0, 1 input, 2 outputs)', async () => {
    expect((await ok({ commit1: UNFUNDED })).ok).toBe(true)
  })
  it('funded settle2 over a funded commit1 with NO change (2 inputs, 2 outputs)', async () => {
    expect((await ok({ commit1: FUNDED_NO_CHANGE(0, 1) })).ok).toBe(true)
  })
  it('fully unfunded chain (p2p: commit1, settle1, commit2, settle2 all OP_0)', async () => {
    expect((await ok({ commit1: UNFUNDED, settle1: UNFUNDED, commit2: UNFUNDED, settle2: UNFUNDED })).ok).toBe(true)
  })

  // -- full matrix: funded+change, funded without change, unfunded on every hop ----------------
  const STATES: Record<string, (src: { tx: number; vout: number }) => Partial<Hop>> = {
    'funded+change': (src) => ({ fund: src, change: true }),
    'funded, no change': (src) => ({ fund: src, change: false }),
    'unfunded, no change': () => UNFUNDED,
    // 'unfunded+change' is impossible by design - the builder throws (tested below)
  }
  const HOPS = {
    commit1: { idx: 2, src: { tx: 0, vout: 1 } },
    settle1: { idx: 3, src: { tx: 1, vout: 2 } },
    commit2: { idx: 4, src: { tx: 2, vout: 1 } },
    settle2: { idx: 5, src: { tx: 3, vout: 2 } },
  } as const
  const perHop: [string, string, number, Partial<Hop>][] = []
  for (const [hop, { idx, src }] of Object.entries(HOPS)) {
    for (const [state, mk] of Object.entries(STATES)) perHop.push([hop, state, idx, mk(src)])
  }
  it.each(perHop)('matrix: %s %s (chain up to and including that hop)', async (hop, _state, idx, h) => {
    expect((await ok({ [hop]: h }, idx)).ok).toBe(true)
  })

  // Every rebuilt-ancestor state (commit1) x every settle2 state.
  const crossed: [string, string][] = []
  for (const a of Object.keys(STATES)) for (const s of Object.keys(STATES)) crossed.push([a, s])
  it.each(crossed)('rebuild matrix: ancestor commit1 %s, settle2 %s', async (a, s) => {
    const c1 = STATES[a]({ tx: 0, vout: 1 })
    const c1FundedChange = !!(c1.fund && c1.change)
    const s1 = { fund: c1FundedChange ? { tx: 1, vout: 2 } : { tx: 0, vout: 2 }, change: true }
    const c2 = { fund: { tx: 2, vout: 1 }, change: true }
    const s2 = STATES[s]({ tx: 3, vout: 2 })
    expect((await ok({ commit1: c1, settle1: s1, commit2: c2, settle2: s2 })).ok).toBe(true)
  })

  // -- builder: unfunded + change is impossible ------------------------------------------------
  it('the builder refuses an unfunded spend that asks for change', async () => {
    const txs = await mintToken(fam)
    await expect(spendToken({
      fam, txs, from: { tx: 0, vout: 0 }, actor: issuerKey, beneficiary: uPkh, fund: null, change: true,
      outputs: [fam.lock(iPkh, uPkh, [0x21], buildOutpoint(txs[0], 0), ZERO36), p2pb(uPkh)],
    })).rejects.toThrow(/unfunded/)
  })

  // -- negative controls: hashPrevouts still binds the input set --------------------------------
  it('REFUSED: fundOutpoint OP_0 while the tx really has a funding input', async () => {
    const txs = await buildChain(fam, {}, 2)
    tamper({ ...fam, pieceNames: ['fundOutpoint', 'changeOutput'], ancestorStart: 26 }, txs[1],
      { fundOutpoint: '', changeOutput: '' })
    const r = verifyChain(txs)
    expect(r.ok).toBe(false)
    expect(r.failedTx).toBe(1)
  })
  it('REFUSED: fundOutpoint names an input the tx does not have', async () => {
    const txs = await buildChain(fam, { commit1: UNFUNDED }, 2)
    tamper({ ...fam, pieceNames: ['fundOutpoint'], ancestorStart: 26 }, txs[1],
      { fundOutpoint: 'ab'.repeat(32) + '01000000' })
    const r = verifyChain(txs)
    expect(r.ok).toBe(false)
    expect(r.failedTx).toBe(1)
  })

  // -- mismatch: the spender misdescribes the rebuilt ancestor's shape --------------------------
  // The rebuild derives vin/vout counts and push prefixes from arg SIZES, and nothing ties the counts
  // to the vin2/change bytes, so every false or inconsistent shape must die at the grandparent txid
  // check (the hash is the binding), not pass and not fail somewhere else.
  const FAKE_OUTPOINT = 'ab'.repeat(32) + '01000000'
  const FAKE_SCRIPT = '47' + 'cd'.repeat(71) + '21' + '02' + 'ef'.repeat(32) // P2PKH-unlock-shaped
  const FAKE_SEQ = 'ffffffff'
  const FAKE_CHANGE_VALUE = '0a00000000000000'
  const FAKE_CHANGE_SCRIPT = '76a914' + '11'.repeat(20) + '88ac'
  const FAKE_CHANGE_OUTPUT = FAKE_CHANGE_VALUE + '19' + FAKE_CHANGE_SCRIPT
  const NO_VIN2 = { Vin2Outpoint: '', Vin2Script: '', Vin2NSequence: '' }

  const MISMATCHES: [string, ChainSpec, Record<string, string>][] = [
    // funded ancestor (commit1 funded, with change)
    ['funded ancestor, fund nulled, vin2 kept (1 counted input, 2 serialised)', {}, { Vin1FundOutpoint: '' }],
    ['funded ancestor, vin2 nulled, fund kept (2 counted inputs, 1 serialised)', {}, NO_VIN2],
    ['funded ancestor passed off as unfunded (fund + vin2 nulled, consistent shape)', {}, { Vin1FundOutpoint: '', ...NO_VIN2 }],
    ['ancestor with change: change script nulled, value kept (vout count 2)', {}, { ChangeScript: '' }],
    ['ancestor with change passed off as change-less (value + script nulled)', {}, { ChangeValue: '', ChangeScript: '' }],
    ['ancestor with change: its scriptSig changeOutput nulled', {}, { Vin1ChangeOutput: '' }],
    // unfunded ancestor (commit1 unfunded, no change)
    ['unfunded ancestor, fake fund outpoint, no vin2 (2 counted inputs, 1 serialised)', { commit1: UNFUNDED },
      { Vin1FundOutpoint: FAKE_OUTPOINT }],
    ['unfunded ancestor, fake vin2, no fund (1 counted input, 2 serialised)', { commit1: UNFUNDED },
      { Vin2Outpoint: FAKE_OUTPOINT, Vin2Script: FAKE_SCRIPT, Vin2NSequence: FAKE_SEQ }],
    ['unfunded ancestor passed off as funded (fake fund + vin2, consistent shape)', { commit1: UNFUNDED },
      { Vin1FundOutpoint: FAKE_OUTPOINT, Vin2Outpoint: FAKE_OUTPOINT, Vin2Script: FAKE_SCRIPT, Vin2NSequence: FAKE_SEQ }],
    ['change-less ancestor given an invented change output (value + script)', { commit1: UNFUNDED },
      { ChangeValue: FAKE_CHANGE_VALUE, ChangeScript: FAKE_CHANGE_SCRIPT }],
    ['change-less ancestor given an invented scriptSig changeOutput', { commit1: UNFUNDED },
      { Vin1ChangeOutput: FAKE_CHANGE_OUTPUT }],
  ]

  it.each(MISMATCHES)('REFUSED at the grandparent txid check: %s', async (_name, hops, pieces) => {
    const txs = await buildChain(fam, hops)
    expect(verifyChain(txs).ok).toBe(true) // the honest chain is valid
    tamper(fam, txs[4], pieces)
    const r = verifyChain(txs)
    expect(r.ok).toBe(false)
    expect(r.failedTx).toBe(4)
    expect(r.message).toMatch(/OP_EQUALVERIFY/)
    expect(r.pc).toBe(grandparentCheckPc(txs[3].outputs[0].lockingScript))
  })
})

