// Section cutting for the Lean glue proof (lean/GLUE-PLAN.md, M1).
//
// Each shipped covenant suffix is cut into chunks so that
//   * every fragment literal proved in lean/BoltProof/Bridge/Gadgets/ (a "landmark") is exactly one chunk,
//   * every OP_IF / OP_NOTIF / OP_ELSE / OP_ENDIF is its own one-byte chunk (so every branch arm is a
//     concatenation of whole chunks), and
//   * a straight-line run is at most MAX_RUN instructions long.
// Every boundary is an instruction start, checked by walking the push lengths. The exporter emits the chunks
// as `List Nat` literals plus the suffix as their right-nested concatenation (Generated/Chunks.lean); one
// `native_decide` theorem per family ties the hex string to that concatenation, and the offset theorems of
// Bridge/Glue/Sections.lean are then `decide` on list literals.

/** A fragment literal and where it sits. With `auto`, `at` is left empty and every occurrence of the literal at an
 *  instruction start is a landmark; `auto` is the number of occurrences there must be. */
export interface Landmark { name: string; hex: string; at: number[]; auto?: number }
export interface Section { name: string; start: number; end: number; kind: 'run' | 'flow' | 'landmark'; instrs: number }

export const MAX_RUN = 120

/** Extra cuts per family: the end of the lock's own OP_PUSH_TX block (the byte after its
 *  `OP_CHECKSIGVERIFY`), so the glue can export that block's run as a prefix of the program. */
export const EXTRA_CUTS: Record<string, number[]> = {
  simpleMulti: [423], minSimple: [414], authBolt: [423], serialBolt: [447],
}

const OP_IF = 0x63, OP_NOTIF = 0x64, OP_ELSE = 0x67, OP_ENDIF = 0x68
const FLOW: Record<number, string> = { [OP_IF]: 'if', [OP_NOTIF]: 'notif', [OP_ELSE]: 'else', [OP_ENDIF]: 'endif' }

// The fragment literals, byte for byte as the Gadgets files define them (NullAncestor.lean, Parity.lean,
// BalanceGuards.lean, BalanceBounds.lean, NftType.lean), with the suffix offsets they sit at.
const nullTail = '82770088'
const parityCheck = '011a79529776630126798b011c798868760127795297' + '7c6300675168' + '88'
const boundCheck = (d: string) => `01${d}797600a2695579a169`
const mergeGuard = '012d79013479935b79a169'
const splitGuard = '012d790134799400a269'
const mergeSettle = '012f79012f797600a26993765e79a169'
const splitSettle = '012f79012f797600a269947600a269'
const nftFlag = '768192'
const nftTypeSel = (d: string) => `01${d}796302010067020121687e`
// The fungible rebuild's blocks whose conditionals turn on the ancestor's data rather than on the arguments
// (lean/BoltProof/Bridge/Glue/SimpleMulti/Blocks.lean): the pad-to-16 loop (`SIZE 16 LESSTHAN IF 00 CAT ENDIF`
// sixteen times), the width-dependent optional push after a `<w>` (`SWAP SIZE ROT EQUAL IF SIZE SWAP CAT ELSE DROP 00
// ENDIF CAT`), and the balance anchor on the ancestor's type.
const pad16 = '82609f6301007e68'.repeat(16)
const optTail = '7c827b876382' + '7c7e6775010068' + '7e'
const anchor = '63014379815188759388677601238763750142798151876394886701427981528877876968670143798151887575886868'
// `IF 3 ELSE 2 ENDIF` and `IF 4 ELSE 3 ENDIF`: the rebuilt transaction's input and output counts, on the flags
// "the ancestor has a second input" and "a second output" (ancestor data again).
const ite32 = '6353675268'
const ite43 = '6354675368'

export const LANDMARKS: Record<string, Landmark[]> = {
  simpleMulti: [
    { name: 'parityCheck', hex: parityCheck, at: [528] },
    { name: 'boundCheck27', hex: boundCheck('27'), at: [610] },
    { name: 'boundCheck2d', hex: boundCheck('2d'), at: [621] },
    { name: 'mergeGuard', hex: mergeGuard, at: [672] },
    { name: 'splitGuard', hex: splitGuard, at: [687] },
    { name: 'mergeSettle', hex: mergeSettle, at: [781] },
    { name: 'splitSettle', hex: splitSettle, at: [935] },
    { name: 'pad16', hex: pad16, at: [], auto: 2 },
    { name: 'optTail', hex: optTail, at: [], auto: 50 },
    { name: 'anchor', hex: anchor, at: [], auto: 2 },
    { name: 'ite32', hex: ite32, at: [], auto: 2 },
    { name: 'ite43', hex: ite43, at: [], auto: 2 },
    { name: 'nullTail', hex: nullTail, at: [4648] },
  ],
  minSimple: [
    { name: 'nftFlag', hex: nftFlag, at: [6] },
    { name: 'nftTypeSel17', hex: nftTypeSel('17'), at: [534] },
    { name: 'nullTail', hex: nullTail, at: [1072] },
  ],
  authBolt: [
    { name: 'nftFlag', hex: nftFlag, at: [6] },
    { name: 'nftTypeSel17', hex: nftTypeSel('17'), at: [543] },
    { name: 'nullTail', hex: nullTail, at: [1094] },
  ],
  serialBolt: [
    { name: 'nftFlag', hex: nftFlag, at: [39] },
    { name: 'nftTypeSel18', hex: nftTypeSel('18'), at: [589] },
    { name: 'nullTail', hex: nullTail, at: [1232] },
  ],
}

const fromHex = (h: string): number[] => Array.from(Buffer.from(h, 'hex'))

/** Instruction starts of a script with only direct pushes (no PUSHDATA1/2/4, which the suffixes never use). */
export function instructionStarts(bytes: number[]): number[] {
  const starts: number[] = []
  let i = 0
  while (i < bytes.length) {
    starts.push(i)
    const op = bytes[i]
    if (op >= 0x4c && op <= 0x4e) throw new Error(`PUSHDATA opcode 0x${op.toString(16)} at ${i}: not supported`)
    const len = 1 + (op >= 1 && op <= 0x4b ? op : 0)
    if (i + len > bytes.length) throw new Error(`push at ${i} runs past the end of the script`)
    i += len
  }
  return starts
}

/** Cut `bytes` into sections (see the header). Throws if a landmark is not where it is said to be. */
export function cutSections(bytes: number[], landmarks: Landmark[], extraCuts: number[] = []): Section[] {
  const starts = instructionStarts(bytes)
  const isStart = new Set(starts)
  landmarks = landmarks.map((lm) => {
    if (lm.auto === undefined) return lm
    const lit = fromHex(lm.hex)
    const at = starts.filter((s) => lit.every((b, j) => bytes[s + j] === b))
    if (at.length !== lm.auto) throw new Error(`${lm.name}: ${at.length} occurrences, ${lm.auto} expected`)
    return { ...lm, at }
  })
  const cuts = new Set<number>([0, bytes.length])
  for (const c of extraCuts) {
    if (!isStart.has(c)) throw new Error(`extra cut ${c} is not an instruction start`)
    cuts.add(c)
  }
  const label = new Map<number, { name: string; kind: 'flow' | 'landmark'; end: number }>()

  // Landmarks first: a flow opcode inside a fragment (the parity check and the NFT type selector carry their
  // own OP_IF/OP_ELSE/OP_ENDIF) belongs to the fragment and is not cut.
  const inLandmark = (o: number): boolean => landmarks.some((lm) => lm.at.some((at) => o >= at && o < at + lm.hex.length / 2))
  for (const s of starts) {
    const op = bytes[s]
    if (FLOW[op] && !inLandmark(s)) { cuts.add(s); cuts.add(s + 1); label.set(s, { name: FLOW[op], kind: 'flow', end: s + 1 }) }
  }
  for (const lm of landmarks) {
    const lit = fromHex(lm.hex)
    for (const at of lm.at) {
      if (!isStart.has(at)) throw new Error(`${lm.name}: offset ${at} is not an instruction start`)
      for (let j = 0; j < lit.length; j++)
        if (bytes[at + j] !== lit[j]) throw new Error(`${lm.name}: bytes at ${at} differ from the literal at +${j}`)
      if (!isStart.has(at + lit.length) && at + lit.length !== bytes.length)
        throw new Error(`${lm.name}: end ${at + lit.length} is not an instruction start`)
      cuts.add(at); cuts.add(at + lit.length)
      label.set(at, { name: lm.name, kind: 'landmark', end: at + lit.length })
    }
  }
  // Long straight-line runs are split every MAX_RUN instructions.
  const sorted = [...cuts].sort((a, b) => a - b)
  for (let k = 0; k + 1 < sorted.length; k++) {
    const [a, b] = [sorted[k], sorted[k + 1]]
    if (label.has(a)) continue
    const inside = starts.filter((s) => s >= a && s < b)
    for (let n = MAX_RUN; n < inside.length; n += MAX_RUN) cuts.add(inside[n])
  }
  const bounds = [...cuts].sort((a, b) => a - b)
  const sections: Section[] = []
  for (let k = 0; k + 1 < bounds.length; k++) {
    const [start, end] = [bounds[k], bounds[k + 1]]
    const l = label.get(start)
    if (l && l.end !== end) throw new Error(`${l.name} at ${start}: a cut falls inside it (${end} < ${l.end})`)
    const instrs = starts.filter((s) => s >= start && s < end).length
    const name = l ? `c${start}_${l.name}` : `c${start}`
    sections.push({ name, start, end, kind: l?.kind ?? 'run', instrs })
  }
  // Every landmark occurrence must be one section.
  for (const lm of landmarks) for (const at of lm.at)
    if (!sections.some((s) => s.start === at && s.kind === 'landmark')) throw new Error(`${lm.name}@${at} is not a section`)
  return sections
}
