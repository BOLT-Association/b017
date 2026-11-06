#!/usr/bin/env node
// Axiom audit for the Lean development (lean/).
//
// Collects every theorem of Layer 1 (listed in lean/AxiomCheck.lean) and of Layer 2 (every theorem
// Lean's environment holds from a module under BoltProof.Bridge, generated files and the
// declarations Lean derives included; enumerated by Lean itself, not by scanning the sources),
// asks Lean for their axioms, and fails if any theorem depends on `sorryAx` or on an axiom not
// listed in lean/AXIOMS-ALLOWED. `Lean.ofReduceBool` is allowed for Layer 2 only.
//
// Run from the repository root after `cd lean && lake build`:  node scripts/lean-axiom-check.mjs
import { execFileSync } from 'node:child_process'
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { join } from 'node:path'

const root = new URL('..', import.meta.url).pathname
const lean = join(root, 'lean')

const allowed = new Set()
const bridgeOnly = new Set()
const bridgeOnlyPatterns = []
for (const line of readFileSync(join(lean, 'AXIOMS-ALLOWED'), 'utf8').split('\n')) {
  const t = line.trim()
  if (!t || t.startsWith('#')) continue
  if (t.startsWith('bridge-only-pattern:')) bridgeOnlyPatterns.push(new RegExp(t.slice('bridge-only-pattern:'.length).trim()))
  else if (t.startsWith('bridge-only:')) bridgeOnly.add(t.slice('bridge-only:'.length).trim())
  else allowed.add(t)
}
const bridgeAllows = (a) => bridgeOnly.has(a) || bridgeOnlyPatterns.some((re) => re.test(a))

const coreList = readFileSync(join(lean, 'AxiomCheck.lean'), 'utf8')
  .split('\n').map((l) => l.match(/^#print axioms\s+(\S+)/)).filter(Boolean).map((m) => m[1])

const scratch = join(lean, '.lake', 'axiom-check')
mkdirSync(scratch, { recursive: true })
const file = join(scratch, 'AxiomCheckAll.lean')
// Layer 2 is enumerated inside Lean: every theorem whose module is under `BoltProof.Bridge`
// (internal names excepted), each reported as `AXIOMS <name>: <axioms>` so no source scan can miss
// or invent a declaration.
writeFileSync(file, [
  'import BoltProof.Core', 'import BoltProof.Bridge', '',
  ...coreList.map((n) => `#print axioms ${n.startsWith('BoltProof.') ? n : 'BoltProof.' + n}`), '',
  'open Lean in',
  '#eval show CoreM Unit from do',
  '  let env ← getEnv',
  '  let mut names : Array Name := #[]',
  '  for (n, ci) in env.constants.map₁.toList do',
  '    if let .thmInfo _ := ci then',
  '      if n.isInternal then continue',
  '      match env.getModuleIdxFor? n with',
  '      | some idx =>',
  '        if (`BoltProof.Bridge).isPrefixOf env.header.moduleNames[idx.toNat]! then names := names.push n',
  '      | none => pure ()',
  '  IO.println s!"ENUMERATED {names.size}"',
  '  for n in names.qsort (fun a b => a.toString < b.toString) do',
  '    let axs ← collectAxioms n',
  '    IO.println s!"AXIOMS {n}: {String.intercalate \", \" (axs.toList.map toString)}"',
  '',
].join('\n'))

let out
try {
  out = execFileSync('lake', ['env', 'lean', file], { cwd: lean, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] })
} catch (e) {
  console.error(e.stdout, e.stderr)
  process.exit(1)
}

const coreSet = new Set(coreList.map((n) => (n.startsWith('BoltProof.') ? n : 'BoltProof.' + n)))
// Lean wraps a long axiom list over several lines; join continuation lines (indented) to their report.
const reports = out.split('\n').reduce((acc, l) => {
  if (/^\s/.test(l) && acc.length) acc[acc.length - 1] += ' ' + l.trim()
  else acc.push(l)
  return acc
}, [])
let bad = 0, seen = 0, enumerated = -1
const check = (name, axioms) => {
  seen++
  const isCore = coreSet.has(name) || !name.startsWith('BoltProof.Bridge')
  for (const a of axioms) {
    if (allowed.has(a)) continue
    if (!isCore && bridgeAllows(a)) continue
    console.error(`FORBIDDEN axiom ${a} in ${name} (${isCore ? 'Layer 1' : 'Layer 2'})`)
    bad++
  }
  console.log(`${name}: ${axioms.length ? axioms.join(', ') : 'none'}`)
}
for (const line of reports) {
  let m
  if ((m = line.match(/^ENUMERATED (\d+)$/))) { enumerated = Number(m[1]); continue }
  if ((m = line.match(/^AXIOMS (\S+): ?(.*)$/))) {
    check(m[1], m[2].split(',').map((s) => s.trim()).filter(Boolean))
    continue
  }
  m = line.match(/^'([^']+)' depends on axioms: \[([^\]]*)\]/)
  const none = line.match(/^'([^']+)' does not depend on any axioms/)
  if (!m && !none) continue
  check((m ?? none)[1], m ? m[2].split(',').map((s) => s.trim()).filter(Boolean) : [])
}
if (enumerated < 0) { console.error('the Layer 2 enumeration did not run'); bad++ }
const expected = coreSet.size + Math.max(enumerated, 0)
if (seen !== expected) { console.error(`expected ${expected} axiom reports, saw ${seen}`); bad++ }
console.log(`${seen} theorems checked, ${bad} violations`)
process.exit(bad ? 1 : 0)
