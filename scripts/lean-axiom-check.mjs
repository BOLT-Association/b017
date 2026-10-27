#!/usr/bin/env node
// Axiom audit for the Lean development (lean/).
//
// Collects every theorem of Layer 1 (listed in lean/AxiomCheck.lean) and of Layer 2 (every
// `theorem` in lean/BoltProof/Bridge/**.lean, generated files included), asks Lean for their
// axioms with `#print axioms`, and fails if any theorem depends on `sorryAx` or on an axiom not
// listed in lean/AXIOMS-ALLOWED. `Lean.ofReduceBool` is allowed for Layer 2 only.
//
// Run from the repository root after `cd lean && lake build`:  node scripts/lean-axiom-check.mjs
import { execFileSync } from 'node:child_process'
import { readFileSync, readdirSync, statSync, writeFileSync, mkdirSync } from 'node:fs'
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

const walk = (dir) => readdirSync(dir).flatMap((f) => {
  const p = join(dir, f)
  return statSync(p).isDirectory() ? walk(p) : p.endsWith('.lean') ? [p] : []
})

/** Fully qualified theorem names declared in a file (namespace-aware, no sections). */
function theoremsOf(file) {
  const names = []
  const stack = []
  for (const raw of readFileSync(file, 'utf8').split('\n')) {
    const line = raw.trim()
    let m
    if ((m = line.match(/^namespace\s+([\w.]+)/))) stack.push(m[1])
    else if ((m = line.match(/^end\s+([\w.]+)/)) && stack.length && stack[stack.length - 1] === m[1]) stack.pop()
    else if ((m = line.match(/^theorem\s+([\w.']+)/))) names.push([...stack, m[1]].join('.'))
  }
  return names
}

const coreList = readFileSync(join(lean, 'AxiomCheck.lean'), 'utf8')
  .split('\n').map((l) => l.match(/^#print axioms\s+(\S+)/)).filter(Boolean).map((m) => m[1])
const bridgeFiles = walk(join(lean, 'BoltProof', 'Bridge'))
const bridgeList = bridgeFiles.flatMap(theoremsOf)

const scratch = join(lean, '.lake', 'axiom-check')
mkdirSync(scratch, { recursive: true })
const file = join(scratch, 'AxiomCheckAll.lean')
writeFileSync(file, [
  'import BoltProof.Core', 'import BoltProof.Bridge', '',
  ...coreList.map((n) => `#print axioms ${n.startsWith('BoltProof.') ? n : 'BoltProof.' + n}`),
  ...bridgeList.map((n) => `#print axioms ${n}`), '',
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
let bad = 0, seen = 0
for (const line of reports) {
  let m = line.match(/^'([^']+)' depends on axioms: \[([^\]]*)\]/)
  const none = line.match(/^'([^']+)' does not depend on any axioms/)
  if (!m && !none) continue
  seen++
  const name = (m ?? none)[1]
  const axioms = m ? m[2].split(',').map((s) => s.trim()).filter(Boolean) : []
  const isCore = coreSet.has(name) || !name.startsWith('BoltProof.Bridge')
  for (const a of axioms) {
    if (allowed.has(a)) continue
    if (!isCore && bridgeAllows(a)) continue
    console.error(`FORBIDDEN axiom ${a} in ${name} (${isCore ? 'Layer 1' : 'Layer 2'})`)
    bad++
  }
  console.log(`${name}: ${axioms.length ? axioms.join(', ') : 'none'}`)
}
const expected = coreSet.size + bridgeList.length
if (seen !== expected) { console.error(`expected ${expected} axiom reports, saw ${seen}`); bad++ }
console.log(`${seen} theorems checked, ${bad} violations`)
process.exit(bad ? 1 : 0)
