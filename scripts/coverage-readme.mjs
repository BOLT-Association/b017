// Maintainer-only: write the test counts and coverage figures into README.md from the last coverage run, so they
// are generated and never hand-edited.
//
//   npm run coverage:readme      (runs the suite with coverage, then rewrites README.md)
//   npm run coverage:check       (runs the suite with coverage, then FAILS if README.md is out of date)
//
// Reads coverage/coverage-summary.json (totals) and coverage/test-results.json (vitest's JSON report).
// Every figure in the README is located by a pattern that must match exactly once: if the README is reworded so
// that a pattern no longer matches, this script fails rather than silently leaving a stale number behind.
import { readFileSync, writeFileSync, existsSync } from 'fs'
import { resolve, dirname } from 'path'
import { fileURLToPath } from 'url'

const PKG = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const CHECK = process.argv.includes('--check')
const need = (p) => {
  const full = resolve(PKG, p)
  if (!existsSync(full)) {
    console.error(`missing ${p}: run this through \`npm run coverage:readme\` (or coverage:check)`)
    process.exit(2)
  }
  return JSON.parse(readFileSync(full, 'utf8'))
}
const total = need('coverage/coverage-summary.json').total
const results = need('coverage/test-results.json')

const tests = results.numTotalTests
const passed = results.numPassedTests
const files = results.numTotalTestSuites !== undefined && Array.isArray(results.testResults) ? results.testResults.length : 0
if (!tests || !files) {
  console.error('coverage/test-results.json has no test totals')
  process.exit(2)
}
if (passed !== tests) {
  console.error(`${tests - passed} of ${tests} tests did not pass: the README is only generated from a green run`)
  process.exit(1)
}

const whole = (m) => Math.floor(m.pct)                     // headline: never round a figure UP
const one = (m) => (Math.floor(m.pct * 10) / 10).toFixed(1) // table: one decimal, rounded down
const frac = (m) => `${m.covered}/${m.total}`

// [what it is, pattern (must match exactly once), replacement]
const EDITS = [
  ['headline',
    /\(\d+\/\d+ unit tests, \*\*[\d.]+% statement \/ [\d.]+% function \/ [\d.]+% branch coverage\*\*\)/g,
    `(${passed}/${tests} unit tests, **${whole(total.statements)}% statement / ${whole(total.functions)}% function / ${whole(total.branches)}% branch coverage**)`],
  ['build block test count', /# vitest \(\d+ tests\)/g, `# vitest (${tests} tests)`],
  ['testing block test count', /# \d+ tests across \d+ files/g, `# ${tests} tests across ${files} files`],
  ['table: statements', /\| Statements \| \*\*[\d.]+%\*\* \(\d+\/\d+\) \|/g, `| Statements | **${one(total.statements)}%** (${frac(total.statements)}) |`],
  ['table: functions', /\| Functions \| \*\*[\d.]+%\*\* \(\d+\/\d+\) \|/g, `| Functions | **${one(total.functions)}%** (${frac(total.functions)}) |`],
  ['table: lines', /\| Lines \| \*\*[\d.]+%\*\* \|/g, `| Lines | **${one(total.lines)}%** |`],
  ['table: branches', /\| Branches \| \*\*[\d.]+%\*\* \(\d+\/\d+\) \|/g, `| Branches | **${one(total.branches)}%** (${frac(total.branches)}) |`],
]

const readmePath = resolve(PKG, 'README.md')
const before = readFileSync(readmePath, 'utf8')
let after = before
for (const [what, pattern, replacement] of EDITS) {
  const hits = after.match(pattern)?.length ?? 0
  if (hits !== 1) {
    console.error(`README.md: expected exactly one "${what}" figure, found ${hits}. Fix the README or this script's pattern.`)
    process.exit(2)
  }
  after = after.replace(pattern, replacement)
}

if (after === before) {
  console.log(`README.md figures are current (${tests} tests, ${files} files, branches ${one(total.branches)}%)`)
  process.exit(0)
}
if (CHECK) {
  console.error('README.md coverage figures are out of date. Run `npm run coverage:readme` and commit the result.')
  process.exit(1)
}
writeFileSync(readmePath, after)
console.log(`README.md updated: ${tests} tests, ${files} files, statements ${one(total.statements)}%, branches ${one(total.branches)}%`)
