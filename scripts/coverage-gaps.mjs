// Maintainer-only: list every branch and statement the test suite does not reach, as file:line, and count the
// `v8 ignore` markers in src/ (each is a claim that a guard cannot fire, so the total should stay visible).
//
//   npm run coverage:gaps        (runs the suite with coverage first)
//   node scripts/coverage-gaps.mjs   (reads the last coverage run)
//
// Exit code 1 when anything is uncovered, so it can gate a release.
import { readFileSync, readdirSync, statSync, existsSync } from 'fs'
import { resolve, dirname, relative, join } from 'path'
import { fileURLToPath } from 'url'

const PKG = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const FINAL = resolve(PKG, 'coverage/coverage-final.json')
if (!existsSync(FINAL)) {
  console.error('no coverage/coverage-final.json: run `npm run test:coverage` first')
  process.exit(2)
}
const cov = JSON.parse(readFileSync(FINAL, 'utf8'))
const rel = (f) => relative(PKG, f).replace(/\\/g, '/')

let branches = 0
let branchesHit = 0
let statements = 0
let statementsHit = 0
const rows = []
for (const [file, d] of Object.entries(cov).sort()) {
  const missB = new Set()
  for (const [id, counts] of Object.entries(d.b)) {
    counts.forEach((c, k) => {
      branches++
      if (c > 0) branchesHit++
      else missB.add((d.branchMap[id].locations[k] ?? d.branchMap[id].loc).start.line)
    })
  }
  const missS = new Set()
  for (const [id, c] of Object.entries(d.s)) {
    statements++
    if (c > 0) statementsHit++
    else missS.add(d.statementMap[id].start.line)
  }
  if (missB.size || missS.size) rows.push({ file: rel(file), missB: [...missB].sort((a, b) => a - b), missS: [...missS].sort((a, b) => a - b) })
}

const walk = (dir) => readdirSync(dir).flatMap((n) => {
  const p = join(dir, n)
  return statSync(p).isDirectory() ? walk(p) : p.endsWith('.ts') ? [p] : []
})
const ignores = walk(resolve(PKG, 'src'))
  .map((f) => ({ file: rel(f), n: (readFileSync(f, 'utf8').match(/v8 ignore/g) ?? []).length }))
  .filter((x) => x.n > 0)

const pct = (a, b) => (b === 0 ? '100.00' : ((100 * a) / b).toFixed(2))
console.log(`branches   ${branchesHit}/${branches} (${pct(branchesHit, branches)}%)`)
console.log(`statements ${statementsHit}/${statements} (${pct(statementsHit, statements)}%)`)
console.log('')
for (const r of rows) {
  if (r.missB.length) for (const line of r.missB) console.log(`branch     ${r.file}:${line}`)
  if (r.missS.length) for (const line of r.missS) console.log(`statement  ${r.file}:${line}`)
}
if (rows.length === 0) console.log('nothing uncovered')
console.log('')
console.log(`v8 ignore markers: ${ignores.reduce((a, x) => a + x.n, 0)}`)
for (const x of ignores) console.log(`  ${x.n}  ${x.file}`)

process.exit(rows.length === 0 ? 0 : 1)
