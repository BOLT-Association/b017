// Maintainer-only: recompile SimpleMultiBolt.sx with the sx toolchain and patch the SMB
// template's ASM suffix (src/multi/SimpleMultiBolt.sx.template.ts). Consumers never run this —
// the package ships the pre-compiled template; the bulky compiled artifact is NOT shipped.
//
//   node scripts/build-contract.mjs
//
// Requires the sibling sx/ package (build-time only; not a runtime dependency).

import { readFileSync, writeFileSync } from 'fs'
import { resolve, dirname } from 'path'
import { fileURLToPath, pathToFileURL } from 'url'

const __dirname = dirname(fileURLToPath(import.meta.url))
const PKG = resolve(__dirname, '..')
const SX = resolve(PKG, '../sx')
const u = (p) => pathToFileURL(p).href

const { default: flatten } = await import(u(resolve(SX, 'src/cli/flatten.js')))
const { SxCompiler } = await import(u(resolve(SX, 'src/compiler.js')))
const bsv = await import(u(resolve(SX, 'node_modules/@bsv/sdk/dist/cjs/mod.js')))
const Script = bsv.Script || bsv.default?.Script

const toAsm = (recs) => recs.map(r => typeof r === 'string' ? Script.fromHex(r).toASM() : r)

const flat = flatten(readFileSync(resolve(SX, 'tests/bolt/multi/SimpleMultiBolt.sx'), 'utf8'))
const result = await new SxCompiler().compile('SimpleMultiBolt.sx', [{ name: 'SimpleMultiBolt.sx', data: flat }])
if (result.error) throw new Error('compile: ' + JSON.stringify(result.error))

const compiled = {
  filename: 'SimpleMultiBolt.sx',
  unlockArgs: result.unlockArgs,
  lockArgs: result.lockArgs,
  lockOps: result.lockOps,
  unlockOps: result.unlockOps,
  lockingRecombinants: toAsm(result.lockingRecombinants),
  unlockingRecombinants: toAsm(result.unlockingRecombinants),
}

const lockASM = compiled.lockingRecombinants.filter(r => typeof r === 'string').pop()
const unlockASM = compiled.unlockingRecombinants.filter(r => typeof r === 'string').pop() || ''
const tplPath = resolve(PKG, 'src/multi/SimpleMultiBolt.sx.template.ts')
let tpl = readFileSync(tplPath, 'utf8')
tpl = tpl.replace(/private readonly UNLOCK_SCRIPT_SUFFIX = "[^"]*"/, `private readonly UNLOCK_SCRIPT_SUFFIX = "${unlockASM}"`)
tpl = tpl.replace(/private readonly LOCK_SCRIPT_SUFFIX = "[^"]*"/, `private readonly LOCK_SCRIPT_SUFFIX = "${lockASM}"`)
writeFileSync(tplPath, tpl)
console.log('Patched', tplPath, `(lock ${lockASM.length} chars, unlock ${unlockASM.length} chars)`)
