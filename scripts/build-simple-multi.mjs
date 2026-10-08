// Maintainer-only: patch the SimpleMultiBolt template's LOCK_SCRIPT_SUFFIX / UNLOCK_SCRIPT_SUFFIX from the
// pre-compiled production artifact (sibling sx/, build-time only). Consumers never run this -
// the package ships the pre-compiled template; the bulky compiled artifact is NOT shipped.
//
//   node scripts/build-simple-multi.mjs      (npm run build:contract)
//
// Same pipeline as build-min-simple-bolt.mjs: the template is patched from the sibling toolchain's frozen
// production artifact, never compiled here.

import { readFileSync, writeFileSync } from 'fs'
import { resolve, dirname } from 'path'
import { fileURLToPath } from 'url'
import { Script } from '@bsv/sdk'

const __dirname = dirname(fileURLToPath(import.meta.url))
const PKG = resolve(__dirname, '..')
const SX = resolve(PKG, '../sx')

const artifactPath = resolve(SX, 'bolt/production/artifacts/SimpleMultiBolt.json')
const artifact = JSON.parse(readFileSync(artifactPath, 'utf8'))
const lockHex = artifact.lockingRecombinants.filter((r) => typeof r === 'string').pop()
if (!lockHex) throw new Error('no string lockingRecombinant in ' + artifactPath)
const lockASM = Script.fromHex(lockHex).toASM()
const unlockHex = artifact.unlockingRecombinants.filter((r) => typeof r === 'string').pop()
const unlockASM = unlockHex ? Script.fromHex(unlockHex).toASM() : ''

const tplPath = resolve(PKG, 'src/tokens/templates/SimpleMulti.sx.template.ts')
let tpl = readFileSync(tplPath, 'utf8')
tpl = tpl.replace(/private readonly UNLOCK_SCRIPT_SUFFIX = "[^"]*"/, `private readonly UNLOCK_SCRIPT_SUFFIX = "${unlockASM}"`)
tpl = tpl.replace(/private readonly LOCK_SCRIPT_SUFFIX = "[^"]*"/, `private readonly LOCK_SCRIPT_SUFFIX = "${lockASM}"`)
writeFileSync(tplPath, tpl)
console.log('Patched SimpleMultiBolt template - lock suffix', lockASM.length, 'chars; unlock suffix', unlockASM.length, 'chars')
