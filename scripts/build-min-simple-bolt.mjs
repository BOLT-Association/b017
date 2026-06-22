// Maintainer-only: patch MinSimpleBolt.sx.template.ts's LOCK_SCRIPT_SUFFIX from the
// pre-compiled production artifact (sibling sx/, build-time only). Consumers never run this.
//
//   node scripts/build-min-simple-bolt.mjs
//
import { readFileSync, writeFileSync } from 'fs'
import { resolve, dirname } from 'path'
import { fileURLToPath } from 'url'
import { Script } from '@bsv/sdk'

const __dirname = dirname(fileURLToPath(import.meta.url))
const PKG = resolve(__dirname, '..')
const SX = resolve(PKG, '../sx')

const artifactPath = resolve(SX, 'bolt/production/artifacts/MinSimpleBolt.json')
const artifact = JSON.parse(readFileSync(artifactPath, 'utf8'))
const lockHex = artifact.lockingRecombinants.filter((r) => typeof r === 'string').pop()
if (!lockHex) throw new Error('no string lockingRecombinant in ' + artifactPath)
const lockASM = Script.fromHex(lockHex).toASM()
const unlockHex = artifact.unlockingRecombinants.filter((r) => typeof r === 'string').pop()
if (!unlockHex) throw new Error('no string unlockingRecombinant in ' + artifactPath)
const unlockASM = Script.fromHex(unlockHex).toASM()

const tplPath = resolve(PKG, 'src/templates/MinSimpleBolt.sx.template.ts')
let tpl = readFileSync(tplPath, 'utf8')
tpl = tpl.replace(
  /private readonly LOCK_SCRIPT_SUFFIX = "[^"]*"/,
  `private readonly LOCK_SCRIPT_SUFFIX = "${lockASM}"`,
)
tpl = tpl.replace(
  /private readonly UNLOCK_SCRIPT_SUFFIX = "[^"]*"/,
  `private readonly UNLOCK_SCRIPT_SUFFIX = "${unlockASM}"`,
)
writeFileSync(tplPath, tpl)
console.log('Patched MinSimpleBolt template — lock suffix', lockASM.length, 'chars; unlock suffix', unlockASM.length, 'chars')
