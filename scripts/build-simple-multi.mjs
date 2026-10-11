// Maintainer-only: patch the fungible templates' LOCK_SCRIPT_SUFFIX / UNLOCK_SCRIPT_SUFFIX (SimpleMultiBolt and the
// genesis family FixedBolt / OpenBolt) from the pre-compiled production artifacts (sibling sx/, build-time only). Consumers never run this -
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

const TARGETS = [
  { artifact: 'SimpleMultiBolt', template: 'SimpleMulti.sx.template.ts' },
  { artifact: 'FixedBolt', template: 'FixedMulti.sx.template.ts', golden: 'FixedBolt.lockSuffix.hex' },
  { artifact: 'OpenBolt', template: 'OpenMulti.sx.template.ts', golden: 'OpenBolt.lockSuffix.hex' },
]

for (const t of TARGETS) {
  const artifactPath = resolve(SX, `bolt/production/artifacts/${t.artifact}.json`)
  const artifact = JSON.parse(readFileSync(artifactPath, 'utf8'))
  const lockHex = artifact.lockingRecombinants.filter((r) => typeof r === 'string').pop()
  if (!lockHex) throw new Error('no string lockingRecombinant in ' + artifactPath)
  const lockASM = Script.fromHex(lockHex).toASM()
  const unlockHex = artifact.unlockingRecombinants.filter((r) => typeof r === 'string').pop()
  const unlockASM = unlockHex ? Script.fromHex(unlockHex).toASM() : ''

  const tplPath = resolve(PKG, 'src/tokens/templates', t.template)
  let tpl = readFileSync(tplPath, 'utf8')
  tpl = tpl.replace(/(private|protected) readonly UNLOCK_SCRIPT_SUFFIX(: string)? = "[^"]*"/, `$1 readonly UNLOCK_SCRIPT_SUFFIX$2 = "${unlockASM}"`)
  tpl = tpl.replace(/(private|protected) readonly LOCK_SCRIPT_SUFFIX(: string)? = "[^"]*"/, `$1 readonly LOCK_SCRIPT_SUFFIX$2 = "${lockASM}"`)
  writeFileSync(tplPath, tpl)
  // Vendor the lock-suffix golden so the template tests run without the sibling sx/.
  if (t.golden) writeFileSync(resolve(PKG, 'test/fixtures', t.golden), lockHex)
  console.log(`Patched ${t.artifact} template - lock suffix`, lockASM.length, 'chars; unlock suffix', unlockASM.length, 'chars')
}
