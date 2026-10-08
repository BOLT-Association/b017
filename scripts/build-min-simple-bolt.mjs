// Maintainer-only: patch the NFT-family templates' LOCK_SCRIPT_SUFFIX / UNLOCK_SCRIPT_SUFFIX from the
// pre-compiled production artifacts (sibling sx/, build-time only) and vendor the lock-suffix goldens.
// Consumers never run this.
//
//   node scripts/build-min-simple-bolt.mjs      (npm run build:nft)
//
// MinSimpleBolt (zero-funding, MSBoltZF) and AuthBolt (MinSimple + owner-supplied/transaction negotiated/challenge based authOrMiscData) are both built here.
import { readFileSync, writeFileSync } from 'fs'
import { resolve, dirname } from 'path'
import { fileURLToPath } from 'url'
import { Script } from '@bsv/sdk'

const __dirname = dirname(fileURLToPath(import.meta.url))
const PKG = resolve(__dirname, '..')
const SX = resolve(PKG, '../sx')

const TARGETS = [
  { artifact: 'MinSimpleBolt', template: 'MinSimple.sx.template.ts', golden: 'MinSimpleBolt.lockSuffix.hex' },
  { artifact: 'AuthBolt', template: 'AuthBolt.sx.template.ts', golden: 'AuthBolt.lockSuffix.hex' },
]

for (const t of TARGETS) {
  const artifactPath = resolve(SX, `bolt/production/artifacts/${t.artifact}.json`)
  const artifact = JSON.parse(readFileSync(artifactPath, 'utf8'))
  const lockHex = artifact.lockingRecombinants.filter((r) => typeof r === 'string').pop()
  if (!lockHex) throw new Error('no string lockingRecombinant in ' + artifactPath)
  const lockASM = Script.fromHex(lockHex).toASM()
  const unlockHex = artifact.unlockingRecombinants.filter((r) => typeof r === 'string').pop()
  if (!unlockHex) throw new Error('no string unlockingRecombinant in ' + artifactPath)
  const unlockASM = Script.fromHex(unlockHex).toASM()

  const tplPath = resolve(PKG, 'src/tokens/templates', t.template)
  let tpl = readFileSync(tplPath, 'utf8')
  tpl = tpl.replace(/private readonly LOCK_SCRIPT_SUFFIX = "[^"]*"/, `private readonly LOCK_SCRIPT_SUFFIX = "${lockASM}"`)
  tpl = tpl.replace(/private readonly UNLOCK_SCRIPT_SUFFIX = "[^"]*"/, `private readonly UNLOCK_SCRIPT_SUFFIX = "${unlockASM}"`)
  writeFileSync(tplPath, tpl)
  // Vendor the lock-suffix golden so the template tests run without the sibling sx/.
  writeFileSync(resolve(PKG, 'test/fixtures', t.golden), lockHex)
  console.log(`Patched ${t.artifact} template - lock suffix`, lockASM.length, 'chars; unlock suffix', unlockASM.length, 'chars')
}
