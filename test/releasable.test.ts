// A2 — b017 must be publishable: no elas, no file: runtime deps, @bsv/sdk as a peer
// (one shared SDK instance), and the pack ships the dist contract json (not the src copy).
import { describe, it, expect } from 'vitest'
import { execSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const root = dirname(dirname(fileURLToPath(import.meta.url)))
const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'))

describe('A2 — b017 is publishable', () => {
  it('no @elas_co/ts in any dependency field', () => {
    for (const field of ['dependencies', 'peerDependencies', 'devDependencies', 'optionalDependencies']) {
      expect(pkg[field]?.['@elas_co/ts']).toBeUndefined()
    }
  })

  it('no file: runtime dependency (file: specs cannot be published)', () => {
    for (const spec of Object.values(pkg.dependencies ?? {})) {
      expect(String(spec)).not.toMatch(/^file:/)
    }
  })

  it('@bsv/sdk is a peer dependency (consumer provides one shared instance)', () => {
    expect(pkg.peerDependencies?.['@bsv/sdk']).toBeTruthy()
  })

  it('npm pack ships dist/index.js + the dist contract json, and NOT the src copy', () => {
    const out = execSync('npm pack --dry-run --json', { cwd: root, encoding: 'utf8' })
    const files = (JSON.parse(out)[0].files as { path: string }[]).map((f) => f.path)
    expect(files.some((f) => /dist[\\/]index\.js$/.test(f))).toBe(true)
    expect(files.some((f) => /dist[\\/]contracts[\\/]SimpleMultiBolt\.sx\.json$/.test(f))).toBe(true)
    expect(files.some((f) => /src[\\/]contracts[\\/]/.test(f))).toBe(false)
  })
})
