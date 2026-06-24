// Shared fixture loader. Resolves from the package root (process.cwd() when vitest runs) so test
// files can live at any folder depth without an import.meta/__dirname dance.
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

export const fixturesDir = resolve(process.cwd(), 'test', 'fixtures')
export const readFixture = (name: string): string => readFileSync(resolve(fixturesDir, name), 'utf8').trim()
export const readFixtureJSON = <T = any>(name: string): T => JSON.parse(readFixture(name)) as T
