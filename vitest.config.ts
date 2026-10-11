import { defineConfig } from 'vitest/config'

export default defineConfig({
  test: {
    include: ['test/**/*.test.ts'],
    testTimeout: 30000,
    // Serial run: the contract builders write shared temp artifacts; parallel files can race on
    // Windows (EBUSY). The suite is fast (~7s) so this costs little and is deterministic.
    fileParallelism: false,
    coverage: {
      provider: 'v8',
      include: ['src/**/*.ts'],
      exclude: ['src/index.ts'], // pure re-export barrel
      reporter: ['text', 'text-summary', 'html', 'json', 'json-summary', 'lcov'],
      reportsDirectory: 'coverage',
      // 100 across the board: a new uncovered branch fails the run. It gets a test, or (a defensive TypeScript
      // guard only) a `v8 ignore` with the reason it cannot fire.
      thresholds: { statements: 100, functions: 100, lines: 100, branches: 100 },
    },
  },
})
