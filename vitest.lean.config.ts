import { defineConfig } from 'vitest/config'

// The Lean vector exporter (`npm run lean:vectors`): a vitest-driven script that builds the
// honest and adversarial transactions of the test suite with the real builders and writes them
// as Lean source under lean/BoltProof/Bridge/Generated/. Kept out of the default vitest config
// so `npm test` and the coverage thresholds are untouched.
export default defineConfig({
  test: {
    include: ['lean/vectors/**/*.test.ts'],
    testTimeout: 300000,
    fileParallelism: false,
  },
})
