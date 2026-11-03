import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';

export default defineConfig({
  // during development every package resolves the base module from source
  resolve: {
    alias: [
      { find: /^@symjs\/symjs$/, replacement: fileURLToPath(new URL('./packages/symjs/src/index.ts', import.meta.url)) },
      { find: /^@symjs\/symjs\/(.*)$/, replacement: fileURLToPath(new URL('./packages/symjs/src/', import.meta.url)) + '$1.ts' },
    ],
  },
  test: {
    include: ['packages/*/tests/**/*.test.ts', 'compat/equivalence.test.ts'],
    // coverage instrumentation slows the heavy cases (factorint of a large number, logic minimization) past the 5 s default
    testTimeout: 30_000,
    coverage: {
      provider: 'v8',
      thresholds: { perFile: true, statements: 100, branches: 100, functions: 100, lines: 100 },
      include: ['packages/*/src/**/*.ts'],
      reporter: ['text-summary', 'json-summary'],
      reportsDirectory: 'coverage',
    },
  },
});
