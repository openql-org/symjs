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
    include: ['packages/*/tests/**/*.test.ts'],
    coverage: {
      provider: 'v8',
      include: ['packages/*/src/**/*.ts'],
      reporter: ['text-summary', 'json-summary'],
      reportsDirectory: 'coverage',
    },
  },
});
