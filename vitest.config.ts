import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';

export default defineConfig({
  // during development every package resolves the base module from source
  resolve: { alias: { '@symjs/symjs': fileURLToPath(new URL('./packages/symjs/src/index.ts', import.meta.url)) } },
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
