import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';

export default defineConfig({
  resolve: {
    alias: [
      { find: /^@symjs\/symjs$/, replacement: fileURLToPath(new URL('../packages/symjs/src/index.ts', import.meta.url)) },
      { find: /^@symjs\/symjs\/(.*)$/, replacement: fileURLToPath(new URL('../packages/symjs/src/', import.meta.url)) + '$1.ts' },
    ],
  },
  // The unit corpus replays thousands of assertions within a single test.
  test: { include: ['compat/**/*.test.ts'], testTimeout: 1_800_000 },
});
