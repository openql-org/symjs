import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';

export default defineConfig({
  resolve: {
    alias: [
      { find: /^@symjs\/symjs$/, replacement: fileURLToPath(new URL('../../../packages/symjs/src/index.ts', import.meta.url)) },
      { find: /^@symjs\/symjs\/(.*)$/, replacement: fileURLToPath(new URL('../../../packages/symjs/src/', import.meta.url)) + '$1.ts' },
    ],
  },
  test: { include: ['tools/sympy-corpus/totests/*.test.ts'], testTimeout: 3_600_000 },
});
