import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';

export default defineConfig({
  resolve: { alias: { '@symjs/symjs': fileURLToPath(new URL('../packages/symjs/src/index.ts', import.meta.url)) } },
  test: { include: ['compat/**/*.test.ts'], testTimeout: 600_000 },
});
