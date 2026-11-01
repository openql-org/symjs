import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: { include: ['compat/**/*.test.ts'], testTimeout: 600_000 },
});
