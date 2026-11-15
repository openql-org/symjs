import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';
import { corpusIndex, writeTestsReport } from './tests-report.js';

const directory = mkdtempSync(join(tmpdir(), 'symjs-unit-results-'));
let start = 0;
const resolve = {
  alias: [
    { find: /^@symjs\/symjs$/, replacement: fileURLToPath(new URL('../packages/symjs/src/index.ts', import.meta.url)) },
    { find: /^@symjs\/symjs\/(.*)$/, replacement: fileURLToPath(new URL('../packages/symjs/src/', import.meta.url)) + '$1.ts' },
  ],
};

export default defineConfig({
  resolve,
  test: {
    maxWorkers: 4,
    testTimeout: 600_000,
    reporters: ['default', {
      onTestRunStart() { start = performance.now(); },
      onTestRunEnd() { writeTestsReport(directory, (performance.now() - start) / 1000); rmSync(directory, { recursive: true, force: true }); },
    }],
    projects: [
      { resolve, test: { name: 'doctests-and-harness', include: ['compat/**/*.test.ts'], exclude: ['compat/tests-compat.test.ts', 'compat/totests/**'], testTimeout: 600_000 } },
      ...Object.keys(corpusIndex().categories).map((category) => ({ resolve, test: {
        name: `unit-${category}`, include: ['compat/tests-compat.test.ts'], testTimeout: 600_000,
        provide: { testsCategory: category, testsResults: directory },
      } })),
    ],
  },
});
