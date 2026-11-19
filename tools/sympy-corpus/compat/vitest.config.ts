import { randomUUID } from 'node:crypto';
import { mkdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vitest/config';
import { writeUnittestReport } from './unittest-report.js';
import { writeDoctestReport, refreshScopeReport } from './doctest-report.js';
import { readIndex, type Kind } from '../corpus.js';

const directory = join(tmpdir(), `symjs-compat-results-${randomUUID()}`);
let start = 0;
const resolve = {
  alias: [
    { find: /^@symjs\/symjs$/, replacement: fileURLToPath(new URL('../../../packages/symjs/src/index.ts', import.meta.url)) },
    { find: /^@symjs\/symjs\/(.*)$/, replacement: fileURLToPath(new URL('../../../packages/symjs/src/', import.meta.url)) + '$1.ts' },
  ],
};

function projects(kind: Kind) {
  const results = join(directory, kind);
  return Object.keys(readIndex(kind).categories).map(category => ({
    resolve, test: {
      name: `${kind}-${category}`, include: [`tools/sympy-corpus/compat/${kind}.test.ts`], testTimeout: 600_000,
      provide: { corpusCategory: category, corpusResults: results },
    },
  }));
}

export default defineConfig({
  resolve,
  test: {
    maxWorkers: 2,
    testTimeout: 600_000,
    reporters: ['default', {
      onTestRunStart() {
        start = performance.now();
        for (const kind of ['doctest', 'unittest']) mkdirSync(join(directory, kind), { recursive: true });
      },
      onTestRunEnd() {
        try {
          const units = writeUnittestReport(join(directory, 'unittest'), (performance.now() - start) / 1000);
          const docs = writeDoctestReport(join(directory, 'doctest'));
          if (units || docs) refreshScopeReport();
        } finally {
          rmSync(directory, { recursive: true, force: true });
        }
      },
    }],
    projects: [
      { resolve, test: {
        name: 'harness', testTimeout: 600_000,
        include: ['tools/sympy-corpus/compat/**/*.test.ts', 'tools/sympy-corpus/serialization.test.ts', 'tools/sympy-corpus/unittest-harness.test.ts'],
        exclude: ['tools/sympy-corpus/compat/doctest.test.ts', 'tools/sympy-corpus/compat/unittest.test.ts'],
      } },
      ...projects('doctest'), ...projects('unittest'),
    ],
  },
});
