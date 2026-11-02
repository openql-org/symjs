// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// The cases of one category that do not pass: CAT=<category> pnpm -s compat:category
import { test } from 'vitest';
import { readFileSync, writeFileSync } from 'node:fs';
import { runCase } from './harness';
test.skipIf(process.env['CAT'] === undefined)('category', () => {
  const corpus = JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8'));
  const cat = process.env['CAT'] ?? 'assumptions';
  const out: string[] = [];
  for (const c of corpus.cases.filter((x: { category: string }) => x.category === cat)) {
    const r = runCase(c);
    out.push([r.status, c.src, '=>', c.expected, '|', 'got' in r ? r.got : 'reason' in r ? r.reason : ''].join(' '));
  }
  writeFileSync(process.env['OUT'] ?? '/dev/stdout', out.join('\n') + '\n');
});
