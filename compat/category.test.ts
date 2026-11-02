// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// The cases of one category that do not pass: CAT=<category> pnpm -s compat:category
import { test } from 'vitest';
import { appendFileSync, readFileSync, writeFileSync } from 'node:fs';
import { runCase } from './harness';
test.skipIf(process.env['CAT'] === undefined)('category', () => {
  const corpus = JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8'));
  const cat = process.env['CAT'] ?? 'assumptions';
  const out: string[] = [];
  for (const c of corpus.cases.filter((x: { category: string }) => x.category === cat)) {
    if (process.env['TRACE']) appendFileSync(process.env['TRACE'], `${c.src}\n`);
    const t0 = Date.now();
    const r = runCase(c);
    if (process.env['TRACE']) appendFileSync(process.env['TRACE'], `  ${Date.now() - t0}ms\n`);
    out.push([r.status, c.src, '=>', c.expected, '|', 'got' in r ? r.got : 'reason' in r ? r.reason : ''].join(' '));
  }
  writeFileSync(process.env['OUT'] ?? '/dev/stdout', out.join('\n') + '\n');
});
