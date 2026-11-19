// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Inspect doctest outcomes in one category: CAT=<category> vitest run --config tools/sympy-corpus/compat/vitest.config.ts category.test.ts
import { test } from 'vitest';
import { appendFileSync, writeFileSync } from 'node:fs';
import { readCases } from '../corpus';
import { runCase } from '../harness';
test.skipIf(process.env['CAT'] === undefined)('category', () => {
  const cat = process.env['CAT'] ?? 'assumptions';
  const out: string[] = [];
  for (const c of readCases('doctest', cat)) {
    if (process.env['TRACE']) appendFileSync(process.env['TRACE'], `${c.src}\n`);
    const t0 = Date.now();
    const r = runCase(c);
    if (process.env['TRACE']) appendFileSync(process.env['TRACE'], `  ${Date.now() - t0}ms\n`);
    out.push([r.status, c.src, '=>', c.expected, '|', 'got' in r ? r.got : 'reason' in r ? r.reason : ''].join(' '));
  }
  writeFileSync(process.env['OUT'] ?? '/dev/stdout', out.join('\n') + '\n');
});
