// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { runTestCase, type TestCase } from '../tests-harness';
import { runCase, type Case } from '../harness';

const cases: TestCase[] = JSON.parse(readFileSync(new URL('../tests-corpus/polys.json', import.meta.url), 'utf8'));
for (const c of cases.filter((c) => /test_eigen$|test_linsolve$/.test(c.module) || c.test === 'test_fglm')) {
  it(`${c.module}:${c.test}:${c.line}:${cases.indexOf(c)}`, () => {
    const outcome = runTestCase(c);
    expect(['pass', 'equivalent'], JSON.stringify(outcome)).toContain(outcome.status);
  });
}
const doctests: { cases: Case[] } = JSON.parse(readFileSync(new URL('../corpus.json', import.meta.url), 'utf8'));
for (const c of doctests.cases.filter((c) => c.module === 'sympy.polys.matrices.linsolve')) {
  it(c.src, () => {
    const outcome = runCase(c);
    expect(['pass', 'equivalent'], JSON.stringify(outcome)).toContain(outcome.status);
  });
}
