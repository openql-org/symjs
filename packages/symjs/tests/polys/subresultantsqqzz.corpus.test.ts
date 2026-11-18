// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { runTestCase, type TestCase } from '../../../../tools/sympy-corpus/tests-harness';

const cases: TestCase[] = JSON.parse(readFileSync(new URL('../../../../tools/sympy-corpus/tests-corpus/polys.json', import.meta.url), 'utf8'));
for (const [index, c] of cases.filter((c) => c.module === 'sympy.polys.tests.test_subresultants_qq_zz').entries()) {
  it(`${c.test}:${c.line} (${index})`, () => {
    expect(['pass', 'equivalent']).toContain(runTestCase(c).status);
  });
}
