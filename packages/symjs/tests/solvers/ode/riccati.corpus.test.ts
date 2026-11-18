// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { runTestCase } from '../../../../../tools/sympy-corpus/tests-harness';
import type { TestCase } from '../../../../../tools/sympy-corpus/tests-harness';

const cases: TestCase[] = JSON.parse(readFileSync(new URL('../../../../../tools/sympy-corpus/tests-corpus/solvers.json', import.meta.url), 'utf8'));
for (const [i, c] of cases.filter((c) => c.module === 'sympy.solvers.ode.tests.test_riccati').entries()) {
  it(`${c.test}:${c.line} (${i})`, () => {
    expect(['pass', 'equivalent']).toContain(runTestCase(c).status);
  });
}
