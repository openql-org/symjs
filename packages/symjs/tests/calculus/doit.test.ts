// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/calculus/doit.ts.
// Evaluation of unevaluated derivatives (doit). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x] = sj.symbols('x');

const s = (e: unknown): string => String(e);

describe('doit and finite differences', () => {
  it('evaluates limits', () => {
    expect(s(sj.doit(new sj.Limit([sj.mul(sj.sin(x), sj.pow(x, -1)), x, sj.S.Zero])))).toBe('1');
  });
});
