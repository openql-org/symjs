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

describe('evalConcreteValue', () => {
  it('the value of a sum with finite integer limits, for evalf', async () => {
    const { evalConcreteValue } = await import('../../src/calculus/doit');
    const [k, n] = sj.symbols('k n', { integer: true }) as [sj.Sym, sj.Sym];
    const c = (e: sj.Expr) => e as sj.Concrete;
    expect(s(evalConcreteValue(c(sj.Sum(k, [k, 1, 3]))))).toBe('6');
    expect(evalConcreteValue(c(sj.Sum(k, [k, 1, n])))).toBeUndefined();
    expect(evalConcreteValue(c(sj.Sum(k, [k, 1, 5000])))).toBeUndefined();
    expect(evalConcreteValue(c(sj.Sum(k.mul(x), [k, 1, 3])))).toBeUndefined();
  });
});
