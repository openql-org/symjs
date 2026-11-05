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
  it('evaluates the entries of a matrix (SymPy MatrixBase.doit)', () => {
    // Matrix([[Integral(x, x), Derivative(x**2, x)]]).doit() -> Matrix([[x**2/2, 2*x]])
    const m = sj.Matrix.of([[new sj.Integral([x!, x!]), new sj.Derivative([sj.pow(x!, 2), x!, sj.S.One])]]);
    expect(s(sj.doit(m))).toBe('Matrix([[x**2/2, 2*x]])');
  });
});

describe('Integral(f, (x, b)): the antiderivative at b', () => {
  const [a, y] = sj.symbols('a y');
  const f = sj.Function('f');
  it('stays unevaluated when the antiderivative is not found (SymPy Integral.doit)', () => {
    expect(s(sj.doit(new sj.Integral([f(x), x, a])))).toBe('Integral(f(x), (x, a))');
    expect(s(sj.doit(new sj.Integral([sj.add(x, f(x)), x, a])))).toBe('Integral(x + f(x), (x, a))');
    expect(s(sj.doit(new sj.Integral([sj.pow(x, 2), x, a])))).toBe('a**3/3');
  });
  it('puts b into the integration limit of indefinite integrals left in the antiderivative', async () => {
    const { antiderivativeAt } = await import('../../src/calculus/doit');
    const v = x as sj.Sym;
    const g = new sj.Integral([sj.exp(sj.pow(x, x)), x]);
    // SymPy: Integral(y*exp(x**x), (x, a)).doit() -> y*Integral(exp(x**x), (x, a))
    expect(s(antiderivativeAt(sj.mul(y, g), v, a))).toBe('y*Integral(exp(x**x), (x, a))');
    // SymPy eval_factored and _eval_interval on x**2/2 + Integral(f(x), x)
    expect(s(antiderivativeAt(sj.add(sj.mul(sj.Rational.of(1, 2), sj.pow(x, 2)), new sj.Integral([f(x), x])), v, a))).toBe(
      'a**2/2 + Integral(f(x), (x, a))',
    );
    // an integral in another variable is an ordinary term
    expect(s(antiderivativeAt(new sj.Integral([sj.mul(x, y), y]), v, a))).toBe('Integral(a*y, y)');
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
