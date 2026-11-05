// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/formal.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse } from '../../src';
import { Expr } from '../../src/core/nodes';

const P = (s: string) => parse(s);
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y] = [V('x'), V('y')];
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v instanceof Expr ? v.toString() : JSON.stringify(v));

describe('fps without a variable', () => {
  it('takes the only free symbol, like SymPy', () => {
    // fps(exp(x)) -> FormalPowerSeries in x; fps(3) -> 3; fps(x*y) -> NotImplementedError
    expect(String(sj.fps(P('exp(x)')))).toBe('FormalPowerSeries(exp(x), x, 0, 1, (SeqFormula(Piecewise((1/factorial(_k), Eq(Mod(_k, 1), 0)), (0, True)), (_k, 1, oo)), SeqFormula(x**_k, (_k, 0, oo)), 1))');
    expect(String(sj.fps(3))).toBe('3');
    expect(() => sj.fps(P('x*y'))).toThrow('multivariate formal power series');
    // a MatrixSymbol is constant (SymPy fps(A) builds FormalPowerSeries(A, A, 0, ...), whose terms cannot be computed)
    expect(String(sj.fps(sj.MatrixSymbol('A', 2, 2)))).toBe('A');
  });
});

describe('formal power series operations', () => {
  const f = (e: string, x0: unknown = 0) => sj.fps(P(e), x, x0 as number);
  it('multiplies, composes and inverts series like SymPy', () => {
    expect(f('sin(x)').product(f('exp(x)'), x).truncate(4).toString()).toBe('x + x**2 + x**3/3 + O(x**4)');
    expect(f('exp(x)').compose(f('sin(x)'), x).truncate().toString()).toBe('1 + x + x**2/2 - x**4/8 - x**5/15 + O(x**6)');
    expect(f('exp(x)').compose(f('sin(x)')).truncate(8).toString()).toBe('1 + x + x**2/2 - x**4/8 - x**5/15 - x**6/240 + x**7/90 + O(x**8)');
    expect(f('exp(x)').inverse().truncate().toString()).toBe('1 - x + x**2/2 - x**3/6 + x**4/24 - x**5/120 + O(x**6)');
    expect(f('cos(x)').inverse().truncate(8).toString()).toBe('1 + x**2/2 + 5*x**4/24 + 61*x**6/720 + O(x**8)');
    expect(() => f('exp(x)').compose(f('cos(x)'), x)).toThrow('The formal power series of the inner function should not have any constant coefficient term.');
    expect(() => f('sin(x)').inverse()).toThrow('Constant coefficient should exist for an inverse of a formal power series to exist.');
    expect(() => f('sin(x)').product(sj.fps(P('exp(y)'), y), x)).toThrow('Both series should have the same symbol.');
    expect(() => f('sin(x)').product(f('exp(x)'), y)).toThrow('Both series should have the same symbol.');
    expect(() => f('sin(x)').product(f('exp(x)', 1), x)).toThrow('Both series should be calculated about the same point.');
  });

  it('integrates series', () => {
    expect(f('sin(x)').integrate(x).truncate().toString()).toBe('-1 + x**2/2 - x**4/24 + O(x**6)');
    expect(f('sin(x)').integrate().truncate().toString()).toBe('-1 + x**2/2 - x**4/24 + O(x**6)');
    expect(f('sin(x)').integrate(x, [0, 1]).toString()).toBe('1 - cos(1)');
  });

  it('keeps a symbolic factor out of the expansion', () => {
    const s = f('x**n*sin(x**2)');
    expect(s.truncate(8).toString()).toBe('-x**(n + 6)/6 + x**(n + 2) + O(x**(n + 8))');
    expect(s.polynomial(8).toString()).toBe('x**(n + 2) - x**(n + 6)/6');
    expect(show(s.terms(2))).toBe('[x**(n + 2), -x**(n + 6)/6]');
    expect(s.coeff(2).toString()).toBe('x**n');
    expect(f('x**n*cos(x)').truncate(4).toString()).toBe('-x**(n + 2)/2 + x**n + O(x**(n + 4))');
    expect(f('a*cos(x)').truncate(4).toString()).toBe('a - a*x**2/2 + O(x**4)');
    // SymPy: a*(-(x - 1)*sin(1) + cos(1)) + O((x - 1)**2, (x, 1)), the same polynomial
    expect(sj.expand(f('a*cos(x)', 1).polynomial(2)).toString()).toBe('-a*x*sin(1) + a*cos(1) + a*sin(1)');
    expect(f('a*cos(x)', 1).truncate(2).toString()).toBe('a*cos(1) - a*(x - 1)*sin(1) + O((x - 1)**2, (x, 1))');
    // SymPy prints the coefficient sequences too
    expect(f('sin(x)').toString()).toBe('FormalPowerSeries(sin(x), x, 0, 1, (SeqFormula(Piecewise(((-1/4)**(_k/2 - 1/2)/(RisingFactorial(3/2, _k/2 - 1/2)*factorial(_k/2 - 1/2)), Eq(Mod(_k, 2), 1)), (0, True)), (_k, 2, oo)), SeqFormula(x**_k, (_k, 0, oo)), x))');
  });
});

describe('coefficient sequence representation', () => {
  it('prints direction, coefficient sequence, power sequence and independent part', () => {
    expect(String(sj.fps(P('cos(x)'), x))).toBe('FormalPowerSeries(cos(x), x, 0, 1, (SeqFormula(Piecewise(((-1/4)**(_k/2)/(RisingFactorial(1/2, _k/2)*factorial(_k/2)), Eq(Mod(_k, 2), 0)), (0, True)), (_k, 1, oo)), SeqFormula(x**_k, (_k, 0, oo)), 1))');
    expect(String(sj.fps(P('exp(x)'), x, 1))).toBe('FormalPowerSeries(exp(x), x, 1, 1, (SeqFormula(Piecewise((E/factorial(_k), Eq(Mod(_k, 1), 0)), (0, True)), (_k, 1, oo)), SeqFormula((x - 1)**_k, (_k, 0, oo)), E))');
    expect(String(sj.fps(P('sin(x)'), x, 0, '-'))).toBe('FormalPowerSeries(sin(x), x, 0, -1, (SeqFormula(Piecewise((-(-1/4)**(_k/2 - 1/2)/(RisingFactorial(3/2, _k/2 - 1/2)*factorial(_k/2 - 1/2)), Eq(Mod(_k, 2), 1)), (0, True)), (_k, 2, oo)), SeqFormula((-x)**_k, (_k, 0, oo)), x))');
    expect(String(sj.fps(P('cos(x)'), x, 0, '-'))).toContain('Piecewise(((-1/4)**(_k/2)/');
  });
  it('prints logarithmic, geometric and binomial coefficient formulas', () => {
    // (-1)^k and 1/(-1)^k agree for every integer sequence index.
    expect(String(sj.fps(P('log(1+x)'), x))).toContain('SeqFormula(-(-1)**_k/_k, (_k, 1, oo))');
    expect(String(sj.fps(P('1/(1-x)'), x))).toBe('FormalPowerSeries(1/(1 - x), x, 0, 1, (SeqFormula(1, (_k, 0, oo)), SeqFormula(x**_k, (_k, 0, oo)), 0))');
    expect(String(sj.fps(P('sqrt(1+x)'), x))).toContain('SeqFormula(binomial(1/2, _k), (_k, 0, oo))');
  });
  it('retains the defining Taylor derivative for coefficients without a closed formula', () => {
    for (const source of ['exp(sin(x))', 'sin(x+1)']) {
      const text = String(sj.fps(P(source), x));
      expect(text).toContain('SeqFormula(Subs(Derivative(');
      expect(text).toContain('/factorial(_k), (_k, 0, oo))');
    }
    expect(String(sj.fps(P('a*exp(sin(x))'), x, 0, '-'))).toContain('SeqFormula((-1)**_k*a*Subs(Derivative(');
  });
  it('does not print Taylor coefficients at a singular expansion point', () => {
    for (const source of ['log(x)', 'x**x', '1/x', 'exp(1/x)']) expect(String(sj.fps(P(source), x))).toBe(source);
    expect(String(sj.fps(x, x))).toBe('FormalPowerSeries(x, x, 0, 1, (SeqFormula(Coeff(x, x, _k), (_k, 1, oo)), SeqFormula(x**_k, (_k, 0, oo)), 0))');
    expect(String(sj.fps(x, x, 1))).toBe('FormalPowerSeries(x, x, 1, 1, (SeqFormula(Coeff(x + 1, x, _k), (_k, 1, oo)), SeqFormula((x - 1)**_k, (_k, 0, oo)), 1))');
    expect(String(sj.fps(P('f(x)'), x))).toBe('f(x)');
  });
  it('represents exponential coefficients on their integer subsequence', () => {
    expect(String(sj.fps(P('exp(x**2)'), x))).toBe('FormalPowerSeries(exp(x**2), x, 0, 1, (SeqFormula(Piecewise((1/factorial(_k/2), Eq(Mod(_k, 2), 0)), (0, True)), (_k, 1, oo)), SeqFormula(x**_k, (_k, 0, oo)), 1))');
    expect(String(sj.fps(P('exp(2*x**3+1)'), x, 0, '-'))).toContain('Piecewise(((-2)**(_k/3)*E/factorial(_k/3), Eq(Mod(_k, 3), 0))');
  });
});
