// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/formal.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse } from '../../src';
import { Expr } from '../../src/core/nodes';
import { readFileSync } from 'node:fs';
import { runTestCase } from '../../../../tools/sympy-corpus/tests-harness';
import type { TestCase } from '../../../../tools/sympy-corpus/tests-harness';

const P = (s: string) => parse(s);
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y] = [V('x'), V('y')];

describe('rationalAlgorithm', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('../../../../tools/sympy-corpus/tests-corpus/series.json', import.meta.url), 'utf8'));
  it.each(cases.filter((c) => c.fn === 'rational_algorithm'))('matches the upstream coefficient formula at line $line', (c) => {
    expect(['pass', 'equivalent']).toContain(runTestCase(c).status);
  });
  it('separates Laurent terms and rejects finite polynomials', () => {
    const k = V('k');
    const result = sj.rationalAlgorithm(P('1/x**2 + 1/(1-x)'), x, k);
    expect(Array.isArray(result) ? result.map(String) : result).toEqual(['1', 'x**(-2)', '0']);
    expect(sj.rationalAlgorithm(P('x + 1'), x, k)).toBe(sj.NoMatch);
    expect(sj.rationalAlgorithm(P('cos(x)'), x, k, 0)).toBe(sj.NoMatch);
  });
});
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
  it('shares SeriesBase indexing, including zero terms, and rebuilds expressions', () => {
    const series = f('sin(x)');
    expect(series).toBeInstanceOf(sj.SeriesBase);
    expect(sj.str(series)).toBe(series.toString());
    expect([series.start, series.stop, series.length, series.interval].map(String)).toEqual(['0', 'oo', 'oo', 'Interval(0, oo)']);
    expect(series.slice(0, 5).map(String)).toEqual(['0', 'x', '0', '-x**3/6', '0']);
    expect(series.slice(3, -1, -1).map(String)).toEqual(['-x**3/6', '0', 'x', '0']);
    const iterator = series[Symbol.iterator]();
    expect([iterator.next().value, iterator.next().value].map(String)).toEqual(['0', 'x']);
    expect(f('1 + x + x**2').slice(0, 5).map(String)).toEqual(['1', 'x', 'x**2', '0', '0']);
    expect(f('x**n*sin(x**2)').slice(0, 4).map(String)).toEqual(['0', '0', 'x**(n + 2)', '0']);
    expect(f('1/x + exp(x)').slice(0, 3).map(String)).toEqual(['1 + 1/x', 'x', 'x**2/2']);
    expect([...sj.freeSymbols(f('a*cos(x)', y))].map(String).sort()).toEqual(['a', 'x', 'y']);
    for (const direction of ['+', '-'] as const) {
      const shifted = sj.fps(sj.mul(y, sj.exp(x)), x, 1, direction);
      const rebuilt = sj.subs(shifted, [[y, 2]]);
      expect(rebuilt).toBeInstanceOf(sj.FormalPowerSeries);
      if (!(rebuilt instanceof sj.FormalPowerSeries)) throw new TypeError('FormalPowerSeries');
      expect(rebuilt.direction).toBe(direction);
      expect(rebuilt.slice(0, 3).map(String)).toEqual(['2*E', '2*E*(x - 1)', 'E*(x - 1)**2']);
    }
    expect(() => series.term(-1)).toThrow(RangeError);
    expect(() => series.term(sj.Rational.of(1, 2))).toThrow(TypeError);
    expect(() => series.term(new Sym('k', { nonnegative: true }))).toThrow(TypeError);
    expect(() => series.term(Number.MAX_SAFE_INTEGER + 1)).toThrow(TypeError);
  });

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

it('constructs normalized exponential and ordinary coefficient recurrences', () => {
  const r = sj.SymFunction('r'), k = V('k');
  expect(String(sj.expRe(P('-f(x) + Derivative(f(x), x)'), r, k))).toBe('-r(k) + r(k + 1)');
  expect(String(sj.expRe(P('Derivative(f(x), x) + Derivative(f(x), (x, 2))'), r, k))).toBe('r(k) + r(k + 1)');
  expect(String(sj.hyperRe(P('-f(x) + Derivative(f(x), x)'), r, k))).toBe('(k + 1)*r(k + 1) - r(k)');
  expect(String(sj.hyperRe(P('-x*f(x) + Derivative(f(x), (x, 2))'), r, k))).toBe('(k + 2)*(k + 3)*r(k + 3) - r(k)');
  expect(String(sj.expRe(P('f(x)'), r, k))).toBe('r(k)');
  expect(() => sj.expRe(P('x*f(x)'), r, k)).toThrow(TypeError);
  expect(() => sj.expRe(1, r, k)).toThrow(TypeError);
  expect(() => sj.hyperRe(P('sin(x)*f(x)'), r, k)).toThrow(TypeError);
  expect(sj.rationalIndependent([], V('x'))).toEqual([]);
  expect(sj.rationalIndependent([P('cos(x)'), P('sin(x)')], V('x')).map(String)).toEqual(['cos(x)', 'sin(x)']);
  expect(sj.rationalIndependent([P('x**2'), P('sin(x)'), P('x*sin(x)'), P('x**3')], V('x')).map(String)).toEqual(['x**3 + x**2', 'x*sin(x) + sin(x)']);
});

it('discovers rational differential equations and solves hypergeometric recurrences', () => {
  const k = V('k'), g = sj.SymFunction('g');
  for (const [source, initial, start] of [['exp(x)', '1', 1], ['log(1+x)', 'x', 2], ['sin(x)', 'x', 2], ['cos(x)', '1', 1]] as const) {
    const result = sj.hyperAlgorithm(P(source), x, k);
    expect(sj.isNoMatch(result)).toBe(false);
    if (sj.isNoMatch(result)) continue;
    expect(String(result[1])).toBe(initial); expect(result[2]).toBe(start);
    for (let n = start; n < 9; n++) {
      const coefficient = sj.simplify(sj.subs(result[0], [[k,n]]));
      expect(sj.simplify(coefficient.sub(sj.fps(P(source), x).coeff(n))).equals(0)).toBe(true);
    }
  }
  const [de, order] = [...sj.simpleDE(P('log(1+x)'), x, g, 2)][0]!;
  expect(order).toBe(2);
  const sol = sj.solveDe(P('log(1+x)'), x, de, order, g, k);
  expect(String(Array.isArray(sol) ? sol[0] : sol)).toBe('Piecewise(((-1)**(k - 1)*factorial(k - 1)/RisingFactorial(2, k - 1), Eq(Mod(k, 1), 0)), (0, True))');
  expect([...sj.simpleDE(P('exp(sin(x))'), x, g, 1)]).toEqual([]);
  expect([...sj.simpleDE(P('x**2'), x, g, 3)].length).toBeGreaterThan(0);
});
it('returns NoMatch when a DE has no supported hypergeometric coefficient form', () => {
  const k = V('k'), g = sj.SymFunction('g');
  expect(sj.hyperAlgorithm(P('exp(sin(x))'), x, k, 1)).toBe(sj.NoMatch);
  expect(sj.hyperAlgorithm(1, x, k, 1)).toBe(sj.NoMatch);
  expect(sj.solveDe(0, x, P('g(x)'), 1, g, k)).toBe(sj.NoMatch);
  expect(sj.solveDe(0, x, P('Derivative(g(x), x)-g(x)'), 1, g, k)).toBe(sj.NoMatch);
  expect(sj.solveDe(P('exp(1/x)'), x, P('x**2*Derivative(g(x), x)+g(x)'), 1, g, k)).toBe(sj.NoMatch);
  expect(sj.solveDe(P('sqrt(x)'), x, P('2*x*Derivative(g(x), (x, 2))+Derivative(g(x), x)'), 2, g, k)).toBe(sj.NoMatch);
  expect(sj.solveDe(0, x, P('(x**5+x+1)*g(x)+Derivative(g(x),x)'), 1, g, k)).toBe(sj.NoMatch);
  expect(() => sj.solveDe(1, x, g(x), 0, g, k)).toThrow(RangeError);
});
it('handles sums during DE discovery and unsupported recurrence factorizations', () => {
  const k = V('k'), g = sj.SymFunction('g');
  expect([...sj.simpleDE(P('exp(x)+sin(x)'), x, g, 3)].length).toBe(1);
  expect(sj.solveDe(0,x,P('x*Derivative(g(x),(x,2))+Derivative(g(x),x)/2-g(x)'),2,g,k)).toBe(sj.NoMatch);
  expect(sj.solveDe(0,x,P('x**5*Derivative(g(x),(x,5))+10*x**4*Derivative(g(x),(x,4))+25*x**3*Derivative(g(x),(x,3))+15*x**2*Derivative(g(x),(x,2))+g(x)+Derivative(g(x),x)'),5,g,k)).toBe(sj.NoMatch);
});
it('declines recurrences with unresolved denominator roots', () => {
  const k = V('k'), g = sj.SymFunction('g');
  const de = sj.add(g(x), ...[-29,210,-285,125,-20,1].map((c,i) => sj.mul(c, x.pow(i), sj.diff(g(x),x,i+1))));
  expect(sj.solveDe(0,x,de,6,g,k)).toBe(sj.NoMatch);
});
