// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/more.ts.
// Orders, leading terms and the remaining series helpers. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse } from '../../src';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';

// Remaining branches of the limit, series and summation code. Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y, z, n, k, a, b, c, m, t] = [V('x'), V('y'), V('z'), V('n'), V('k'), V('a'), V('b'), V('c'), V('m'), V('t')];
const [pp, qq, rr] = [V('p'), V('q'), V('r')];
const show = (v: unknown): string =>
  Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v === undefined ? 'None' : v instanceof Expr || v instanceof NoMatchResult ? v.toString() : typeof v === 'string' ? v : JSON.stringify(v);
const pw = (e: unknown): sj.Piecewise => {
  if (!(e instanceof sj.Piecewise)) throw new TypeError('a Piecewise expected');
  return e;
};
/** The result, or the class name and message of what it throws. */
const run = (f: () => unknown): string => {
  try {
    return show(f());
  } catch (e) {
    return e instanceof Error ? `ERR ${e.constructor.name}: ${e.message}` : 'ERR';
  }
};
const conc = (e: unknown): sj.Concrete => {
  if (!(e instanceof sj.Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const conv = (e: unknown) => sj.isConvergent(conc(e));
const aconv = (e: unknown) => sj.isAbsolutelyConvergent(conc(e));
const moo = P('-oo');
void [x, y, z, n, k, a, b, c, m, t, pp, qq, rr, conv, aconv, moo, pw];

describe('results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["(() => { const it = sj.lseries(P('sqrt(x)*(1 + x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 2) break; } return o; })()", () => (() => { const it = sj.lseries(P('sqrt(x)*(1 + x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 2) break; } return o; })(), "[I*sqrt(-x), -I*(-x)**(3/2)]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

// Series, orders and leading terms (series/series.ts, series/more.ts, series/puiseux.ts). Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

describe('results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[...sj.lseries(P('x**2 + x'), x, 1)]", () => [...sj.lseries(P('x**2 + x'), x, 1)], "[2, 3*x - 3, (x - 1)**2]"],
    ["(() => { const it = sj.lseries(P('sin(x)'), x); const o = []; for (const u of it) { o.push(u); if (o.length >= 5) break; } return o; })()", () => (() => { const it = sj.lseries(P('sin(x)'), x); const o = []; for (const u of it) { o.push(u); if (o.length >= 5) break; } return o; })(), "[x, -x**3/6, x**5/120, -x**7/5040, x**9/362880]"],
    ["(() => { const it = sj.lseries(P('1/(1 - x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 4) break; } return o; })()", () => (() => { const it = sj.lseries(P('1/(1 - x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 4) break; } return o; })(), "[1, x, x**2, x**3]"],
    ["sj.dir(P('sqrt(x)'), x, 1)", () => sj.dir(P('sqrt(x)'), x, 1), "1/2"],
    ["sj.dir(P('x*log(x)'), x, 1)", () => sj.dir(P('x*log(x)'), x, 1), "-oo"],
    ["sj.dir(P('sin(x)/x - 1'), x, 1)", () => sj.dir(P('sin(x)/x - 1'), x, 1), "-1/3"],
    ["sj.dir(P('x**2 + x**3'), x, -1)", () => sj.dir(P('x**2 + x**3'), x, -1), "2"],
    ["sj.dir(P('0'), x, 1)", () => sj.dir(P('0'), x, 1), "0"],
    ["sj.dir(P('x**(3/2)*log(x)'), x, 1)", () => sj.dir(P('x**(3/2)*log(x)'), x, 1), "-oo"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // SymPy 1.14 raises AttributeError for a polynomial
    ["[...sj.lseries(P('x**2'), x)]", () => [...sj.lseries(P('x**2'), x)], "[x**2]", "ERR AttributeError"],
    // AccumBounds are not implemented
    ["sj.dir(P('sqrt(x)*(2 + sin(1/x))'), x, 1)", () => sj.dir(P('sqrt(x)*(2 + sin(1/x))'), x, 1), "Limit((sin(1/x) + 2)/(2*sqrt(x)) - cos(1/x)/x**(3/2), x, 0, dir='+')", "oo*sign(AccumBounds(-1, 1))"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('dir when the leading term of a derivative is not found', () => {
  it('takes the limit of the derivative', () => {
    // the derivative is zoo at 0 and gamma(1/x) has an essential singularity there, so the leading term
    // is not found and the limit is taken. Deliberate difference: SymPy evaluates gamma(1/x) at x = 0 and
    // returns zoo*gamma(zoo)*polygamma(0, zoo) + zoo*gamma(zoo) (and zoo*gamma(zoo)*polygamma(0, zoo) + zoo),
    // which is not a direction; the derivatives tend to oo (and -oo) as x -> 0+
    expect(sj.dir(P('log(x)*gamma(1/x)'), x, 1).toString()).toBe('oo');
    expect(sj.dir(P('1/x + gamma(1/x)'), x, 1).toString()).toBe('-oo');
  });
  it('takes the limit when the derivative has a power with an irrational exponent', () => {
    // the expansion of x**sqrt(2) is not found (SymPy 1.14 gives the same limits)
    expect(sj.dir(P('log(x) + x**sqrt(2)'), x, 1).toString()).toBe('oo');
    expect(sj.dir(P('x*log(x) + x**(1 + sqrt(2))'), x, 1).toString()).toBe('-oo');
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
    expect(f('sin(x)').toString()).toBe('FormalPowerSeries(sin(x), x, 0)');
  });
});

describe('Fourier series operations', () => {
  const s = () => sj.fourierSeries(P('x**2'), x);
  it('shifts and scales like SymPy', () => {
    expect(s().shiftx(1).truncate().toString()).toBe('-4*cos(x + 1) + cos(2*x + 2) + pi**2/3');
    expect(s().scalex(2).truncate().toString()).toBe('-4*cos(2*x) + cos(4*x) + pi**2/3');
    expect(s().shift(1).truncate().toString()).toBe('-4*cos(x) + cos(2*x) + 1 + pi**2/3');
    expect(s().scale(2).truncate().toString()).toBe('-8*cos(x) + 2*cos(2*x) + 2*pi**2/3');
    expect(s().shift(1).scale(2).truncate().toString()).toBe('-8*cos(x) + 2*cos(2*x) + 2 + 2*pi**2/3');
    expect(s().scale(2).shift(1).truncate().toString()).toBe('-8*cos(x) + 2*cos(2*x) + 1 + 2*pi**2/3');
    expect(s().scalex(2).shiftx(1).truncate().toString()).toBe('-4*cos(2*x + 2) + cos(4*x + 4) + pi**2/3');
    expect(s().shiftx(1).fn.toString()).toBe('(x + 1)**2');
    expect(s().scalex(2).fn.toString()).toBe('4*x**2');
    for (const op of ['shift', 'scale', 'shiftx', 'scalex'] as const) expect(() => s()[op](x)).toThrow("'x' should be independent of x");
  });

  it('gives sigma approximations like SymPy', () => {
    expect(sj.fourierSeries(x, x).truncate(4).toString()).toBe('2*sin(x) - sin(2*x) + 2*sin(3*x)/3 - sin(4*x)/2');
    expect(sj.fourierSeries(x, x).sigmaApproximation(4).toString()).toBe('2*sin(x)*sinc(pi/4) - 2*sin(2*x)/pi + 2*sin(3*x)*sinc(3*pi/4)/3');
    expect(sj.fourierSeries(x, x).sigmaApproximation().toString()).toBe('2*sin(x)*sinc(pi/3) - sin(2*x)*sinc(2*pi/3)');
    expect(s().sigmaApproximation(3).toString()).toBe('-4*cos(x)*sinc(pi/3) + cos(2*x)*sinc(2*pi/3) + pi**2/3');
  });
});
