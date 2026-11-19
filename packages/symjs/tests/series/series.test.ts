// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/series.ts.
// Series expansion. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse, DiracDelta, Heaviside, series, symbol, sstr, symbols } from '../../src';
import { SeriesError } from '../../src/series/puiseux';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';
import { readFileSync } from 'node:fs';
import { runTestCase, testCaseKey } from '../../../../tools/sympy-corpus/tests-harness';
import type { TestCase } from '../../../../tools/sympy-corpus/tests-harness';
import orderCaseIds from './order-case-ids.json';

describe('Order upstream regressions', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('../../../../tools/sympy-corpus/tests-corpus/series.json', import.meta.url), 'utf8'));
  const ids = new Set(orderCaseIds);
  it.each(cases.filter((c) => ids.has(testCaseKey(c))))('$test:$line', (c) => {
    expect(['pass', 'equivalent']).toContain(runTestCase(c).status);
  });
});

it('propagates accumulation bounds through exponential leading terms', () => {
  const x = symbol('x');
  expect(sstr(sj.asLeadingTerm(parse('exp(x*log(cos(1/x) + 2))'), x))).toBe('1');
  expect(sstr(sj.asLeadingTerm(parse('exp(x*log(sin(1/x)**2))'), x))).toBe('AccumBounds(0, 1)');
  expect(sj.asLeadingTerm(parse('log(cos(1/x) - 2)'), x)).toBe(sj.S.NaN);
  expect(sstr(sj.asLeadingTerm(parse('log(2*cos(1/x) + 3)'), x))).toBe('AccumBounds(0, log(5))');
  expect(sstr(sj.asLeadingTerm(parse('exp(x*log(sin(1/x)**2))'), x, { cdir: -1 }))).toBe('AccumBounds(1, oo)');
  expect(sstr(sj.asLeadingTerm(parse('exp(x*log(sin(1/x)**2))'), x, { cdir: sj.S.Zero }))).toBe('AccumBounds(0, 1)');
  const constantPower = new sj.Pow(parse('sin(1/x)'), sj.S.Zero);
  const rawLog = sj.fn('log', [constantPower], { evaluate: false });
  expect(sj.asLeadingTerm(new sj.Pow(sj.S.E, new sj.Mul([x, rawLog])), x).equals(sj.S.One)).toBe(true);
});

it('leaves nonconstant scaling of oscillatory bounds to the general series machinery', () => {
  const x = symbol('x');
  for (const source of [
    'log(cos(1/x) + x)',
    'log(cos(1/x)**x)',
    'exp(log(cos(1/x) + 2)/x)',
    'exp(y*x*log(sin(1/x)**2))',
  ]) expect(() => sj.asLeadingTerm(parse(source), x)).toThrow(/essential singularity/);
});

it('uses the direction of an argument and preserves its zero-order remainder', () => {
  const x = symbol('x');
  const phase = sj.arg(x);
  expect(sj.asLeadingTerm(phase, x)).toBe(sj.S.Zero);
  expect(sj.asLeadingTerm(phase, x, { cdir: sj.S.Zero })).toBe(sj.S.Zero);
  expect(sj.asLeadingTerm(phase, x, { cdir: -1 })).toBe(sj.pi);
  expect(sstr(series(phase, x, 0, 0))).toBe('O(1)');
  expect(series(sj.sign(x), x, 0, 0).equals(sj.S.One)).toBe(true);
  expect(series(new sj.Add([sj.abs(x), sj.mul(-1, x)]), x, 0, 0).equals(sj.S.Zero)).toBe(true);
  expect(() => sj.asLeadingTerm(parse('sin(x + x**2)'), x, { cdir: sj.I })).toThrow(/nonreal direction/);
  const p = sj.Piecewise([1, sj.Lt(x, -1)], [sj.sin(x), true]);
  expect(sj.asLeadingTerm(p, x).equals(x)).toBe(true);
});

it('expands logarithms along the positive imaginary ray at infinity', () => {
  const x = symbol('x');
  expect(sstr(series(parse('log(1 + x)'), x, sj.mul(sj.S.Infinity, sj.S.I), 2)))
    .toBe('1/x + I*pi/2 - log(I/x) + O(x**(-2), (x, oo*I))');
});

// Series, orders and leading terms (series/series.ts, series/more.ts, series/puiseux.ts). Expected values are the str() forms printed by SymPy 1.14
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

describe('special-function local and asymptotic series', () => {
  it.each([
    ['besselj(0, x**1.1)', 4, '1 - x**2.2/4 + O(x**4)'],
    ['besselj(2, sin(x))', 4, '(-x**3/12 + x/2)**2/2 + O(x**4)'],
    ['besselk(1/2, x**2)', 2, 'sqrt(2)*sqrt(pi)/(2*x) - sqrt(2)*sqrt(pi)*x/2 + O(x**2)'],
    ['besselk(2, x)', 1, '2/x**2 - 1/2 + O(x)'],
    ['bessely(0, log(1+x))', 3, '2*EulerGamma/pi - 2*log(2)/pi + 2*log(x)/pi - x/pi + x**2*(-log(x)/(2*pi) + (2 - 2*EulerGamma)/(4*pi) + log(2)/(2*pi) + 5/(12*pi)) + O(x**3*log(x))'],
    ['expint(1, x)', 4, '-EulerGamma - log(x) + x - x**2/4 + x**3/18 + O(x**4)'],
    ['polylog(3/2, -x)', 4, '-x + sqrt(2)*x**2/4 - sqrt(3)*x**3/9 + O(x**4)'],
    ['polygamma(3, 1/x)', 4, '2*x**3 + O(x**4)'],
    ['li(x)', 2, 'x*(1/log(x) + 1 + O(log(x)**(-2)))/log(x)'],
  ] as const)('expands %s at zero', (f, n, expected) => {
    expect(String(series(P(f), x, 0, n))).toBe(expected);
  });

  it.each([
    ['besseli(0, x)', 2, 'sqrt(2)*(sqrt(1/x) + (1/x)**(3/2)/8 + O((1/x)**(5/2), (x, oo)))*exp(x)/(2*sqrt(pi))'],
    ['erf(x)', 4, '-(-1/(2*x**3) + 1/x + O(x**(-4), (x, oo)))*exp(-x**2)/sqrt(pi) + 1'],
    ['erfi(x)', 4, '(1/(2*x**3) + 1/x + O(x**(-4), (x, oo)))*exp(x**2)/sqrt(pi) - I'],
    ['Ci(x)', 4, '-(x**(-2) + O(x**(-4), (x, oo)))*cos(x) + (-2/x**3 + 1/x + O(x**(-4), (x, oo)))*sin(x)'],
    ['fresnelc(x)', 4, '-cos(pi*x**2/2)/(pi**2*x**3) + sin(pi*x**2/2)/(pi*x) + 1/2 + O(x**(-4), (x, oo))'],
  ] as const)('expands %s at infinity', (f, n, expected) => {
    expect(String(series(P(f), x, sj.oo, n))).toBe(expected);
  });

  it('finds leading terms across singular points', () => {
    expect(sj.asLeadingTerm(P('besselk(1, sin(x))'), x).equals(P('1/x'))).toBe(true);
    expect(sj.asLeadingTerm(P('bessely(-1/2, x)'), x).equals(P('sqrt(2)*sqrt(x)/sqrt(pi)'))).toBe(true);
    expect(sj.asLeadingTerm(P('erf(1/x)'), x).equals(1)).toBe(true);
    expect(sj.asLeadingTerm(P('erfc(1/x)'), x).equals(0)).toBe(true);
    expect(sj.asLeadingTerm(sj.SingularityFunction(x, 3, 2), x).equals(0)).toBe(true);
    expect(sj.asLeadingTerm(sj.SingularityFunction(x, 0, 0), x).equals(1)).toBe(true);
    expect(sj.asLeadingTerm(sj.SingularityFunction(x, 0, 0), x, { cdir: -1 }).equals(0)).toBe(true);
  });
});
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
    ["sj.O(P('x**2 + x'), [x])", () => sj.O(P('x**2 + x'), [x]), "O(x)"],
    ["sj.O(P('x**2 + x*y'), [x, y])", () => sj.O(P('x**2 + x*y'), [x, y]), "O(x**2 + x*y, x, y)"],
    ["sj.O(P('x*y'), [x, y])", () => sj.O(P('x*y'), [x, y]), "O(x*y, x, y)"],
    ["sj.O(P('x**2 + y'), [x, y], sj.oo)", () => sj.O(P('x**2 + y'), [x, y], sj.oo), "O(x**2 + y, (x, oo), (y, oo))"],
    ["sj.O(P('x**3 + x'), x, sj.oo)", () => sj.O(P('x**3 + x'), x, sj.oo), "O(x**3, (x, oo))"],
    ["sj.O(P('exp(x)'), x, sj.oo)", () => sj.O(P('exp(x)'), x, sj.oo), "O(exp(x), (x, oo))"],
    ["sj.O(P('cos(x)'), x, P('pi/2'))", () => sj.O(P('cos(x)'), x, P('pi/2')), "O(x - pi/2, (x, pi/2))"],
    ["sj.series(P('1/x'), x, sj.oo, 0)", () => sj.series(P('1/x'), x, sj.oo, 0), "O(1, (x, oo))"],
    ["sj.series(P('1/(1 + x)'), x, sj.oo, 3)", () => sj.series(P('1/(1 + x)'), x, sj.oo, 3), "-1/x**2 + 1/x + O(x**(-3), (x, oo))"],
    ["sj.series(P('1/(1 + x)'), x, P('-oo'), 3)", () => sj.series(P('1/(1 + x)'), x, P('-oo'), 3), "-1/x**2 + 1/x + O(-1/x**3, (x, -oo))"],
    ["sj.series(P('1/(x + 1)'), x, sj.oo, 2)", () => sj.series(P('1/(x + 1)'), x, sj.oo, 2), "1/x + O(x**(-2), (x, oo))"],
    ["sj.series(P('x/(x + 1)'), x, sj.oo, 1)", () => sj.series(P('x/(x + 1)'), x, sj.oo, 1), "1 + O(1/x, (x, oo))"],
    ["sj.series(P('5'), x, 1)", () => sj.series(P('5'), x, 1), "5"],
    ["sj.series(P('sinc(x)'), x, 0, 5)", () => sj.series(P('sinc(x)'), x, 0, 5), "1 - x**2/6 + x**4/120 + O(x**5)"],
    ["sj.series(P('cot(x)'), x, 0, 4)", () => sj.series(P('cot(x)'), x, 0, 4), "1/x - x/3 - x**3/45 + O(x**4)"],
    ["sj.series(P('csc(x)'), x, 0, 4)", () => sj.series(P('csc(x)'), x, 0, 4), "1/x + x/6 + 7*x**3/360 + O(x**4)"],
    ["sj.series(P('tan(x)'), x, P('pi/2'), 3)", () => sj.series(P('tan(x)'), x, P('pi/2'), 3), "-1/(x - pi/2) - pi/6 + x/3 + O((x - pi/2)**3, (x, pi/2))"],
    ["sj.series(P('coth(x)'), x, 0, 4)", () => sj.series(P('coth(x)'), x, 0, 4), "1/x + x/3 - x**3/45 + O(x**4)"],
    ["sj.series(P('sec(x)'), x, P('pi/2'), 2)", () => sj.series(P('sec(x)'), x, P('pi/2'), 2), "-1/(x - pi/2) + pi/12 - x/6 + O((x - pi/2)**2, (x, pi/2))"],
    ["sj.series(P('LambertW(x)'), x, 0, 5)", () => sj.series(P('LambertW(x)'), x, 0, 5), "x - x**2 + 3*x**3/2 - 8*x**4/3 + O(x**5)"],
    ["sj.series(P('acosh(1 + x)'), x, 0, 3)", () => sj.series(P('acosh(1 + x)'), x, 0, 3), "sqrt(2)*sqrt(x) - sqrt(2)*x**(3/2)/12 + 3*sqrt(2)*x**(5/2)/160 + O(x**3)"],
    ["sj.series(P('acosh(x)'), x, -1, 2)", () => sj.series(P('acosh(x)'), x, -1, 2), "I*pi - sqrt(2)*I*sqrt(x + 1) - sqrt(2)*I*(x + 1)**(3/2)/12 + O((x + 1)**2, (x, -1))"],
    ["sj.series(P('sign(x)'), x, 0, 3)", () => sj.series(P('sign(x)'), x, 0, 3), "1"],
    ["sj.series(P('sign(1 + x)'), x, 0, 3)", () => sj.series(P('sign(1 + x)'), x, 0, 3), "1"],
    ["sj.series(P('sign(-x + x**2)'), x, 0, 3)", () => sj.series(P('sign(-x + x**2)'), x, 0, 3), "-1"],
    ["sj.series(P('abs(x)'), x, 0, 3)", () => sj.series(P('abs(x)'), x, 0, 3), "x"],
    ["sj.series(P('abs(-x + x**2)'), x, 0, 3)", () => sj.series(P('abs(-x + x**2)'), x, 0, 3), "-x**2 + x"],
    ["sj.series(P('floor(x + 1/2)'), x, 0, 3)", () => sj.series(P('floor(x + 1/2)'), x, 0, 3), "0"],
    ["sj.series(P('floor(sin(x))'), x, 0, 3)", () => sj.series(P('floor(sin(x))'), x, 0, 3), "0"],
    ["sj.series(P('floor(-sin(x))'), x, 0, 3)", () => sj.series(P('floor(-sin(x))'), x, 0, 3), "-1"],
    ["sj.series(P('gamma(x)'), x, 0, 2)", () => sj.series(P('gamma(x)'), x, 0, 2), "1/x - EulerGamma + x*(EulerGamma**2/2 + pi**2/12) + O(x**2)"],
    ["sj.series(P('gamma(x)'), x, -1, 1)", () => sj.series(P('gamma(x)'), x, -1, 1), "-1/(x + 1) + EulerGamma - 1 + O(x + 1, (x, -1))"],
    ["sj.series(P('(x + x**2)**(1/2)'), x, 0, 2)", () => sj.series(P('(x + x**2)**(1/2)'), x, 0, 2), "sqrt(x) + x**(3/2)/2 + O(x**2)"],
    ["sj.series(P('(1 + x)**y'), x, 0, 3)", () => sj.series(P('(1 + x)**y'), x, 0, 3), "1 + x*y + x**2*y*(y - 1)/2 + O(x**3)"],
    ["sj.series(P('(x + y)**(1/2)'), x, 0, 2)", () => sj.series(P('(x + y)**(1/2)'), x, 0, 2), "sqrt(y) + x/(2*sqrt(y)) + O(x**2)"],
    ["sj.series(P('(x*y + x**2)**(1/2)'), x, 0, 2)", () => sj.series(P('(x*y + x**2)**(1/2)'), x, 0, 2), "sqrt(x)*sqrt(y) + x**(3/2)/(2*sqrt(y)) + O(x**2)"],
    ["sj.series(P('log(x + x**2)'), x, 0, 3)", () => sj.series(P('log(x + x**2)'), x, 0, 3), "log(x) + x - x**2/2 + O(x**3)"],
    ["sj.series(P('log(sin(x) - x)'), x, 0, 5)", () => sj.series(P('log(sin(x) - x)'), x, 0, 5), "I*pi - log(6) + 3*log(x) - x**2/20 - x**4/16800 + O(x**5)"],
    ["sj.series(P('(1 - cos(a)**2 - sin(a)**2 + x)**(1/2)'), x, 0, 2)", () => sj.series(P('(1 - cos(a)**2 - sin(a)**2 + x)**(1/2)'), x, 0, 2), "sqrt(x)"],
    ["sj.series(P('besselj(1, x)'), x, 0, 4)", () => sj.series(P('besselj(1, x)'), x, 0, 4), "x/2 - x**3/16 + O(x**4)"],
    ["sj.series(P('atan2(x, y)'), x, 0, 2)", () => sj.series(P('atan2(x, y)'), x, 0, 2), "atan2(0, y) + x/y + O(x**2)"],
    ["sj.series(P('sin(x)'), x, 0, 0)", () => sj.series(P('sin(x)'), x, 0, 0), "O(1)"],
    ["sj.series(P('1/x'), x, 0, 3)", () => sj.series(P('1/x'), x, 0, 3), "1/x"],
    ["sj.series(P('cos(x) - 1 + x**2/2 - x**4/24 + x**6/720'), x, 0, 4)", () => sj.series(P('cos(x) - 1 + x**2/2 - x**4/24 + x**6/720'), x, 0, 4), "O(x**4)"],
    ["sj.leadterm(P('cos(x) - 1 + x**2/2 - x**4/24 + x**6/720 - x**8/40320 + x**10/3628800 - x**12/479001600 + x**14/87178291200 - x**16/20922789888000 + x**18/6402373705728000 - x**20/2432902008176640000 + x**22/1124000727777607680000 - x**24/620448401733239439360000 + x**26/403291461126605635584000000'), x)", () => sj.leadterm(P('cos(x) - 1 + x**2/2 - x**4/24 + x**6/720 - x**8/40320 + x**10/3628800 - x**12/479001600 + x**14/87178291200 - x**16/20922789888000 + x**18/6402373705728000 - x**20/2432902008176640000 + x**22/1124000727777607680000 - x**24/620448401733239439360000 + x**26/403291461126605635584000000'), x), "[1/304888344611713860501504000000, 28]"],
    ["sj.leadterm(P('x*log(x)'), x)", () => sj.leadterm(P('x*log(x)'), x), "[log(x), 1]"],
    ["sj.leadterm(P('y'), x)", () => sj.leadterm(P('y'), x), "[y, 0]"],
    ["sj.asLeadingTerm(P('sin(x) + x**2'), x)", () => sj.asLeadingTerm(P('sin(x) + x**2'), x), "x"],
    ["sj.getn(sj.O(P('x**2')))", () => sj.getn(sj.O(P('x**2'))), "2"],
    ["sj.getn(sj.O(x))", () => sj.getn(sj.O(x)), "1"],
    ["sj.getn(sj.O(P('x*y')))", () => sj.getn(sj.O(P('x*y'))), "1"],
    ["sj.extractLeadingOrder(P('x + x**2 + 1/x'), x)", () => sj.extractLeadingOrder(P('x + x**2 + 1/x'), x), "[[1/x, O(1/x)]]"],
    ["sj.extractLeadingOrder(P('x + y'), x)", () => sj.extractLeadingOrder(P('x + y'), x), "[[y, O(1)]]"],
    ["sj.extractLeadingOrder(P('x**2'), x)", () => sj.extractLeadingOrder(P('x**2'), x), "[[x**2, O(x**2)]]"],
    ["sj.extractLeadingOrder(P('x + 2*x + x**3'), x)", () => sj.extractLeadingOrder(P('x + 2*x + x**3'), x), "[[3*x, O(x)]]"],
    ["sj.taylorTerm(P('exp(x)'), 3, x)", () => sj.taylorTerm(P('exp(x)'), 3, x), "x**3/6"],
    ["sj.aseries(P('exp(x)'), x)", () => sj.aseries(P('exp(x)'), x), "exp(x)"],
    ["sj.aseries(P('exp(-x**2)'), x)", () => sj.aseries(P('exp(-x**2)'), x), "exp(-x**2)"],
    ["sj.aseries(P('1/(1 + x)'), x, 3)", () => sj.aseries(P('1/(1 + x)'), x, 3), "-1/x**2 + 1/x + O(x**(-3), (x, oo))"],
    ["sj.aseries(P('exp(-x)'), x, 3)", () => sj.aseries(P('exp(-x)'), x, 3), "exp(-x)"],
    ["sj.aseries(P('exp(-x)/x'), x, 3)", () => sj.aseries(P('exp(-x)/x'), x, 3), "exp(-x)/x"],
    ["sj.O(P('x**3 + y'), [x, y])", () => sj.O(P('x**3 + y'), [x, y]), "O(x**3 + y, x, y)"],
    ["sj.O(P('x**2 + x*y + y**3'), [x, y])", () => sj.O(P('x**2 + x*y + y**3'), [x, y]), "O(x**2 + x*y + y**3, x, y)"],
    ["sj.O(P('x*y + x**2*y**2'), [x, y])", () => sj.O(P('x*y + x**2*y**2'), [x, y]), "O(x*y, x, y)"],
    ["sj.O(P('x + y + x*y'), [x, y], sj.oo)", () => sj.O(P('x + y + x*y'), [x, y], sj.oo), "O(x*y, (x, oo), (y, oo))"],
    ["sj.O(P('x**2*y + x*y'), [x, y], sj.oo)", () => sj.O(P('x**2*y + x*y'), [x, y], sj.oo), "O(x**2*y, (x, oo), (y, oo))"],
    ["sj.O(P('2*x*y'), [x, y])", () => sj.O(P('2*x*y'), [x, y]), "O(x*y, x, y)"],
    ["sj.O(P('x*y*z'))", () => sj.O(P('x*y*z')), "O(x*y*z, x, y, z)"],
    ["sj.series(P('x**2'), x, 0, 0)", () => sj.series(P('x**2'), x, 0, 0), "O(1)"],
    ["sj.series(P('1/x'), x, 0, 0)", () => sj.series(P('1/x'), x, 0, 0), "1/x"],
    ["sj.series(P('1/(1 + x)'), x, P('-oo'), 4)", () => sj.series(P('1/(1 + x)'), x, P('-oo'), 4), "x**(-3) - 1/x**2 + 1/x + O(x**(-4), (x, -oo))"],
    ["sj.series(P('1/(1 + x)'), x, P('-oo'), 2)", () => sj.series(P('1/(1 + x)'), x, P('-oo'), 2), "1/x + O(x**(-2), (x, -oo))"],
    ["sj.getn(sj.O(P('1')))", () => sj.getn(sj.O(P('1'))), "0"],
    ["sj.getn(sj.O(P('x**2*log(x)')))", () => sj.getn(sj.O(P('x**2*log(x)'))), "2"],
    ["sj.getn(sj.O(P('(x - 1)**2'), x, 1))", () => sj.getn(sj.O(P('(x - 1)**2'), x, 1)), "2"],
    ["sj.getn(sj.add(x, sj.O(P('x**3'))))", () => sj.getn(sj.add(x, sj.O(P('x**3')))), "3"],
    ["sj.getn(sj.O(P('y*x**2'), [x, y]))", () => sj.getn(sj.O(P('y*x**2'), [x, y])), "1"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('leading terms of matrix products', () => {
  it('take the leading term of the scalar coefficient', () => {
    const A = sj.MatrixSymbol('A', 2, 2);
    // SymPy: (x*A).as_leading_term(x) and (sin(x)*A).as_leading_term(x) -> x*(A), the nested MatMul(x, MatMul(A)) equal to x*A
    expect(String(sj.asLeadingTerm(sj.mul(x, A), x))).toBe('x*A');
    expect(String(sj.asLeadingTerm(sj.mul(sj.sin(x), A), x))).toBe('x*A');
    // SymPy (x*A).leadterm(x) fails with TypeError: Mix of Matrix and Scalar symbols; the leading term is A*x**1
    expect(sj.leadterm(sj.mul(x, A), x).map(String)).toEqual(['A', '1']);
    expect(() => sj.leadterm(sj.mul(x, sj.MatrixSymbol('B', x, x)), x)).toThrow('whose matrix factors depend on x');
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // several variables at a point other than 0 and oo: the expression is kept
    ["sj.O(P('x*y'), [x, y], 1)", () => sj.O(P('x*y'), [x, y], 1), "O(x*y, (x, 1), (y, 1))", "O(1, (x, 1), (y, 1))"],
    // logx stands for log(x) (SymPy 1.14 raises TypeError for a logx without a dummy)
    ["sj.series(P('log(x)*sin(x)'), x, 0, 4, '+', { logx: y })", () => sj.series(P('log(x)*sin(x)'), x, 0, 4, '+', { logx: y }), "x*y - x**3*y/6 + O(x**4)", "ERR TypeError"],
    // logx stands for log(x)
    ["sj.series(P('log(x)'), x, 0, 4, '+', { logx: y })", () => sj.series(P('log(x)'), x, 0, 4, '+', { logx: y }), "y", "ERR TypeError"],
    // x**a = exp(a*log(x)) with log(x) = logx
    ["sj.series(P('x**a'), x, 0, 4, '+', { logx: y })", () => sj.series(P('x**a'), x, 0, 4, '+', { logx: y }), "exp(a*y)", "ERR TypeError"],
    // sign(I + x) = (I + x)/sqrt(1 + x**2) is not constant near 0 (SymPy gives its value I)
    ["sj.series(P('sign(I + x)'), x, 0, 3)", () => sj.series(P('sign(I + x)'), x, 0, 3), "ERR SeriesError: cannot expand sign", "I"],
    // the expansion variable is positive, as in SymPy: |y*x| = x*|y|
    ["sj.series(P('abs(y*x)'), x, 0, 3)", () => sj.series(P('abs(y*x)'), x, 0, 3), "x*Abs(y)", "x*Abs(y)"],
    // floor is continuous from the right, also at an integer y
    ["sj.series(P('floor(x + y)'), x, 0, 3)", () => sj.series(P('floor(x + y)'), x, 0, 3), "floor(y)", "floor(y)"],
    ["sj.series(P('ceiling(x + y)'), x, 0, 3, '-')", () => sj.series(P('ceiling(x + y)'), x, 0, 3, '-'), "ceiling(y)", "ceiling(y)"],
    // a symbolic point is not an integer generically: the value there on the other side as well (SymPy)
    ["sj.series(P('floor(x + y)'), x, 0, 3, '-')", () => sj.series(P('floor(x + y)'), x, 0, 3, '-'), "floor(y)", "floor(y)"],
    ["sj.series(P('ceiling(x + y)'), x, 0, 3)", () => sj.series(P('ceiling(x + y)'), x, 0, 3), "ceiling(y)", "ceiling(y)"],
    // SymPy raises NotImplementedError
    ["sj.series(P('ceiling(y*x)'), x, 0, 3)", () => sj.series(P('ceiling(y*x)'), x, 0, 3), "ERR SeriesError: cannot expand ceiling", "ERR NotImplementedError"],
    // exp(g) with g -> oo is returned unchanged; with g -> -oo it is smaller than every power (SymPy exp._eval_nseries)
    ["sj.series(P('exp(1/x)'), x, 0, 2)", () => sj.series(P('exp(1/x)'), x, 0, 2), "exp(1/x)", "exp(1/x)"],
    ["sj.series(P('exp(y/x)'), x, 0, 2)", () => sj.series(P('exp(y/x)'), x, 0, 2), "exp(y/x)", "exp(y/x)"],
    ["sj.series(P('exp(1/x)'), x, 0, 3, '-')", () => sj.series(P('exp(1/x)'), x, 0, 3, '-'), "O(x**3)", "O(x**3)"],
    ["sj.series(P('exp(-1/x)/x**5'), x, 0, 3)", () => sj.series(P('exp(-1/x)/x**5'), x, 0, 3), "O(x**3)", "O(x**3)"],
    ["sj.series(P('exp(-1/x) + sin(x)'), x, 0, 3)", () => sj.series(P('exp(-1/x) + sin(x)'), x, 0, 3), "x + O(x**3)", "x + O(x**3)"],
    // SymPy raises PoleError
    ["sj.series(P('exp(I/x)'), x, 0, 2)", () => sj.series(P('exp(I/x)'), x, 0, 2), "ERR EssentialSingularity: essential singularity", "ERR PoleError"],
    // SymPy raises ValueError
    ["sj.series(P('cos(x)'), x, 0, -1)", () => sj.series(P('cos(x)'), x, 0, -1), "ERR RangeError: series: the order n must be nonnegative", "ERR ValueError"],
    // SymPy raises TypeError (None - 0) for an infinite factor that stays
    ["sj.series(P('oo*sin(x)'), x, 0, 3)", () => sj.series(P('oo*sin(x)'), x, 0, 3), "ERR SeriesError: infinite coefficient", "ERR TypeError"],
    // the leading term of the exponent decides
    ["sj.series(P('exp(1/x**2 - 1/x)'), x, 0, 3)", () => sj.series(P('exp(1/x**2 - 1/x)'), x, 0, 3), "exp(-1/x + x**(-2))", "exp(-1/x + x**(-2))"],
    ["sj.series(P('exp(-1/x**2 + 1/x)'), x, 0, 3)", () => sj.series(P('exp(-1/x**2 + 1/x)'), x, 0, 3), "O(x**3)", "O(x**3)"],
    ["sj.series(P('sign(r + x)'), x, 0, 3)", () => sj.series(P('sign(r + x)'), x, 0, 3), "sign(r)", "sign(r)"],
    // SymPy gives sign(y)*(x*y + x**2), which is wrong for y = I: x*I*sign(I) = -x is negative
    ["sj.series(P('abs(y*x + x**2)'), x, 0, 3)", () => sj.series(P('abs(y*x + x**2)'), x, 0, 3), "ERR SeriesError: cannot expand abs", "x**2*sign(y) + x*y*sign(y)"],
    ["sj.series(P('abs(x - x**2)'), x, 0, 3)", () => sj.series(P('abs(x - x**2)'), x, 0, 3), "-x**2 + x", "-x**2 + x"],
    ["sj.series(P('abs(x**2 - x)'), x, 0, 3)", () => sj.series(P('abs(x**2 - x)'), x, 0, 3), "-x**2 + x", "-x**2 + x"],
    // oo*x is oo for the positive expansion variable
    ["sj.series(P('oo*x'), x, 0, 2)", () => sj.series(P('oo*x'), x, 0, 2), "oo", "oo"],
    ["sj.series(P('oo*x'), x, 0, 2, '-')", () => sj.series(P('oo*x'), x, 0, 2, '-'), "-oo", "-oo"],
    // SymPy raises PoleError
    ["sj.series(P('sin(1/x)'), x, 0, 3)", () => sj.series(P('sin(1/x)'), x, 0, 3), "ERR SeriesError: essential singularity", "ERR PoleError"],
    // an expression that is 0 (SymPy does not finish)
    ["sj.leadterm(P('sin(x)**2 + cos(x)**2 - 1'), x)", () => sj.leadterm(P('sin(x)**2 + cos(x)**2 - 1'), x), "ERR SeriesError: leading term not found", "TIMEOUT"],
    // no Order term: NoMatch (SymPy None)
    ["sj.getn(x)", () => sj.getn(x), "NoMatch", "None"],
    // without hir only the leading power of exp(-x) is kept
    ["sj.aseries(P('exp(-x) + exp(-2*x)'), x, 3)", () => sj.aseries(P('exp(-x) + exp(-2*x)'), x, 3), "exp(-x)", "exp(-x) + exp(-2*x)"],
    // with hir the powers of exp(-x) below n, with the Order term
    ["sj.aseries(P('exp(-x) + exp(-2*x)'), x, 3, true)", () => sj.aseries(P('exp(-x) + exp(-2*x)'), x, 3, true), "exp(-2*x) + exp(-x) + O(exp(-3*x), (x, oo))", "exp(-x) + exp(-2*x)"],
    // no power of exp(-x) below the order: the expression is returned
    ["sj.aseries(P('sin(exp(-x))**5'), x, 3)", () => sj.aseries(P('sin(exp(-x))**5'), x, 3), "sin(exp(-x))**5", "O(exp(-3*x), (x, oo))"],
    // exponentials of non-linear arguments are returned unchanged
    ["sj.aseries(P('exp(exp(-x))'), x, 3)", () => sj.aseries(P('exp(exp(-x))'), x, 3), "exp(exp(-x))", "exp(-2*x)/2 + exp(-x) + 1 + O(exp(-3*x), (x, oo))"],
    // with hir the coefficient of exp(-x) is kept as it is, with the Order term
    ["sj.aseries(P('exp(-x)*(1 + 1/x)'), x, 3, true)", () => sj.aseries(P('exp(-x)*(1 + 1/x)'), x, 3, true), "(1 + 1/x)*exp(-x) + O(exp(-3*x), (x, oo))", "exp(-x) + exp(-x)/x"],
    // SymPy raises NotImplementedError too
    ["sj.getn(sj.O(P('log(x)*log(y)'), [x, y]))", () => sj.getn(sj.O(P('log(x)*log(y)'), [x, y])), "ERR NotImplementedError: not sure of order of log(x)*log(y)", "ERR NotImplementedError"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

// Remaining branches of the limit, series and summation code. Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

describe('results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["sj.O(P('a*z*y*x'))", () => sj.O(P('a*z*y*x')), "O(a*x*y*z, a, x, y, z)"],
    ["sj.O(P('x*y + y*z + x*z'))", () => sj.O(P('x*y + y*z + x*z')), "O(x*y + x*z + y*z, x, y, z)"],
    ["sj.getn(sj.O(P('x**2*y**3'), [x, y]))", () => sj.getn(sj.O(P('x**2*y**3'), [x, y])), "2"],
    ["sj.getn(sj.O(P('1/(x**2*y)'), [x, y], sj.oo))", () => sj.getn(sj.O(P('1/(x**2*y)'), [x, y], sj.oo)), "2"],
    ["sj.aseries(P('exp(-3*x) + exp(-x)'), x, 3, true)", () => sj.aseries(P('exp(-3*x) + exp(-x)'), x, 3, true), "exp(-x) + O(exp(-3*x), (x, oo))"],
    ["sj.aseries(P('exp(-x/2) + exp(-2*x)'), x, 2, true)", () => sj.aseries(P('exp(-x/2) + exp(-2*x)'), x, 2, true), "exp(-x/2) + O(exp(-x), (x, oo))"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // SymPy raises NotImplementedError too
    ["sj.getn(sj.O(P('log(x)**2*log(y)**2'), [x, y]))", () => sj.getn(sj.O(P('log(x)**2*log(y)**2'), [x, y])), "ERR NotImplementedError: not sure of order of log(x)**2*log(y)**2", "ERR NotImplementedError"],
    // SymPy raises NotImplementedError too
    ["sj.getn(sj.O(P('x**a*log(y)'), [x, y]))", () => sj.getn(sj.O(P('x**a*log(y)'), [x, y])), "ERR NotImplementedError: not sure of order of x**a*log(y)", "ERR NotImplementedError"],
    // SymPy raises NotImplementedError too
    ["sj.getn(sj.O(P('log(x)'), [x, y]))", () => sj.getn(sj.O(P('log(x)'), [x, y])), "ERR NotImplementedError: not sure of order of log(x)", "ERR NotImplementedError"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

// Expected values are the str() forms printed by SymPy 1.14.

const PH = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
/** The variable argument as a symbol. */
const asSym = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

const showList = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe("series: SymPy 1.14 test_series cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("cos(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1 - x**2/2 + x**4/24 + O(x**6)"],
    ["series(Qs(\"exp(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1 + x + x**2/2 + x**3/6 + x**4/24 + x**5/120 + O(x**6)"],
    ["series(Qs(\"exp(cos(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(cos(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "E - E*x**2/2 + E*x**4/6 + O(x**6)"],
    ["series(Qs(\"1/(x**(-2) + x**(-3))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1/(x**(-2) + x**(-3))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x**3 - x**4 + x**5 + O(x**6)"],
    ["series(Qs(\"sin(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("sin(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x - x**3/6 + x**5/120 + O(x**6)"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("cos(x)", []), asSym(Qs("x", [])), Qs("0", []), 3, "+"), "1 - x**2/2 + O(x**3)"],
    ["series(Qs(\"1/x\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1/x", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1/x"],
    ["series(Qs(\"x*log(x) - x\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("x*log(x) - x", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x*(log(x) - 1)"],
    ["series(Qs(\"sqrt(a + b + c*x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(a + b + c*x)", []), asSym(Qs("x", [])), Qs("0", []), 1, "+"), "sqrt(a + b) + O(x)"],
    ["series(Qs(\"sqrt(a + b + c*x + c)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(a + b + c*x + c)", []), asSym(Qs("x", [])), Qs("0", []), 1, "+"), "sqrt(a + b + c) + O(x)"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"1\", []), 1, \"+\")", () => series(Qs("cos(x)", []), asSym(Qs("x", [])), Qs("1", []), 1, "+"), "cos(1) + O(x - 1, (x, 1))"],
    ["series(Qs(\"(1 - 1/(x/2 - 1/(2*x))**4)**(1/8)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 17, \"+\")", () => series(Qs("(1 - 1/(x/2 - 1/(2*x))**4)**(1/8)", []), asSym(Qs("x", [])), Qs("0", []), 17, "+"), "1 - 2*x**4 - 8*x**6 - 34*x**8 - 152*x**10 - 714*x**12 - 3472*x**14 - 17318*x**16 + O(x**17)"],
    ["series(Qs(\"x**a\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("x**a", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x**a"],
    ["series(Qs(\"x**(-2*a)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("x**(-2*a)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x**(-2*a)"],
    ["series(Qs(\"exp(a*log(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(a*log(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "exp(a*log(x))"],
    ["series(Qs(\"exp(x)/x**(3/2)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(x)/x**(3/2)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x**(-3/2) + 1/sqrt(x) + sqrt(x)/2 + x**(3/2)/6 + x**(5/2)/24 + x**(7/2)/120 + x**(9/2)/720 + x**(11/2)/5040 + O(x**6)"],
    ["series(Qs(\"x*(x*(1 - x) + 1)/(x*(1 - x) - (1 - x)**2 + 1)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 4, \"+\")", () => series(Qs("x*(x*(1 - x) + 1)/(x*(1 - x) - (1 - x)**2 + 1)", []), asSym(Qs("x", [])), Qs("oo", []), 4, "+"), "-9/(32*x**3) - 3/(16*x**2) - 1/(8*x) + 1/4 + x/2 + O(x**(-4), (x, oo))"],
    ["series(Qs(\"exp(-I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("exp(-I*pi*(2*x + 1))", []), asSym(Qs("x", [])), Qs("0", []), 3, "+"), "-1 + 2*I*pi*x + 2*pi**2*x**2 + O(x**3)"],
    ["series(Qs(\"exp(-I*pi*(2*x + 1))*gamma(x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("exp(-I*pi*(2*x + 1))*gamma(x + 1)", []), asSym(Qs("x", [])), Qs("0", []), 3, "+"), "-1 + x*(EulerGamma + 2*I*pi) + x**2*(-EulerGamma**2/2 + 23*pi**2/12 - 2*EulerGamma*I*pi) + O(x**3)"],
    ["series(Qs(\"2**(-I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("2**(-I*pi*(2*x + 1))", []), asSym(Qs("x", [])), Qs("0", []), 2, "+"), "exp(-I*pi*log(2)) - 2*I*pi*x*exp(-I*pi*log(2))*log(2) + O(x**2)"],
    ["series(Qs(\"y**(I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("y**(I*pi*(2*x + 1))", []), asSym(Qs("x", [])), Qs("0", []), 2, "+"), "exp(I*pi*log(y)) + 2*I*pi*x*exp(I*pi*log(y))*log(y) + O(x**2)"],
    ["series(Qs(\"(I*y)**(I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("(I*y)**(I*pi*(2*x + 1))", []), asSym(Qs("x", [])), Qs("0", []), 2, "+"), "exp(I*pi*log(I*y)) + 2*I*pi*x*exp(I*pi*log(I*y))*log(I*y) + O(x**2)"],
    ["series(Qs(\"cos(x**2 + x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 5, \"+\")", () => series(Qs("cos(x**2 + x + 1)", []), asSym(Qs("x", [])), Qs("0", []), 5, "+"), "cos(1) - x*sin(1) + x**2*(-sin(1) - cos(1)/2) + x**3*(-cos(1) + sin(1)/6) + x**4*(-11*cos(1)/24 + sin(1)/2) + O(x**5)"],
    ["series(Qs(\"1\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"1\", []), 6, \"+\")", () => series(Qs("cos(x)", []), asSym(Qs("x", [])), Qs("1", []), 6, "+"), "cos(1) - (x - 1)*sin(1) - (x - 1)**2*cos(1)/2 + (x - 1)**3*sin(1)/6 + (x - 1)**4*cos(1)/24 - (x - 1)**5*sin(1)/120 + O((x - 1)**6, (x, 1))"],
    ["series(Qs(\"cos(x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("cos(x + 1)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "cos(1) - x*sin(1) - x**2*cos(1)/2 + x**3*sin(1)/6 + x**4*cos(1)/24 - x**5*sin(1)/120 + O(x**6)"],
    ["series(Qs(\"exp(x)\", []), V(Qs(\"x\", [])), Qs(\"1\", []), 3, \"-\")", () => series(Qs("exp(x)", []), asSym(Qs("x", [])), Qs("1", []), 3, "-"), "E - E*(1 - x) + E*(1 - x)**2/2 + O((x - 1)**3, (x, 1))"],
    ["series(Qs(\"sin(1/x)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 5, \"+\")", () => series(Qs("sin(1/x)", []), asSym(Qs("x", [])), Qs("oo", []), 5, "+"), "-1/(6*x**3) + 1/x + O(x**(-5), (x, oo))"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 5, \"+\")", () => series(Qs("Abs(x)", []), asSym(Qs("x", [])), Qs("oo", []), 5, "+"), "x"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"-oo\", []), 5, \"-\")", () => series(Qs("Abs(x)", []), asSym(Qs("x", [])), Qs("-oo", []), 5, "-"), "-x"],
    ["series(Qs(\"1/cos(x/log(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1/cos(x/log(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1 + x**2/(2*log(x)**2) + 5*x**4/(24*log(x)**4) + O(x**6)"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"pi\", []), 3, \"+\")", () => series(Qs("cos(x)", []), asSym(Qs("x", [])), Qs("pi", []), 3, "+"), "-1 + (x - pi)**2/2 + O((x - pi)**3, (x, pi))"],
    ["series(Qs(\"(x**2 + x + 1)/(x**3 + x**2)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 6, \"+\")", () => series(Qs("(x**2 + x + 1)/(x**3 + x**2)", []), asSym(Qs("x", [])), Qs("oo", []), 6, "+"), "x**(-5) - 1/x**4 + x**(-3) + 1/x + O(x**(-6), (x, oo))"],
    ["series(Qs(\"Subs(sin(x), x, y)\", []), V(Qs(\"z\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("Subs(sin(x), x, y)", []), asSym(Qs("z", [])), Qs("0", []), 6, "+"), "Subs(sin(x), x, y)"],
    ["series(Qs(\"sin(x*y)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("sin(x*y)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x*y - x**3*y**3/6 + x**5*y**5/120 + O(x**6)"],
    ["series(Qs(\"exp(x)\", []), V(Qs(\"x\", [])), Qs(\"10\", []), 1, \"+\")", () => series(Qs("exp(x)", []), asSym(Qs("x", [])), Qs("10", []), 1, "+"), "exp(10) + O(x - 10, (x, 10))"],
    ["series(Qs(\"ceiling(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"ceiling(-x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(-x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"ceiling(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"ceiling(-sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(-sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"ceiling(-cos(x)) + 1\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(-cos(x)) + 1", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"ceiling(x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("ceiling(x)", []), asSym(Qs("x", [])), Qs("2", []), 6, "+"), "3"],
    ["series(Qs(\"ceiling(-x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("ceiling(-x)", []), asSym(Qs("x", [])), Qs("2", []), 6, "+"), "-2"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("Abs(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"-\")", () => series(Qs("Abs(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "-"), "-x"],
    ["series(Qs(\"floor(x) + 2\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(x) + 2", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "2"],
    ["series(Qs(\"floor(x) + 2\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"-\")", () => series(Qs("floor(x) + 2", []), asSym(Qs("x", [])), Qs("0", []), 6, "-"), "1"],
    ["series(Qs(\"sin(x + y)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"-\")", () => series(Qs("sin(x + y)", []), asSym(Qs("x", [])), Qs("0", []), 6, "-"), "sin(y) + x*cos(y) - x**2*sin(y)/2 - x**3*cos(y)/6 + x**4*sin(y)/24 + x**5*cos(y)/120 + O(x**6)"],
    ["series(Qs(\"sin(x + y)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("sin(x + y)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "sin(y) + x*cos(y) - x**2*sin(y)/2 - x**3*cos(y)/6 + x**4*sin(y)/24 + x**5*cos(y)/120 + O(x**6)"],
    ["series(Qs(\"(x + 1)*log(sin(2*x)/x)\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 2, \"+\")", () => series(Qs("(x + 1)*log(sin(2*x)/x)", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 2, "+"), "log(2) + x*log(2) + O(x**2)"],
    ["series(Qs(\"exp((x + 1)*log(sin(2*x)/x))\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 2, \"+\")", () => series(Qs("exp((x + 1)*log(sin(2*x)/x))", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 2, "+"), "2 + 2*x*log(2) + O(x**2)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("exp(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 1, "+"), "1 + O(x)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("exp(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 2, "+"), "1 + x + O(x**2)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("exp(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 3, "+"), "1 + x + x**2/2 + O(x**3)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 4, \"+\")", () => series(Qs("exp(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 4, "+"), "1 + x + x**2/2 + O(x**4)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 5, \"+\")", () => series(Qs("exp(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 5, "+"), "1 + x + x**2/2 - x**4/8 + O(x**5)"],
    ["series(Qs(\"floor(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(-x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-x)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "-1"],
    ["series(Qs(\"floor(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(-sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-sin(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "-1"],
    ["series(Qs(\"floor(x**3)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(x**3)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(-x**3)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-x**3)", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "-1"],
    ["series(Qs(\"floor(cos(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(cos(x))", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(sin(x)) + 5\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(sin(x)) + 5", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "5"],
    ["series(Qs(\"floor(-sin(x)) + 5\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-sin(x)) + 5", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "4"],
    ["series(Qs(\"floor(x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("floor(x)", []), asSym(Qs("x", [])), Qs("2", []), 6, "+"), "2"],
    ["series(Qs(\"floor(-x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("floor(-x)", []), asSym(Qs("x", [])), Qs("2", []), 6, "+"), "-3"],
    ["series(Qs(\"asin(a*x)/x\", []), V(Qs(\"x\", [])), Qs(\"4\", []), 2, \"+\")", () => series(Qs("asin(a*x)/x", []), asSym(Qs("x", [])), Qs("4", []), 2, "+"), "asin(4*a)/4 + (x - 4)*(a/(4*sqrt(1 - 16*a**2)) - asin(4*a)/16) + O((x - 4)**2, (x, 4))"],
    ["series(Qs(\"log(sin(x))\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 5, \"+\")", () => series(Qs("log(sin(x))", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 5, "+"), "log(x) - x**2/6 - x**4/180 + O(x**5)"],
    ["series(Qs(\"x*(-log(x) + log(sin(2*x))) - log(x) + log(sin(2*x))\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 5, \"+\")", () => series(Qs("x*(-log(x) + log(sin(2*x))) - log(x) + log(sin(2*x))", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 5, "+"), "log(2) + x*log(2) - 2*x**2/3 - 2*x**3/3 - 4*x**4/45 + O(x**5)"],
    ["series(Qs(\"1/(a*x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 5, \"+\")", () => series(Qs("1/(a*x + 1)", []), asSym(Qs("x", [])), Qs("0", []), 5, "+"), "1 - a*x + a**2*x**2 - a**3*x**3 + a**4*x**4 + O(x**5)"],
    ["series(Qs(\"1/(x*(a + b) + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("1/(x*(a + b) + 1)", []), asSym(Qs("x", [])), Qs("0", []), 3, "+"), "1 + x*(-a - b) + x**2*(a + b)**2 + O(x**3)"],
    ["series(Qs(\"(x + 1)**2\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("(x + 1)**2", []), asSym(Qs("x", [])), Qs("0", []), 6, "+"), "x**2 + 2*x + 1"],
    ["series(Qs(\"(a**2 + x**2)**(-2)\", []), V(Qs(\"x\", [])), Qs(\"I*a\", []), 0, \"+\")", () => series(Qs("(a**2 + x**2)**(-2)", []), asSym(Qs("x", [])), Qs("I*a", []), 0, "+"), "-I/(4*a**3*(-I*a + x)) - 1/(4*a**2*(-I*a + x)**2) + O(1, (x, I*a))"],
    ["series(Qs(\"(a**2 + x**2)**(-2)\", []), V(Qs(\"x\", [])), Qs(\"I*a\", []), 1, \"+\")", () => series(Qs("(a**2 + x**2)**(-2)", []), asSym(Qs("x", [])), Qs("I*a", []), 1, "+"), "3/(16*a**4) - I/(4*a**3*(-I*a + x)) - 1/(4*a**2*(-I*a + x)**2) + O(-I*a + x, (x, I*a))"],
    ["series(Qs(\"sqrt(x + z)\", []), V(Qs(\"z\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(x + z)", []), asSym(Qs("z", [])), Qs("0", []), 1, "+"), "sqrt(x) + O(z)"],
    ["series(Qs(\"sqrt(x + y + z)\", []), V(Qs(\"z\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(x + y + z)", []), asSym(Qs("z", [])), Qs("0", []), 1, "+"), "sqrt(x + y) + O(z)"],
    ["series(Qs(\"(sin(2*w)/w)**(w + 1)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 1, \"+\")", () => series(Qs("(sin(2*w)/w)**(w + 1)", [symbol("w", { real: true })]), asSym(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 1, "+"), "2 + O(w)"],
    ["series(Qs(\"(sin(2*w)/w)**(w + 1)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 3, \"+\")", () => series(Qs("(sin(2*w)/w)**(w + 1)", [symbol("w", { real: true })]), asSym(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 3, "+"), "2 + 2*w*log(2) + w**2*(-4/3 + log(2)**2) + O(w**3)"],
    ["series(Qs(\"(sin(2*w)/w)**(w + 1)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 2, \"+\")", () => series(Qs("(sin(2*w)/w)**(w + 1)", [symbol("w", { real: true })]), asSym(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 2, "+"), "2 + 2*w*log(2) + O(w**2)"],
    ["series(Qs(\"log(sin(2*w)/w)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 5, \"+\")", () => series(Qs("log(sin(2*w)/w)", [symbol("w", { real: true })]), asSym(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 5, "+"), "log(2) - 2*w**2/3 - 4*w**4/45 + O(w**5)"],
    ["series(P('ceiling(x)'), V(x), 0)", () => series(PH('ceiling(x)'), asSym(x), 0), "1"],
    ["series(P('ceiling(-x)'), V(x), 0)", () => series(PH('ceiling(-x)'), asSym(x), 0), "0"],
    ["series(P('floor(x)'), V(x), 0)", () => series(PH('floor(x)'), asSym(x), 0), "0"],
    ["series(P('floor(-x)'), V(x), 0)", () => series(PH('floor(-x)'), asSym(x), 0), "-1"],
    ["series(P('floor(sin(x))'), V(x), 0, 6, '-')", () => series(PH('floor(sin(x))'), asSym(x), 0, 6, '-'), "-1"],
    ["series(P('ceiling(sin(x))'), V(x), 0)", () => series(PH('ceiling(sin(x))'), asSym(x), 0), "1"],
    ["series(P('floor(x + 1/2)'), V(x), 0)", () => series(PH('floor(x + 1/2)'), asSym(x), 0), "0"],
    ["series(P('floor(x + sqrt(2))'), V(x), 0)", () => series(PH('floor(x + sqrt(2))'), asSym(x), 0), "1"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showList(run())).toBe(want);
  });
});


describe('series at infinity and aseries', () => {
  it('match SymPy', async () => {
    const { series, aseries, oo } = await import('../../src');
    const x = symbols('x')[0];
    expect(sstr(series(parse('cos(1/x)'), x, oo, 6))).toBe('1/(24*x**4) - 1/(2*x**2) + 1 + O(x**(-6), (x, oo))');
    expect(sstr(series(parse('x/(x+1)'), x, oo, 4))).toBe('-1/x**3 + x**(-2) - 1/x + 1 + O(x**(-4), (x, oo))');
    const e = parse('sin(1/x + exp(-x)) - sin(1/x)');
    expect(sstr(aseries(e, x))).toBe('(1/(24*x**4) - 1/(2*x**2) + 1 + O(x**(-6), (x, oo)))*exp(-x)');
    expect(sstr(aseries(e, x, 3, true))).toBe('-exp(-2*x)*sin(1/x)/2 + exp(-x)*cos(1/x) + O(exp(-3*x), (x, oo))');
    expect(sstr(aseries(parse('1/x'), x, 8))).toBe('1/x');
  });
});

describe('O(...) read by the parser', () => {
  it('reduces to the leading term (SymPy 1.14)', () => {
    expect(sstr(parse('O(x + x**2)'))).toBe('O(x)');
    expect(sstr(parse('O(1/x, (x, oo))'))).toBe('O(1/x, (x, oo))');
    expect(sstr(parse('O(1)'))).toBe('O(1)');
  });
});

describe('essential singularities, complex infinity and irrational exponents (SymPy 1.14)', () => {
  const S = (e: string, d: '+' | '-' = '+', n = 6) => show(sj.series(P(e), x, 0, n, d));
  it('keeps the factors exp(g) with g -> oo and drops those with g -> -oo', () => {
    expect(show(sj.series(P('x*exp(1/x)'), x, 0, 2))).toBe('x*exp(1/x)');
    expect(S('x*exp(1/x)', '-')).toBe('O(x**6)');
    expect(S('x + exp(1/x)')).toBe('x + exp(1/x)');
    expect(S('x + exp(1/x)', '-')).toBe('x + O(x**6)');
    expect(S('exp(1/x)*sin(x)')).toBe('x*exp(1/x) - x**3*exp(1/x)/6 + x**5*exp(1/x)/120 + O(x**6*exp(1/x))');
    expect(S('exp(1/x)/(1 + x)')).toBe('exp(1/x) - x*exp(1/x) + x**2*exp(1/x) - x**3*exp(1/x) + x**4*exp(1/x) - x**5*exp(1/x) + O(x**6*exp(1/x))');
    expect(S('exp(1/x)*(1 + x)')).toBe('x*exp(1/x) + exp(1/x)');
    expect(S('exp(-1/x)*x', '-')).toBe('x*exp(-1/x)');
    expect(S('exp(1/x) + exp(-1/x)')).toBe('exp(1/x) + O(x**6)');
    expect(S('exp(y/x)*x')).toBe('x*exp(y/x)');
    expect(S('exp(y/x)*x', '-')).toBe('x*exp(y/x)');
    expect(S('2**(1/x)*x')).toBe('x*exp(log(2)/x)');
    expect(S('2**(1/x)*x', '-')).toBe('O(x**6)');
    expect(S('2**(-1/x)', '-')).toBe('exp(-log(2)/x)');
    // SymPy raises PoleError: exp(I/x) oscillates
    expect(() => sj.series(P('exp(I/x)*x'), x)).toThrow('essential singularity');
  });

  it('expands a Laurent polynomial at zoo as itself', () => {
    expect(show(sj.series(x, x, P('zoo')))).toBe('x');
    expect(show(sj.series(P('x**2 + 1/x'), x, P('zoo')))).toBe('x**2 + 1/x');
    expect(show(sj.series(y, x, P('zoo')))).toBe('y');
    expect(show(sj.series(P('x*y + x**(-3)'), x, P('zoo')))).toBe('x*y + x**(-3)');
    // (SymPy returns expressions in sign(zoo) for the others)
    expect(() => sj.series(P('sin(x)'), x, P('zoo'))).toThrow('expansion at this point is not supported');
  });

  it('finds leading terms with irrational exponents', () => {
    expect(show(sj.leadterm(P('x**(-sqrt(2))'), x))).toBe('[1, -sqrt(2)]');
    expect(show(sj.leadterm(P('x**(1 - sqrt(2))*(1 + x)'), x))).toBe('[1, 1 - sqrt(2)]');
    expect(show(sj.dir(P('x**(-sqrt(2))'), x, 1))).toBe('-sqrt(2)');
    expect(show(sj.dir(P('x**(1 - sqrt(2))'), x, 1))).toBe('1 - sqrt(2)');
  });
});

it('retains order variables and implements asymptotic containment and products', () => {
  const x=V('x'),y=V('y');
  const o = (e: sj.ExprLike, v?: sj.Sym, p: sj.ExprLike=0) => sj.O(e,v,p) as sj.Order;
  expect(o(1).contains(o(1,x))).toBe(false);
  expect(o(1,x).contains(o(x))).toBe(true);
  expect(o(x).contains(o(sj.pow(x,2)))).toBe(true);
  expect(o(sj.pow(x,2)).contains(x)).toBe(false);
  expect(o(x).contains(0)).toBe(true);
  expect(o(1).contains(2)).toBe(true);
  expect(o(1).contains(x)).toBe(true);
  expect(new sj.Order([sj.S.Zero]).contains(1)).toBe(false);
  expect(o(1).contains(sj.oo)).toBe(false);
  expect(o(x).contains(o(x,x,1))).toBe('unknown');
  expect((sj.O(sj.mul(x,y),[x,y]) as sj.Order).contains(sj.mul(x,y))).toBe(true);
  expect(o(1,x).contains(sj.SymFunction('h')(x))).toBe('unknown');
  expect(o(1,x).contains(sj.S.NaN)).toBe(false);
  expect(new sj.Order([sj.mul(y,x),x,sj.S.Zero]).contains(x)).toBe(true);
  expect(String(sj.mul(o(x),x))).toBe('O(x**2)');
  expect(String(sj.sub(o(x),o(x)))).toBe('O(x)');
  expect(String(sj.mul(o(x),o(y)))).toBe('O(x*y, x, y)');
  expect(() => sj.mul(o(x),o(x,x,1))).toThrow(sj.NotImplementedError);
  expect(String(sj.mul(o(x),0))).toBe('O(0)');
});

describe('series terms of functions without a Maclaurin series (SymPy taylor_term)', () => {
  const x = new Sym('x');
  const tt = (f: string, n: number): string => sstr(sj.taylorTerm(parse(f), n, x));
  it('gives the Laurent terms of cot and csc', () => {
    expect(tt('cot(x)', 0)).toBe('1/x');
    expect(tt('cot(x)', 1)).toBe('-x/3');
    expect(tt('cot(x)', 3)).toBe('-x**3/45');
    expect(tt('cot(x)', 2)).toBe('0');
    expect(tt('csc(x)', 0)).toBe('1/x');
    expect(tt('csc(x)', 2)).toBe('0');
    expect(tt('csc(x)', 1)).toBe('x/6');
    expect(tt('csc(x)', 3)).toBe('7*x**3/360');
    expect(tt('csc(x)', 5)).toBe('31*x**5/15120');
  });
  it('gives the terms of asec, acsc, asech and acsch', () => {
    expect(tt('asech(x)', 0)).toBe('log(2/x)');
    expect(tt('asech(x)', 1)).toBe('0');
    expect(tt('asech(x)', 8)).toBe('-35*x**8/1024');
    expect(tt('acsch(x)', 0)).toBe('log(2/x)');
    expect(tt('acsch(x)', 3)).toBe('0');
    expect(tt('acsch(x)', 2)).toBe('x**2/4');
    expect(tt('acsch(x)', 6)).toBe('5*x**6/96');
    expect(tt('acsch(x)', 4)).toBe('-3*x**4/32');
    expect(tt('asec(x)', 0)).toBe('I*log(2/x)');
    expect(tt('asec(x)', 1)).toBe('0');
    expect(tt('asec(x)', 6)).toBe('-5*I*x**6/96');
    expect(tt('acsc(x)', 0)).toBe('I*log(x) + pi/2 - I*log(2)');
    expect(tt('acsc(x)', 1)).toBe('0');
    expect(tt('acsc(x)', 8)).toBe('35*I*x**8/1024');
    expect(tt('sin(x)', 3)).toBe('-x**3/6');
    expect(tt('cot(2*x)', 0)).toBe('zoo');
  });
});

it('carries formal logarithms through directional leading terms', () => {
  const x = new sj.Sym('x');
  const p = new sj.Sym('p');
  expect(sj.sstr(sj.asLeadingTerm(sj.parse('log(-2*x)'), x, { cdir: -1, logx: p }))).toBe('p + log(2) - I*pi');
  expect(sj.sstr(sj.asLeadingTerm(sj.parse('log(-2*x)'), x, { cdir: 1, logx: p }))).toBe('p + log(2) + I*pi');
  expect(() => sj.asLeadingTerm(sj.arg(x), x, { cdir: sj.S.I })).toThrow(sj.NotImplementedError);
});

it('registers the leading-term dispatcher used by expression extensions', async () => {
  const { impl } = await import('../../src/core/nodes');
  const x = new sj.Sym('x');
  expect(impl.leadterm?.(sj.parse('sin(x)'), x).map(String)).toEqual(['1', '1']);
});

it('uses the log(1 + x) convention for logarithmic Taylor terms', () => {
  const x = new sj.Sym('x');
  for (const [n, expected] of [[-1, '0'], [0, 'x'], [1, '-x**2/2'], [4, 'x**5/5']] as const) {
    expect(sj.sstr(sj.taylorTerm(sj.log(x), n, x))).toBe(expected);
  }
});

it('preserves variables and undecidable growth in Order construction', () => {
  const x = new sj.Sym('x'), y = new sj.Sym('y');
  expect(String(sj.O(sj.O(x), [x, y]))).toBe('O(x, x, y)');
  const unknown = sj.add(sj.SymFunction('f')(x), sj.SymFunction('g')(x));
  expect(String(sj.O(unknown, x))).toBe('O(f(x) + g(x))');
  expect(String(sj.O(unknown, x, sj.oo))).toBe('O(f(x) + g(x), (x, oo))');
  expect(sj.O(sj.nan)).toBe(sj.nan);
});

it('retains the logarithmic bound of omitted series terms', () => {
  const x = new sj.Sym('x');
  expect(String(sj.series(sj.parse('sin(x)*log(x)'), x, 0, 3))).toBe('x*log(x) + O(x**3*log(x))');
  expect(String(sj.series(sj.parse('sin(x*log(x))'), x, 0, 3))).toBe('x*log(x) + O(x**3*log(x)**3)');
  expect(String(sj.series(sj.parse('log(x) + exp(x)'), x, 0, 2))).toBe('1 + log(x) + x + O(x**2)');
});

it('normalises multivariate orders whose exponents vanish at 0 like SymPy', () => {
  const x = new sj.Sym('x'), y = new sj.Sym('y');
  // the scaled leading term of x**y is 1; an exponent with a constant term keeps its power
  expect(String(sj.O(sj.pow(x, y)))).toBe('O(1, x, y)');
  expect(String(sj.O(sj.mul(x, sj.pow(x, y))))).toBe('O(x, x, y)');
  expect(String(sj.O(sj.pow(x, sj.add(y, 1))))).not.toBe('O(1, x, y)');
  expect(String(sj.add(x, sj.O(sj.pow(x, y))))).toBe('O(1, x, y)');
});


it('compares algebraic growth without losing logarithms or mixed directions', () => {
  const [x, y] = sj.symbols('x y');
  const mixed = new sj.Order([sj.mul(x, sj.pow(y, -1)), x, y, sj.S.Zero]);
  expect(mixed.contains(1)).toBe('unknown');
  expect((sj.O(sj.log(x), x) as sj.Order).contains(1)).toBe(true);
  expect((sj.O(sj.pow(sj.log(x), -1), x) as sj.Order).contains(1)).toBe(false);
  expect((sj.O(sj.pow(x, -1), x, sj.oo) as sj.Order).contains(sj.pow(x, -2))).toBe(true);
  expect((sj.O(sj.pow(x, -1), x, sj.neg(sj.oo)) as sj.Order).contains(sj.pow(x, -2))).toBe(true);
});


it('handles empty orders and inconsistent algebraic and logarithmic growth', () => {
  const [x, y] = sj.symbols('x y');
  expect(String(sj.add(x, new sj.Order([sj.S.Zero])))).toBe('x');
  expect(new sj.Order([sj.mul(x, sj.log(y)), x, y, sj.S.Zero]).contains(1)).toBe('unknown');
});

it('evaluates derivatives and integrals before extracting their leading term', () => {
  const x = new sj.Sym('x');
  const y = new sj.Sym('y');
  const cube = sj.pow(x, 3);
  const examples: [sj.Expr, string][] = [
    [sj.derivative(cube, [[x, 1]]), '3*x**2'],
    [sj.derivative(cube, [[y, 1]]), '0'],
    [new sj.Integral([cube, x]), 'x**4/4'],
    [new sj.Integral([cube, y]), 'x**3*y'],
    [sj.derivative(sj.exp(x), [[x, 1]]), '1'],
    [sj.derivative(sj.log(x), [[x, 1]]), '1/x'],
  ];
  for (const [expr, expected] of examples) expect(String(sj.asLeadingTerm(expr, x))).toBe(expected);
});

it('retains unevaluated integrals independent of the expansion variable', async () => {
  const { impl } = await import('../../src/core/nodes');
  const x = new sj.Sym('x');
  const y = new sj.Sym('y');
  const unknown = new sj.Integral([sj.SymFunction('f')(y), y]);
  expect(sj.asLeadingTerm(unknown, x).key).toBe(unknown.key);
  const saved = { ...impl };
  try {
    impl.doit = undefined;
    expect(sj.asLeadingTerm(unknown, x)).toBe(unknown);
  } finally {
    Object.assign(impl, saved);
  }
});

it('removes explicit zero order terms when adding expressions', () => {
  const x = new sj.Sym('x');
  expect(sj.add(x, new sj.Order([sj.S.Zero, x, sj.S.Zero])).key).toBe(x.key);
});

it('finds a leading term with a symbolic power or an essential singularity in an argument', () => {
  const x = sj.symbol('x');
  const f = sj.defineFunction('f');
  expect(String(sj.asLeadingTerm(sj.parse('3 + x**(log(3)/log(2) - 1)'), x))).toBe('3');
  expect(String(sj.asLeadingTerm(sj.parse('sinh(tanh(1/x))'), x, { cdir: 1 }))).toBe('sinh(1)');
  expect(String(sj.asLeadingTerm(sj.parse('sinh(tanh(1/x))'), x, { cdir: -1 }))).toBe('-sinh(1)');
  expect(sj.asLeadingTerm(f(x.pow(-1)), x).key).toBe(f(x.pow(-1)).key);
  expect(() => sj.asLeadingTerm(f(x), x)).toThrow(sj.NotImplementedError);
});

it('substitutes a supplied logarithm along the positive ray and uses directional rules', () => {
  const [x, y] = sj.symbols('x y');
  expect(String(sj.series(sj.parse('loggamma(log(1/x))'), x, 0, 1, '+', { logx: y }))).toBe('loggamma(-y)');
  expect(String(sj.asLeadingTerm(sj.floor(sj.neg(x)), x))).toBe('-1');
  expect(() => sj.leadterm(sj.add(x.pow(y), 1), x)).toThrow(sj.NotImplementedError);
  expect(() => sj.asLeadingTerm(sj.parse('sinh(1/x + sin(1/x))'), x)).toThrow(sj.NotImplementedError);
});

it('rebuilds an order with its implicit variable and origin', () => {
  const [x, y] = sj.symbols('x y');
  const order = new sj.Order([x.pow(2)]);
  expect(sj.replace(order, x, y)).toEqual(sj.O(y.pow(2), y));
  const power = x.pow(sj.sqrt(2));
  expect(() => sj.leadterm(new sj.Add([power, sj.neg(power)]), x)).toThrow(SeriesError);
});
it('merges Order variables and checks expansion arguments', () => {
  expect(String(sj.O(P('sin(x)*y + x**2'), [x,y]))).toBe('O(x**2 + x*y, x, y)');
  const o = new sj.Order([x, x, sj.S.Zero]);
  expect(sj.asExprVariables(o)).toEqual([x, [[x, sj.S.Zero]]]);
  expect(sj.asExprVariables(o, [[y, sj.S.Zero]])).toEqual([x, [[x, sj.S.Zero], [y, sj.S.Zero]]]);
  expect(() => sj.asExprVariables(o, [[y, sj.oo]])).toThrow(sj.NotImplementedError);
  expect(sj.asExprVariables(new sj.Order([x]))).toEqual([x, [[x, sj.S.Zero]]]);
  expect(() => sj.O(x, [x, x])).toThrow(RangeError);
  expect(() => sj.getn(sj.add(sj.O(x), sj.O(y)))).toThrow(sj.NotImplementedError);
  expect(String(sj.pow(sj.O(1), sj.O(1)))).toBe('O(1)');
  expect(String(sj.pow(sj.O(1), sj.O(x)))).toContain('**');
  expect(series(x)).toEqual(x);
  expect(series(1).equals(1)).toBe(true);
  expect(() => series(x.add(y))).toThrow(RangeError);
  expect(() => Reflect.apply(series, undefined, [x, x, 0, 4, ''])).toThrow(RangeError);
  expect(() => series(x.pow(sj.I), x)).toThrow(sj.PoleError);
  expect(String(series(sj.Subs(x, x, y), y))).toBe('Subs(x, x, y)');
  expect(String(series(sj.derivative(x, [[y, 1]]), x))).toBe('Derivative(x, y)');
  expect(String(sj.aseries(P('(exp(exp(-x)+1/x)-exp(1/x))*exp(x)'), x, 3, true))).toContain('O(');
  expect(String(sj.O(P('x*y*sin(x)*Integral(x,(x,1,2))')))).toBe('O(x**2*y, x, y)');
});

it('preserves unresolved multivariate orders and checks logarithmic oscillations', () => {
  for (const src of ['sin(x*y)', 'gamma(1/x)', 'sin(1/x)', 'sin(x)-x+y', 'sin(x)-x+y+y**2'])
    expect(String(sj.O(P(src), [x,y]))).toContain('O(');
  expect(() => series(new sj.Pow(sj.S.E, sj.mul(sj.I, sj.log(x))), x)).toThrow(sj.PoleError);
  expect(String(series(new sj.Pow(x, sj.pi), x))).toBe('x**pi');
  expect(String(sj.aseries(P('exp(x)+exp(-x)'), x))).toBe('exp(x) + exp(-x)');
});

it('reports a missing leading term when no Piecewise branch holds at zero', () => {
  const x = new sj.Sym('x');
  expect(() => sj.asLeadingTerm(sj.piecewise([x, sj.Gt(x, 1)]), x)).toThrow(/cannot expand Piecewise/);
});

it('uses the expansion point for the local singularity series', () => {
  const F = sj.SingularityFunction;
  const l = new Sym('l', { positive: true });
  const half = sj.rational(1, 2);
  const shift = sj.add(x, l);
  const sum = sj.add(sj.mul(half, F(shift, 0, 1)), sj.neg(F(shift, sj.mul(half, l), 1)), sj.mul(half, F(shift, l, 1)));
  expect(String(sj.asLeadingTerm(sum, x))).toBe('-x/2');
  expect(String(sj.nseries(sum, x))).toBe('-x/2 + O(x**6)');
  expect(sj.series(sum, x)).toBe(sj.S.Zero);
  expect(sj.nseries(F(x, 0, 1), x)).toBe(sj.S.Zero);
  expect(sj.nseries(F(x, 0, 0), x)).toBe(sj.S.One);
  expect(sj.nseries(F(x, 0, 0), x, 0, 6, { cdir: -1 })).toBe(sj.S.Zero);
  expect(sj.nseries(F(x, y, 1), x)).toBe(sj.S.Zero);
  expect(sj.nseries(F(x, 0, -1), x)).toBe(sj.S.Zero);
  expect(String(sj.nseries(F(shift, 0, 1), x))).toBe('l + x');
});

it('finds signed leading terms and asymptotic branches', () => {
  expect(String(sj.asLeadingTerm(P('besseli(0,1/x)'), x))).toBe('sqrt(2)*exp(1/x)/(2*sqrt(pi)*sqrt(1/x))');
  expect(sj.asLeadingTerm(P('besseli(0,1/x)'), x, { cdir: -1 }).equals(P('besseli(0,1/x)'))).toBe(true);
  expect(sj.asLeadingTerm(P('besselj(x,1)'), x).equals(P('besselj(0,1)'))).toBe(true);
  expect(sj.asLeadingTerm(P('erf(1/x)'), x, { cdir: -1 })).toBe(sj.S.NegOne);
  expect(sj.asLeadingTerm(P('erfc(1/x)'), x, { cdir: -1 })).toBe(sj.S.Two);
  expect(String(series(P('erf(1/x)'), x, sj.oo, 2))).toBe('2/(sqrt(pi)*x) + O(x**(-2), (x, oo))');
  expect(String(series(P('fresnelc(x)'), x, sj.S.NegativeInfinity, 2))).toBe('sin(pi*x**2/2)/(pi*x) - 1/2 + O(x**(-2), (x, -oo))');
  expect(String(sj.taylorTerm(sj.fresnelc(x), 0, x))).toBe('x');
  expect(sj.taylorTerm(sj.fresnelc(x), -1, x)).toBe(sj.S.Zero);
});

it('composes Bessel series at regular and complex arguments', () => {
  expect(String(series(P('besselj(0,x+1)'), x, 0, 2))).toBe('besselj(0, 1) - x*besselj(1, 1) + O(x**2)');
  expect(String(series(P('bessely(0,I*x)'), x, 0, 2))).toBe('(2*log(x) - 2*log(2) + 2*EulerGamma + I*pi)/pi + O(x**2*log(x))');
  expect(String(series(P('bessely(0,x**2+x)'), x, 0, 0))).toBe('O(log(x))');
  expect(() => series(P('besselj(0,x**y)'), x)).toThrow(sj.NotImplementedError);
});

it('handles signed and unsupported leading-term sectors', () => {
  expect(String(sj.asLeadingTerm(P('bessely(-1/3,x)'), x))).toBe('-2**(1/3)*sqrt(3)/(3*x**(1/3)*gamma(2/3))');
  expect(sj.asLeadingTerm(sj.fn('besselk', [-1, x], { evaluate: false }), x).equals(P('1/x'))).toBe(true);
  expect(String(sj.asLeadingTerm(P('besselk(y,x)'), x))).toBe('besselk(y, 0)');
  expect(() => sj.asLeadingTerm(P('besselj(0,1/x)'), x)).toThrow(sj.NotImplementedError);
  expect(() => sj.asLeadingTerm(P('erfc(I/x)'), x)).toThrow(sj.NotImplementedError);
});

it('selects infinity series by the argument direction and valuation', () => {
  expect(String(series(P('Si(x)'), x, sj.S.NegativeInfinity, 2))).toContain('-pi/2');
  expect(String(series(P('erf(x+1)'), x, sj.oo))).toBe('1 + O(x**(-6), (x, oo))');
  expect(String(series(sj.fn('erfc', [sj.neg(x)], { evaluate: false }), x, sj.oo))).toBe('2 + O(x**(-6), (x, oo))');
});


it('expands special functions on the positive and negative real rays', () => {
  const expand = (source: string, n: number, point: sj.Expr = sj.oo) => String(series(P(source), x, point, n));
  expect(expand('lowergamma(x,2)', 3)).toBe('2**x*(1 + 2/(x + 1))*exp(-2)/x + O(exp(x*log(2))/x**3, (x, oo))');
  expect(expand('besseli(0,x)', 2, sj.S.NegativeInfinity)).toContain('exp(-x)');
  expect(expand('besselk(0,x)', 2)).toContain('sqrt(1/x) - (1/x)**(3/2)/8');
  expect(expand('besselk(0,x)', 2, sj.S.NegativeInfinity)).toContain('-I*sqrt(-1/x)');
  expect(expand('erfi(x)', 4)).toBe('(1/(2*x**3) + 1/x + O(x**(-4), (x, oo)))*exp(x**2)/sqrt(pi) - I');
  expect(expand('erfc(x)', 4)).toBe('(-1/(2*x**3) + 1/x + O(x**(-4), (x, oo)))*exp(-x**2)/sqrt(pi)');
  expect(expand('expint(2,x)', 3)).toBe('(6/x**2 - 2/x + 1 + O(x**(-3), (x, oo)))*exp(-x)/x');
  expect(expand('Ei(x)', 3)).toBe('(2/x**2 + 1/x + 1 + O(x**(-3), (x, oo)))*exp(x)/x');
  expect(expand('fresnels(x)', 4)).toBe('-sin(pi*x**2/2)/(pi**2*x**3) - cos(pi*x**2/2)/(pi*x) + 1/2 + O(x**(-4), (x, oo))');
  expect(expand('Si(x)', 3)).toBe('-(x**(-2) + O(x**(-3), (x, oo)))*sin(x) - (1/x + O(x**(-3), (x, oo)))*cos(x) + pi/2');
  expect(expand('Ci(x)', 3, sj.S.NegativeInfinity)).toContain('I*pi');
  expect(expand('Ci(x)', 3)).toBe('-(x**(-2) + O(x**(-3), (x, oo)))*cos(x) + (1/x + O(x**(-3), (x, oo)))*sin(x)');
  expect(expand('Li(x)', 2, sj.S.Zero)).toBe('x*(1/log(x) + 1 + O(log(x)**(-2)))/log(x) - li(2)');
});

it('keeps local Bessel powers and logarithms', () => {
  expect(String(series(P('besseli(1,sin(x))'), x, 0, 2))).toBe('x/2 + O(x**2)');
  expect(String(series(P('besselj(0,sin(x))'), x, 0, 2))).toBe('1 + O(x**2)');
  expect(String(series(P('bessely(1,x)'), x, 0, 2))).toContain('O(x**2*log(x))');
  expect(String(series(P('bessely(2,x)'), x, 0, 1))).toBe('-4/(pi*x**2) - 1/pi + O(x)');
  expect(String(series(P('besselk(0,x+x**2)'), x, 0, 4))).toContain('(2 - 2*EulerGamma)*(x**3/4 + x**2/8)');
  expect(String(series(P('bessely(0,x+x**2)'), x, 0, 4))).toContain('(2 - 2*EulerGamma)*(-x**3/(2*pi) - x**2/(4*pi))');
  const cases = [
    ['besselj(0,1+x)', 'besselj(0,1)'], ['besselj(1,x)', 'x/2'],
    ['besselk(0,1/x)', 'sqrt(pi)*exp(-1/x)/sqrt(2/x)'],
    ['bessely(0,x)', '2*(log(x)-log(2)+EulerGamma)/pi'],
    ['besselk(0,x)', 'log(2)-EulerGamma-log(x)'], ['bessely(1,x)', '-2/(pi*x)'],
    ['erfi(1/x)', 'erfi(1/x)'], ['erfc(x)', '1'],
  ] as const;
  for (const [source, expected] of cases) {
    expect(sj.expandMul(sj.asLeadingTerm(P(source), x)).equals(sj.expandMul(P(expected))), source).toBe(true);
  }
  expect(String(sj.taylorTerm(sj.fresnelc(x), 1, x))).toBe('-pi**2*x**5/40');
});

it('expands gamma, exponential integrals and oscillatory integrals at infinity', () => {
  for (const [f, point, n, expected] of [
    ['lowergamma(x,2)', sj.oo, 3, '2**x*(1 + 2/(x + 1))*exp(-2)/x + O(exp(x*log(2))/x**3, (x, oo))'],
    ['erfc(x)', sj.oo, 3, '(1/x + O(x**(-3), (x, oo)))*exp(-x**2)/sqrt(pi)'],
    ['erfi(x)', sj.oo, 3, '(1/x + O(x**(-3), (x, oo)))*exp(x**2)/sqrt(pi) - I'],
    ['Ei(x)', sj.oo, 3, '(2/x**2 + 1/x + 1 + O(x**(-3), (x, oo)))*exp(x)/x'],
    ['expint(3,x)', sj.oo, 3, '(12/x**2 - 3/x + 1 + O(x**(-3), (x, oo)))*exp(-x)/x'],
    ['fresnels(x)', sj.S.NegativeInfinity, 4, '-sin(pi*x**2/2)/(pi**2*x**3) - cos(pi*x**2/2)/(pi*x) - 1/2 + O(x**(-4), (x, -oo))'],
    ['Ci(x)', sj.S.NegativeInfinity, 3, '-(x**(-2) + O(-1/x**3, (x, -oo)))*cos(x) + (1/x + O(-1/x**3, (x, -oo)))*sin(x) + I*pi'],
    ['Si(x)', sj.oo, 3, '-(x**(-2) + O(x**(-3), (x, oo)))*sin(x) - (1/x + O(x**(-3), (x, oo)))*cos(x) + pi/2'],
    ['Li(x)', sj.S.Zero, 2, 'x*(1/log(x) + 1 + O(log(x)**(-2)))/log(x) - li(2)'],
  ] as const) expect(String(series(P(f), x, point, n))).toBe(expected);
  expect(() => series(P('lowergamma(x,2)'), x, sj.S.NegativeInfinity, 2)).toThrow(sj.NotImplementedError);
  expect(() => series(P('lowergamma(y,x)'), x, sj.oo, 2)).toThrow(sj.NotImplementedError);
  expect(() => series(P('lowergamma(x,x)'), x, sj.oo, 2)).toThrow(sj.NotImplementedError);
  expect(String(sj.taylorTerm(P('fresnelc(x)'), 1, x))).toBe('-pi**2*x**5/40');
});

it('uses the appropriate growing or decaying Bessel factors on each real ray', () => {
  for (const [f, point, expected] of [
    ['besseli(1,x)', sj.oo, 'sqrt(2)*(sqrt(1/x) + O((1/x)**(3/2), (x, oo)))*exp(x)/(2*sqrt(pi))'],
    ['besseli(1,x)', sj.S.NegativeInfinity, 'sqrt(2)*(-sqrt(-1/x) + O((-1/x)**(3/2), (x, -oo)))*exp(-x)/(2*sqrt(pi))'],
    ['besselk(1,x)', sj.oo, 'sqrt(2)*sqrt(pi)*(sqrt(1/x) + O((1/x)**(3/2), (x, oo)))*exp(-x)/2'],
    ['besselk(1,x)', sj.S.NegativeInfinity, 'sqrt(2)*sqrt(pi)*(-I*sqrt(-1/x) + O((-1/x)**(3/2), (x, -oo)))*exp(-x)/2'],
  ] as const) expect(String(series(P(f), x, point, 1))).toBe(expected);
});

it('composes local Bessel series and preserves logarithmic orders', () => {
  for (const [f, n, expected] of [
    ['besseli(1,x+x**2)', 3, 'x/2 + x**2/2 + O(x**3)'],
    ['besselj(1,x+x**2)', 5, 'x/2 + x**2/2 - x**3/16 - 3*x**4/16 + O(x**5)'],
  ] as const) expect(String(series(P(f), x, 0, n))).toBe(expected);
  expect(String(series(P('besselk(0,x+x**2)'), x, 0, 6))).toContain('O(x**6*log(x))');
  expect(String(series(P('bessely(0,x+x**2)'), x, 0, 6))).toContain('O(x**6*log(x))');
  for (const name of ['besselk', 'bessely'] as const) {
    expect(String(series(P(`${name}(1,x)`), x, 0, 0))).toContain('O(1)');
  }
  expect(String(series(P('besselk(1,x)'), x, 0, 2)))
    .toBe('1/x + x*(log(x)/2 - log(2)/2 - 1/4 + EulerGamma/2) + O(x**2*log(x))');
});

it('finds the leading terms of Bessel and error functions at their branch points', () => {
  for (const [f, expected] of [
    ['besselj(1,x)', 'x/2'], ['besseli(1,x)', 'x/2'],
    ['besselk(1,1/x)', 'sqrt(2)*sqrt(pi)*exp(-1/x)/(2*sqrt(1/x))'],
    ['besselk(0,x)', '-log(x) - EulerGamma + log(2)'],
    ['bessely(0,x)', '2*(log(x) - log(2) + EulerGamma)/pi'],
    ['bessely(1,x)', '-2/(pi*x)'], ['besselj(0,x+1)', 'besselj(0, 1)'],
    ['erfi(1/x)', 'erfi(1/x)'], ['erfc(x)', '1'],
  ] as const) expect(String(sj.asLeadingTerm(P(f), x))).toBe(expected);
  const oscillation = new sj.Pow(sj.S.E, new sj.Add([P('log(sin(1/x))'), x]));
  expect(sj.asLeadingTerm(oscillation, x)).toBe(sj.S.NaN);
  expect(() => sj.asLeadingTerm(P('besselj(1,x**y)'), x)).toThrow(sj.NotImplementedError);
});

it('expands exponential and oscillatory series at infinity', () => {
  const cases = [
    ['lowergamma(x, 2)', '2**x*(1 + 2/(x + 1))*exp(-2)/x + O(exp(x*log(2))/x**3, (x, oo))'],
    ['lowergamma(2,x)', '1 + O(x**(-3), (x, oo))'],
    ['besselk(0,x)', 'sqrt(2)*sqrt(pi)*(sqrt(1/x) - (1/x)**(3/2)/8 + 9*(1/x)**(5/2)/128 + O((1/x)**(7/2), (x, oo)))*exp(-x)/2'],
    ['besselk(0,-x)', 'sqrt(2)*sqrt(pi)*(-I*sqrt(1/x) - I*(1/x)**(3/2)/8 - 9*I*(1/x)**(5/2)/128 + O((1/x)**(7/2), (x, oo)))*exp(x)/2'],
    ['besseli(0,-x)', 'sqrt(2)*(sqrt(1/x) + (1/x)**(3/2)/8 + 9*(1/x)**(5/2)/128 + O((1/x)**(7/2), (x, oo)))*exp(x)/(2*sqrt(pi))'],
    ['erfc(x)', '(1/x + O(x**(-3), (x, oo)))*exp(-x**2)/sqrt(pi)'],
    ['Ei(x)', '(2/x**2 + 1/x + 1 + O(x**(-3), (x, oo)))*exp(x)/x'],
    ['expint(3,x)', '(12/x**2 - 3/x + 1 + O(x**(-3), (x, oo)))*exp(-x)/x'],
    ['fresnels(x)', '-cos(pi*x**2/2)/(pi*x) + 1/2 + O(x**(-3), (x, oo))'],
    ['Si(x)', '-(x**(-2) + O(x**(-3), (x, oo)))*sin(x) - (1/x + O(x**(-3), (x, oo)))*cos(x) + pi/2'],
    ['Ci(-x)', '-(x**(-2) + O(x**(-3), (x, oo)))*cos(x) - (-1/x + O(x**(-3), (x, oo)))*sin(x) + I*pi'],
  ] as const;
  for (const [input, expected] of cases) expect(String(series(P(input), x, sj.oo, 3))).toBe(expected);
  expect(() => series(P('lowergamma(x, 2)'), x, sj.S.NegativeInfinity, 3)).toThrow(sj.NotImplementedError);
});

it('composes local logarithmic and Bessel series', () => {
  expect(String(series(P('Li(x)'), x, 0, 3))).toBe('x*(2/log(x)**2 + 1/log(x) + 1 + O(log(x)**(-3)))/log(x) - li(2)');
  expect(String(series(P('besseli(1,x+x**2)'), x, 0, 3))).toBe('x/2 + x**2/2 + O(x**3)');
  expect(String(series(P('besselj(1,x+x**2)'), x, 0, 5))).toBe('x/2 + x**2/2 - x**3/16 - 3*x**4/16 + O(x**5)');
  expect(String(series(P('besselk(0,x+x**2)'), x, 0, 5))).toContain('O(x**5*log(x))');
  expect(String(series(P('bessely(0,x+x**2)'), x, 0, 5))).toContain('O(x**5*log(x))');
  expect(String(series(P('besselk(0,x)'), x, 0, 3))).toContain('O(x**3*log(x))');
  expect(String(sj.taylorTerm(sj.fresnelc(x), 1, x))).toBe('-pi**2*x**5/40');
});

it('finds the leading Bessel and error terms on the given ray', () => {
  const cases = [
    ['besselk(0,1/x)', 'sqrt(2)*sqrt(pi)*exp(-1/x)/(2*sqrt(1/x))'],
    ['besselj(0,x)', '1'],
    ['besseli(0,x)', '1'],
    ['bessely(0,sqrt(x))', '2*(log(sqrt(x)) - log(2) + EulerGamma)/pi'],
    ['besselk(0,sqrt(x))', '-log(sqrt(x)) - EulerGamma + log(2)'],
    ['bessely(2,x)', '-4/(pi*x**2)'],
    ['besselj(0,1+x)', 'besselj(0, 1)'],
    ['erf(x)', '2*x/sqrt(pi)'],
    ['erfi(1/x)', 'erfi(1/x)'],
  ] as const;
  for (const [input, expected] of cases) expect(String(sj.asLeadingTerm(P(input), x))).toBe(expected);
  const order = new sj.Order([x.pow(2), x, sj.S.One]);
  expect(sj.replace(order, x, y)).toEqual(sj.O(sj.S.One, y, sj.S.One));
});

it('keeps an unresolved argument branch as a leading-term error', () => {
  expect(() => sj.asLeadingTerm(P('arg(x + I)'), x, { cdir: 1 })).toThrow(sj.NotImplementedError);
});

it('keeps the Bessel I phase on the negative argument ray', () => {
  const bessel = sj.fn('besseli', [sj.Rational.of(1, 3), sj.neg(x)], { evaluate: false });
  expect(String(sj.series(bessel, x, sj.oo, 2))).toBe(
    'sqrt(2)*(sqrt(1/x)*exp(I*pi/3) + 5*(1/x)**(3/2)*exp(I*pi/3)/72 + O((1/x)**(5/2), (x, oo)))*exp(x)/(2*sqrt(pi))',
  );
});

it('finds a finite constant by a limit when the remaining power has irrational order', () => {
  expect(sj.leadterm(P('1+(x+x**2)**sqrt(2)'), x).map(String)).toEqual(['1', '0']);
  expect(() => sj.leadterm(P('(x+x**2)**sqrt(2)-x'), x)).toThrow(SeriesError);
  expect(() => sj.leadterm(P('y+(x+x**2)**sqrt(2)'), x)).toThrow(SeriesError);
});

it('expands binomials with logarithmic power ratios', () => {
  const r = P('log(5)/log(3)');
  const f = sj.mul(x.pow(-1), sj.sub(sj.log(sj.add(y, y.pow(r))), sj.log(y.pow(r.add(1)))));
  expect(String(sj.nseries(f, y, 0, 1))).toBe('-log(5)*log(y)/(x*log(3)) + y**(-1 + log(5)/log(3))/x - y**(-2 + 2*log(5)/log(3))/(2*x) + O(y)');
  expect(String(sj.nseries(P('1/(1/x+x**(log(3)/log(2)))'), x, 0, 5))).toBe('-x**(log(3)/log(2) + 2) + x + O(x**5)');
});

it('uses the degree of the increment in local exponential and logarithmic series', () => {
  expect(String(sj.nseries(P('exp(1+sqrt(x))'), x, 0, 3))).toBe('E + E*x/2 + E*sqrt(x) + O(x**(3/2))');
  expect(String(sj.nseries(P('sin(x)**y'), x, 0, 1, { logx: z }))).toBe('exp(y*z) + O(x)');
  expect(String(sj.nseries(P('exp(1+x)'), x, 0, 2))).toBe('E + E*x + O(x**2)');
  expect(String(sj.series(P('frac(1/x)'), x, 0, 3))).toContain('AccumBounds(0, 1)');
});

it('keeps unresolved order comparisons during addition', () => {
  const o = new sj.Order([x.pow(3)]);
  expect(() => o.contains(x.pow(y))).toThrow(sj.NotImplementedError);
  expect(sj.add(x.pow(y), o)).toBeInstanceOf(sj.Add);
});

it('recognizes constant phase and independent symbolic logarithms', () => {
  expect(String(sj.O(P('x*(2*x)**(I/2)'), x))).toBe('O(x**(1 + I/2))');
  expect(String(series(P('log(x**sqrt(2))'), x, 0, 1))).toBe('sqrt(2)*log(x)');
  expect(String(sj.nseries(P('exp(x+sqrt(x))'), x, 0, 1))).toBe('1 + sqrt(x) + O(x)');
  expect(String(sj.nseries(P('(1+x)**y'), x, 0, 2, { logx: z }))).toBe('1 + x*y + O(x**2)');
  expect(() => sj.nseries(P('(-x+x**2)**y'), x, 0, 2, { logx: z, dir: '-' })).toThrow(SeriesError);
});

it('retains an explicit failure for unsupported generalized power expansions', () => {
  for (const source of [
    '(1+x**sqrt(2))**y', '1/(x+x**sqrt(2)+x**sqrt(3))', 'log(-x+x**sqrt(2))',
    'log(x**sqrt(2))+x**sqrt(3)', '(x**sqrt(2)+x**(sqrt(2)+1/10000000))**(-1)',
    '(x**sqrt(2)+x**(sqrt(2)+log(4)-2*log(2)))**(-1)',
    '1/(1+x**(1+sqrt(2)-14142135623731/10000000000000))',
  ]) expect(() => series(P(source), x, 0, 1)).toThrow(SeriesError);
});

it('carries an order-valued replacement into constant remainders', () => {
  const constant = sj.O(1, x);
  expect(constant.subs(x, sj.O(y)).equals(sj.O(1, y))).toBe(true);
  expect(constant.subs(x, sj.O(y.pow(-1), y, sj.oo)).equals(sj.O(1, y, sj.oo))).toBe(true);
  expect(() => sj.O(x, x, sj.oo).subs(x, sj.O(y))).toThrow(sj.NotImplementedError);
  expect(sj.O(x).subs(x, sj.SymFunction('f')(y))).toBeInstanceOf(sj.Subs);
  expect(String(sj.O(P('x*sin(x+I*x)'), x, sj.oo))).toContain('sin(x + I*x)');
});
