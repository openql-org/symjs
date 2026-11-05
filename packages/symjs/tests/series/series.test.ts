// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/series.ts.
// Series expansion. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse, DiracDelta, Heaviside, series, symbol, sstr, symbols } from '../../src';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';

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
    // a variable inside a function: the expression is kept (SymPy expands sin(x))
    ["sj.O(P('sin(x)*y + x**2'), [x, y])", () => sj.O(P('sin(x)*y + x**2'), [x, y]), "O(x**2 + y*sin(x), x, y)", "O(x**2 + x*y, x, y)"],
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
    // SymPy gives floor(y) and ceiling(y), which is wrong for an integer y (floor(-x) = -1 for x -> 0+)
    ["sj.series(P('floor(x + y)'), x, 0, 3, '-')", () => sj.series(P('floor(x + y)'), x, 0, 3, '-'), "ERR SeriesError: cannot expand floor", "floor(y)"],
    ["sj.series(P('ceiling(x + y)'), x, 0, 3)", () => sj.series(P('ceiling(x + y)'), x, 0, 3), "ERR SeriesError: cannot expand ceiling", "ceiling(y)"],
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
