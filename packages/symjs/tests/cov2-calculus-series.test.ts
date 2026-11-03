// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Series, orders and leading terms (series/series.ts, series/more.ts, series/puiseux.ts). Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Sym, parse } from '../src';
import { Expr } from '../src/core/nodes';
import { NoMatchResult } from '../src/core/truth';

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
    ["[...sj.lseries(P('x**2 + x'), x, 1)]", () => [...sj.lseries(P('x**2 + x'), x, 1)], "[2, 3*x - 3, (x - 1)**2]"],
    ["(() => { const it = sj.lseries(P('sin(x)'), x); const o = []; for (const u of it) { o.push(u); if (o.length >= 5) break; } return o; })()", () => (() => { const it = sj.lseries(P('sin(x)'), x); const o = []; for (const u of it) { o.push(u); if (o.length >= 5) break; } return o; })(), "[x, -x**3/6, x**5/120, -x**7/5040, x**9/362880]"],
    ["(() => { const it = sj.lseries(P('1/(1 - x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 4) break; } return o; })()", () => (() => { const it = sj.lseries(P('1/(1 - x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 4) break; } return o; })(), "[1, x, x**2, x**3]"],
    ["sj.dir(P('sqrt(x)'), x, 1)", () => sj.dir(P('sqrt(x)'), x, 1), "1/2"],
    ["sj.dir(P('x*log(x)'), x, 1)", () => sj.dir(P('x*log(x)'), x, 1), "-oo"],
    ["sj.dir(P('sin(x)/x - 1'), x, 1)", () => sj.dir(P('sin(x)/x - 1'), x, 1), "-1/3"],
    ["sj.dir(P('x**2 + x**3'), x, -1)", () => sj.dir(P('x**2 + x**3'), x, -1), "2"],
    ["sj.dir(P('0'), x, 1)", () => sj.dir(P('0'), x, 1), "0"],
    ["sj.dir(P('x**(3/2)*log(x)'), x, 1)", () => sj.dir(P('x**(3/2)*log(x)'), x, 1), "-oo"],
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
    // expansions at complex infinity are not implemented
    ["sj.series(x, x, P('zoo'))", () => sj.series(x, x, P('zoo')), "ERR NotImplementedError: series: expansion at this point is not supported", "x"],
    // sign(I + x) = (I + x)/sqrt(1 + x**2) is not constant near 0 (SymPy gives its value I)
    ["sj.series(P('sign(I + x)'), x, 0, 3)", () => sj.series(P('sign(I + x)'), x, 0, 3), "ERR SeriesError: cannot expand sign", "I"],
    // |y*x| is not analytic in x for a complex y
    ["sj.series(P('abs(y*x)'), x, 0, 3)", () => sj.series(P('abs(y*x)'), x, 0, 3), "ERR SeriesError: cannot expand abs", "x*Abs(y)"],
    // floor(x + y) jumps at x = 0 when y is an integer
    ["sj.series(P('floor(x + y)'), x, 0, 3)", () => sj.series(P('floor(x + y)'), x, 0, 3), "ERR SeriesError: cannot expand floor", "floor(y)"],
    // SymPy raises NotImplementedError
    ["sj.series(P('ceiling(y*x)'), x, 0, 3)", () => sj.series(P('ceiling(y*x)'), x, 0, 3), "ERR SeriesError: cannot expand ceiling", "ERR NotImplementedError"],
    // an essential singularity (SymPy returns the expression)
    ["sj.series(P('exp(1/x)'), x, 0, 2)", () => sj.series(P('exp(1/x)'), x, 0, 2), "ERR SeriesError: essential singularity", "exp(1/x)"],
    // SymPy raises ValueError
    ["sj.series(P('cos(x)'), x, 0, -1)", () => sj.series(P('cos(x)'), x, 0, -1), "ERR RangeError: series: the order n must be nonnegative", "ERR ValueError"],
    // an infinite coefficient
    ["sj.series(P('oo*x'), x, 0, 2)", () => sj.series(P('oo*x'), x, 0, 2), "ERR SeriesError: infinite coefficient", "oo"],
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
    // SymPy 1.14 raises AttributeError for a polynomial
    ["[...sj.lseries(P('x**2'), x)]", () => [...sj.lseries(P('x**2'), x)], "[x**2]", "ERR AttributeError"],
    // AccumBounds are not implemented
    ["sj.dir(P('sqrt(x)*(2 + sin(1/x))'), x, 1)", () => sj.dir(P('sqrt(x)*(2 + sin(1/x))'), x, 1), "Limit((sin(1/x) + 2)/(2*sqrt(x)) - cos(1/x)/x**(3/2), x, 0, dir='+')", "oo*sign(AccumBounds(-1, 1))"],
    // SymPy raises NotImplementedError too
    ["sj.getn(sj.O(P('log(x)*log(y)'), [x, y]))", () => sj.getn(sj.O(P('log(x)*log(y)'), [x, y])), "ERR NotImplementedError: not sure of order of log(x)*log(y)", "ERR NotImplementedError"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});
