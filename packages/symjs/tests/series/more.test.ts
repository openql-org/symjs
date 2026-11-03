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
});
