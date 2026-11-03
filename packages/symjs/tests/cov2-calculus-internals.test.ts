// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Remaining branches of the limit, series and summation code. Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Rational, Sym, parse } from '../src';
import { Expander, SeriesError } from '../src/series/puiseux';
import { limitWithin } from '../src/series/limits';
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
    ["sj.summation(P('g(2)**k'), [k, 0, sj.oo])", () => sj.summation(P('g(2)**k'), [k, 0, sj.oo]), "Piecewise((1/(1 - g(2)), Abs(g(2)) < 1), (Sum(g(2)**k, (k, 0, oo)), True))"],
    ["conv(sj.Sum(P('log(k)/k**2'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('log(k)/k**2'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('(-1)**k/k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k/k'), [k, 1, sj.oo])), "true"],
    ["sj.O(P('a*z*y*x'))", () => sj.O(P('a*z*y*x')), "O(a*x*y*z, a, x, y, z)"],
    ["sj.O(P('x*y + y*z + x*z'))", () => sj.O(P('x*y + y*z + x*z')), "O(x*y + x*z + y*z, x, y, z)"],
    ["sj.getn(sj.O(P('x**2*y**3'), [x, y]))", () => sj.getn(sj.O(P('x**2*y**3'), [x, y])), "2"],
    ["sj.getn(sj.O(P('1/(x**2*y)'), [x, y], sj.oo))", () => sj.getn(sj.O(P('1/(x**2*y)'), [x, y], sj.oo)), "2"],
    ["sj.aseries(P('exp(-3*x) + exp(-x)'), x, 3, true)", () => sj.aseries(P('exp(-3*x) + exp(-x)'), x, 3, true), "exp(-x) + O(exp(-3*x), (x, oo))"],
    ["sj.aseries(P('exp(-x/2) + exp(-2*x)'), x, 2, true)", () => sj.aseries(P('exp(-x/2) + exp(-2*x)'), x, 2, true), "exp(-x/2) + O(exp(-x), (x, oo))"],
    ["(() => { const it = sj.lseries(P('sqrt(x)*(1 + x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 2) break; } return o; })()", () => (() => { const it = sj.lseries(P('sqrt(x)*(1 + x)'), x, 0, '-'); const o = []; for (const u of it) { o.push(u); if (o.length >= 2) break; } return o; })(), "[I*sqrt(-x), -I*(-x)**(3/2)]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // |x**(I*x)| = 1: x plus a bounded term (SymPy raises NotImplementedError)
    ["sj.limit(P('x + x**(I*x)'), x, sj.oo)", () => sj.limit(P('x + x**(I*x)'), x, sj.oo), "oo", "ERR NotImplementedError"],
    // a bounded oscillation (SymPy raises NotImplementedError)
    ["sj.limit(P('x**(I*x)'), x, sj.oo)", () => sj.limit(P('x**(I*x)'), x, sj.oo), "Limit(x**(I*x), x, oo, dir='-')", "ERR NotImplementedError"],
    // poles at k = 0 and 1 inside the range (SymPy: zoo)
    ["sj.summation(P('k/(k**3 - k)'), [k, 0, sj.oo])", () => sj.summation(P('k/(k**3 - k)'), [k, 0, sj.oo]), "Sum(k/(k**3 - k), (k, 0, oo))", "zoo"],
    // comparison with 1/(n*log(log(n))) is not implemented
    ["conv(sj.Sum(P('1/(k*log(log(k)))'), [k, 3, sj.oo]))", () => conv(sj.Sum(P('1/(k*log(log(k)))'), [k, 3, sj.oo])), "unknown", "false"],
    // SymPy raises ValueError
    ["conv(sj.Sum(P('(-1)**k*sin(k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k*sin(k)'), [k, 1, sj.oo])), "unknown", "ERR ValueError"],
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

describe('the expansion in t (series/puiseux.ts)', () => {
  const tt = new Sym('_t', { positive: true });
  const E = () => new Expander(tt);
  const Q = (s: string) => parse(s, { symbols: [tt] });
  const ser = (s: string, order: number) => {
    const ps = E().ser(Q(s), Rational.of(order));
    return ps.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ') + ` | order ${ps.order.toString()}`;
  };

  it('to an order that is not positive gives the value at 0 (exact for the exponents below the order)', () => {
    expect(ser('sin(_t)', 0)).toBe(' | order 1000000');
    expect(ser('exp(_t)', 0)).toBe('1*t**0 | order 1000000');
    expect(ser('besselj(1, _t)', 0)).toBe(' | order 1000000');
  });

  it('expands cot(t)**2 with more precision for the pole (SymPy: 1/t**2 - 2/3 + t**2/15)', () => {
    expect(ser('cot(_t)**2', 3)).toBe('1*t**-2 + -2/3*t**0 + 1/15*t**2 | order 3');
  });

  it('raises when the leading term is 0 to every order it tries', () => {
    expect(() => E().ser(Q('((sin(a)**2 + cos(a)**2 - 1)*_t + _t**10)**(1/2)'), Rational.of(2))).toThrow(SeriesError);
    expect(() => E().ser(Q('log((sin(a)**2 + cos(a)**2 - 1)*_t)'), Rational.of(2))).toThrow(SeriesError);
    expect(() => E().ser(Q('sign((sin(a)**2 + cos(a)**2 - 1)*_t)'), Rational.of(2))).toThrow(SeriesError);
  });

  it('stops at a nesting depth of 200', () => {
    let e = '_t';
    for (let i = 0; i < 201; i++) e = `exp(${e})`;
    expect(() => E().ser(Q(e), Rational.of(1))).toThrow('recursion too deep');
  });
});

describe('limits with a small budget of nested limit computations', () => {
  it('gives up when the budget is spent (SymPy 1.14: 0)', () => {
    expect(String(limitWithin(P('sin(x)*sin(1/x)'), x, 0, '+', 1))).toBe("Limit(sin(1/x)*sin(x), x, 0, dir='+')");
    expect(String(limitWithin(P('sin(x)*sin(1/x)'), x, 0, '+', 1000))).toBe('0');
  });

  it("does not apply L'Hopital's rule deeper than 30 nested limits (SymPy 1.14: 0)", () => {
    let e = 'x*Ei(x)';
    for (let i = 0; i < 31; i++) e = `sin(${e})`;
    expect(String(sj.limit(P(e), x, 0))).toBe(`Limit(${P(e).toString()}, x, 0, dir='+')`);
    expect(String(sj.limit(P('x*Ei(x)'), x, 0))).toBe('0');
  });
});
