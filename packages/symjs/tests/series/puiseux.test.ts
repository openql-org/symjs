// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/puiseux.ts.
// Puiseux series expansion. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Rational, Sym, add, beta, hyper, mul, parse, pow, series, str } from '../../src';
import type { Expr } from '../../src';
import { Expander, SCALED_BESSELI, SCALED_EI, SCALED_ERFC, SeriesError } from '../../src/series/puiseux';
import { UndefFn } from '../../src/core/nodes';

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
const pw = (e: unknown): sj.Piecewise => {
  if (!(e instanceof sj.Piecewise)) throw new TypeError('a Piecewise expected');
  return e;
};
const conc = (e: unknown): sj.Concrete => {
  if (!(e instanceof sj.Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const conv = (e: unknown) => sj.isConvergent(conc(e));
const aconv = (e: unknown) => sj.isAbsolutelyConvergent(conc(e));
const moo = P('-oo');
void [x, y, z, n, k, a, b, c, m, t, pp, qq, rr, conv, aconv, moo, pw];

describe('the expansion in t (series/puiseux.ts)', () => {
  const tt = new Sym('_t', { positive: true });
  const E = () => new Expander(tt);
  const Q = (s: string) => parse(s, { symbols: [tt] });
  const ser = (s: string, order: number) => {
    const ps = E().ser(Q(s), Rational.of(order));
    return ps.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ') + ` | order ${ps.order.toString()}`;
  };
  it('expands the scaled Ei and erfc helpers only at positive infinity', () => {
    for (const name of [SCALED_EI, SCALED_ERFC]) {
      expect(() => E().ser(new UndefFn(name, [tt]), Rational.of(2))).toThrow(SeriesError);
      const ps = E().ser(new UndefFn(name, [pow(tt, -1)]), Rational.of(4));
      expect(ps.terms.map((t) => [String(t.e), String(t.c)])).toEqual(name === SCALED_EI ? [['1', '1'], ['2', '1'], ['3', '2']] : [['1', '1/sqrt(pi)'], ['3', '-1/(2*sqrt(pi))']]);
    }
  });

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

describe('expansions on branch cuts and at branch points (SymPy 1.14 series)', () => {
  it.each([
    ['acoth(x)', '-I*pi/2 + x + O(x**3)'],
    ['acoth(-x)', 'I*pi/2 - x + O(x**3)'],
    ['asech(x)', 'log(2) - log(x) - x**2/4 + O(x**3)'],
    ['asech(-x)', 'I*pi + log(2) - log(x) - x**2/4 + O(x**3)'],
    ['acsch(x)', 'log(2) - log(x) + x**2/4 + O(x**3)'],
    ['acsch(-x)', '-log(2) + log(x) - x**2/4 + O(x**3)'],
    ['sqrt(-1 + a*x)', 'I - I*a*x/2 - I*a**2*x**2/8 + O(x**3)'],
    ['sqrt(-1 + f(1)*x)', 'I - I*x*f(1)/2 - I*x**2*f(1)**2/8 + O(x**3)'],
    ['1/(f(a) + 1 + x)', '1/(f(a) + 1) - x/(f(a) + 1)**2 + x**2/(f(a) + 1)**3 + O(x**3)'],
    ['loggamma(x + 1)', '-EulerGamma*x + pi**2*x**2/12 + O(x**3)'],
    ['log(-1 - I*x)', '-I*pi + I*x + x**2/2 + O(x**3)'],
    ['sqrt(-1 - I*x**2)', '-I + x**2/2 + O(x**3)'],
  ])('series(%s, x, 0, 3) = %s', (e, expected) => {
    const [x] = sj.symbols('x');
    expect(String(sj.series(parse(e), x, 0, 3))).toBe(expected);
  });
  it('keeps acsch real for a small negative argument', () => {
    // SymPy 1.14 gives I*pi + log(2) - log(x) + x + 3*x**2/4 + O(x**3), which is wrong: acsch(-1/1000) = -7.6009...
    // is real (acsch is odd), and this series is -acsch(x - x**2)
    const [x] = sj.symbols('x');
    expect(String(sj.series(parse('acsch(x**2 - x)'), x, 0, 3))).toBe('-log(2) + log(x) - x - 3*x**2/4 + O(x**3)');
  });
  it('does not expand acoth at 0 along an unknown direction', () => {
    // SymPy 1.14: log(1/a)/2 - log(-1/a)/2 + a*x + O(x**3)
    const [x] = sj.symbols('x');
    expect(() => sj.series(parse('acoth(a*x)'), x, 0, 3)).toThrow();
  });
});

describe('Ei, frac and the Gruntz Bessel helpers (SymPy 1.14)', () => {
  const [u, w] = sj.symbols('u w');
  const S = (e: sj.Expr, d: '+' | '-' = '+', k = 6) => String(sj.series(e, u, 0, k, d));
  const Q = (s: string) => parse(s, { symbols: [u, w], locals: { frac: sj.frac } });
  it('expands Ei at 0 with log(g), or log(-g) on the negative real axis', () => {
    expect(S(Q('Ei(-u)'))).toBe('EulerGamma + log(u) - u + u**2/4 - u**3/18 + u**4/96 - u**5/600 + O(u**6)');
    expect(S(Q('Ei(-u)'), '-')).toBe('EulerGamma + log(-u) - u + u**2/4 - u**3/18 + u**4/96 - u**5/600 + O(u**6)');
    expect(S(Q('Ei(u**2)'), '-')).toBe('EulerGamma + 2*log(-u) + u**2 + u**4/4 + O(u**6)');
    expect(S(Q('Ei(I*u)'))).toBe('I*pi/2 + EulerGamma + log(u) + I*u - u**2/4 - I*u**3/18 + u**4/96 + I*u**5/600 + O(u**6)');
    expect(S(Q('Ei(u*w)'))).toBe('EulerGamma + log(w) + log(u) + u*w + u**2*w**2/4 + u**3*w**3/18 + u**4*w**4/96 + u**5*w**5/600 + O(u**6)');
    expect(S(Q('Ei(-log(2)*u)'), '+', 2)).toBe('EulerGamma + log(log(2)) + log(u) - u*log(2) + O(u**2)');
  });

  it('expands frac on either side of its jumps', () => {
    expect(S(Q('frac(u)'))).toBe('u');
    expect(S(Q('frac(u)'), '-')).toBe('u + 1');
    expect(S(Q('frac(-u)'))).toBe('1 - u');
    expect(S(Q('frac(u + 1/2)'), '-')).toBe('u + 1/2');
    expect(S(Q('frac(3 + u**2)'), '-', 3)).toBe('u**2');
    expect(S(Q('frac(w + u)'))).toBe('u + frac(w)');
    // the side is not known (SymPy: u*w), or w could be an integer (SymPy: -u + frac(w), wrong for an integer w)
    expect(() => S(Q('frac(u*w)'))).toThrow(SeriesError);
    expect(() => S(Q('frac(w - u)'))).toThrow(SeriesError);
    // (no power of u in the argument shows the side)
    expect(() => S(Q('frac(1 + exp(-1/u))'))).toThrow(SeriesError);
  });

  it('keeps exp(c/u) for a constant c of unknown sign', () => {
    expect(S(Q('exp(f(1)/u)'))).toBe('exp(f(1)/u)');
  });

  it('expands the scaled Bessel functions only at an argument tending to oo', () => {
    const t = new Sym('t', { positive: true });
    expect(() => new Expander(t).ser(new UndefFn(SCALED_BESSELI, [Rational.of(0), t]), Rational.of(1))).toThrow(SeriesError);
  });
});

describe('series of hyper and beta (sympy.stats moments from moment generating functions)', () => {
  const [t, a, b] = [new Sym('t'), new Sym('a'), new Sym('b')];
  const sr = (e: Expr, n: number): string => str(series(e, t, 0, n));
  it('hyper with an argument that vanishes at 0', () => {
    expect(sr(hyper([a], [b], t), 3)).toBe('1 + a*t/b + a*t**2*(a + 1)/(2*b*(b + 1)) + O(t**3)');
    expect(sr(hyper([1], [Rational.of(3, 2)], mul(Rational.of(1, 2), pow(t, 2))), 5)).toBe('1 + t**2/3 + t**4/15 + O(t**5)');
  });
  it('hyper with an argument that does not vanish at 0', () => {
    // SymPy: E - 1 + t + O(t**2) (by hyperexpand); symjs expands only about a vanishing argument
    expect(() => series(hyper([1], [2], add(1, t)), t, 0, 2)).toThrow('cannot expand');
  });
  it('beta as a quotient of gamma functions', () => {
    expect(sr(beta(add(1, mul(-1, t)), add(1, t)), 3)).toBe('1 + pi**2*t**2/6 + O(t**3)');
  });
});

describe('abs of a term with a negative leading coefficient', () => {
  it('Expander: abs(t**2 - t) = t - t**2 for t -> 0+', () => {
    const t = new Sym('_t', { positive: true });
    const ps = new Expander(t).ser(parse('Abs(_t**2 - _t)', { symbols: [t] }), Rational.of(3));
    expect(ps.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ')).toBe('1*t**1 + -1*t**2');
    const qs = new Expander(t).ser(parse('Abs(_t + b*_t**2)', { symbols: [t] }), Rational.of(3));
    expect(qs.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ')).toBe('1*t**1 + b*t**2');
    // a symbolic leading coefficient: its sign is not known
    expect(() => new Expander(t).ser(parse('Abs(b*_t + _t**2)', { symbols: [t] }), Rational.of(3))).toThrow(SeriesError);
  });
});
