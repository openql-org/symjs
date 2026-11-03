// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/puiseux.ts.
// Puiseux series expansion. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Rational, Sym, parse } from '../../src';
import { Expander, SeriesError } from '../../src/series/puiseux';

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
