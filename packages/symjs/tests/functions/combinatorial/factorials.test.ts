// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { ff, rf, Fn, Poly, S, Sym, expand, mul, pow, rational } from '../../../src';
import { add, and, ask, binomial, diff, fn, Q, rewrite } from '../../../src';

const x = new Sym('x');
const y = new Sym('y');

it('evaluates ordinary factorial products through the expression API', () => {
  expect(ff(5, 3)).toEqual(rational(60));
  expect(rf(5, 3)).toEqual(rational(210));
  expect(rf(-1, S.Pi)).toBe(S.Zero);
});

it('shifts polynomial generators and preserves polynomial results', () => {
  const p = Poly.from(mul(x, x), [x]);
  for (const [f, direction] of [[ff, -1], [rf, 1]] as const) {
    const result = f(p, 3);
    expect(result).toBeInstanceOf(Poly);
    if (!(result instanceof Poly)) throw new TypeError('expected Poly');
    expect(result.asExpr().equals(expand(mul(p.asExpr(), p.shift(direction).asExpr(), p.shift(2 * direction).asExpr())))).toBe(true);
    expect(f(p, -2).equals(pow(expand(mul(p.shift(-direction).asExpr(), p.shift(-2 * direction).asExpr())), -1))).toBe(true);
    expect(f(p, 0)).toBe(S.One);
    expect(() => f(p, rational(1, 2))).toThrow(TypeError);
    expect(() => f(Poly.from(x, [x, y]), 2)).toThrow(RangeError);
    expect(() => f(Poly.from(x, [x, y]), -2)).toThrow(RangeError);
  }
});

it('uses the public constructors as expression heads', () => {
  expect(new Fn('ff', [x, y]).func).toBe(ff);
  expect(new Fn('rf', [x, y]).func).toBe(rf);
});

it('rewrites factorial products and keeps factorial quotients conditional on the index domain', () => {
  const n = new Sym('n', { integer: true });
  const k = new Sym('k', { integer: true });
  expect(rewrite(rf(x, k), 'FallingFactorial')).toEqual(ff(add(x, k, -1), k));
  expect(rewrite(ff(x, k), 'RisingFactorial')).toEqual(rf(add(x, mul(-1, k), 1), k));
  for (const f of [rf, ff]) {
    expect(rewrite(f(n, k), 'factorial').kind).toBe('Piecewise');
    expect(rewrite(f(x, k), 'factorial')).toEqual(f(x, k));
    expect(rewrite(f(n, y), 'factorial')).toEqual(f(n, y));
    expect(rewrite(f(x, k), 'binomial').has(fn('factorial', [k]))).toBe(true);
    expect(rewrite(f(x, y), 'binomial')).toEqual(f(x, y));
  }
  expect(rewrite(ff(x, k), 'gamma').kind).toBe('Piecewise');
  expect(rewrite(ff(5, k), 'gamma')).toEqual(mul(120, pow(fn('gamma', [add(6, mul(-1, k))]), -1)));
  expect(rewrite(fn('factorial2', [k]), 'gamma').has(fn('gamma', [add(mul(S.Half, k), 1)]))).toBe(true);
  expect(rewrite(fn('subfactorial', [x]), 'uppergamma')).toEqual(mul(pow(S.E, -1), fn('uppergamma', [add(x, 1), -1])));
});

it('differentiates binomial coefficients with respect to both arguments', () => {
  const f = binomial(x, y);
  const psi = (z: typeof f) => fn('polygamma', [0, add(z, 1)]);
  const gap = psi(add(x, mul(-1, y)));
  expect(diff(f, x)).toEqual(mul(f, add(psi(x), mul(-1, gap))));
  expect(diff(f, y)).toEqual(mul(f, add(gap, mul(-1, psi(y)))));
});

it('derives factorial facts from the argument domain and parity', () => {
  const n = new Sym('n', { integer: true });
  const m = new Sym('m', { integer: true, nonnegative: true });
  const even = new Sym('even', { even: true, positive: true });
  const odd = new Sym('odd', { odd: true, positive: true });
  const negativeOdd = new Sym('negativeOdd', { odd: true, negative: true });
  const noninteger = new Sym('noninteger', { noninteger: true });
  const factorial = (v: typeof n | ReturnType<typeof add>) => fn('factorial', [v]);
  const double = (v: typeof n | ReturnType<typeof add> | number) => fn('factorial2', [v], { evaluate: false });
  const subfactorial = (v: typeof n) => fn('subfactorial', [v]);

  expect(ask(Q.integer(factorial(m)))).toBe(true);
  expect(ask(Q.integer(factorial(x)), and(Q.integer(x), Q.nonnegative(x)))).toBe(true);
  expect(ask(Q.positive(factorial(m)))).toBe(true);
  expect(ask(Q.real(factorial(noninteger)))).toBe(true);
  expect(ask(Q.real(factorial(n)))).toBe('unknown');
  expect(ask(Q.even(factorial(add(m, 2))))).toBe(true);
  expect(ask(Q.composite(factorial(add(m, 3))))).toBe(true);
  expect(ask(Q.nonnegative(subfactorial(m)))).toBe(true);
  expect(ask(Q.even(subfactorial(odd)))).toBe(true);
  expect(ask(Q.odd(subfactorial(even)))).toBe(true);
  expect(ask(Q.odd(subfactorial(n)))).toBe('unknown');
  expect(ask(Q.odd(subfactorial(m)))).toBe('unknown');
  expect(ask(Q.odd(factorial(m)))).toBe('unknown');
  expect(ask(Q.integer(double(add(odd, -4))))).toBe(true);
  expect(ask(Q.nonnegative(double(negativeOdd)))).toBe('unknown');
  expect(ask(Q.positive(double(add(even, -3))))).toBe(true);
  expect(ask(Q.positive(double(-5)))).toBe(true);
  expect(ask(Q.positive(double(m)))).toBe(true);
  expect(ask(Q.even(double(negativeOdd)))).toBe(false);
  expect(ask(Q.even(double(even)))).toBe(true);
  expect(ask(Q.odd(double(even)))).toBe(false);
  expect(ask(Q.odd(double(odd)))).toBe(true);
  expect(ask(Q.even(double(0)))).toBe(false);
  expect(ask(Q.odd(double(0)))).toBe(true);
  expect(ask(Q.integer(double(x)))).toBe('unknown');
  expect(ask(Q.even(double(n)))).toBe('unknown');
  expect(ask(Q.even(double(mul(2, n))))).toBe('unknown');
});

it('keeps integrality unknown for products and binomial coefficients with undecided domains', () => {
  const n = new Sym('n', { integer: true });
  const m = new Sym('m', { integer: true, nonnegative: true });
  const neg = new Sym('neg', { integer: true, negative: true });
  const odd = new Sym('odd', { odd: true, positive: true });
  const noninteger = new Sym('noninteger', { noninteger: true });
  const raw = (head: Fn['name'], a: Sym | typeof S.Pi, b: Sym | number) => fn(head, [a, b], { evaluate: false });
  for (const f of [rf, ff]) {
    expect(ask(Q.integer(f(n, m)))).toBe(true);
    expect(ask(Q.integer(f(n, n)))).toBe('unknown');
    expect(ask(Q.integer(f(S.Pi, m)))).toBe('unknown');
  }
  expect(ask(Q.integer(raw('rf', n, 0)))).toBe(true);
  expect(ask(Q.nonnegative(raw('rf', n, m)))).toBe('unknown');
  expect(ask(Q.integer(raw('ff', n, noninteger)))).toBe(false);
  expect(ask(Q.integer(raw('rf', m, noninteger)))).toBe(false);
  expect(ask(Q.integer(raw('rf', neg, noninteger)))).toBe('unknown');
  expect(ask(Q.integer(raw('binomial', x, 0)))).toBe(true);
  expect(ask(Q.integer(raw('binomial', n, n)))).toBe(true);
  expect(ask(Q.integer(raw('binomial', x, noninteger)))).toBe('unknown');
  expect(ask(Q.integer(raw('binomial', neg, noninteger)))).toBe(false);
  expect(ask(Q.nonnegative(raw('binomial', m, m)))).toBe(true);
  expect(ask(Q.nonnegative(raw('binomial', n, neg)))).toBe(true);
  expect(ask(Q.nonnegative(raw('binomial', n, 2)))).toBe(true);
  expect(ask(Q.nonnegative(raw('binomial', neg, odd)))).toBe(false);
  expect(ask(Q.nonnegative(raw('binomial', neg, n)))).toBe('unknown');
  expect(ask(Q.nonnegative(raw('binomial', x, n)))).toBe('unknown');
  expect(ask(Q.composite(raw('binomial', x, n)))).toBe('unknown');
});
