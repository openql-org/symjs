// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import * as sj from '../../src';
import { Concrete, Integral, Product, Q, Rational, S, Sum, Sym, add, ask, hasFiniteLimits, hasReversedLimits, isFinite, isNegative, isPositive, isZero, variables } from '../../src';
const x = new Sym('x'), y = new Sym('y'), M = new Sym('M'), N = new Sym('N',{integer:true,positive:true});
const sum = (a: number, b: number | Sym) => new Concrete('Sum',[x,x,Rational.of(a),typeof b === 'number' ? Rational.of(b) : b]);
it('normalizes discrete ranges in both directions using their spacing', () => {
  for (const ctor of [Sum, Product]) {
    for (const range of [sj.Range.of(3, 10, 2), sj.Range.of(3, S.Infinity, 2), sj.Range.of(S.NegativeInfinity, 5, 2)]) {
      if (!(range instanceof sj.Range)) throw new TypeError('Expected a Range');
      const expected = range.start === S.NegativeInfinity ? ctor(sj.sub(3, x.mul(2)), [x, 0, S.Infinity])
        : ctor(x.mul(2).add(3), [x, 0, range.stop === S.Infinity ? S.Infinity : 3]);
      expect(ctor(x, [x, range]).key).toBe(expected.key);
      expect(ctor(x, [x, range.reversed]).key).toBe(expected.key);
    }
    expect(ctor(x, [x, sj.Range.of(3, 10)]).key).toBe(ctor(x, [x, 3, 9]).key);
    expect(() => ctor(x, [x, sj.interval(1, 3)])).toThrow(TypeError);
    expect(() => ctor(x, [x, sj.finiteSet(1, 3)])).toThrow(sj.NotImplementedError);
  }
});
it('reads variables and finiteness of limits', () => {
  const inner = new Integral([x,x,S.One,S.Infinity]);
  expect(variables(new Integral([inner,y]))).toEqual([x,y]);
  expect(variables(sum(1,8))).toEqual([x]);
  expect(hasFiniteLimits(inner)).toBe(false);
  expect(hasFiniteLimits(sum(1,8))).toBe(true);
  expect(hasFiniteLimits(sum(1,M))).toBe('unknown');
  expect(hasFiniteLimits(sum(1,N))).toBe(true);
  expect(hasFiniteLimits(new Integral([x,x]))).toBe('unknown');
  expect(hasFiniteLimits(new Integral([N,N]))).toBe(true);
  expect(hasFiniteLimits(new Integral([x,N,S.One,M]))).toBe(true);
});
it('keeps unknown orientation distinct from normal and reversed limits', () => {
  expect(hasReversedLimits(sum(8,1))).toBe(true);
  expect(hasReversedLimits(sum(1,8))).toBe(false);
  expect(hasReversedLimits(sum(1,M))).toBe('unknown');
  expect(hasReversedLimits(new Integral([x,x]))).toBe('unknown');
  expect(hasReversedLimits(new Integral([x,x,S.One]))).toBe('unknown');
  expect(hasReversedLimits(new Integral([x,x,S.One,S.Infinity]))).toBe(false);
  expect(hasReversedLimits(new Concrete('Product',[x,x,Rational.of(2),add(N,2)]))).toBe(false);
});

it('derives finite sum and product facts from their terms without evaluating them', () => {
  const M = new Sym('M', { positive: true, integer: true });
  const positive = new Sym('p', { positive: true });
  const negative = new Sym('n', { negative: true });
  const nonnegative = new Sym('a', { nonnegative: true });
  for (const make of [Sum, Product]) {
    expect(isFinite(make(x, [x, 1, M]))).toBe('unknown');
    expect(isFinite(make(positive, [x, 1, M]))).toBe(true);
    expect(isFinite(make(positive, [x, 1, S.Infinity]))).toBe('unknown');
    expect(isPositive(make(positive, [x, 1, M]))).toBe(true);
    expect(isZero(make(0, [x, 1, M]))).toBe(true);
    expect(ask(Q.extended_real(make(S.I, [x, 1, M])))).toBe(false);
    expect(ask(Q.extended_real(make(x, [x, 1, M])))).toBe('unknown');
    expect(ask(Q.nonnegative(make(nonnegative, [x, 0, M])))).toBe(true);
    expect(isNegative(make(nonnegative, [x, 0, M]))).toBe(false);
    expect(ask(Q.integer(make(x, [x, 1, M])))).toBe('unknown');
    expect(isFinite(make(0, [x, M, M.sub(1)]))).toBe(true);
    expect(ask(Q.extended_real(make(0, [x, M, M.sub(1)])))).toBe(true);
  }
  expect(isZero(Sum(x, [x, 1, 0]))).toBe(true);
  expect(isPositive(Product(0, [x, 1, 0]))).toBe(true);
  expect(isZero(Product(0, [x, 1, 0]))).toBe(false);
  expect(isNegative(Sum(negative, [x, M.neg(), -1]))).toBe(true);
  expect(isNegative(Product(negative, [x, M.neg(), -1]))).toBe('unknown');
  expect(isPositive(Sum(positive, [x, M, 1]))).toBe('unknown');
  expect(isPositive(Sum(positive, [x, 1, x]))).toBe('unknown');
  expect(ask(Q.negative(Product(2, [x, 0, S.Infinity])))).toBe(false);
  expect(ask(Q.positive(x))).toBe('unknown');
});

it('accepts connected continuous domains and rejects discrete or disconnected domains', () => {
  expect(sj.integral(x, sj.and(sj.Ge(x, 0), sj.Lt(x, 3))).equals(sj.integral(x, [x, 0, 3]))).toBe(true);
  expect(() => sj.integral(x, [x, sj.Range.of(3)])).toThrow(TypeError);
  expect(() => sj.integral(x, [x, sj.finiteSet(0, 2)])).toThrow(sj.NotImplementedError);
});
