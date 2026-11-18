// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { cast } from '../../src/core/guard';
import { EmptySet, FiniteSet, ImageSet, Interval, SetExpr, SetExpression, Sym, Union, add, mul } from '../../src';
it('computes pointwise sums and scales without changing set union semantics', () => {
  const a = SetExpression(Interval.of(0, 5)), b = new SetExpression(FiniteSet.of(1, 10));
  expect(String(a.add(b))).toBe('SetExpr(Union(Interval(1, 6), Interval(10, 15)))');
  expect(String(add(mul(2, a), b))).toBe('SetExpr(Interval(1, 20))');
  expect(a.set).toBeInstanceOf(SetExpr);
  expect(a).not.toBeInstanceOf(SetExpr);
  expect(String(a.applyfunc((x) => x.pow(2)).set)).toBe('Interval(0, 25)');
  expect(a.withArgs([b.set]).set).toBe(b.set);
});
it('distributes over unions, handles empty sets and preserves open endpoints', () => {
  const a = SetExpression(Union(Interval.of(0, 1), Interval.of(3, 4)));
  const b = SetExpression(Interval.open(0, 1));
  expect(String(a.add(b))).toBe('SetExpr(Union(Interval.open(0, 2), Interval.open(3, 5)))');
  expect(String(b.add(a))).toBe(String(a.add(b)));
  expect(String(b.sub(SetExpression(Interval.Ropen(2, 3))))).toBe('SetExpr(Interval.open(-3, -1))');
  expect(String(SetExpression(FiniteSet.of(1, 2)).mul(3))).toBe('SetExpr({3, 6})');
  expect(String(SetExpression(Interval.of(1, 2)).pow(2))).toBe('SetExpr(Interval(1, 4))');
  expect(String(SetExpression(EmptySet).add(b))).toBe('SetExpr(EmptySet)');
  expect(String(b.add(SetExpression(EmptySet)))).toBe('SetExpr(EmptySet)');
  const result = b.mul(b);
  expect(String(result)).toBe('SetExpr(Interval.open(0, 1))');
  const x = new Sym('x');
  expect(String(add(x, x))).toBe('2*x');
});
it('subtracts closed intervals and keeps general images exact', async () => {
  const { Reals } = await import('../../src');
  const closed = SetExpression(Interval.of(0,1));
  expect(String(closed.sub(SetExpression(Interval.of(2,3))))).toBe('SetExpr(Interval(-3, -1))');
  expect(closed.add(SetExpression(Reals)).args[0]).toBeInstanceOf(ImageSet);
  expect(SetExpression(Reals).mul(closed).args[0]).toBeInstanceOf(ImageSet);
});
it('keeps exact endpoint images for products, reciprocals and integer powers', async () => {
  const { S, rational, containsQ } = await import('../../src');
  const wrap = (a: number, b: number, left = false, right = false) => SetExpression(Interval.of(a, b, left, right));
  expect(String(wrap(-1, 3).pow(-2))).toBe('SetExpr(Interval(1/9, oo))');
  expect(String(wrap(-3, 1).pow(-2))).toBe('SetExpr(Interval(1/9, oo))');
  expect(String(wrap(-1, 1, true, false).pow(-2))).toBe('SetExpr(Interval(1, oo))');
  expect(String(wrap(-1, 1, true, true).pow(-2))).toBe('SetExpr(Interval.open(1, oo))');
  expect(String(wrap(-1, 1, true, false).pow(2))).toBe('SetExpr(Interval(0, 1))');
  expect(String(wrap(-3, 1).pow(2))).toBe('SetExpr(Interval(0, 9))');
  expect(String(wrap(-1, 3).pow(2))).toBe('SetExpr(Interval(0, 9))');
  expect(String(wrap(0, 2).pow(-1))).toBe('SetExpr(Interval(1/2, oo))');
  expect(String(wrap(-2, 0).pow(-1))).toBe('SetExpr(Interval(-oo, -1/2))');
  expect(String(wrap(0, 2, true).pow(2))).toBe('SetExpr(Interval.Lopen(0, 4))');
  expect(String(wrap(0, 2).pow(rational(1, 2)))).toBe('SetExpr(Interval(0, sqrt(2)))');
  expect(String(wrap(0, 4).pow(rational(-1, 2)))).toBe('SetExpr(Interval(1/2, oo))');
  expect(String(wrap(1, 4).pow(rational(-1, 2)))).toBe('SetExpr(Interval(1/2, 1))');
  expect(String(wrap(-2, 3).pow(rational(1, 2)))).toContain('ImageSet');
  expect(String(wrap(0, 2).pow(S.NegativeInfinity))).toBe('SetExpr(Interval(0, oo))');
  expect(String(wrap(-2, 3).pow(S.NegativeInfinity))).toContain('ImageSet');
  const reciprocal = wrap(-2, 2).pow(-1);
  expect(containsQ(cast(reciprocal, SetExpression).set, rational(0))).toBe(false);
  expect(String(wrap(-2, 3).div(wrap(-2, 3)))).toBe('SetExpr(Interval(-oo, oo))');
  expect(String(wrap(0, 1).mul(SetExpression(Interval.of(1, S.Infinity))))).toBe('SetExpr(Interval(0, oo))');
  expect(String(wrap(0, 1, true).mul(SetExpression(Interval.of(1, S.Infinity))))).toBe('SetExpr(Interval.open(0, oo))');
  expect(String(wrap(0, 1).mul(wrap(-1, 0)))).toBe('SetExpr(Interval(-1, 0))');
  expect(String(wrap(-1, 1).mul(wrap(-1, 1, true, true)))).toBe('SetExpr(Interval.open(-1, 1))');
  const x = new Sym('x');
  expect(String(wrap(1, 2).pow(x))).toContain('ImageSet');
  expect(String(SetExpression(Interval.of(x, x.add(1))).pow(2))).toContain('ImageSet');
  expect(String(SetExpression(Interval.of(x, x.add(1))).mul(wrap(1, 2)))).toContain('ImageSet');
});
