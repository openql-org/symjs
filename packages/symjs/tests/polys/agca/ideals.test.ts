// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { PolynomialRingBase, QQ } from '../../../src/polys';
import { Sym, parse as p, str } from '../../../src/core';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const x = new Sym('x'), y = new Sym('y'), R = new PolynomialRingBase(QQ, [x, y]);
it('computes ideal operations using rank-one modules', () => {
  const I = R.ideal(x), J = R.ideal(y);
  expect(String(I.intersect(J))).toBe(refs['ideal_intersection']);
  expect(I.product(J).equals(I.intersect(J))).toBe(true);
  expect(String(R.ideal(p('x*y')).quotient(R.ideal(x, y)))).toBe(refs['ideal_quotient']);
  expect(I.union(J).subset([x, y, p('x+y')])).toBe(true);
  expect(I.subset(R.ideal(p('x*x')))).toBe(true);
  expect(I.subset([x, 1])).toBe(false);
  expect(I.isWholeRing()).toBe(false);
  expect(R.ideal(3).isWholeRing()).toBe(true);
  expect(new PolynomialRingBase(QQ, [x], 'ilex').ideal(p('x+2')).isWholeRing()).toBe(true);
  expect(R.ideal().isZero()).toBe(true);
  expect(I.isZero()).toBe(false);
  expect(str(R.ideal(p('x*x-y')).reduceElement(p('x*x+y')))).toBe('2*y'); // SymPy 1.14.0
  const other = new PolynomialRingBase(QQ, [x]).ideal(x);
  expect(I.equals(other)).toBe(false);
  expect(() => I.intersect(other)).toThrow(RangeError);
  expect(() => I.union(other)).toThrow(RangeError);
  expect(() => I.product(other)).toThrow(RangeError);
  expect(() => I.quotient(other)).toThrow(RangeError);
});
it('supports the ideal operators +, * and ** (SymPy test_ideal_operations)', async () => {
  const { NotImplementedError } = await import('../../../src/core/errors');
  const I = R.ideal(x), J = R.ideal(y), T = R.ideal(x, y), S = R.ideal(p('x*y'));
  expect(I.add(J).equals(T)).toBe(true);
  expect(I.mul(J).equals(S)).toBe(true);
  expect(I.mul(y).equals(S)).toBe(true);
  expect(T.pow(0).equals(R.ideal(1))).toBe(true);
  expect(T.pow(2).equals(R.ideal(p('x**2'), p('y**2'), p('x*y')))).toBe(true);
  expect(() => T.pow(-1)).toThrow(NotImplementedError);
});
