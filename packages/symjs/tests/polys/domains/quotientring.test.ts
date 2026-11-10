// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { QQ, PolynomialRingBase, QuotientRing } from '../../../src/polys';
import { Sym, parse as p, str } from '../../../src/core';
import { NotImplementedError } from '../../../src/core/errors';
const x = new Sym('x'), y = new Sym('y'), R = new PolynomialRingBase(QQ, [x, y]);
it('reduces polynomial representatives and tests equality of defining ideals', () => {
  const K = new QuotientRing(R, [p('x*x-y*y')]);
  expect(String(K)).toBe('QQ[x,y]/<x**2 - y**2>');
  expect(K.dom).toBe(QQ);
  expect(str(K.fromSympy(p('x*x+y*y')))).toBe('2*y**2');
  expect(K.equals(R.quotientRing(R.ideal(p('2*x*x-2*y*y'))))).toBe(true);
  expect(K.equals(R.quotientRing([x]))).toBe(false);
  expect(K.equals(R)).toBe(false);
  expect(K.equals(QQ.oldPolyRing(x).quotientRing([x]))).toBe(false);
  expect(() => K.getField()).toThrow(NotImplementedError);
  expect(() => new QuotientRing(R, QQ.oldPolyRing(x).ideal(x))).toThrow(RangeError);
  expect(() => new PolynomialRingBase(QQ, [x], 'ilex').quotientRing([x])).toThrow(NotImplementedError);
  const nested = K.quotientRing([y]);
  expect(str(nested.fromSympy(p('x*x+y')))).toBe('0');
  expect(nested.freeModule(1).submodule([x]).syzygyModule().contains([x])).toBe(true);
});
