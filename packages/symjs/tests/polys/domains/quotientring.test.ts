// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { QQ, PolynomialRingBase, QuotientRing } from '../../../src/polys';
import { Sym, parse as p, str } from '../../../src/core';
import { at } from '../../../src/core/guard';
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
  expect(new PolynomialRingBase(QQ, [x], 'ilex').quotientRing([x]).fromSympy(x).key).toBe(p('0').key);
  const nested = K.quotientRing([y]);
  expect(str(nested.fromSympy(p('x*x+y')))).toBe('0');
  expect(nested.freeModule(1).submodule([x]).syzygyModule().contains([x])).toBe(true);
});

it('preserves fractional cosets over local orders and reconstructs module coordinates', () => {
  const L = new PolynomialRingBase(QQ, [x, y], 'ilex');
  const C = L.quotientRing([p('x*x'), p('y*y')]);
  const a = p('(1+x)/(1+y)');
  expect(C.canon(p('(1+y)*((1+x)/(1+y))-(1+x)')).key).toBe(p('0').key);
  expect(C.fromSympy(a).key).not.toBe(p('1+x').key);
  const F = C.freeModule(1), M = F.submodule([p('1+x')]);
  const coefficients = M.inTermsOfGenerators([a]);
  expect(M.gens.reduce((sum, g, j) => sum.add(g.mul(at(coefficients, j))), F.convert(0)).equals(F.convert([a]))).toBe(true);
  expect(F.submodule([x]).contains([p('x/(1+y)')])).toBe(true);
  expect(C.fromSympy(p('x*x/(1+y)')).key).toBe(p('0').key);
  expect(L.quotientRing([]).fromSympy(a).key).toBe(L.fromSympy(a).key);
});
