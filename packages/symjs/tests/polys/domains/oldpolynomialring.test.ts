// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { QQ, GF, PolynomialRingBase, CoercionFailed } from '../../../src/polys';
import { Sym, parse as p, str } from '../../../src/core';
import { NotImplementedError } from '../../../src/core/errors';
const x = new Sym('x'), y = new Sym('y');
it('creates polynomial presentations with explicit coefficient fields and orders', () => {
  const R = new PolynomialRingBase(QQ, [x, y]);
  expect(String(R)).toBe('QQ[x,y]');
  expect(R.dom).toBe(QQ);
  expect(str(R.fromSympy(p('(x+y)**2')))).toBe('x**2 + 2*x*y + y**2');
  expect(str(R.canon(p('(x+1)**2')))).toBe('x**2 + 2*x + 1');
  expect(() => R.fromSympy(p('1/x'))).toThrow(CoercionFailed);
  expect(R.equals(new PolynomialRingBase(QQ, [x, y]))).toBe(true);
  expect(R.equals(new PolynomialRingBase(QQ, [x, y], 'lex'))).toBe(false);
  expect(R.equals(new PolynomialRingBase(QQ, [y, x]))).toBe(false);
  expect(R.equals(QQ)).toBe(false);
  expect(String(R.getField())).toBe('QQ(x,y)');
  expect(String(QQ.oldPolyRing(x).ideal(p('x*x')))).toBe('<x**2>');
  expect(String(QQ.oldPolyRing(x).quotientRing([p('x*x')]))).toBe('QQ[x]/<x**2>');
  const L = new PolynomialRingBase(QQ, [x], 'ilex');
  expect(String(L)).toBe('QQ[x] order=ilex');
  expect(L.ideal(p('1+x')).reduceElement(1).key).toBe(p('0').key);
  expect(() => L.freeModule(1).submodule([p('1+x')]).inTermsOfGenerators([1])).toThrow(NotImplementedError);
  // SymPy returns 1/(1+x) in this localization; the representation is pending.
  expect(() => L.freeModule(1).contains([p('1/(1+x)')])).toThrow(NotImplementedError);
  expect(() => new PolynomialRingBase(GF(5), [x]).getField()).toThrow(NotImplementedError);
});
