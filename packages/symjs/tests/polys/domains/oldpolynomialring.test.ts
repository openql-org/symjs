// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { QQ, ZZ, GF, PolynomialRingBase, CoercionFailed } from '../../../src/polys';
import { Sym, parse as p, str } from '../../../src/core';
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
  expect(L.freeModule(1).submodule([p('1+x')]).inTermsOfGenerators([1]).map(str)).toEqual(['1/(x + 1)']);
  expect(L.freeModule(1).contains([p('1/(1+x)')])).toBe(true);
  expect(String(new PolynomialRingBase(GF(5), [x]).getField())).toBe('GF(5)(x)');
});

it('sets the coefficient domain and finds units of global and local rings (SymPy test_units)', async () => {
  const { RR, ZZ } = await import('../../../src/polys/domains');
  const R = new PolynomialRingBase(RR, [x], 'ilex');
  expect(String(R.setDomain(GF(5)))).toBe('GF(5)[x] order=ilex');
  expect(R.isExact).toBe(false);
  expect(String(R.getExact())).toBe('QQ[x] order=ilex');
  expect(R.hasCharacteristicZero).toBe(true);
  expect(R.characteristic()).toBe(0n);
  expect(R.hasAssocRing).toBe(true);
  expect(R.isUnit(p('1 + x'))).toBe(true);
  expect(R.isUnit(p('x'))).toBe(false);
  const Z = new PolynomialRingBase(ZZ, [x]);
  expect(Z.isUnit(p('1'))).toBe(true);
  expect(Z.isUnit(p('2'))).toBe(false);
  expect(Z.isUnit(p('1 + x'))).toBe(false);
  expect(String(Z.unify(QQ))).toBe('QQ[x]');
  expect(String(QQ.unify(Z))).toBe('QQ[x]');
});

it('accepts only denominators with constant leading monomial in a localization', () => {
  for (const order of ['ilex', 'igrlex', 'igrevlex']) {
    const L = new PolynomialRingBase(QQ, [x, y], order);
    expect(L.contains(p('(x+y)/(1+x+y)'))).toBe(true);
    expect(L.contains(p('1/x'))).toBe(false);
    expect(L.contains(p('1/(x+y)'))).toBe(false);
    expect(L.contains(p('1/(1+z)'))).toBe(false);
    expect(L.contains(p('1/(1-x)-1/(1+x)'))).toBe(true);
    expect(L.isUnit(p('(1+y)/(1+x)'))).toBe(true);
    expect(L.isUnit(p('x/(1+x)'))).toBe(false);
    expect(str(L.canon(p('(x*x-1)/(x-1)')))).toBe('x + 1');
    expect(() => L.fromSympy(p('1/0'))).toThrow(CoercionFailed);
  }
  const finite = new PolynomialRingBase(GF(5), [x], 'ilex');
  expect(finite.contains(p('1/5'))).toBe(false);
  expect(finite.contains(p('1/(5*x+5)'))).toBe(false);
  expect(str(finite.fromSympy(p('(x+6)/(1+x)')))).toBe('1');
  const Z = new PolynomialRingBase(ZZ, [x], 'ilex');
  expect(Z.isUnit(p('2/(1+x)'))).toBe(false);
});

it('matches SymPy fraction fields over finite, polynomial, rational and algebraic coefficient domains', async () => {
  const { readFileSync } = await import('node:fs');
  const { ZZ, sqrt } = await import('../../../src');
  const references: { fields: { domain: string; expression: string; expected: string }[] } = JSON.parse(readFileSync(new URL('../agca/local.references.json', import.meta.url), 'utf8'));
  const domains = new Map([['GF(5)', GF(5)], ['ZZ[y]', ZZ.polyRing(y)], ['QQ(y)', QQ.fracField(y)], ['QQ<sqrt(2)>', QQ.algebraicField(sqrt(2))]]);
  for (const reference of references.fields) {
    const K = domains.get(reference.domain);
    if (!K) throw new RangeError('missing coefficient domain');
    const field = new PolynomialRingBase(K, [x]).getField();
    expect(field.dom.equals(K)).toBe(true);
    expect(field.isZero(field.sub(field.fromSympy(p(reference.expression)), field.fromSympy(p(reference.expected))))).toBe(true);
  }
  const F = new PolynomialRingBase(GF(5), [x]).getField();
  expect(str(F.fromSympy(p('(x+6)/(x+2)')))).toBe('(x + 1)/(x + 2)');
});

it('uses Mora localization for a mixed product order', async () => {
  const { buildProductOrder } = await import('../../../src/polys');
  const order = buildProductOrder([['lex', x], ['ilex', y]], [x, y]);
  const R = new PolynomialRingBase(QQ, [x, y], order);
  expect(R.order.isGlobal).toBe('unknown');
  expect(R.contains(p('1/(1+y)'))).toBe(true);
  expect(R.isUnit(p('1+y'))).toBe(true);
  expect(R.isUnit(p('1+x'))).toBe(false);
  expect(R.contains(p('1/(1+x)'))).toBe(false);
  const F = R.freeModule(1);
  expect(F.submodule([p('1+y')]).contains([1])).toBe(true);
});
