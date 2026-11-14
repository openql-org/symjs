// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { CC, CoercionFailed, GF, QQ, QQ_I, ZZ, ZZ_I } from '../../../src/polys';
import { GeneratorsError } from '../../../src/polys/polyerrors';
import { CompositeFractionField, CompositePolynomialRing } from '../../../src/polys/domains/compositedomain';
import { Sym, parse as p, str } from '../../../src/core';

const [x, y, z] = [new Sym('x'), new Sym('y'), new Sym('z')];

it('builds polynomial rings over non-ground coefficient domains', () => {
  const R = GF(5).polyRing(x) as CompositePolynomialRing;
  expect(R).toBeInstanceOf(CompositePolynomialRing);
  expect(String(R)).toBe('GF(5)[x]');
  expect(R.dom).toBe(R.domain);
  expect(R.gens.map(String)).toEqual(['x']);
  expect(str(R.fromSympy(p('7*x + 3')))).toBe('2*x - 2');
  expect(str(R.canon(p('5*x')))).toBe('0');
  expect(() => R.fromSympy(p('1/x'))).toThrow(CoercionFailed);
  expect(R.isExact).toBe(true);
  expect(R.hasCharacteristicZero).toBe(false);
  expect(R.characteristic()).toBe(5n);
  expect(R.hasAssocRing).toBe(true);
  expect(String(R.getField())).toBe('GF(5)(x)');
  expect(String(R.setDomain(CC))).toBe('CC[x]');
  expect(String(R.inject(y))).toBe('GF(5)[x,y]');
  expect(() => R.inject(x)).toThrow(GeneratorsError);
  expect(String(R.inject(y).drop(x))).toBe('GF(5)[y]');
  expect(String(R.drop(x))).toBe('GF(5)');
  expect(R.isUnit(p('2'))).toBe(true);
  expect(R.isUnit(p('x'))).toBe(false);
});

it('computes exactness, units and canonical units from the coefficient domain', () => {
  const R = CC.polyRing(x, y);
  expect(R.isExact).toBe(false);
  expect(String(R.getExact())).toBe('QQ_I[x,y]');
  expect(R.hasCharacteristicZero).toBe(true);
  expect(R.characteristic()).toBe(0n);
  const Zi = ZZ_I.polyRing(x);
  expect(str(Zi.canonicalUnit(Zi.fromSympy(p('I*x'))) as never)).toBe('-I');
  expect(Zi.isUnit(p('I'))).toBe(true);
  expect(Zi.isUnit(p('2'))).toBe(false);
});

it('builds rational function fields over non-ground coefficient domains', () => {
  const F = GF(5).fracField(x) as CompositeFractionField;
  expect(F).toBeInstanceOf(CompositeFractionField);
  expect(String(F)).toBe('GF(5)(x)');
  expect(F.getField()).toBe(F);
  expect(String(F.getRing())).toBe('GF(5)[x]');
  expect(str(F.fromSympy(p('(x**2 - 1)/(6*x + 6)')))).toBe('x - 1');
  expect(String(F.setDomain(QQ_I))).toBe('QQ_I(x)');
  expect(String(F.inject(y))).toBe('GF(5)(x,y)');
  expect(String(F.drop(x))).toBe('GF(5)');
  expect(() => F.fromSympy(p('sin(x)'))).toThrow(CoercionFailed);
  expect(() => F.fromSympy({} as never)).toThrow(TypeError);
});

it('builds rings over fraction fields and propagates other errors', () => {
  const R = ZZ.fracField(x).polyRing(y);
  expect(String(R)).toBe('ZZ(x)[y]');
  expect(str(R.fromSympy(p('y/x')))).toBe('y/x');
  expect(String(R.drop(x))).toBe('ZZ[y]');
  expect(String(R.drop(y))).toBe('ZZ(x)');
  expect(String(R.getField())).toBe('ZZ(x)(y)');
  expect(String(ZZ.fracField(x).fracField(z))).toBe('ZZ(x)(z)');
  expect(QQ.algebraicField(p('sqrt(2)')).polyRing(x).characteristic()).toBe(0n);
});
