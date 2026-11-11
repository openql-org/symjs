// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Finite extensions K[x]/(f) (SymPy 1.14 polys/agca/extensions.py); expected values from SymPy.
import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { ExactQuotientFailed, NotImplementedError, NotInvertible } from '../../../src/core/errors';
import { ExtensionElement, FiniteExtension } from '../../../src/polys/agca/extensions';
import { CoercionFailed } from '../../../src/polys/domains';
import { GeneratorsError } from '../../../src/polys/polyerrors';

const [x, t, y] = sj.symbols('x t y');
const P = (e: string, gens: sj.Sym[] = [x], opts: sj.PolyConstructionOptions = {}): sj.Poly => sj.Poly.from(sj.parse(e), gens, opts);
const s = (v: unknown): string => String(v);

describe('FiniteExtension', () => {
  it('over ZZ (the docstring examples)', () => {
    const R = new FiniteExtension(P('x**2 - 2'));
    const a = R.new(sj.parse('1 + x'));
    expect(s(R)).toBe('ZZ[x]/(x**2 - 2)');
    expect(R.rank).toBe(2);
    expect(s(a.mul(sj.parse('3 - 2*x')))).toBe('x - 1');
    expect([a.add(1), a.sub(x), a.neg(), a.pow(3), a.pow(0)].map(s)).toEqual(['x + 2', '1', '-x - 1', '5*x + 7', '1']);
    expect(R.basis.map(s)).toEqual(['1', 'x']);
    expect([R.generator, R.zero, R.one].map(s)).toEqual(['x', '0', '1']);
    expect(a.equals(R.new(sj.parse('1 + x')))).toBe(true);
    expect(a.equals(1)).toBe(false);
    expect(a.isGround).toBe(false);
    expect(s(R.new(5).toGround())).toBe('5');
    expect(() => R.new(x).toGround()).toThrow(RangeError);
    expect([R.isUnit(R.one), R.isUnit(a), R.isUnit(R.new(2))]).toEqual([true, 'unknown', false]);
    expect(R.characteristic()).toBe(0n);
    expect(R.hasCharacteristicZero).toBe(true);
    expect(s(R.exquo(R.new(sj.parse('x**3')), R.generator))).toBe('2');
    expect(s(R.quo(R.new(sj.parse('x**3')), R.generator))).toBe('2');
    expect(() => a.inverse()).toThrow(NotImplementedError);
    expect(() => R.new(2).pow(-1)).toThrow(RangeError);
    expect([R.one.pow(-1), R.new(-1).inverse()].map(s)).toEqual(['1', '-1']);
    expect(s(R.fromSympy(sj.parse('x**3')))).toBe('2*x');
    expect(s(R.toSympy(R.new(sj.parse('x**3'))))).toBe('2*x');
    expect(R.isNegative(a)).toBe(false);
    expect(new FiniteExtension(P('x**2 - 2')).equals(R)).toBe(true);
    expect(R.equals(1)).toBe(false);
    expect(R.generator.parent()).toBe(R);
    expect(s(R.generator.asExpr())).toBe('x');
    expect(s(R.new(P('x**3')))).toBe('2*x');
    expect(R.convert(a)).toBe(a);
    expect(() => R.new(y)).toThrow(CoercionFailed);
    expect(() => R.convert(new FiniteExtension(P('x**2 + 1')).generator)).toThrow(CoercionFailed);
    expect(() => a.add(new FiniteExtension(P('x**2 + 1')).generator)).toThrow(CoercionFailed);
    expect(s(a.add(R.generator))).toBe('2*x + 1');
    expect(s(new FiniteExtension(P('-x**2 + 2')))).toBe('ZZ[x]/(x**2 - 2)');
  });
  it('over GF(5) and fields of fractions', () => {
    const F = new FiniteExtension(P('x**3 + x**2 + 2', [x], { modulus: 5 }));
    expect(s(F)).toBe('GF(5)[x]/(x**3 + x**2 + 2)');
    expect(F.basis.map(s)).toEqual(['1', 'x', 'x**2']);
    expect(s(F.new(sj.parse('x + 3')).div(sj.parse('x**2 + 2')))).toBe('-2*x**2 + x + 2');
    expect(s(F.new(sj.parse('x + 3')).mod(sj.parse('x**2 + 2')))).toBe('0');
    expect(s(F.generator.pow(-2))).toBe('2*x + 2');
    expect(F.characteristic()).toBe(5n);
    expect(F.hasCharacteristicZero).toBe(false);
    expect([F.isUnit(F.generator), F.isUnit(F.zero)]).toEqual([true, false]);
    expect(() => F.generator.div(F.zero)).toThrow(RangeError);
    expect(() => F.generator.mod(0)).toThrow(RangeError);
    expect(() => F.zero.inverse()).toThrow(NotInvertible);
    expect(() => F.zero.pow(-1)).toThrow(NotInvertible);
    const G = new FiniteExtension(P('t**2 - x**3 - x + 1', [t], { field: true }));
    expect(s(G)).toBe('ZZ(x)[t]/(t**2 - x**3 - x + 1)');
    expect(s(G.setDomain('QQ(x)'))).toBe('QQ(x)[t]/(t**2 - x**3 - x + 1)');
    expect(s(new FiniteExtension(P('t**2 - x', [t], { field: true })).new(t).pow(-1))).toBe('t/x');
    expect(s(new FiniteExtension(P('t**2 - x', [t], { domain: 'QQ(x,y)' })).drop(y))).toBe('QQ(x)[t]/(t**2 - x)');
  });
  it('drop and errors', () => {
    const K = new FiniteExtension(P('t**2 - x', [t], { domain: 'ZZ[x,y]' }));
    expect(s(K)).toBe('ZZ[x,y][t]/(t**2 - x)');
    expect(s(K.drop(y))).toBe('ZZ[x][t]/(t**2 - x)');
    expect(s(K.new(sj.parse('x*t**3')))).toBe('t*x**2');
    expect(s(new FiniteExtension(P('t**2 - 2', [t], { domain: 'ZZ[x]' })).drop(x))).toBe('ZZ[t]/(t**2 - 2)');
    expect(() => K.drop(t)).toThrow(GeneratorsError);
    expect(() => new FiniteExtension(P('x*y', [x, y]))).toThrow(TypeError);
    // SymPy: mod.monic(auto=False) over ZZ raises ExactQuotientFailed
    expect(() => new FiniteExtension(P('2*x**2 + 1'))).toThrow(ExactQuotientFailed);
    expect(new ExtensionElement(P('x'), new FiniteExtension(P('x**2 - 2'))).isZero).toBe(false);
  });
});

it('provides expression arithmetic modulo the defining polynomial to DomainMatrix', () => {
  const x = new sj.Sym('x');
  const extension = new sj.FiniteExtension(sj.Poly.from(x.pow(2).sub(2), [x], { domain: 'QQ' }));
  const K = extension.toDomain();
  expect(K.toString()).toBe(String(extension));
  expect(K.getField()).toBe(K);
  expect(String(K.fromSympy(x.pow(3)))).toBe('2*x');
  expect(String(K.mul(x, x))).toBe('2');
  expect(String(K.quo(K.one, x))).toBe('x/2');
  expect(() => K.quo(K.one, K.zero)).toThrow();
  expect(() => new sj.FiniteExtension(sj.Poly.from(x.pow(2).sub(2), [x], { domain: 'ZZ' })).toDomain().getField()).toThrow('not a field');
});
