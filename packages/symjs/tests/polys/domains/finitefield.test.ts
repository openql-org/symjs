// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.domains.finitefield, modularinteger).

import { describe, expect, it } from 'vitest';
import { Rational } from '../../../src/index';
import { NotInvertible } from '../../../src/core/errors';
import { CoercionFailed, QQ, ZZ } from '../../../src/polys/domains';
import { FF, FiniteField, GF, ModularInteger } from '../../../src/polys/domains/finitefield';

const F = GF(7);

describe('GF(p)', () => {
  it('elements print like SymPy', () => {
    expect([String(GF(5).new(3)), GF(5).new(3).repr(), String(GF(5).new(4)), GF(5, false).new(4).repr(), String(GF(5, false).new(4))]).toEqual(['3 mod 5', 'SymmetricModularIntegerMod5(3)', '4 mod 5', 'ModularIntegerMod5(4)', '4 mod 5']);
    expect([String(F), String(FF(5)), F.characteristic(), F.new(3).mod, F.new(3).sym]).toEqual(['GF(7)', 'GF(5)', 7n, 7n, true]);
    expect(() => new FiniteField(0)).toThrow(RangeError);
  });
  it('arithmetic', () => {
    const a = F.new(3);
    expect([a.add(5), a.sub(F.new(4)), a.mul(3n), a.div(2), a.neg(), a.pow(-1), a.pow(3), a.pow(2)].map(String)).toEqual(['1 mod 7', '6 mod 7', '2 mod 7', '5 mod 7', '4 mod 7', '5 mod 7', '6 mod 7', '2 mod 7']);
    expect(() => a.div(0)).toThrow(NotInvertible);
    expect([a.equals(F.new(10)), a.equals(GF(5).new(3)), a.equals(10), a.equals(Rational.of(1n, 2n)), F.new(0).isZero]).toEqual([true, false, true, false, true]);
  });
  it('domain methods', () => {
    expect([F.convert(Rational.of(8n)), F.convert(F.new(2)), F.convert(3, ZZ), F.convert(9n)].map(String)).toEqual(['1 mod 7', '2 mod 7', '3 mod 7', '2 mod 7']);
    expect(() => F.convert(Rational.of(1n, 2n))).toThrow(CoercionFailed);
    expect([F.toSympy(F.new(6)), F.toSympy(2), F.canon(Rational.of(13n)), F.fromSympy(9)].map(String)).toEqual(['-1', '2', '-1', '2']);
    expect([F.ofType(F.new(1)), F.ofType(GF(5).new(1)), F.ofType(1), F.isZero(F.new(7)), F.isZero(0), F.isPositive(1), F.isPositive(0), F.isNegative(F.new(6))]).toEqual([true, false, false, true, true, true, false, false]);
    expect([F.gcd(2, 3), F.gcd(0, 0), F.lcm(2, 3), F.exquo(3, 2), F.rem(3, 2)].map(String)).toEqual(['1 mod 7', '0 mod 7', '6 mod 7', '5 mod 7', '0 mod 7']);
    expect(F.div(3, 2).map(String)).toEqual(['5 mod 7', '0 mod 7']);
    expect([F.getField() === F, F.equals(GF(7)), F.equals(GF(7, false)), F.equals(QQ), new ModularInteger(-1n, F).val]).toEqual([true, true, false, false, 6n]);
  });
});
