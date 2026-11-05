// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.domains.gaussiandomains).

import { describe, expect, it } from 'vitest';
import { I, Rational, add, mul, parseExpr as P } from '../../../src/index';
import { ExactQuotientFailed } from '../../../src/core/errors';
import { CoercionFailed, QQ, ZZ } from '../../../src/polys/domains';
import { PythonMPQ } from '../../../src/polys/domains/pythonrational';
import { GaussianInteger, GaussianRational, QQ_I, ZZ_I } from '../../../src/polys/domains/gaussiandomains';

const z = (x: number, y = 0): GaussianInteger => ZZ_I.new(x, y);

describe('ZZ_I', () => {
  it('elements', () => {
    expect([String(z(3, 4)), z(3, 4).repr(), String(z(5)), String(z(0, -1)), String(z(2, -1))]).toEqual(['3 + 4*I', 'ZZ_I(3, 4)', '5', '-I', '2 - I']);
    expect([z(3, 4).x, z(3, 4).y]).toEqual([3n, 4n]);
    expect(() => new GaussianInteger(new PythonMPQ(1n, 2n))).toThrow(CoercionFailed);
    expect([z(5, 1).add(z(1)), z(5, 1).sub(1), z(1, 1).mul(z(1, -1)), z(1, 1).neg(), z(1, 1).pow(3), z(1, 1).pow(0), z(1, 1).pow(2)].map(String)).toEqual(['6 + I', '4 + I', '2', '-1 - I', '-2 + 2*I', '1', '2*I']);
    expect(String(z(1, 1).pow(-1))).toBe('1/2 - I/2');
    expect(z(5, 1).divmod(z(2, 3)).map(String)).toEqual(['1 - I', '0']);
    expect(() => z(1).divmod(0)).toThrow(RangeError);
    expect(String(z(1).div(z(0, 2)))).toBe('-I/2');
    expect(() => z(1).div(0)).toThrow(RangeError);
    expect([z(2, 1), z(-2, 1), z(-2, -1), z(2, -1), z(-2), z(2)].map((a) => a.quadrant())).toEqual([0, 1, 2, 3, 2, 0]);
    expect([z(1).equals(z(1)), z(1).equals(QQ_I.new(1)), z(0).isZero]).toEqual([true, false, true]);
  });
  it('domain methods', () => {
    expect([String(ZZ_I), String(ZZ_I.getField()), String(ZZ_I.dom), ZZ_I.characteristic(), ZZ_I.isField]).toEqual(['ZZ_I', 'QQ_I', 'ZZ', 0n, false]);
    expect([ZZ_I.exquo(z(13, 13), z(2, 3)), ZZ_I.gcd(z(10), z(2)), ZZ_I.gcd(z(5), z(2, 1)), ZZ_I.lcm(z(2), z(1, 1)), ZZ_I.rem(z(5, 1), z(2, 3))].map(String)).toEqual(['5 - I', '2', '2 + I', '2', '0']);
    expect(ZZ_I.div(z(5), z(2)).map(String)).toEqual(['3', '-1']);
    expect(ZZ_I.gcdex(z(5), z(2, 1)).map((a) => a.repr())).toEqual(['ZZ_I(0, 0)', 'ZZ_I(1, 0)', 'ZZ_I(2, 1)']);
    expect(() => ZZ_I.exquo(z(5), z(2))).toThrow(ExactQuotientFailed);
    expect([ZZ_I.convert(add(3, mul(4, I))), ZZ_I.convert(I), ZZ_I.convert(QQ_I.new(2, 1)), ZZ_I.convert(3, ZZ), ZZ_I.convert(7n)].map(String)).toEqual(['3 + 4*I', 'I', '2 + I', '3', '7']);
    expect(() => ZZ_I.convert(P('x + I'))).toThrow(CoercionFailed);
    expect(() => ZZ_I.convert('a')).toThrow(CoercionFailed);
    expect([ZZ_I.toSympy(z(1, 2)), ZZ_I.toSympy(3), ZZ_I.canon(P('(1+I)**2')), ZZ_I.fromSympy(P('2*I + 1'))].map(String)).toEqual(['1 + 2*I', '3', '2*I', '1 + 2*I']);
    expect([ZZ_I.ofType(z(1)), ZZ_I.ofType(1), ZZ_I.isZero(z(0)), ZZ_I.isZero(0), ZZ_I.isNegative(z(-1)), ZZ_I.isPositive(z(1)), ZZ_I.isNonnegative(z(1)), ZZ_I.isNonpositive(z(-1))]).toEqual([true, false, true, true, false, false, false, false]);
    expect([ZZ_I.canonicalUnit(z(0, 1)), ZZ_I.imagUnit(), ZZ_I.oneElement()].map(String)).toEqual(['-I', 'I', '1']);
    expect([ZZ_I.equals(ZZ_I), ZZ_I.equals(QQ_I)]).toEqual([true, false]);
  });
});

describe('QQ_I', () => {
  it('elements and domain methods', () => {
    const a = QQ_I.new(Rational.of(2n, 3n), Rational.of(4n, 5n));
    expect([String(a), a.repr(), String(a.x), String(a.y)]).toEqual(['2/3 + 4*I/5', 'QQ_I(2/3, 4/5)', '2/3', '4/5']);
    expect([a.add(1), a.sub(a), a.mul(2), a.neg()].map(String)).toEqual(['5/3 + 4*I/5', '0', '4/3 + 8*I/5', '-2/3 - 4*I/5']);
    expect(a.divmod(2).map(String)).toEqual(['1/3 + 2*I/5', '0']);
    expect([String(QQ_I), String(QQ_I.getRing()), String(QQ_I.getField()), String(QQ_I.dom), QQ_I.isField]).toEqual(['QQ_I', 'ZZ_I', 'QQ_I', 'QQ', true]);
    expect([QQ_I.exquo(QQ_I.new(1, 2), QQ_I.new(3, 4)), QQ_I.rem(1, 2), QQ_I.gcd(1, 2), QQ_I.gcd(0, 0), QQ_I.lcm(2, 3)].map(String)).toEqual(['11/25 + 2*I/25', '0', '1', '0', '6']);
    expect(QQ_I.div(QQ_I.new(1, 2), QQ_I.new(3, 4)).map((e) => e.repr())).toEqual(['QQ_I(11/25, 2/25)', 'QQ_I(0, 0)']);
    const h = QQ_I.new(Rational.of(1n, 2n), Rational.of(1n, 3n));
    expect([QQ_I.denom(h), QQ_I.numer(h), QQ_I.convert(z(1, 1))].map(String)).toEqual(['6', '3 + 2*I', '1 + I']);
    expect([QQ_I.ofType(h), QQ_I.ofType(z(1)), QQ_I.convert(QQ.new(1, 2), QQ).repr()]).toEqual([true, false, 'QQ_I(1/2, 0)']);
    expect(new GaussianRational(1n).parent()).toBe(QQ_I);
  });
});
