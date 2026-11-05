// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/domainops.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Float, I, Rational, Sym } from '../../../src/core';
import { ExactQuotientFailed, NotImplementedError } from '../../../src/core/errors';
import { add, mul, pow, sqrt } from '../../../src/core/ops';
import { CoercionFailed, EX, QQ, RR, ZZ } from '../../../src/polys/domains';
import * as ops from '../../../src/polys/matrices/domainops';
import { EXRAW } from '../../../src/polys/domains/expressionrawdomain';
import { QQ_I, ZZ_I } from '../../../src/polys/domains/gaussiandomains';

const q = (p: number, d = 1) => Rational.of(BigInt(p), BigInt(d));
const x = new Sym('x');
const ZX = ZZ.polyRing(x);
const FX = ZZ.fracField(x);

describe('domain operations', () => {
  it('division in ZZ and fields', () => {
    expect(ops.div(ZZ, q(-7), q(2)).map(String)).toEqual(['-4', '1']);
    expect(ops.div(ZZ, q(7), q(-2)).map(String)).toEqual(['-4', '-1']);
    expect(ops.div(ZZ, q(6), q(2)).map(String)).toEqual(['3', '0']);
    expect(ops.div(QQ, q(1, 2), q(3)).map(String)).toEqual(['1/6', '0']);
    expect(() => ops.div(ZZ, q(1), q(0))).toThrow(RangeError);
    expect(() => ops.div(ZX, x, x)).toThrow(NotImplementedError);
    expect([String(ops.quo(ZZ, q(7), q(2))), String(ops.rem(ZZ, q(7), q(2)))]).toEqual(['3', '1']);
    expect(String(ops.exquo(ZZ, q(6), q(3)))).toBe('2');
    expect(() => ops.exquo(ZZ, q(7), q(3))).toThrow(ExactQuotientFailed);
    expect(() => ops.exquo(ZZ, q(7), q(0))).toThrow(RangeError);
    expect(String(ops.exquo(QQ, q(1), q(3)))).toBe('1/3');
    expect(String(ops.exquo(ZX, add(mul(x, x), -1), add(x, 1)))).toBe('x - 1');
    expect(() => ops.exquo(ZX, x, add(x, 1))).toThrow(ExactQuotientFailed);
    expect(String(ops.inv(QQ, q(2)))).toBe('1/2');
    expect(String(ops.fdiv(QQ, q(1), q(2)))).toBe('1/2');
  });
  it('gcd, lcm, gcdex and cofactors', () => {
    expect(String(ops.gcd(ZZ, q(-4), q(6)))).toBe('2');
    expect(String(ops.lcm(ZZ, q(-4), q(6)))).toBe('12');
    expect(String(ops.gcd(QQ, q(2, 3), q(4, 9)))).toBe('2/9');
    expect(String(ops.lcm(QQ, q(2, 3), q(4, 9)))).toBe('4/3');
    expect(String(ops.gcd(ZX, add(mul(2, x), 2), add(mul(-4, x), -4)))).toBe('2*x + 2');
    expect(String(ops.lcm(ZX, x, add(mul(-1, x), -1)))).toBe('-x**2 - x');
    expect(String(ops.gcd(FX, mul(2, x, q(1, 3)), mul(4, x, q(1, 9))))).toBe('2*x/9');
    expect(String(ops.lcm(FX, mul(2, x, q(1, 3)), mul(4, x, q(1, 9))))).toBe('4*x/3');
    expect(String(ops.gcd(RR, new Float(2), new Float(3)))).toBe('1');
    expect(String(ops.lcm(RR, new Float(2), new Float(3)))).toContain('6.0');
    expect(ops.gcdex(ZZ, q(4), q(6)).map(String)).toEqual(['-1', '1', '2']);
    expect(() => ops.gcdex(QQ, q(4), q(6))).toThrow(NotImplementedError);
    expect(ops.cofactors(ZZ, q(4), q(6)).map(String)).toEqual(['2', '2', '3']);
    expect(ops.cofactors(ZZ, q(0), q(0)).map(String)).toEqual(['0', '0', '0']);
  });
  it('units, signs and rings', () => {
    expect(String(ops.canonicalUnit(ZZ, q(-3)))).toBe('-1');
    expect(String(ops.canonicalUnit(ZX, add(mul(-1, x), 1)))).toBe('-1');
    expect(ops.isNegative(FX, mul(-1, x, pow(add(x, 1), -1)))).toBe(true);
    expect([String(ops.numer(QQ, q(2, 3))), String(ops.denom(QQ, q(2, 3))), String(ops.denom(ZZ, q(2)))]).toEqual(['2', '3', '1']);
    expect([String(ops.numer(FX, mul(x, pow(add(x, 1), -1)))), String(ops.denom(FX, mul(x, pow(add(x, 1), -1))))]).toEqual(['x', 'x + 1']);
    expect([ops.hasAssocRing(QQ), ops.hasAssocRing(FX), ops.hasAssocRing(ZZ), ops.hasAssocField(ZX), ops.hasAssocField(QQ)]).toEqual([true, true, false, true, false]);
    expect([ops.isPID(ZZ), ops.isPID(QQ), ops.isPID(ZX), ops.isPID(QQ.polyRing(x)), ops.isPID(RR), ops.isPID(FX)]).toEqual([true, true, false, true, false, true]);
    expect([ops.isExact(RR), ops.isExact(QQ)]).toEqual([false, true]);
    expect(String(ops.convertFrom(QQ, q(2), ZZ))).toBe('2');
    expect(String(ops.convertFrom(ZZ, q(2), ZZ))).toBe('2');
    expect([ops.elemStr(QQ, q(1, 2)), ops.elemRepr(QQ, q(1, 2)), ops.elemRepr(ZZ, q(2))]).toEqual(['1/2', 'MPQ(1,2)', '2']);
    expect([ops.bitLength(0n), ops.bitLength(-5n)]).toEqual([0, 3]);
    expect(() => ops.rat(x)).toThrow();
  });
  it('EXRAW and the Gaussian domains in the expression form of the matrices', () => {
    expect(String(EXRAW)).toBe('EXRAW');
    expect(String(EXRAW.add(x, x))).toBe('2*x');
    expect(EXRAW.canon(add(x, x)) instanceof Object).toBe(true);
    expect(String(ZZ_I.fromSympy(add(1, I)))).toBe('1 + I');
    expect(() => ZZ_I.fromSympy(add(q(1, 2), I))).toThrow(CoercionFailed);
    expect(String(QQ_I.fromSympy(add(q(1, 2), I)))).toBe('1/2 + I');
    expect(() => QQ_I.fromSympy(sqrt(2))).toThrow(CoercionFailed);
    expect(String(ZZ_I.getField())).toBe('QQ_I');
    expect(String(QQ_I.quo(q(1), add(1, I)))).toBe('1/2 - I/2');
    expect(String(ZZ_I.mul(add(1, I), add(1, I)))).toBe('2*I');
  });
  it('construct_domain', () => {
    const c = (es: unknown[], field = false) => String(ops.domainOfExprs(es as never, { field })[0]);
    expect([c([1, 2]), c([q(1, 2)]), c([new Float(1.5)]), c([add(1, I)]), c([add(q(1, 2), I)]), c([x, 2]), c([x, 2], true), c([mul(x, q(1, 2))]), c([pow(x, -1)])]).toEqual(['ZZ', 'QQ', 'RR', 'ZZ_I', 'QQ_I', 'ZZ[x]', 'ZZ(x)', 'QQ[x]', 'ZZ(x)']);
    expect([c([sqrt(2)]), c([x, new Float(1.5)]), c([x, sqrt(2), new Float(1.5)]), c([1], true), c([])]).toEqual(['EX', 'RR[x]', 'EX', 'QQ', 'ZZ']);
    expect(String(ops.domainOfExprs([EX.one])[1])).toBe('1');
  });
});
