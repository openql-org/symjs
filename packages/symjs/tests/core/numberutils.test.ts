// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/numberutils.ts.
// Number utilities (rational conversion, integer roots, gcd and friends, symbols() name ranges).
// Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { impl } from '../../src/core/nodes';
import { expandSymbolNames, rationalFromString } from '../../src/core/numberutils';

const R = (p: number | bigint, q: number | bigint = 1) => sj.Rational.of(BigInt(p), BigInt(q));

describe('rationalFromFloat / rationalFromString', () => {
  it('exact value of a double (Rational(float))', () => {
    expect(String(sj.rationalFromFloat(0.2))).toBe('3602879701896397/18014398509481984');
    expect(String(sj.rationalFromFloat(-0.75))).toBe('-3/4');
    // the hook the core uses for Rational(Float)
    expect(String(impl.rationalFromFloat?.(new sj.Float(0.5)))).toBe('1/2');
    expect(String(sj.rationalFromFloat(1e20))).toBe('100000000000000000000');
    expect(String(sj.rationalFromFloat(-3))).toBe('-3');
    expect(String(sj.rationalFromFloat(2.5e30))).toBe('2499999999999999908974073741312');
    // subnormal: 2**-1074
    expect(sj.rationalFromFloat(5e-324).q).toBe(2n ** 1074n);
    expect(() => sj.rationalFromFloat(Infinity)).toThrow(RangeError);
    expect(() => sj.rationalFromFloat(NaN)).toThrow(RangeError);
  });
  it('decimal strings (Rational(str))', () => {
    expect(['1.23', '1e-2', '1e-2/3.2', '-.5', '12_3.4', '3.', '+2E3'].map((t) => String(sj.rationalFromString(t)))).toEqual([
      '123/100',
      '1/100',
      '1/320',
      '-1/2',
      '617/5',
      '3',
      '2000',
    ]);
    expect(() => sj.rationalFromString('abc')).toThrow(SyntaxError);
    expect(() => sj.rationalFromString('.')).toThrow(SyntaxError);
  });
});

describe('integerLog / integerNthroot', () => {
  it('integer_log', () => {
    const cases: [bigint, bigint, [bigint, boolean]][] = [
      [8n, 2n, [3n, true]],
      [9n, 2n, [3n, false]],
      [-8n, 2n, [3n, false]],
      [-27n, -3n, [3n, true]],
      [27n, -3n, [3n, false]],
      [-8n, -2n, [3n, true]],
      [16n, -2n, [4n, true]],
      [-9n, 3n, [0n, false]],
      [1n, 5n, [0n, true]],
      [100n, 10n, [2n, true]],
    ];
    for (const [n, b, r] of cases) expect(sj.integerLog(n, b)).toEqual(r);
    expect(() => sj.integerLog(5n, 1n)).toThrow(RangeError);
    expect(() => sj.integerLog(0n, 2n)).toThrow(RangeError);
  });
  it('integer_nthroot', () => {
    const cases: [bigint, number, [bigint, boolean]][] = [
      [0n, 3, [0n, true]],
      [1n, 3, [1n, true]],
      [27n, 3, [3n, true]],
      [28n, 3, [3n, false]],
      [2n ** 100n, 5, [1048576n, true]],
      [10n ** 30n + 1n, 2, [10n ** 15n, false]],
      [2n, 2, [1n, false]],
    ];
    for (const [v, n, r] of cases) expect(sj.integerNthroot(v, n)).toEqual(r);
    expect(() => sj.integerNthroot(-1n, 2)).toThrow(RangeError);
  });
});

describe('igcd, ilcm, trailing, numDigits, modInverse, limitDenominator', () => {
  it('integer helpers', () => {
    expect(sj.igcd(12n, -18n, 8n)).toBe(2n);
    expect(sj.ilcm(4n, 6n, -10n)).toBe(60n);
    expect(sj.ilcm(3n, 0n, 5n)).toBe(0n);
    expect([sj.trailing(0n), sj.trailing(-12n), sj.trailing(40n)]).toEqual([0, 2, 3]);
    expect([sj.numDigits(-12345n), sj.numDigits(255n, 16), sj.numDigits(0n)]).toEqual([5, 2, 1]);
    // bases above 36 (beyond Number#toString), as SymPy
    expect([sj.numDigits(69n ** 32n, 69), sj.numDigits(69n ** 32n - 1n, 69), sj.numDigits(-100n, 1000)]).toEqual([33, 32, 1]);
    expect(sj.numDigits(0n, 0)).toBe(1);
    expect(() => sj.numDigits(5n, -2)).toThrow(RangeError);
    expect(() => sj.numDigits(5n, 1)).toThrow(RangeError);
  });
  it('mod_inverse: the result has the sign of m', () => {
    expect(String(sj.modInverse(R(3), R(11)))).toBe('4');
    expect(String(sj.modInverse(R(-3), R(11)))).toBe('7');
    expect(String(sj.modInverse(R(3), R(-11)))).toBe('-7');
    expect(String(sj.modInverse(R(-1), R(-5)))).toBe('-1');
    expect(String(sj.modInverse(R(2, 3), R(5)))).toBe('3/2');
    expect(String(sj.modInverse(R(2, 7), R(5, 2)))).toBe('7/2');
    for (const [a, m] of [
      [R(4), R(6)],
      [R(2), R(4)],
      [R(1), R(1)],
      [R(5), R(1)],
      [R(1), R(-1)],
      [R(1, 2), R(1)],
    ] as const) {
      expect(() => sj.modInverse(a, m)).toThrow(RangeError);
    }
  });
  it('limit_denominator (Python Fraction)', () => {
    const cases: [[number, number], number, string][] = [
      [[3141592653589793, 10 ** 15], 1000, '355/113'],
      [[3, 7], 10, '3/7'],
      [[-355, 113], 50, '-22/7'],
      [[1, 3], 2, '1/2'],
      [[-7, 10], 3, '-2/3'],
      [[5, 7], 2, '1/2'],
    ];
    for (const [[p, q], m, r] of cases) expect(String(sj.limitDenominator(R(p, q), BigInt(m)))).toBe(r);
  });
});

describe('symbols() name ranges', () => {
  it('escapes, ranges and parentheses', () => {
    const names = (t: string) => sj.expandSymbolNames(t);
    expect(names('x\\,y, a\\:b, c\\ d')).toEqual(['x,y', 'a:b', 'c d']);
    expect(names('x:3')).toEqual(['x0', 'x1', 'x2']);
    expect(names('x5:7')).toEqual(['x5', 'x6']);
    expect(names('a:d')).toEqual(['a', 'b', 'c', 'd']);
    expect(names(':c')).toEqual(['a', 'b', 'c']);
    expect(names('x(:c)')).toEqual(['xa', 'xb', 'xc']);
    expect(names('x:2(1:3)')).toEqual(['x01', 'x02', 'x11', 'x12']);
    expect(names('x, y,')).toEqual(['x', 'y']);
    expect(names('x3:1')).toEqual([]);
    expect(names('x:0,y')).toEqual(['y']);
    expect(names('a b  c')).toEqual(['a', 'b', 'c']);
    expect(names('x(:2)y')).toEqual(['x0y', 'x1y']);
    expect(() => names('x:')).toThrow('missing end range');
    // SymPy raises ValueError('no symbols given'); symjs returns no names
    expect(names(' ')).toEqual([]);
  });
});

describe('number utilities', () => {
  it('rejects strings without digits', () => {
    for (const t of ['', '.', '+', 'e5', '-.e3']) expect(() => rationalFromString(t)).toThrow(SyntaxError);
  });
  it('protects escaped separators from a private-use character in the name', () => {
    // symbols('a\\,b') is one symbol named 'a,b'
    expect(expandSymbolNames('a\\,b')).toEqual(['a,b']);
  });
});

describe('igcdex / isqrt', () => {
  it('extended Euclidean algorithm with SymPy signs', () => {
    expect(sj.igcdex(2n, 3n)).toEqual([-1n, 1n, 1n]);
    expect(sj.igcdex(10n, 12n)).toEqual([-1n, 1n, 2n]);
    expect(sj.igcdex(100n, 2004n)).toEqual([-20n, 1n, 4n]);
    expect(sj.igcdex(0n, 0n)).toEqual([0n, 0n, 0n]);
    expect(sj.igcdex(0n, -5n)).toEqual([0n, -1n, 5n]);
    expect(sj.igcdex(0n, 5n)).toEqual([0n, 1n, 5n]);
    expect(sj.igcdex(-4n, 0n)).toEqual([-1n, 0n, 4n]);
    expect(sj.igcdex(4n, 0n)).toEqual([1n, 0n, 4n]);
    expect(sj.igcdex(-12n, 8n)).toEqual([-1n, -1n, 4n]);
    expect(sj.igcdex(7n, -3n)).toEqual([1n, 2n, 1n]);
  });
  it('integer square root', () => {
    expect(sj.isqrt(0n)).toBe(0n);
    expect(sj.isqrt(9n)).toBe(3n);
    expect(sj.isqrt(10n)).toBe(3n);
    expect(sj.isqrt(10n ** 30n + 5n)).toBe(10n ** 15n);
    expect(() => sj.isqrt(-1n)).toThrow(RangeError);
  });
});

describe('literal values, rational square roots and enclosing intervals', () => {
  it('tests literal integrality without rounding to a double', () => {
    for (const value of [2n, 2, R(2), new sj.Float(0), new sj.Float(4)]) expect(sj.intValued(value)).toBe(true);
    for (const value of [NaN, Infinity, 1.5, R(1, 2), new sj.Float(1.5), sj.pi, sj.Symbol('n', { integer: true })]) expect(sj.intValued(value)).toBe(false);
    expect(() => Reflect.apply(sj.igcd, undefined, [R(1)])).toThrow(RangeError);
  });
  it('takes the integer square root of the entire fraction', () => {
    expect(sj.isqrt(R(9007199523176447n, 2n))).toBe(67108864n);
    expect(sj.isqrt(R(1n, 10n ** 1000n))).toBe(0n);
    expect(sj.isqrt(R(10n ** 1100n - 1n, 10n ** 1000n))).toBe(10n ** 50n - 1n);
    expect(sj.isqrt(new sj.Float(9))).toBe(3n);
    expect(sj.isqrt(new sj.Float(8.9))).toBe(2n);
    expect(() => sj.isqrt(R(-1, 100))).toThrow(RangeError);
    expect(() => sj.isqrt(new sj.Float(-0.1))).toThrow(RangeError);
    expect(sj.integerNthroot(3n, 10n ** 1000n)).toEqual([1n, false]);
    expect(sj.integerNthroot(27n, 3n)).toEqual([3n, true]);
    expect(sj.integerNthroot(0n, 100)).toEqual([0n, true]);
    for (const degree of [0, -1, 1.5, NaN, Infinity]) expect(() => sj.integerNthroot(3n, degree)).toThrow(RangeError);
  });
  it('encloses each real number symbol with proven rational bounds', () => {
    for (const [name, interval] of [['pi', '3,4'], ['E', '2,3'], ['GoldenRatio', '1,2'], ['TribonacciConstant', '1,2'], ['EulerGamma', '0,1'], ['Catalan', '0,1']] as const) {
      expect(String(sj.approximationInterval(new sj.NumberSymbol(name)))).toBe(interval);
    }
    for (const [name, interval] of [['pi', '223/71,22/7'], ['EulerGamma', '1/2,3/5'], ['Catalan', '9/10,1']] as const) {
      expect(String(sj.approximationInterval(new sj.NumberSymbol(name), 'Rational'))).toBe(interval);
    }
    expect(sj.approximationInterval(sj.E, 'Rational')).toBe(sj.NoMatch);
    expect(sj.approximationInterval(new sj.NumberSymbol('I'))).toBe(sj.NoMatch);
  });
  it('uses Lehmer batches for large inputs and Euclid for the remainder', () => {
    const fib = (n: number) => {
      let a = 0n, b = 1n;
      for (let i = 0; i < n; i++) [a, b] = [b, a + b];
      return a;
    };
    for (const [a, b] of [[0n, 0n], [0n, -8n], [-12n, 18n], [2n ** 100n, 1n], [((2n ** 58n + 1n) * 2n) << 40n, (2n ** 58n) << 40n], [fib(500), fib(499)], [fib(500), fib(400)], [2n ** 100n, 2n ** 80n], [10n ** 100n, 10n ** 50n + 1n]]) {
      if (a !== undefined && b !== undefined) expect(sj.igcdLehmer(a, b)).toBe(sj.igcd(a, b));
    }
  });
});
