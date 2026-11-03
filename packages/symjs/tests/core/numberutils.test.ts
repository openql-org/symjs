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
