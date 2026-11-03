// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpf.ts.

import { describe, expect, it } from 'vitest';
import * as F from '../../src/numeric/mpf';

const P = 103;
const r = (s: string) => F.fromStr(s, P);

// Every method of every constant table, forced through the internal API, at
// several precisions including the table boundaries, against mpmath 1.3.0
// (see mpconst.ref.ts); the internal table API; the integer square root.

describe('integer square root (divide and conquer)', () => {
  // deterministic pseudo-random integers
  let seed = 12345n;
  const rand = (bits: number): bigint => {
    let r = 1n;
    for (let i = 0; i < bits; i += 31) {
      seed = (seed * 1103515245n + 12345n) % 2147483648n;
      r = (r << 31n) | seed;
    }
    return r >> BigInt(Math.max(0, F.bitLength(r) - bits));
  };
  const reference = (n: bigint): bigint => {
    if (n < 2n) return n;
    let x = 1n << BigInt(Math.ceil(F.bitLength(n) / 2));
    for (;;) {
      const y = (x + n / x) >> 1n;
      if (y >= x) return x;
      x = y;
    }
  };

  it('matches Newton iteration on random numbers, squares and their neighbours', () => {
    for (let n = 0n; n < 2000n; n++) expect(F.sqrtrem(n)).toEqual([reference(n), n - reference(n) ** 2n]);
    for (const bits of [47, 48, 49, 50, 64, 100, 127, 128, 129, 300, 1000, 4000, 20000]) {
      for (let i = 0; i < 20; i++) {
        const x = rand(bits);
        const s = rand(bits >> 1);
        for (const n of [x, s * s, s * s - 1n, s * s + 2n * s, s * s + 1n]) {
          const r = reference(n);
          expect(F.sqrtrem(n), `${n}`).toEqual([r, n - r * r]);
          expect(F.isqrt(n)).toBe(r);
        }
      }
    }
  });

  it('rejects negative numbers and keeps mpf sqrt exact', () => {
    expect(() => F.sqrtrem(-1n)).toThrow(RangeError);
    expect(F.toStr(F.sqrt(F.fromInt(1n << 400n), 53), 10)).toBe('1.606938044e+60');
    expect(F.toStr(F.sqrt(F.fromInt(2n), 200), 40)).toBe('1.41421356237309504880168872420969807857');
  });
});

describe('mpf arbitrary precision (values from mpmath, dps=50)', () => {
  it('to_str', () => {
    expect(F.floatToString(F.fromNumber(3.5), 53, false)).toBe('3.50000000000000');
    expect(F.floatToString(F.fromNumber(1e20), 53, false)).toBe('1.00000000000000e+20');
    expect(F.floatToString(F.fromStr('1e-3', F.dpsToPrec(3)), F.dpsToPrec(3), false)).toBe('0.00100');
    expect(F.floatToString(F.fromNumber(0.3), F.dpsToPrec(20), false)).toBe('0.29999999999999998890');
  });
});

// Expected values from mpmath 1.3 (libmp.to_str, from_float, mpf_pow_int) and
// SymPy 1.14 (str of low-precision Floats).

describe('mpf primitives', () => {
  it('integers and doubles', () => {
    expect(F.bitLength(-5n)).toBe(3);
    expect(F.bitLength(0n)).toBe(0);
    expect(F.fromInt(0n)).toEqual(F.ZERO);
    expect(F.fromInt(12n)).toEqual({ man: 3n, exp: 2 });
    // mpmath from_int(13, 2) = (0, 3, 2, 2)
    expect(F.fromInt(13n, 2)).toEqual({ man: 3n, exp: 2 });
    expect(() => F.fromNumber(Infinity)).toThrow(RangeError);
    expect(F.toStr(F.fromNumber(5e-324), 20)).toBe('4.9406564584124654418e-324');
    expect(F.fromNumber(-0.75)).toEqual({ man: -3n, exp: -2 });
    expect(F.fromRational(1n, -4n, P)).toEqual({ man: -1n, exp: -2 });
    expect(F.fromRational(0n, 3n, P)).toEqual(F.ZERO);
  });
  it('division, roots and powers', () => {
    expect(() => F.div(F.ONE, F.ZERO, P)).toThrow(RangeError);
    expect(F.div(F.ZERO, F.ONE, P)).toEqual(F.ZERO);
    expect(F.div(F.fromInt(-3n), F.fromInt(4n), P)).toEqual({ man: -3n, exp: -2 });
    expect(() => F.isqrt(-1n)).toThrow(RangeError);
    expect([F.isqrt(0n), F.isqrt(1n), F.isqrt(99n)]).toEqual([0n, 1n, 9n]);
    expect(() => F.sqrt(F.fromInt(-1n), P)).toThrow(RangeError);
    expect(F.sqrt(F.ZERO, P)).toEqual(F.ZERO);
    expect(F.powInt(r('1.5'), 0n, P)).toEqual(F.ONE);
    expect(F.toStr(F.powInt(r('1.5'), -3n, P), 30)).toBe('0.296296296296296296296296296296');
    expect(F.toStr(F.powInt(r('1.1'), 10000n, P), 30)).toBe('8.44990025120034795728149042687e+413');
    expect(F.toFixed({ man: 5n, exp: -4 }, 2)).toBe(1n);
    expect(F.toFixed({ man: 5n, exp: 1 }, 2)).toBe(40n);
    expect(F.fromFixed(12n, 2)).toEqual({ man: 3n, exp: 0 });
    expect(F.fromFixed(13n, 2, 2)).toEqual({ man: 3n, exp: 0 });
  });
  it('parses literals', () => {
    expect(F.toStr(F.fromStr('1/3', P), 30)).toBe('0.333333333333333333333333333333');
    expect(F.toStr(F.fromStr('-2/-4', P), 30)).toBe('0.5');
    expect(() => F.fromStr('.', P)).toThrow(SyntaxError);
    expect(() => F.fromStr('1.2.3', P)).toThrow(SyntaxError);
    expect(() => F.fromStr('e5', P)).toThrow(SyntaxError);
    expect(F.toStr(F.fromStr('.5', P), 5)).toBe('0.5');
    expect(F.fromStr('-1_0e2', P)).toEqual(F.fromInt(-1000n));
  });
});

describe('mpf toStr (mpmath to_str)', () => {
  it('rounds and chooses the notation', () => {
    const cases: [string, number, string][] = [
      ['0.99999996', 5, '1.0'],
      ['9.99996', 5, '10.0'],
      ['0.0001234', 6, '0.0001234'],
      ['0.0000001234', 6, '1.234e-7'],
      ['123456789', 5, '1.2346e+8'],
      ['12345', 8, '12345.0'],
      ['2.5', 0, '.0e+0'],
      ['7.5', 0, '.0e+1'],
    ];
    for (const [x, d, want] of cases) expect([x, d, F.toStr(r(x), d)]).toEqual([x, d, want]);
    expect(F.toStr(r('1234.5'), 6, true, -2, 2)).toBe('1.2345e+3');
    expect(F.toStr(F.ZERO, 0)).toBe('.0');
    expect(F.toStr(r('12345'), 3, true, -5, 10)).toBe('12300.0');
    expect(F.toStr(F.ZERO, 5)).toBe('0.0');
    expect(F.toStr(F.fromInt(2n ** 4000n), 10)).toBe('1.318204093e+1204');
    expect(F.toStr(F.powInt(F.fromInt(2n), -4000n, P), 10)).toBe('7.586078703e-1205');
    expect(F.toStr(r('-1.5'), 10, false)).toBe('-1.500000000');
  });
  it('prints low-precision Floats like SymPy', () => {
    // str(Float(s, precision=3))
    const cases: [string, string][] = [
      ['0.3', '0.e-1'],
      ['-0.3', '-0.e-1'],
      ['7', '0.e+1'],
      ['-7', '-0.e+1'],
      ['0.6', '0.e+0'],
    ];
    for (const [x, want] of cases) expect([x, F.floatToString(F.fromStr(x, 3), 3, true)]).toEqual([x, want]);
  });
});
