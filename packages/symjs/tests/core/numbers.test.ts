// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/numbers.ts.
// Number classes and integer helpers. Expected values are SymPy 1.14's (sympy.core.tests.test_numbers).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Rational } from '../../src/core/nodes';
import { bitLength, factorInt, ipow, iroot, lcm, perfectPower } from '../../src/core/numbers';

describe('factorInt: a cofactor above the trial-division limit that is a perfect power', () => {
  it('65537**2', () => {
    expect([...factorInt(4295098369n)]).toEqual([[65537n, 2n]]);
  });
});

describe('numeric helpers', () => {
  it('computes bigint helpers', () => {
    expect(lcm(0n, 5n)).toBe(0n);
    expect(lcm(4n, -6n)).toBe(12n);
    expect(() => ipow(2n, -1n)).toThrow(RangeError);
    expect(() => iroot(-1n, 2n)).toThrow(RangeError);
    expect(iroot(1n, 3n)).toBe(1n);
    expect(iroot(10n, 1n)).toBe(10n);
    expect(iroot(3n, 64n)).toBe(1n);
    expect(iroot(26n, 3n)).toBe(2n);
    expect(iroot(27n, 3n)).toBe(3n);
    expect(() => factorInt(0n)).toThrow(RangeError);
  });

  it('takes integer roots beyond the double range', () => {
    // a floating-point first guess overflows beyond 2**1024
    const big = 2n ** 1100n;
    expect(iroot(big, 2n)).toBe(2n ** 550n);
    expect(iroot(big + 1n, 2n)).toBe(2n ** 550n);
    expect(iroot(big - 1n, 2n)).toBe(2n ** 550n - 1n);
    const c = 3n ** 700n;
    expect(iroot(c, 7n)).toBe(3n ** 100n);
    // SymPy: sqrt(2**1100) = 2**550
    expect(sj.sqrt(Rational.of(big)).equals(Rational.of(2n ** 550n))).toBe(true);
  });
});

it('takes an integer root with a degree larger than the bit length', () => {
  expect(iroot(16n, 10n ** 17n)).toBe(1n);
  expect(iroot(16n, 4n)).toBe(2n);
});

describe('large integers', () => {
  it('bitLength counts the bits', () => {
    expect([1n, 2n, 255n, 256n, (1n << 200n) - 1n, 1n << 200n].map(bitLength)).toEqual([1, 2, 8, 9, 200, 201]);
  });
  it('perfectPower gives the base that is no perfect power and the largest exponent', () => {
    expect(perfectPower(1n)).toBeUndefined();
    expect(perfectPower(3n)).toBeUndefined();
    expect(perfectPower(4n)).toEqual([2n, 2n]);
    expect(perfectPower(64n)).toEqual([2n, 6n]);
    expect(perfectPower(ipow(6n, 35n))).toEqual([6n, 35n]);
    expect(perfectPower(ipow(1000003n, 12n))).toEqual([1000003n, 12n]);
    expect(perfectPower(ipow(1000003n, 12n) + 1n)).toBeUndefined();
    // divisible by the residue modulus of the exponent
    expect(perfectPower(49n)).toEqual([7n, 2n]);
    expect(perfectPower(ipow(7n, 3n))).toEqual([7n, 3n]);
  });
  it('factorInt divides a large integer by its small prime factors and keeps the cofactor', () => {
    const cofactor = (1n << 127n) - 1n;
    const n = 4n * 9n * 25n * ipow(65521n, 2n) * 101n * ipow(cofactor, 3n);
    const expected = [[2n, 2n], [3n, 2n], [5n, 2n], [101n, 1n], [65521n, 2n], [cofactor, 3n]];
    expect([...factorInt(n)]).toEqual(expected);
    // the remembered factorization is returned as a copy
    factorInt(n).clear();
    expect([...factorInt(n)]).toEqual(expected);
    // a large prime power below the square of the trial limit after division
    expect([...factorInt((1n << 130n) * 65537n)]).toEqual([[2n, 130n], [65537n, 1n]]);
    expect([...factorInt(5n * 49n * 11n)]).toEqual([[5n, 1n], [7n, 2n], [11n, 1n]]);
    // nothing is left after the first chunk of trial divisors
    expect([...factorInt(ipow(5n, 60n))]).toEqual([[5n, 60n]]);
    // more than 512 large factorizations empty the memory
    for (let i = 0n; i < 520n; i++) expect(factorInt((1n << 140n) + i).size).toBeGreaterThan(0);
  });
});
