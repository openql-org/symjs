// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of ntheory/primetest.ts, factor.ts and qs.ts: the Lucas-Lehmer
 * test of an exponent GIMPS has not verified, the widening of the ECM bounds
 * and a factor found as the large prime of a partial relation of the
 * quadratic sieve. Expected values from SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import { isMersennePrime } from '../src/ntheory/index';
import { lucasLehmer, mersennePrimeCheck } from '../src/ntheory/primetest';
import { factorintInt } from '../src/ntheory/factor';
import { qs, qsFactor } from '../src/ntheory/qs';

describe('Mersenne primes', () => {
  it('runs the Lucas-Lehmer test above the verified bound', () => {
    // 2**11 - 1 = 2047 = 23*89, 2**7 - 1 = 127 is prime
    expect(lucasLehmer(7)).toBe(true);
    expect(lucasLehmer(11)).toBe(false);
    expect(lucasLehmer(13)).toBe(true);
    // with a bound of 0 the exponent 11 (a prime not in the list) goes to Lucas-Lehmer
    expect(mersennePrimeCheck(2047n, 0)).toBe(false);
    // a known exponent answers before the test, a composite exponent after the bound check
    expect(mersennePrimeCheck(8191n, 0)).toBe(true);
    expect(mersennePrimeCheck(2n ** 15n - 1n, 0)).toBe(false);
    // SymPy is_mersenne_prime(2047) = False, is_mersenne_prime(2**61 - 1) = True
    expect(isMersennePrime(2047n)).toBe(false);
    expect(isMersennePrime(2n ** 61n - 1n)).toBe(true);
  });
});

describe('factorint: ECM bounds', () => {
  it('widens the bounds when the first ECM round finds nothing', () => {
    // a 25-digit semiprime goes to ECM after three rounds of trial division,
    // Pollard p-1 and rho; with B1 = 20 the first round fails and B1 grows to 100
    // SymPy factorint(1000000012367*3000000000793) = {1000000012367: 1, 3000000000793: 1}
    const f = factorintInt(1000000012367n * 3000000000793n, { ecmB1: 20n });
    expect([...f].sort((a, b) => (a[0] < b[0] ? -1 : 1))).toEqual([
      [1000000012367n, 1n],
      [3000000000793n, 1n],
    ]);
  });
});

describe('qs: a prime factor from a partial relation', () => {
  it('takes out a factor of N above the factor base', () => {
    // 1009 is not in the factor base of primes below 100; it divides N and
    // shows up as the large prime of a partial relation
    // SymPy: qs_factor(1009*100003, 100, 10000) = {1009: 1, 100003: 1}
    expect([...qsFactor(1009n * 100003n, 100n, 10000n)]).toEqual([
      [1009n, 1n],
      [100003n, 1n],
    ]);
    // SymPy: qs(1009*1000003*100003, 100, 10000) = {1009, 100003300009}
    expect([...qs(1009n * 1000003n * 100003n, 100n, 10000n)]).toEqual([1009n, 100003300009n]);
  });
});
