// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of ntheory/generate.ts and ntheory/sieve.ts, starting from a
 * reset sieve (primes up to 13) so that the paths beyond the sieve run;
 * the expected values are those of SymPy 1.14 after sieve._reset().
 */

import { beforeEach, describe, expect, it } from 'vitest';
import { Rational } from '../src/core/nodes';
import type { Expr } from '../src/core/nodes';
import { Unsolved } from '../src/core/truth';
import { asInt } from '../src/ntheory/intutil';
import { composite, compositepi, cycleLength, nextprime, prevprime, prime, primerange, primorial, sieve } from '../src/ntheory/index';
import { primepiInt } from '../src/ntheory/generate';

beforeEach(() => sieve.reset());

describe('ntheory generate: results equal SymPy 1.14', () => {
  it('nextprime', () => {
    expect([nextprime(0), nextprime(-5, 2), nextprime(10, 10), nextprime(1.5)]).toEqual([2n, 3n, 43n, 2n]);
    // 10**12 + 60 = 0 (mod 6) with 10**12 + 61 prime; 10**12 + 59 = 5 (mod 6) with 10**12 + 61 prime
    // n = 0 (mod 6): n + 1 prime (10**12 + 38) or not (10**12 + 2); n = 5 (mod 6): n + 2 prime (10**12 + 37) or not (10**12 + 1)
    expect([nextprime(1000000000038n), nextprime(1000000000038n, 2), nextprime(1000000000002n)]).toEqual([1000000000039n, 1000000000061n, 1000000000039n]);
    expect([nextprime(1000000000037n), nextprime(1000000000037n, 2), nextprime(1000000000001n)]).toEqual([1000000000039n, 1000000000061n, 1000000000039n]);
    expect([nextprime(1000000000060n, 2), nextprime(1000000000060n), nextprime(1000000000059n, 2), nextprime(1000000000059n)]).toEqual([1000000000063n, 1000000000061n, 1000000000063n, 1000000000061n]);
  });
  it('prevprime', () => {
    expect([prevprime(5), prevprime(7)]).toEqual([3n, 5n]);
    expect([prevprime(10n ** 12n + 1n), prevprime(10n ** 12n + 6n), prevprime(10n ** 12n + 7n), prevprime(10n ** 12n + 2n)]).toEqual([999999999989n, 999999999989n, 999999999989n, 999999999989n]);
    expect([prevprime(1000000000061n), prevprime(1000000000062n), prevprime(1000000000063n)]).toEqual([1000000000039n, 1000000000061n, 1000000000061n]);
  });
  it('primerange', () => {
    expect([...primerange(-5, 30)]).toEqual([2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n]);
    sieve.reset();
    expect([...primerange(15, 40)]).toEqual([17n, 19n, 23n, 29n, 31n, 37n]);
    sieve.reset();
    expect([...primerange(16, 40)]).toEqual([17n, 19n, 23n, 29n, 31n, 37n]);
    sieve.reset();
    expect([...primerange(170, 200)]).toEqual([173n, 179n, 181n, 191n, 193n, 197n, 199n]);
    sieve.reset();
    expect([...primerange(169, 170)]).toEqual([]);
    expect([...primerange(30, 20)]).toEqual([]);
    sieve.reset();
    expect([...primerange(100, 101)]).toEqual([]);
    sieve.reset();
    expect([...primerange(10n ** 12n, 10n ** 12n + 40n)]).toEqual([1000000000039n]);
  });
  it('composite, compositepi, prime, primorial and primepi', () => {
    expect([composite(1), composite(11), composite(30), composite(1000), composite(20000)]).toEqual([4n, 20n, 45n, 1197n, 22518n]);
    sieve.reset();
    expect([25000, 30000, 12345, 40000, 50001].map((n) => composite(n))).toEqual([28062n, 33598n, 13996n, 44640n, 55648n]);
    // within an extended sieve
    sieve.extend(2000);
    expect([100, 101, 500, 777].map((n) => composite(n))).toEqual([133n, 134n, 612n, 936n]);
    sieve.reset();
    expect([compositepi(3), compositepi(100), compositepi(Rational.of(201n, 2n)), primepiInt(1n)]).toEqual([0n, 74n, 74n, 0n]);
    sieve.reset();
    expect([prime(5), prime(100), prime(1001), primorial(5, { nth: false }), primorial(Rational.of(11n, 2n), { nth: false })]).toEqual([11n, 541n, 7927n, 30n, 30n]);
    // a limitation of symjs: the Lucy method runs in doubles
    expect(() => primepiInt(1n << 53n)).toThrow(RangeError);
  });
  it('cycle_length', () => {
    // expression values: equal terms are different objects
    const f = (x: Expr): Expr => Rational.of((asInt(x) ** 2n + 1n) % 100n);
    expect([...cycleLength(f, Rational.of(3n))]).toEqual([[6n, 2n]]);
    const g = (x: Expr): Expr => Rational.of((asInt(x) ** 2n + 1n) % 17n);
    expect([...cycleLength(g, Rational.of(2n), { values: true })].map((e) => asInt(e))).toEqual([2n, 5n, 9n, 14n, 10n, 16n, 2n, 5n, 9n, 14n, 10n, 16n, 2n]);
    const h = (x: bigint): bigint => (x * x + 1n) % 1000n;
    expect([...cycleLength(h, 3n, { nmax: 4 })]).toEqual([[4n, Unsolved]]);
    expect([...cycleLength(h, 3n, { nmax: 4, values: true })]).toEqual([3n, 10n, 101n, 202n]);
  });
});

describe('ntheory sieve: results equal SymPy 1.14', () => {
  it('empty ranges, indices and resets', () => {
    expect([...sieve.primerange(10, 5)]).toEqual([]);
    expect([...sieve.totientrange(0, 5)]).toEqual([1n, 1n, 2n, 2n]);
    expect([...sieve.totientrange(5, 5)]).toEqual([]);
    expect([...sieve.mobiusrange(-1, 5)]).toEqual([1n, -1n, -1n, 0n]);
    expect([...sieve.mobiusrange(7, 3)]).toEqual([]);
    expect(() => sieve.slice(0, 5)).toThrow(RangeError);
    expect(() => sieve.slice(1, 5, 0)).toThrow(RangeError);
    expect(sieve.slice(1, 10, 3)).toEqual([2n, 7n, 17n]);
    sieve.extend(100);
    expect([...sieve.totientrange(1, 50)].length).toBe(49);
    sieve.reset({ totient: true });
    expect(sieve.primes.length).toBe(25);
    sieve.reset({ prime: true });
    expect(sieve.primes.length).toBe(6);
    // a limitation of symjs: the sieve holds 32-bit primes
    expect(() => sieve.extend(2n ** 32n)).toThrow(RangeError);
    expect(() => [...sieve.primerange(2n ** 32n, 2n ** 32n + 20n)]).toThrow(RangeError);
  });
});
