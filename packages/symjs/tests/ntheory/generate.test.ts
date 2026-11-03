// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/generate.ts.

import { beforeEach, describe, expect, it } from 'vitest';
import { Expr, Rational } from '../../src/core/nodes';
import { sqrt } from '../../src/core/ops';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { primepiInt } from '../../src/ntheory/generate';
import { composite, compositepi, cycleLength, nextprime, prevprime, prime, primerange, primorial, randprime, seed, sieve } from '../../src/ntheory/index';
import { asInt } from '../../src/ntheory/intutil';
import { isprime } from '../../src/ntheory/primetest';

/** Python's printed form of a result. */
function py(v: unknown): string {
  if (v === NoMatch || v === Unsolved || v === undefined || v === null) return 'None';
  if (v === true) return 'True';
  if (v === false) return 'False';
  if (typeof v === 'bigint' || typeof v === 'number' || typeof v === 'string') return String(v);
  if (v instanceof Expr) return v.toString();
  if (Array.isArray(v)) return `[${v.map(py).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${py(k)}: ${py(w)}`).join(', ')}}`;
  if (v instanceof Set) return `[${[...v].map(py).join(', ')}]`;
  return Object.prototype.toString.call(v);
}

beforeEach(() => sieve.reset());

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[10,11,12,13,14].map((i) => [i, nextprime(i)])", () => [10,11,12,13,14].map((i) => [i, nextprime(i)]), "[[10, 11], [11, 13], [12, 13], [13, 17], [14, 17]]"],
    ["nextprime(2, 2)", () => nextprime(2, 2), "5"],
    ["[10,11,12,13,14].map((i) => [i, prevprime(i)])", () => [10,11,12,13,14].map((i) => [i, prevprime(i)]), "[[10, 7], [11, 7], [12, 11], [13, 11], [14, 13]]"],
    ["[prime(10), prime(1), prime(100000), prime(1000), prime(5000), prime(25)]", () => [prime(10), prime(1), prime(100000), prime(1000), prime(5000), prime(25)], "[29, 2, 1299709, 7919, 48611, 97]"],
    ["[...primerange(19)]", () => [...primerange(19)], "[2, 3, 5, 7, 11, 13, 17]"],
    ["[...primerange(7, 19)]", () => [...primerange(7, 19)], "[7, 11, 13, 17]"],
    ["[...primerange(prime(10) + 1n)]", () => [...primerange(prime(10) + 1n)], "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"],
    ["[...primerange(1000000, 1000100)]", () => [...primerange(1000000, 1000100)], "[1000003, 1000033, 1000037, 1000039, 1000081, 1000099]"],
    ["[primorial(4), primorial(4, { nth: false }), primorial(1), primorial(1, { nth: false }), primorial(sqrt(101), { nth: false })]", () => [primorial(4), primorial(4, { nth: false }), primorial(1), primorial(1, { nth: false }), primorial(sqrt(101), { nth: false })], "[210, 6, 2, 1, 210]"],
    ["[composite(36), composite(1), composite(17737), composite(100000)]", () => [composite(36), composite(1), composite(17737), composite(100000)], "[52, 4, 20000, 110487]"],
    ["[compositepi(25), compositepi(1000), compositepi(10**6)]", () => [compositepi(25), compositepi(1000), compositepi(10**6)], "[15, 831, 921501]"],
    ["cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n).next().value", () => cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n).next().value, "[6, 3]"],
    ["[...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { values: true })]", () => [...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { values: true })], "[4, 17, 35, 2, 5, 26, 14, 44, 50, 2, 5, 26, 14]"],
    ["cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4 }).next().value", () => cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4 }).next().value, "[4, None]"],
    ["[...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4, values: true })]", () => [...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4, values: true })], "[4, 17, 35, 2]"],
    ["[0n,1n,2n,3n,4n].map((s) => cycleLength((x: bigint) => (2048n * x * x + 32767n) % 16843009n, s).next().value)", () => [0n,1n,2n,3n,4n].map((s) => cycleLength((x: bigint) => (2048n * x * x + 32767n) % 16843009n, s).next().value), "[[2489, 43], [78, 121], [1482, 100], [1482, 286], [1482, 101]]"],
    ["cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n).next().value", () => cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n).next().value, "[3, 3]"],
    ["[...cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n, { values: true })]", () => [...cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n, { values: true })], "[2, 16, 13, 11, 14, 4]"],
    ["(seed(3), [randprime(1, 30), randprime(1000, 2000), randprime(10n**20n, 10n**21n), randprime(5, 5)])", () => (seed(3), [randprime(1, 30), randprime(1000, 2000), randprime(10n**20n, 10n**21n), randprime(5, 5)]), "[11, 1607, 526680989626225826647, None]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

describe('primality', () => {
  it('randprime gives primes in the range', () => {
    for (let i = 0; i < 5; i++) {
      const p = randprime(1, 30);
      expect(typeof p === 'bigint' && isprime(p) && p < 30n).toBe(true);
    }
    expect(randprime(30, 1)).toBe(NoMatch);
    expect(() => randprime(24, 28)).toThrow(RangeError);
    seed(1);
  });
});

/**
 * Coverage of ntheory/generate.ts and ntheory/sieve.ts, starting from a
 * reset sieve (primes up to 13) so that the paths beyond the sieve run;
 * the expected values are those of SymPy 1.14 after sieve._reset().
 */

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
