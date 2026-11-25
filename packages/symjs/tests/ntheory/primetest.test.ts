// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/primetest.ts.

import { describe, expect, it } from 'vitest';
import { Expr, I, Rational, Sym } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { parseExpr } from '../../src/index';
import { isPerfect, MERSENNE_PRIME_EXPONENTS } from '../../src/ntheory/index';
import { FactorCache, factorCache, isGaussianPrime, isMersennePrime, isprime, isStrongBpswPrp, lucasLehmer, lucasSequence, mersennePrimeCheck, mr } from '../../src/ntheory/primetest';

const P = (s: string): Expr => parseExpr(s);

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

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[isMersennePrime(6), isMersennePrime(127), isMersennePrime(2n**61n - 1n), isMersennePrime(2n**67n - 1n)]", () => [isMersennePrime(6), isMersennePrime(127), isMersennePrime(2n**61n - 1n), isMersennePrime(2n**67n - 1n)], "[False, True, True, False]"],
    ["['2+3*I', '3', '7*I', '1+I', '4+I', '-3', '5', '11*I', '2*I'].map((z) => isGaussianPrime(P(z)))", () => ['2+3*I', '3', '7*I', '1+I', '4+I', '-3', '5', '11*I', '2*I'].map((z) => isGaussianPrime(P(z))), "[True, True, True, True, True, True, False, True, False]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

describe('factor cache', () => {
  it('stores the largest prime factor (SymPy factor_cache)', () => {
    factorCache.set(15, 5);
    expect(factorCache.has(15)).toBe(true);
    expect(factorCache.get(15)).toBe(5n);
    expect(factorCache.getItem(15)).toBe(5n);
    factorCache.set(15, 3);
    expect(factorCache.get(15)).toBe(5n);
    expect(() => factorCache.set(15, 4)).toThrow(RangeError);
    expect(factorCache.get(13)).toBe(13n);
    factorCache.delete(15);
    expect(factorCache.get(1000000000000000000n * 3n)).toBe(NoMatch);
    expect(() => factorCache.getItem(4)).toThrow(RangeError);
  });

  it('LRU size limit and external source', () => {
    expect(new FactorCache().maxsize).toBe(Infinity);
    const c = new FactorCache(2);
    expect(c.maxsize).toBe(2);
    c.set(15, 5);
    c.set(21, 7);
    c.get(15);
    c.set(35, 7);
    expect([...c.keys()]).toEqual([15n, 35n]);
    expect(c.size).toBe(2);
    c.maxsize = 1;
    expect([...c.keys()]).toEqual([35n]);
    expect(() => (c.maxsize = 0)).toThrow(RangeError);
    c.maxsize = Infinity;
    expect(c.maxsize).toBe(Infinity);
    c.maxsize = 1;
    c.cacheClear();
    expect(c.size).toBe(0);
    class Ext extends FactorCache {
      getExternal(n: bigint): bigint[] {
        return n === 1001n ? [7n, 11n, 13n] : [];
      }
    }
    const e = new Ext();
    expect(e.get(1001)).toBe(13n);
    expect(e.get(77)).toBe(11n);
  });
});

describe('primality', () => {
  it('isprime agrees with SymPy on pseudoprimes and large primes', () => {
    const L = [
      3825123056546413051n, 318665857834031151167461n, 3317044064679887385961981n, 2n ** 89n - 1n, 2n ** 127n - 1n, 561n, 2n ** 127n + 1n, 10n ** 30n + 57n, 341531n,
      4296595241n, 8321n, 1000003n, 2n ** 61n - 1n, 3215031751n, 2152302898747n, 1122004669633n, 3474749660383n, 341550071728321n, 3825123056546413051n * 3n,
      10n ** 100n + 267n, 10n ** 100n + 949n,
    ];
    expect(py(L.map((n) => isprime(n)))).toBe(
      '[False, False, False, True, True, False, False, True, False, False, False, True, True, False, False, False, False, False, False, True, True]',
    );
  });

  it('known Mersenne exponents', () => {
    expect(MERSENNE_PRIME_EXPONENTS.length).toBe(52);
    expect(isPerfect(2n ** 12n * (2n ** 13n - 1n))).toBe(true);
  });
});

/**
 * Coverage of ntheory/primetest.ts: Miller-Rabin and the strong BPSW test,
 * Mersenne and Gaussian primes and the factor cache, with the expected
 * values of SymPy 1.14.
 */

describe('ntheory primetest: results equal SymPy 1.14', () => {
  it('mr and _lucas_sequence', () => {
    expect([mr(1n, [2n]), mr(10n, [2n]), mr(2n, [2n])]).toEqual([false, false, true]);
    expect(lucasSequence(10n, 3n, 1n, 0n)).toEqual([0n, 2n, 1n]);
  });
  it('is_strong_bpsw_prp', () => {
    expect(() => isStrongBpswPrp(0n)).toThrow(RangeError);
    expect([isStrongBpswPrp(1n), isStrongBpswPrp(2n), isStrongBpswPrp(4n), isStrongBpswPrp(341n)]).toEqual([false, true, false, false]);
    // strong pseudoprimes to base 2: (D/n) = 0 for a D sharing a factor with n, and squares stopped at D = 13
    expect([15841n, 29341n, 74665n, 800605n, 1093n ** 2n, 3511n ** 2n].map(isStrongBpswPrp)).toEqual([false, false, false, false, false, false]);
  });
  it('is_mersenne_prime', () => {
    expect([isMersennePrime(0n), isMersennePrime(-1n), isMersennePrime(2n ** 11n - 1n), isMersennePrime(2n ** 127n - 1n), isMersennePrime(6n)]).toEqual([false, false, false, true, false]);
  });
  it('is_gaussian_prime', () => {
    expect(() => isGaussianPrime(new Sym('x'))).toThrow(TypeError);
    expect(() => isGaussianPrime(Rational.of(1n, 2n))).toThrow(TypeError);
    expect(() => isGaussianPrime(new Sym('x').add(I.mul(2)))).toThrow(TypeError);
    expect([isGaussianPrime(I.mul(3).add(2)), isGaussianPrime(I.mul(3)), isGaussianPrime(-7n), isGaussianPrime(4n)]).toEqual([true, true, true, false]);
  });
  it('FactorCache', () => {
    expect(factorCache.maxsize).toBe(1000);
    expect(() => new FactorCache(0)).toThrow(RangeError);
    const c = new FactorCache();
    c.set(15n, 5n);
    expect(() => c.delete(16n)).toThrow(RangeError);
    expect(() => c.set(15n, 4n)).toThrow(RangeError);
    // an update keeps the place of the entry: SymPy list(c) == [21, 35]
    const d = new FactorCache(2);
    d.set(15n, 5n);
    d.set(21n, 7n);
    d.set(15n, 3n);
    d.set(35n, 7n);
    expect([...d.keys()]).toEqual([21n, 35n]);
    d.maxsize = 1;
    expect([...d.keys()]).toEqual([35n]);
  });
  it('FactorCache.getExternal', () => {
    class C extends FactorCache {
      override getExternal(n: bigint): bigint[] | typeof NoMatch {
        if (n === 15n) return [5n, 3n];
        if (n === 1001n) return [7n, 11n, 13n];
        return NoMatch;
      }
    }
    const c = new C();
    expect([c.get(15n), c.get(1001n)]).toEqual([5n, 13n]);
    expect([...c.keys()]).toEqual([15n, 3n, 1001n, 77n, 7n]);
    expect([c.get(77n), c.get(10n ** 9n + 9n)]).toEqual([11n, NoMatch]);
    // SymPy raises KeyError here: maxsize 1 evicts 15 while add() caches the factors of 3;
    // the largest factor 5 is still the answer
    expect(new C(1).get(15n)).toBe(5n);
  });
});

/**
 * Coverage of ntheory/primetest.ts, factor.ts and qs.ts: the Lucas-Lehmer
 * test of an exponent GIMPS has not verified, the widening of the ECM bounds
 * and a factor found as the large prime of a partial relation of the
 * quadratic sieve. Expected values from SymPy 1.14.
 */

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

it('public Miller-Rabin and Proth tests accept integer-like inputs', async () => {
  const { mr, prothTest } = await import('../../src/ntheory');
  expect(mr(Rational.of(1373651), [2, 3])).toBe(false);
  expect(mr(479001599, [31, 73])).toBe(true);
  expect(() => prothTest(2)).toThrow(RangeError);
  expect(() => prothTest(7)).toThrow(RangeError);
  for (let n = 3; n < 4000; n += 2) {
    let k = n - 1, power = 1;
    while (k % 2 === 0) { k /= 2; power *= 2; }
    if (k >= power) continue;
    let prime = true;
    for (let d = 2; d * d <= n; d++) if (n % d === 0) prime = false;
    expect(prothTest(n), String(n)).toBe(prime);
  }
});

describe('Fermat, Euler and extra strong Lucas probable prime tests (SymPy 1.14 primetest)', () => {
  it('is_fermat_pseudoprime', async () => {
    const { isFermatPseudoprime } = await import('../../src/ntheory/primetest');
    expect(isFermatPseudoprime(5, 1)).toBe(true);
    expect(isFermatPseudoprime(9, 1)).toBe(true);
    expect(isFermatPseudoprime(2, 1)).toBe(true);
    expect(isFermatPseudoprime(4, 1)).toBe(false);
    expect(isFermatPseudoprime(341, 2)).toBe(true);
    expect(isFermatPseudoprime(15, 2)).toBe(false);
    expect(isFermatPseudoprime(1, 2)).toBe(false);
    expect(isFermatPseudoprime(4, 3)).toBe(false);
    expect(isFermatPseudoprime(2, 3)).toBe(true);
    expect(isFermatPseudoprime(13, 15)).toBe(true);
    expect(() => isFermatPseudoprime(9, 3)).toThrow(RangeError);
    expect(() => isFermatPseudoprime(9, 0)).toThrow(RangeError);
    expect(() => isFermatPseudoprime(0, 2)).toThrow(RangeError);
  });
  it('is_euler_pseudoprime and is_euler_jacobi_pseudoprime', async () => {
    const { isEulerPseudoprime, isEulerJacobiPseudoprime } = await import('../../src/ntheory/primetest');
    // SymPy: the Euler pseudoprimes to base 2 below 1000 are 341 and 561, the Euler-Jacobi one is 561
    const below = (t: (n: number) => boolean): number[] => Array.from({ length: 999 }, (_, i) => i + 1).filter((n) => t(n) && !isprime(n));
    expect(below((n) => isEulerPseudoprime(n, 2))).toEqual([341, 561]);
    expect(below((n) => isEulerJacobiPseudoprime(n, 2))).toEqual([561]);
    expect(isEulerJacobiPseudoprime(11, 1)).toBe(true);
    expect(isEulerJacobiPseudoprime(15, 1)).toBe(true);
    expect(isEulerJacobiPseudoprime(2, 3)).toBe(true);
    expect(isEulerPseudoprime(9, 1)).toBe(true);
    expect(isEulerPseudoprime(4, 1)).toBe(false);
    expect(isEulerPseudoprime(4, 3)).toBe(false);
    expect(isEulerPseudoprime(2, 3)).toBe(true);
    expect(isEulerPseudoprime(1, 3)).toBe(false);
    expect(() => isEulerPseudoprime(0, 3)).toThrow(RangeError);
    expect(() => isEulerPseudoprime(9, 3)).toThrow(RangeError);
    expect(() => isEulerJacobiPseudoprime(9, 3)).toThrow(RangeError);
  });
  it('is_extra_strong_lucas_prp', async () => {
    const { isExtraStrongLucasPrp } = await import('../../src/ntheory/primetest');
    const composites = Array.from({ length: 6000 }, (_, i) => i).filter((n) => isExtraStrongLucasPrp(n) && !isprime(n));
    expect(composites).toEqual([989, 3239, 5777]);
    expect(isExtraStrongLucasPrp(10877)).toBe(true);
    for (const n of [2, 3, 5, 7, 101]) expect(isExtraStrongLucasPrp(n)).toBe(true);
    for (const n of [0, 1, 4, 9, 15, 16, 169]) expect(isExtraStrongLucasPrp(n)).toBe(false);
  });
});
