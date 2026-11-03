// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of ntheory/primetest.ts: Miller-Rabin and the strong BPSW test,
 * Mersenne and Gaussian primes and the factor cache, with the expected
 * values of SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import { I, Rational, Sym } from '../src/core/nodes';
import { NoMatch } from '../src/core/truth';
import { FactorCache, factorCache, isGaussianPrime, isMersennePrime, isStrongBpswPrp, lucasSequence, mr } from '../src/ntheory/primetest';

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
