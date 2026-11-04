// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/index.ts.

import { describe, expect, it } from 'vitest';
import { Expr, pi, Rational } from '../../src/core/nodes';
import { sqrt } from '../../src/core/ops';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { fn } from '../../src/functions/elementary/elementary';
import { parseExpr } from '../../src/index';
import { abundance, binomialCoefficients, binomialCoefficientsList, composite, continuedFraction, continuedFractionConvergents, continuedFractionIterator, continuedFractionPeriodic, continuedFractionReduce, countDigits, digits, discreteLog, divisorCount, dra, drm, ecm, egyptianFraction, factorint, isAmicable, isNthpowResidue, isPalindromic, isPrimitiveRoot, isQuadResidue, mersennePrimeExponent, multinomialCoefficients, multinomialCoefficientsIterator, multiplicity, multiplicityInFactorial, nextprime, nOrder, npartitions, nthrootMod, perfectPower, pollardPm1, pollardRho, polynomialCongruence, prevprime, prime, primitiveRoot, primorial, qsFactor, quadraticCongruence, quadraticResidues, Random, sqrtMod, sqrtModIter } from '../../src/ntheory/index';

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

function take<T>(g: Iterator<T>, k: number): T[] {
  const out: T[] = [];
  for (let i = 0; i < k; i++) {
    const r = g.next();
    if (r.done === true) break;
    out.push(r.value);
  }
  return out;
}

describe('ntheory: more results', () => {
  it('values that SymPy checks with ==', () => {
    expect(prevprime(25)).toBe(prime(9));
    expect(nOrder(3, 10) === 4n && isPrimitiveRoot(3, 10)).toBe(true);
    expect(divisorCount(6, 1, { proper: true })).toBe(3n);
    expect(abundance(6)).toBe(0n);
    expect(isAmicable(220, 284)).toBe(true);
    expect(py(npartitions(25))).toBe('1958');
    expect(multiplicity(fn('factorial', [25]), fn('factorial', [2n ** 100n], { evaluate: false }))).toBe(multiplicityInFactorial(fn('factorial', [25]), 2n ** 100n));
    expect(py(continuedFractionReduce([1, 4, 2, [3, 1]]))).toBe('(sqrt(21) + 287)/238');
    expect(py(continuedFractionReduce([[1]]))).toBe('(1 + sqrt(5))/2');
  });

  it('errors', () => {
    expect(() => prime(0)).toThrow(RangeError);
    expect(() => composite(0)).toThrow(RangeError);
    expect(() => nextprime(5, 0)).toThrow(RangeError);
    expect(() => prevprime(2)).toThrow(RangeError);
    expect(() => primorial(0)).toThrow(RangeError);
    expect(() => pollardRho(4)).toThrow(RangeError);
    expect(() => pollardPm1(3)).toThrow(RangeError);
    expect(() => digits(35, 10, 1)).toThrow(RangeError);
    expect(() => digits(35, 1)).toThrow(RangeError);
    expect(() => egyptianFraction(-1)).toThrow(RangeError);
    expect(() => egyptianFraction(P('x'))).toThrow(TypeError);
    expect(() => multiplicity(1, 5)).toThrow(RangeError);
    expect(() => multiplicity(2, 0)).toThrow(RangeError);
    expect(() => multiplicityInFactorial(0, 5)).toThrow(RangeError);
    expect(() => discreteLog(7, 3, 2)).toThrow(RangeError);
    expect(() => nOrder(2, 4)).toThrow(RangeError);
    expect(() => nOrder(2, 1)).toThrow(RangeError);
    expect(() => isPrimitiveRoot(2, 4)).toThrow(RangeError);
    expect(() => primitiveRoot(1)).toThrow(RangeError);
    expect(() => ecm(15, { B1: 101 })).toThrow(RangeError);
    expect(() => qsFactor(1, 10, 10)).toThrow(RangeError);
    expect(() => mersennePrimeExponent(52)).toThrow(RangeError);
    expect(() => mersennePrimeExponent(0)).toThrow(RangeError);
    expect(() => continuedFractionPeriodic(1, 0)).toThrow(RangeError);
    expect(() => continuedFractionPeriodic(1, 2, -1)).toThrow(RangeError);
    expect(() => continuedFraction(P('x'))).toThrow(RangeError);
    expect(() => continuedFraction(P('sqrt(2) + sqrt(3)'))).toThrow(RangeError);
    expect(() => dra(5, 1)).toThrow(RangeError);
    expect(() => drm(5, 1)).toThrow(RangeError);
    expect(() => quadraticCongruence(1, 1, 1, 1)).toThrow(RangeError);
    expect(() => nthrootMod(1, 0, 7)).toThrow(RangeError);
    expect(() => isNthpowResidue(1, -1, 7)).toThrow(RangeError);
    expect(() => isQuadResidue(1, 0)).toThrow(RangeError);
    expect(() => polynomialCongruence(P('x*y + 1'), 5)).toThrow(RangeError);
    expect(() => polynomialCongruence(P('x/2 + 1'), 5)).toThrow(RangeError);
    expect(() => factorint(Rational.of(1, 2))).toThrow(TypeError);
    expect(() => perfectPower(P('x'))).toThrow(TypeError);
  });

  it('remaining API surface', () => {
    expect(py(sqrtMod(3, 7))).toBe('None');
    expect(py(nthrootMod(3, 3, 7))).toBe('None');
    expect(nthrootMod(3, 3, 7, true)).toEqual([]);
    expect(py(primitiveRoot(12))).toBe('None');
    expect(py(take(sqrtModIter(4, 15), 10))).toBe('[7, 13, 2, 8]');
    expect(py(quadraticResidues(10))).toBe('[0, 1, 4, 5, 6, 9]');
    expect(py(countDigits(0))).toBe('{0: 1}');
    expect(isPalindromic(12321)).toBe(true);
    expect(py(binomialCoefficients(2))).toBe('{[0, 2]: 1, [2, 0]: 1, [1, 1]: 2}');
    expect(py(binomialCoefficientsList(0))).toBe('[1]');
    expect(py([...multinomialCoefficientsIterator(2, 2)])).toBe('[[[0, 2], 1], [[2, 0], 1], [[1, 1], 2]]');
    expect(py(multinomialCoefficients(3, 2))).toBe('{[2, 0, 0]: 1, [1, 1, 0]: 2, [0, 2, 0]: 1, [1, 0, 1]: 2, [0, 1, 1]: 2, [0, 0, 2]: 1}');
    expect(py(take(continuedFractionConvergents(continuedFractionIterator(sqrt(2))), 4))).toBe('[1, 3/2, 7/5, 17/12]');
    expect(py(factorint(Rational.of(12), { multiple: true }))).toBe('[2, 2, 3]');
    expect(py(new Random(5).randbelow(10n))).toBe('9');
    expect(py(pi)).toBe('pi');
  });
});
