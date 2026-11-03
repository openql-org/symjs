// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of ntheory/egyptian.ts, modular.ts, digits.ts, multinomial.ts
 * and random.ts, with the expected values of SymPy 1.14 (and of Python's
 * random.Random for the Mersenne Twister).
 */

import { describe, expect, it } from 'vitest';
import { Rational } from '../src/core/nodes';
import { NoMatch } from '../src/core/truth';
import { digits, egyptianFraction, multinomialCoefficientsIterator, solveCongruence } from '../src/ntheory/index';
import { Random } from '../src/ntheory/random';

const R = (p: bigint, q: bigint): Rational => Rational.of(p, q);

describe('ntheory egyptian, modular, digits, multinomial and random: results equal SymPy 1.14', () => {
  it('egyptian_fraction', () => {
    expect([R(3n, 8n), R(4n, 9n), R(5n, 9n), R(7n, 9n), R(6n, 7n), R(8n, 15n)].map((r) => egyptianFraction(r, 'Takenouchi'))).toEqual([
      [4n, 8n],
      [3n, 15n, 23n, 1035n],
      [3n, 9n, 15n, 23n, 1035n],
      [3n, 5n, 9n, 15n, 23n, 45n, 1035n],
      [2n, 4n, 14n, 28n],
      [2n, 30n],
    ]);
    expect(egyptianFraction(R(11n, 6n))).toEqual([1n, 2n, 3n]);
    expect(egyptianFraction(R(25n, 12n))).toEqual([1n, 2n, 3n, 4n]);
  });
  it('solve_congruence and digits', () => {
    expect(solveCongruence([
      [2, 3],
      [1, 3],
    ])).toBe(NoMatch);
    expect(solveCongruence([
      [2, 3],
      [5, 3],
      [1, 5],
    ])).toEqual([11n, 15n]);
    expect(digits(35, 10, 2)).toEqual([10n, 3n, 5n]);
  });
  it('multinomial_coefficients_iterator(3, 0)', () => {
    expect([...multinomialCoefficientsIterator(3, 0)]).toEqual([[[0n, 0n, 0n], 1n]]);
  });
  it('random.Random', () => {
    // a seed longer than the 624-word state
    const r = new Random(2n ** (32n * 700n) + 12345n);
    expect([r.getrandbits(32), r.getrandbits(32), r.getrandbits(32), r.getrandbits(0)]).toEqual([3687411726n, 559672658n, 722415311n, 0n]);
    expect(() => r.getrandbits(-1)).toThrow(RangeError);
    expect(() => r.randrange(5n, 5n)).toThrow(RangeError);
  });
});
