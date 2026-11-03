// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/egyptian.ts.

import { describe, expect, it } from 'vitest';
import { Expr, Rational } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { egyptianFraction } from '../../src/ntheory/index';

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

const R = (p: bigint, q: bigint): Rational => Rational.of(p, q);

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[egyptianFraction(Rational.of(3, 7)), egyptianFraction([3, 7], 'Graham Jewett'), egyptianFraction([3, 7], 'Takenouchi'), egyptianFraction([3, 7], 'Golomb'), egyptianFraction([11, 5], 'Golomb')]", () => [egyptianFraction(Rational.of(3, 7)), egyptianFraction([3, 7], 'Graham Jewett'), egyptianFraction([3, 7], 'Takenouchi'), egyptianFraction([3, 7], 'Golomb'), egyptianFraction([11, 5], 'Golomb')], "[[3, 11, 231], [7, 8, 9, 56, 57, 72, 3192], [4, 7, 28], [3, 15, 35], [1, 2, 3, 4, 9, 234, 1118, 2580]]"],
    ["[egyptianFraction(2), egyptianFraction([4, 3]), egyptianFraction([7, 6]), egyptianFraction([5, 121]), egyptianFraction([5, 121], 'Graham Jewett'), egyptianFraction([5, 121], 'Takenouchi'), egyptianFraction([5, 121], 'Golomb'), egyptianFraction([4, 13], 'Takenouchi'), egyptianFraction(3), egyptianFraction([1, 7])]", () => [egyptianFraction(2), egyptianFraction([4, 3]), egyptianFraction([7, 6]), egyptianFraction([5, 121]), egyptianFraction([5, 121], 'Graham Jewett'), egyptianFraction([5, 121], 'Takenouchi'), egyptianFraction([5, 121], 'Golomb'), egyptianFraction([4, 13], 'Takenouchi'), egyptianFraction(3), egyptianFraction([1, 7])], "[[1, 2, 3, 6], [1, 3], [1, 6], [25, 757, 763309, 873960180913, 1527612795642093418846225], [121, 122, 123, 124, 125, 14762, 14763, 14764, 14765, 15006, 15007, 15008, 15252, 15253, 15500, 217931406, 217931407, 217931408, 217960932, 217960933, 217990460, 225195042, 225195043, 225225056, 232638756, 47494097939068242, 47494097939068243, 47494098374931056, 47506968096269556, 50712807166576806, 2255689339045806279678209072038806], [31, 121, 1891, 3691, 27243271], [25, 1225, 3577, 7081, 11737], [4, 28, 46, 4186], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 230, 57960], [7]]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

/**
 * Coverage of ntheory/egyptian.ts, modular.ts, digits.ts, multinomial.ts
 * and random.ts, with the expected values of SymPy 1.14 (and of Python's
 * random.Random for the Mersenne Twister).
 */

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
});
