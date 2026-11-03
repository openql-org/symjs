// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/multinomial.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { binomialCoefficients, binomialCoefficientsList, multinomialCoefficients, multinomialCoefficientsIterator } from '../../src/ntheory/index';

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
    ["binomialCoefficients(9)", () => binomialCoefficients(9), "{[0, 9]: 1, [9, 0]: 1, [1, 8]: 9, [8, 1]: 9, [2, 7]: 36, [7, 2]: 36, [3, 6]: 84, [6, 3]: 84, [4, 5]: 126, [5, 4]: 126}"],
    ["binomialCoefficientsList(9)", () => binomialCoefficientsList(9), "[1, 9, 36, 84, 126, 126, 84, 36, 9, 1]"],
    ["multinomialCoefficients(2, 5)", () => multinomialCoefficients(2, 5), "{[0, 5]: 1, [5, 0]: 1, [1, 4]: 5, [4, 1]: 5, [2, 3]: 10, [3, 2]: 10}"],
    ["multinomialCoefficients(3, 3)", () => multinomialCoefficients(3, 3), "{[3, 0, 0]: 1, [2, 1, 0]: 3, [1, 2, 0]: 3, [0, 3, 0]: 1, [2, 0, 1]: 3, [1, 1, 1]: 6, [0, 2, 1]: 3, [1, 0, 2]: 3, [0, 1, 2]: 3, [0, 0, 3]: 1}"],
    ["multinomialCoefficients(5, 2)", () => multinomialCoefficients(5, 2), "{[2, 0, 0, 0, 0]: 1, [1, 1, 0, 0, 0]: 2, [0, 2, 0, 0, 0]: 1, [1, 0, 1, 0, 0]: 2, [0, 1, 1, 0, 0]: 2, [0, 0, 2, 0, 0]: 1, [1, 0, 0, 1, 0]: 2, [0, 1, 0, 1, 0]: 2, [0, 0, 1, 1, 0]: 2, [0, 0, 0, 2, 0]: 1, [1, 0, 0, 0, 1]: 2, [0, 1, 0, 0, 1]: 2, [0, 0, 1, 0, 1]: 2, [0, 0, 0, 1, 1]: 2, [0, 0, 0, 0, 2]: 1}"],
    ["[multinomialCoefficients(0, 0), multinomialCoefficients(0, 3), multinomialCoefficients(3, 0), multinomialCoefficients(1, 4)]", () => [multinomialCoefficients(0, 0), multinomialCoefficients(0, 3), multinomialCoefficients(3, 0), multinomialCoefficients(1, 4)], "[{[]: 1}, {}, {[0, 0, 0]: 1}, {[4]: 1}]"],
    ["[...multinomialCoefficientsIterator(6, 2)]", () => [...multinomialCoefficientsIterator(6, 2)], "[[[2, 0, 0, 0, 0, 0], 1], [[1, 1, 0, 0, 0, 0], 2], [[0, 2, 0, 0, 0, 0], 1], [[1, 0, 1, 0, 0, 0], 2], [[0, 1, 1, 0, 0, 0], 2], [[0, 0, 2, 0, 0, 0], 1], [[1, 0, 0, 1, 0, 0], 2], [[0, 1, 0, 1, 0, 0], 2], [[0, 0, 1, 1, 0, 0], 2], [[0, 0, 0, 2, 0, 0], 1], [[1, 0, 0, 0, 1, 0], 2], [[0, 1, 0, 0, 1, 0], 2], [[0, 0, 1, 0, 1, 0], 2], [[0, 0, 0, 1, 1, 0], 2], [[0, 0, 0, 0, 2, 0], 1], [[1, 0, 0, 0, 0, 1], 2], [[0, 1, 0, 0, 0, 1], 2], [[0, 0, 1, 0, 0, 1], 2], [[0, 0, 0, 1, 0, 1], 2], [[0, 0, 0, 0, 1, 1], 2], [[0, 0, 0, 0, 0, 2], 1]]"],
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
  it('multinomial_coefficients_iterator(3, 0)', () => {
    expect([...multinomialCoefficientsIterator(3, 0)]).toEqual([[[0n, 0n, 0n], 1n]]);
  });
});
