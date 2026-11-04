// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/digits.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { fn } from '../../src/functions/elementary/elementary';
import { countDigits, digits, isPalindromic } from '../../src/ntheory/index';

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
    ["[digits(35), digits(-35), digits(27, 2), digits(35, 10, 4), digits(0), digits(255, 16)]", () => [digits(35), digits(-35), digits(27, 2), digits(35, 10, 4), digits(0), digits(255, 16)], "[[10, 3, 5], [-10, 3, 5], [2, 1, 1, 0, 1, 1], [10, 0, 0, 3, 5], [10, 0], [16, 15, 15]]"],
    ["[countDigits(1111339), countDigits(250), countDigits(250, 16), countDigits(-100)]", () => [countDigits(1111339), countDigits(250), countDigits(250, 16), countDigits(-100)], "[{1: 4, 3: 2, 9: 1}, {2: 1, 5: 1, 0: 1}, {15: 1, 10: 1}, {1: 1, 0: 2}]"],
    ["[0,1,2,3,4,5,6,7,8,9].filter((i) => countDigits(fn('factorial', [77])).get(BigInt(i)) === 7n)", () => [0,1,2,3,4,5,6,7,8,9].filter((i) => countDigits(fn('factorial', [77])).get(BigInt(i)) === 7n), "[1, 3, 7, 9]"],
    ["[[-11, 1, 22, 121].every((i) => isPalindromic(i)), isPalindromic(88, 8), isPalindromic(0o121), isPalindromic(121, 8) && isPalindromic(121)]", () => [[-11, 1, 22, 121].every((i) => isPalindromic(i)), isPalindromic(88, 8), isPalindromic(0o121), isPalindromic(121, 8) && isPalindromic(121)], "[True, False, False, True]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});
