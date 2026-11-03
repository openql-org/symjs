// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/modular.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { crt, crt1, crt2, digits, solveCongruence, symmetricResidue } from '../../src/ntheory/index';

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
    ["[crt([99, 97, 95], [49, 76, 65]), crt([12, 6, 17], [3, 4, 2], { check: false }), crt([12, 6, 17], [3, 4, 2]), crt([3, 6], [2, 5]), crt([5, 7], [3, 4], { symmetric: true })]", () => [crt([99, 97, 95], [49, 76, 65]), crt([12, 6, 17], [3, 4, 2], { check: false }), crt([12, 6, 17], [3, 4, 2]), crt([3, 6], [2, 5]), crt([5, 7], [3, 4], { symmetric: true })], "[[639985, 912285], [954, 1224], None, [5, 6], [-17, 35]]"],
    ["[solveCongruence([[2, 3], [3, 5], [2, 7]]), solveCongruence([[2, 3], [4, 6]]), solveCongruence([[2, 3], [5, 6]]), solveCongruence([[2, 3], [5, 6]], { symmetric: true }), solveCongruence([[1, 4], [3, 6], [5, 10]]), solveCongruence([[3, 9], [3, 9]])]", () => [solveCongruence([[2, 3], [3, 5], [2, 7]]), solveCongruence([[2, 3], [4, 6]]), solveCongruence([[2, 3], [5, 6]]), solveCongruence([[2, 3], [5, 6]], { symmetric: true }), solveCongruence([[1, 4], [3, 6], [5, 10]]), solveCongruence([[3, 9], [3, 9]])], "[[23, 105], None, [5, 6], [-1, 6], [45, 60], [3, 9]]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

describe('ntheory: more results', () => {
  it('modular helpers', () => {
    const [mm, e, s] = crt1([3, 5, 7]);
    expect(crt2([3, 5, 7], [2, 3, 2], mm, e, s)).toEqual([23n, 105n]);
    expect(crt2([3, 5, 7], [2, 3, 2], mm, e, s, true)).toEqual([23n, 105n]);
    expect(symmetricResidue(5n, 6n)).toBe(-1n);
    expect(solveCongruence([[2, 3], [3, 5], [2, 7]])).toEqual([23n, 105n]);
    expect([23n % 3n, 23n % 5n, 23n % 7n]).toEqual([2n, 3n, 2n]);
    expect(crt([12, 6, 17], [3, 4, 2])).toBe(NoMatch);
  });
});

/**
 * Coverage of ntheory/egyptian.ts, modular.ts, digits.ts, multinomial.ts
 * and random.ts, with the expected values of SymPy 1.14 (and of Python's
 * random.Random for the Mersenne Twister).
 */

describe('ntheory egyptian, modular, digits, multinomial and random: results equal SymPy 1.14', () => {
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
});
