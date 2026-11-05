// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/utilities/memoization.ts (SymPy recurrence_memo and assoc_recurrence_memo).

import { describe, expect, it } from 'vitest';
import { assocRecurrenceMemo, recurrenceMemo } from '../../src/utilities/memoization';

describe('recurrenceMemo (SymPy doctest)', () => {
  it('factorial', () => {
    let calls = 0;
    const factorial = recurrenceMemo([1])((n, prev) => {
      calls++;
      return n * prev[prev.length - 1]!;
    });
    expect(factorial(4)).toBe(24);
    // the cached values are used
    expect(factorial(3)).toBe(6);
    expect(calls).toBe(4);
    expect(factorial.cacheLength()).toBe(5);
    expect(factorial.fetchItem(2, 4)).toEqual([2, 6]);
    expect(factorial.fetchItem(4)).toBe(24);
  });
});

describe('assocRecurrenceMemo', () => {
  it('the binomial triangle', () => {
    // C(n, 0) = 1, C(n, m) = C(n-1, m-1) + C(n-1, m) (0 beyond the previous row)
    const C = assocRecurrenceMemo(() => 1)((n, m, rows) => rows[n - 1]![m - 1]! + (rows[n - 1]![m] ?? 0));
    expect(C(4, 2)).toBe(6);
    expect(C(2, 1)).toBe(2);
    expect([0, 1, 2, 3, 4, 5].map((m) => C(5, m))).toEqual([1, 5, 10, 10, 5, 1]);
  });
});
