// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/groupnumbers.ts.
// Nilpotent, abelian and cyclic numbers and the number of groups of order n. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { groupsCount, isAbelianNumber, isCyclicNumber, isNilpotentNumber } from '../../src/combinatorics';

describe('group numbers', () => {
  it('nilpotent, abelian and cyclic numbers', () => {
    expect([21, 4, 15, 1, 8, 6, 45].map(isNilpotentNumber)).toEqual([false, true, true, true, true, false, true]);
    expect([4, 60, 1, 8, 9, 45].map(isAbelianNumber)).toEqual([true, false, true, false, true, true]);
    expect([15, 4, 1, 6, 35].map(isCyclicNumber)).toEqual([true, false, true, false, true]);
    expect(() => isCyclicNumber(0)).toThrow(RangeError);
  });
  it('groups_count', () => {
    const cases: [number, bigint][] = [
      [1, 1n], [2, 1n], [3, 1n], [4, 2n], [8, 5n], [9, 2n], [10, 2n], [12, 5n], [15, 1n], [16, 14n], [27, 5n], [30, 4n], [32, 51n], [64, 267n],
      [81, 15n], [243, 67n], [729, 504n], [2187, 9310n], [125, 5n], [625, 15n], [3125, 77n], [16807, 83n], [15625, 684n], [117649, 860n],
      [78125, 34297n], [823543, 113147n], [19487171, 750735n], [6, 2n], [21, 2n], [105, 2n], [1155, 4n], [255255, 10n], [92, 4n], [30030, 144n], [1806, 30n], [609, 3n], [25, 2n], [5, 1n],
    ];
    for (const [n, c] of cases) expect(groupsCount(n)).toBe(c);
    for (const n of [5 ** 8, 100, 3 ** 10]) expect(() => groupsCount(n)).toThrow(RangeError);
  });
});
