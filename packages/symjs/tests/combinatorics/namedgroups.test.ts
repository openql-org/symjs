// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference values from SymPy 1.14 combinatorics.named_groups.
import { expect, it } from 'vitest';
import { AlternatingGroup, CyclicGroup, DihedralGroup, SymmetricGroup } from '../../src/combinatorics';
it.each([1, 2, 3, 4, 5])('constructs named groups for n=%i', (n) => {
  expect(CyclicGroup(n).order()).toBe(BigInt(n)); expect(CyclicGroup(n).isAbelian).toBe(true);
  expect(DihedralGroup(n).order()).toBe(BigInt(n * 2)); expect(DihedralGroup(n).isAbelian).toBe(n <= 2);
  expect(DihedralGroup(n).degree).toBe(n < 3 ? n * 2 : n);
  expect(AlternatingGroup(n).order()).toBe([1n, 1n, 3n, 12n, 60n][n - 1]);
  expect(AlternatingGroup(n).isAlternating).toBe(true);
});
it('requires positive integer parameters', () => {
  // SymPy CyclicGroup(0) reports order zero, which violates the group axioms.
  // symjs deliberately rejects this invalid parameter instead.
  for (const f of [AlternatingGroup, CyclicGroup, DihedralGroup, SymmetricGroup]) {
    for (const n of [0, -1, 1.5, Infinity]) expect(() => f(n)).toThrow('positive integer');
  }
});
