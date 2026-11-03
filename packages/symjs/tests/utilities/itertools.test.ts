// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/utilities/itertools.ts.
// The Python itertools helpers.

import { describe, expect, it } from 'vitest';
import { combinationsWithReplacement, permutations, product } from '../../src/utilities/itertools';

describe('itertools', () => {
  it('empty results', () => {
    expect([...permutations([1, 2], 3)]).toEqual([]);
    expect([...permutations([1, 2], -1)]).toEqual([]);
    expect([...combinationsWithReplacement([], 2)]).toEqual([]);
    expect([...combinationsWithReplacement([1], -1)]).toEqual([]);
    expect([...product([[1], []])]).toEqual([]);
  });
});
