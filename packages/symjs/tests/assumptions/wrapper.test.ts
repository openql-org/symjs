// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/wrapper.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { isExtendedNonnegative, isExtendedReal, isInfinite } from '../../src/assumptions';

const { Q } = sj;
const [a, x] = sj.symbols('a x');

describe('assumption wrappers', () => {
  it('is_infinite, is_extended_real, is_extended_nonnegative', () => {
    expect(isInfinite(a!, Q.finite(a!))).toBe(false);
    expect(isInfinite(sj.S.Infinity)).toBe(true);
    expect(isExtendedReal(sj.I)).toBe(false);
    expect(isExtendedNonnegative(-1)).toBe(false);
    expect(isExtendedNonnegative(x!, Q.positive(x!))).toBe(true);
  });
});
