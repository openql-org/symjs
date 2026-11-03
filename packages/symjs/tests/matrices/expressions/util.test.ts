// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/util.ts.
//
// The matrix expression utilities. Expected values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import { symbol, symbols } from '../../../src';
import { relTruth } from '../../../src/matrices/expressions/util';

const [n, , , k] = symbols('n i j k', { integer: true });

describe('remaining branches (SymPy 1.14)', () => {
  it('relational truth from the sign of the difference', () => {
    const ip = symbol('i', { integer: true, positive: true });
    const jn = symbol('j', { integer: true, nonnegative: true });
    expect(relTruth('Gt', n.add(ip), n)).toBe(true);
    expect(relTruth('Le', n.add(ip), n)).toBe(false);
    expect(relTruth('Ge', n.add(jn), n)).toBe(true);
    expect(relTruth('Lt', n.add(jn), n)).toBe(false);
    expect(relTruth('Ge', n.add(ip), n.add(ip.mul(2)))).toBe(false);
    expect(relTruth('Lt', n, k)).toBe('unknown');
    expect(relTruth('Eq', n, k)).toBe('unknown');
  });
});
