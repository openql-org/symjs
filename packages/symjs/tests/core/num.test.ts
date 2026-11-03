// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/num.ts.
// Numeric helpers. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import '../../src';
import { Expr, Float, Rational, S } from '../../src/core/nodes';
import { numAdd, numCmp, numInv, numMul, numPowInt } from '../../src/core/num';

const s = (e: Expr): string => e.toString();
const R = (p: number, q = 1) => Rational.of(p, q);

describe('numeric helpers', () => {
  it('works on Floats and Rationals', () => {
    expect(s(numAdd(new Float(1.5), R(1, 2)))).toBe('2.00000000000000');
    expect(s(numMul(R(1, 2), new Float(3)))).toBe('1.50000000000000');
    expect(s(numAdd(new Float(1.5, 100), new Float(1.5)))).toBe('3.0000000000000000000000000000');
    expect(numCmp(new Float(1.5), R(3, 2))).toBe(0);
    expect(numCmp(R(1), new Float(1.5))).toBe(-1);
    expect(numCmp(new Float(2.5), new Float(1.5))).toBe(1);
    expect(() => numInv(S.Zero)).toThrow(RangeError);
    expect(() => numPowInt(S.Zero, -1n)).toThrow(RangeError);
  });
});
