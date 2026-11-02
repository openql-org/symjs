// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { AlgebraicNumber, Rational, add, sqrt } from '../src';

describe('AlgebraicNumber (SymPy)', () => {
  it('elements as polynomials in a primitive element', () => {
    const a1 = new AlgebraicNumber(sqrt(2));
    expect(String(a1.evalf(10))).toBe('1.414213562');
    const a2 = new AlgebraicNumber(a1, [3, -5]);
    expect(String(a2.asExpr())).toBe('-5 + 3*sqrt(2)');
    expect(String(new AlgebraicNumber(a2, [2, -1]).asExpr())).toBe('-11 + 6*sqrt(2)');
  });
  it('an element of Q(sqrt(2) + sqrt(3))', () => {
    const a4 = new AlgebraicNumber(add(sqrt(2), sqrt(3)), [Rational.of(1, 2), 0, Rational.of(-9, 2), 0]);
    expect(String(a4.toRoot())).toBe('sqrt(2)');
    expect(String(a4.primitiveElement())).toBe('sqrt(2) + sqrt(3)');
    expect(a4.coeffs().map(String)).toEqual(['1/2', '0', '-9/2', '0']);
  });
});
