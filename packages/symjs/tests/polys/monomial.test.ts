// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/monomial.ts: monomials and monomial orders; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];

describe('Monomial', () => {
  it('operations zip the exponent tuples like SymPy', () => {
    const m = new sj.Monomial([1, 2]);
    expect(String(m.asExpr(x, y))).toBe('x*y**2');
    expect(String(m.mul(new sj.Monomial([1, 0])))).toBe('Monomial((2, 2))');
    expect(String(m.gcd(new sj.Monomial([0, 3])))).toBe('Monomial((0, 2))');
    expect(String(m.lcm(new sj.Monomial([3, 0])))).toBe('Monomial((3, 2))');
    // Monomial((1, 2))*(1,), .gcd((5,)), .lcm((0,)) -> Monomial((2,)), Monomial((1,)), Monomial((1,))
    expect(String(m.mul([1]))).toBe('Monomial((2,))');
    expect(String(m.gcd([5]))).toBe('Monomial((1,))');
    expect(String(m.lcm([0]))).toBe('Monomial((1,))');
    expect(String(m.asExpr(x))).toBe('x');
    expect(String(new sj.Monomial([1], [x, y]).asExpr())).toBe('x');
    expect(String(new sj.Monomial([1, 2], [x, y]))).toBe('x**1*y**2');
    expect(String(new sj.Monomial([1, 2], [x, y]).mul(new sj.Monomial([1, 1])).asExpr())).toBe('x**2*y**3');
    expect(String(new sj.Monomial([2], [x]))).toBe('x**2');
    expect(String(new sj.Monomial([2]))).toBe('Monomial((2,))');
    expect(() => m.asExpr()).toThrow('Cannot convert Monomial((1, 2)) to an expression without generators');
  });
});
