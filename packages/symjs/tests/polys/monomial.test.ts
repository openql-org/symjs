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

describe('monomial operations (sympy.polys.monomials)', () => {
  it('compute on exponent tuples like SymPy', () => {
    expect(sj.monomialMul([3, 4, 1], [1, 2, 0])).toEqual([4, 6, 1]);
    expect(sj.monomialDiv([3, 4, 1], [1, 2, 0])).toEqual([2, 2, 1]);
    expect(sj.isNoMatch(sj.monomialDiv([3, 4, 1], [1, 2, 2]))).toBe(true);
    expect(sj.monomialLdiv([3, 4, 1], [1, 2, 2])).toEqual([2, 2, -1]);
    expect(sj.monomialPow([1, 2], 3)).toEqual([3, 6]);
    expect(sj.monomialGcd([1, 4, 1], [3, 2, 0])).toEqual([1, 2, 0]);
    expect(sj.monomialLcm([1, 4, 1], [3, 2, 0])).toEqual([3, 4, 1]);
    expect(sj.monomialDivides([1, 2], [3, 4])).toBe(true);
    expect(sj.monomialDivides([1, 2], [0, 2])).toBe(false);
    expect(sj.monomialMax([3, 4, 5], [0, 5, 1], [6, 3, 9])).toEqual([6, 5, 9]);
    expect(sj.monomialMin([3, 4, 5], [0, 5, 1], [6, 3, 9])).toEqual([0, 3, 1]);
    expect(sj.monomialMax([1, 2])).toEqual([1, 2]);
    expect(sj.monomialMin()).toEqual([]);
    expect(sj.monomialDeg([1, 2])).toBe(3);
    expect(sj.monomialCount(2, 2).toString()).toBe('6');
    expect(sj.monomialCount(3, 4).toString()).toBe('35');
  });

  it('itermonomials gives the monomials of SymPy', () => {
    const strs = (es: sj.Expr[]) => es.map((e) => e.toString()).sort();
    expect(strs(sj.itermonomials([x, y], 2))).toEqual(['1', 'x', 'x**2', 'x*y', 'y', 'y**2']);
    expect(strs(sj.itermonomials([x, y], [2, 4], [1, 2]))).toEqual(['x**2*y**2', 'x**2*y**3', 'x**2*y**4', 'x*y**2', 'x*y**3', 'x*y**4']);
    expect(strs(sj.itermonomials([x, y], [1, 1]))).toEqual(['1', 'x', 'x*y', 'y']);
    expect(strs(sj.itermonomials([x, y], 3, 2))).toEqual(['x**2', 'x**2*y', 'x**3', 'x*y', 'x*y**2', 'y**2', 'y**3']);
    expect(sj.itermonomials([x], 1, 2)).toEqual([]);
    expect(strs(sj.itermonomials([], 3))).toEqual(['1']);
    expect(strs(sj.itermonomials([x], 0))).toEqual(['1']);
    const [A, B] = sj.symbols('A B', { commutative: false }) as [sj.Sym, sj.Sym];
    expect(strs(sj.itermonomials([A, B], 2))).toEqual(['1', 'A', 'A**2', 'A*B', 'B', 'B**2', 'B*A']);
  });

  it('itermonomials rejects invalid degrees like SymPy', () => {
    expect(() => sj.itermonomials([x, y], [1])).toThrow(RangeError);
    expect(() => sj.itermonomials([x, y], [1, 1], 1)).toThrow(TypeError);
    expect(() => sj.itermonomials([x, y], [1, 1], [1])).toThrow(RangeError);
    expect(() => sj.itermonomials([x, y], [1, 1], [-1, 0])).toThrow(RangeError);
    expect(() => sj.itermonomials([x, y], [1, 1], [2, 0])).toThrow(RangeError);
    expect(() => sj.itermonomials([x], -1)).toThrow(RangeError);
    expect(() => sj.itermonomials([x], 2, [1])).toThrow(TypeError);
    expect(() => sj.itermonomials([x], 2, -1)).toThrow(RangeError);
  });
});
