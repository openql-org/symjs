// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/numberfields.ts: AlgebraicNumber and minimal polynomials; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { add, AlgebraicNumber, Rational, sqrt } from '../../src';

const { parse } = sj;
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('AlgebraicNumber', () => {
  it('values, coefficients and elements of elements', () => {
    const a = new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 3]);
    expect(show(a.coeffs())).toBe('[1, 3]');
    expect(String(a.asExpr())).toBe('sqrt(2) + 3');
    expect(String(a.toRoot())).toBe('sqrt(2) + 3');
    expect(String(a.primitiveElement())).toBe('sqrt(2)');
    expect(String(a.evalf(10))).toBe('4.414213562');
    expect(String(new sj.AlgebraicNumber(parse('sqrt(2)')).asExpr())).toBe('sqrt(2)');
    const b = new sj.AlgebraicNumber(a, [2, 1]);
    expect(show(b.coeffs())).toBe('[2, 7]');
    expect(String(b.asExpr())).toBe('2*sqrt(2) + 7');
    expect(String(b.root)).toBe('sqrt(2)');
    expect(show(new sj.AlgebraicNumber(a, [1, 0, 0]).coeffs())).toBe('[6, 11]');
    // AlgebraicNumber(AlgebraicNumber(sqrt(2), [1, 0, 0]), [1, 0]).coeffs() -> [2]
    expect(show(new sj.AlgebraicNumber(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, 0]), [1, 0]).coeffs())).toBe('[2]');
    // AlgebraicNumber(AlgebraicNumber(sqrt(2), [1, 0, 5]), [1, 0]).coeffs() -> [7]
    expect(show(new sj.AlgebraicNumber(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, 5]), [1, 0]).coeffs())).toBe('[7]');
    const c = new sj.AlgebraicNumber(parse('2**(1/3)'), [1, 0, 0]);
    expect(String(c.asExpr())).toBe('2**(2/3)');
    // AlgebraicNumber(AlgebraicNumber(cbrt(2), [1, 0, 0]), [1, 0, 0]): [2, 0], 2*2**(1/3)
    const d = new sj.AlgebraicNumber(c, [1, 0, 0]);
    expect(show(d.coeffs())).toBe('[2, 0]');
    expect(String(d.asExpr())).toBe('2*2**(1/3)');
    expect(show(new sj.AlgebraicNumber(c, [1, 0]).coeffs())).toBe('[1, 0, 0]');
  });
  it('reduction modulo the minimal polynomial', () => {
    expect(show(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, 0]).coeffs())).toBe('[2]');
    expect(show(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, -2]).coeffs())).toBe('[0]');
    expect(show(new sj.AlgebraicNumber(parse('3'), [1, 3]).coeffs())).toBe('[6]');
    const s = new sj.AlgebraicNumber(parse('sqrt(2) + sqrt(3)'), [1, 0, 0]);
    expect(show(s.coeffs())).toBe('[1, 0, 0]');
    expect(show(new sj.AlgebraicNumber(s, [1, 0]).coeffs())).toBe('[1, 0, 0]');
    const s2 = new sj.AlgebraicNumber(s, [1, 0, 0]);
    expect(show(s2.coeffs())).toBe('[10, 0, -1]');
    expect(String(s2.asExpr())).toBe('20*sqrt(6) + 49');
    // SymPy reduces modulo minimal_polynomial(cos(pi/7)) = 8*x**3 - 4*x**2 - 4*x + 1, giving
    // [3/4, 1/8, -1/16]; symjs has no minimal polynomial for cos(pi/7) and keeps the composition
    const c = new sj.AlgebraicNumber(parse('cos(pi/7)'), [1, 0, 0]);
    expect(show(new sj.AlgebraicNumber(c, [1, 0, 0]).coeffs())).toBe('[1, 0, 0, 0, 0]');
  });
  it('minimal polynomials of radicals', () => {
    const X = new sj.Sym('x');
    expect(String(sj.minimalPolynomial(parse('2**(1/3)'), X))).toBe('x**3 - 2');
    expect(String(sj.minimalPolynomial(parse('2**(2/3)'), X))).toBe('x**3 - 4');
    expect(String(sj.minimalPolynomial(parse('sqrt(2) + sqrt(3)'), X))).toBe('x**4 - 10*x**2 + 1');
    expect(String(sj.minimalPolynomial(3, X))).toBe('x - 3');
    // SymPy: x**4 - 2*x**2 - 1 and NotAlgebraic for 2**pi; symjs handles rational radicals and square-root towers over QQ only
    expect(() => sj.minimalPolynomial(parse('sqrt(1 + sqrt(2))'), X)).toThrow(sj.NotImplementedError);
    expect(() => sj.minimalPolynomial(parse('2**pi'), X)).toThrow(sj.NotImplementedError);
  });
});

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
