// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/*: constructors, numerics with symbol values, and the adjoint and
// transpose of non-commutative symbols. Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  Li,
  Sym,
  acosh,
  adjoint,
  arg,
  asec,
  asech,
  beta,
  binomial,
  catalan,
  conjugate,
  erf,
  erfc,
  erfcinv,
  erfi,
  exp,
  ff,
  fn,
  fresnelc,
  fresnels,
  harmonic,
  li,
  parse,
  pow,
  re,
  subfactorial,
  toComplex,
  transpose,
  zeta,
} from '../src';

const x = new Sym('x');
const y = new Sym('y');
const A = new Sym('A', { commutative: false });

describe('functions: constructors and numerics', () => {
  it('constructors', () => {
    const got = [asec(x), acosh(x), asech(x), harmonic(x, 2), beta(x, y), zeta(x), li(x), Li(x), fresnels(x), fresnelc(x), erfi(x), subfactorial(x), catalan(x), ff(x, 2)].map(String);
    expect(got).toEqual(['asec(x)', 'acosh(x)', 'asech(x)', 'harmonic(x, 2)', 'beta(x, y)', 'zeta(x)', 'li(x)', 'Li(x)', 'fresnels(x)', 'fresnelc(x)', 'erfi(x)', 'subfactorial(x)', 'catalan(x)', 'x*(x - 1)']);
    expect(String(erfcinv(2))).toBe('-oo');
  });
  it('double-precision values with symbol values', () => {
    // SymPy N(binomial(5.5, 2.5)), N(erf(-3)), N(erfc(-0.5))
    expect(toComplex(binomial(x, y), { x: 5.5, y: 2.5 }).re).toBeCloseTo(14.4375, 10);
    expect(toComplex(erf(x), { x: -3 }).re).toBeCloseTo(-0.999977909503001, 12);
    expect(toComplex(erfc(x), { x: -0.5 }).re).toBeCloseTo(1.52049987781305, 12);
  });
  it('arg of real constants decided numerically', () => {
    expect(String(arg(parse('1 - sqrt(2)')))).toBe('pi');
    expect(String(arg(parse('sqrt(3) - 1')))).toBe('0');
    expect(String(conjugate(re(x)))).toBe('re(x)');
  });
  it('adjoint and transpose of non-commutative symbols', () => {
    expect(String(transpose(pow(A, 2)))).toBe('transpose(A)**2');
    expect(String(transpose(transpose(A)))).toBe('A');
    expect(String(transpose(conjugate(A)))).toBe('adjoint(A)');
    expect(String(transpose(adjoint(A)))).toBe('conjugate(A)');
    expect(String(transpose(exp(A)))).toBe('exp(transpose(A))');
    expect(String(adjoint(transpose(A)))).toBe('conjugate(A)');
    expect(String(adjoint(conjugate(A)))).toBe('transpose(A)');
    expect(String(adjoint(pow(A, 2)))).toBe('adjoint(A)**2');
    expect(String(adjoint(adjoint(A)))).toBe('A');
    expect(String(fn('transpose', [transpose(A)]))).toBe('A');
    expect(String(fn('adjoint', [adjoint(A)]))).toBe('A');
    expect(String(fn('transpose', [A]))).toBe('transpose(A)');
    expect(String(fn('adjoint', [A]))).toBe('adjoint(A)');
  });
});
