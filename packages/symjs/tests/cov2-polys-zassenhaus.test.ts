// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Factorization over ZZ (Berlekamp-Zassenhaus) and over GF(p)
 * (polys/zassenhaus through factor); expected values from SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const { parse } = sj;
// the product of the odd primes up to 113: x**2 - N is square-free modulo none of them
const N = '15805027320208803894072603145771831246637343495';

describe('factor over ZZ', () => {
  it.each([
    ['x**4+1', 'x**4 + 1'],
    ['x**4-10*x**2+1', 'x**4 - 10*x**2 + 1'],
    ['(x**2+1)*(x**2+2)', '(x**2 + 1)*(x**2 + 2)'],
    ['x**8-40*x**6+352*x**4-960*x**2+576', 'x**8 - 40*x**6 + 352*x**4 - 960*x**2 + 576'],
    ['(x**2+x+1)*(x**3+2)*(2*x**2-3)', '(2*x**2 - 3)*(x**3 + 2)*(x**2 + x + 1)'],
    ['(x**4+1)*(x**4+2)', '(x**4 + 1)*(x**4 + 2)'],
    ['6*x**4+5*x**3+x**2+30', '6*x**4 + 5*x**3 + x**2 + 30'],
    ['x**6+x**3+1', 'x**6 + x**3 + 1'],
    ['(x**3-3)*(x**3-5)*(x**3-7)', '(x**3 - 7)*(x**3 - 5)*(x**3 - 3)'],
    ['2*x**2+2*x+2', '2*(x**2 + x + 1)'],
    [`x**2-${N}`, `x**2 - ${N}`],
    [`${N}*x**2-1`, `${N}*x**2 - 1`],
  ])('factor(%s)', (f, expected) => {
    expect(String(sj.factor(parse(f)))).toBe(expected);
  });
});

describe('factor modulo a prime', () => {
  it.each([
    ['x**4+x+1', 2, 'x**4 + x + 1'],
    ['x**6+x**5+x**3+x**2+x+1', 2, '(x + 1)*(x**5 + x**2 + 1)'],
    // SymPy prints 2*x**4, but 2*x**4 + 4 is zero modulo 2
    ['2*x**4+4', 2, '0'],
    ['x*(x+1)**3', 5, 'x*(x + 1)**3'],
    ['x**8+x**4+1', 2, '(x**2 + x + 1)**4'],
    ['x**9 + x**3 + 1', 3, '(x - 1)**3*(x**2 + x - 1)**3'],
    ['(x**3+x+1)*(x**3+x**2+1)', 2, '(x**3 + x + 1)*(x**3 + x**2 + 1)'],
    ['3*x + 1', 3, '1'],
    ['x**2 + 3*x + 2', 5, '(x + 1)*(x + 2)'],
    ['x*(x+1)**2', 2, 'x*(x + 1)**2'],
    ['(x**4+x+1)*(x**4+x**3+1)*(x**4+x**3+x**2+x+1)', 2, '(x**4 + x + 1)*(x**4 + x**3 + 1)*(x**4 + x**3 + x**2 + x + 1)'],
  ])('factor(%s, modulus=%d)', (f, p, expected) => {
    expect(String(sj.factor(parse(f), { modulus: p }))).toBe(expected);
  });
  it('a composite modulus', () => {
    // SymPy: NotInvertible: zero divisor
    expect(() => sj.factor(parse('x**2 + 3*x + 2'), { modulus: 4 })).toThrow();
  });
});

describe('deprecated factorPoly', () => {
  it('a single factor', () => {
    const x = new sj.Sym('x');
    expect(String(sj.factorPoly(parse('(x + 1)**2'), x))).toBe('(x + 1)**2');
    expect(String(sj.factorPoly(parse('x**2 - 1'), x))).toBe('(x - 1)*(x + 1)');
  });
});
