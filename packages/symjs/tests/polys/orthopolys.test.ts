// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/orthopolys.ts: the orthogonal polynomials of a given degree; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, a, b] = sj.symbols('x a b');
const half = sj.Rational.of(1, 2);

describe('orthogonal polynomials as expressions', () => {
  it('in a given variable', () => {
    expect(String(sj.jacobiPoly(2, a, b, x))).toBe(
      'a**2/8 - a*b/4 - a/8 + b**2/8 - b/8 + x**2*(a**2/8 + a*b/4 + 7*a/8 + b**2/8 + 7*b/8 + 3/2) + x*(a**2/4 + 3*a/4 - b**2/4 - 3*b/4) - 1/2',
    );
    expect(String(sj.gegenbauerPoly(3, half, x))).toBe('5*x**3/2 - 3*x/2');
    expect(String(sj.gegenbauerPoly(2, a, x))).toBe('-a + x**2*(2*a**2 + 2*a)');
    expect(String(sj.chebyshevtPoly(4, x))).toBe('8*x**4 - 8*x**2 + 1');
    expect(String(sj.chebyshevtPoly(0, x))).toBe('1');
    expect(String(sj.chebyshevuPoly(3, x))).toBe('8*x**3 - 4*x');
    expect(String(sj.hermitePoly(3, x))).toBe('8*x**3 - 12*x');
    expect(String(sj.hermiteProbPoly(4, x))).toBe('x**4 - 6*x**2 + 3');
    expect(String(sj.legendrePoly(3, x))).toBe('5*x**3/2 - 3*x/2');
    expect(String(sj.laguerrePoly(3, x))).toBe('-x**3/6 + 3*x**2/2 - 3*x + 1');
    expect(String(sj.laguerrePoly(2, x, a))).toBe('a**2/2 + 3*a/2 + x**2/2 + x*(-a - 2) + 1');
  });
  it('in a dummy variable', () => {
    expect(String(sj.jacobiPoly(1, 1, 2))).toBe('5*_x/2 - 1/2');
  });
  it('a negative index', () => {
    expect(() => sj.chebyshevtPoly(-1, x)).toThrow('Cannot generate Chebyshev polynomial of the first kind of index -1');
  });
});

describe('orthogonal polynomials as Poly objects', () => {
  it('Poly in x and PurePoly in a dummy variable', () => {
    expect(String(sj.jacobiPoly(1, 1, 2, x, { polys: true }))).toBe("Poly(5/2*x - 1/2, x, domain='QQ')");
    expect(String(sj.chebyshevtPoly(2, undefined, { polys: true }))).toBe("PurePoly(2*_x**2 - 1, _x, domain='ZZ')");
    expect(String(sj.legendrePoly(2, x, { polys: true }))).toBe("Poly(3/2*x**2 - 1/2, x, domain='QQ')");
    expect(String(sj.laguerrePoly(1, undefined, 0, { polys: true }))).toBe("PurePoly(-_x + 1, _x, domain='QQ')");
    expect(String(sj.hermitePoly(2, undefined, { polys: true }))).toBe("PurePoly(4*_x**2 - 2, _x, domain='ZZ')");
    expect(String(sj.hermiteProbPoly(2, x, { polys: true }))).toBe("Poly(x**2 - 1, x, domain='ZZ')");
    expect(String(sj.chebyshevuPoly(1, x, { polys: true }))).toBe("Poly(2*x, x, domain='ZZ')");
    expect(String(sj.gegenbauerPoly(1, half, x, { polys: true }))).toBe("Poly(x, x, domain='QQ')");
    // SymPy: domain='ZZ(a)'
    expect(String(sj.gegenbauerPoly(1, a, x, { polys: true }).asExpr())).toBe('2*a*x');
  });
});
