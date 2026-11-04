// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/implicitregion.ts (SymPy sympy/vector/implicitregion.py
// and sympy/vector/tests/test_implicitregion.py). Expected values are those
// of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Float, Rational, S, Tuple, add, mul, pow, sin, str, symbol } from '../../src';
import type { Expr } from '../../src';
import { Point } from '../../src/geometry';
import { ImplicitRegion } from '../../src/vector';
import { conicCoeff, totalDegree } from '../../src/vector/implicitregion';

const [x, y, z, s, t] = ['x', 'y', 'z', 's', 't'].map((n) => symbol(n)) as [ReturnType<typeof symbol>, ReturnType<typeof symbol>, ReturnType<typeof symbol>, ReturnType<typeof symbol>, ReturnType<typeof symbol>];
const tuple = (xs: readonly Expr[]): string => `(${xs.map(str).join(', ')})`;
const sq = (e: Expr): Expr => pow(e, 2);

describe('ImplicitRegion (SymPy test_implicitregion)', () => {
  it('constructs regions', () => {
    const ellipse = ImplicitRegion([x, y], add(mul(sq(x), Rational.of(1, 4)), mul(sq(y), Rational.of(1, 16)), -1));
    expect(str(ellipse.equation)).toBe('x**2/4 + y**2/16 - 1');
    expect(ellipse.variables).toEqual([x, y]);
    expect(ellipse.degree).toBe(2);
    const r = ImplicitRegion([x, y, z], Eq(add(pow(x, 4), sq(y), mul(-1, x, y)), 6));
    expect(str(r.equation)).toBe('x**4 - x*y + y**2 - 6');
    expect(r.degree).toBe(4);
    expect(str(ImplicitRegion([x, y], add(sq(x), sq(y), -4)))).toBe('ImplicitRegion((x, y), x**2 + y**2 - 4)');
    expect(str(ImplicitRegion([x, y], Eq(mul(y, x), 1)))).toBe('ImplicitRegion((x, y), x*y - 1)');
    expect(() => ImplicitRegion([S.One], x).variables).toThrow('variable');
    expect(totalDegree(S.One)).toBe(0);
    expect(() => conicCoeff([x, y], pow(x, 3))).toThrow(RangeError);
  });

  it('regular_point', () => {
    expect(tuple(ImplicitRegion([x], add(sq(x), -16)).regularPoint())).toBe('(-4)');
    expect(tuple(ImplicitRegion([x, y], add(sq(x), sq(y), -4)).regularPoint())).toBe('(0, -2)');
    expect(tuple(ImplicitRegion([x, y], add(sq(add(x, Rational.of(-5, 2))), sq(y), Rational.of(-1, 16))).regularPoint())).toBe('(5/2, -1/4)');
    expect(tuple(ImplicitRegion([x, y], add(sq(add(y, -5)), mul(-16, add(x, -5)))).regularPoint())).toBe('(5, 5)');
    expect(tuple(ImplicitRegion([x, y], add(sq(x), mul(-4, x, y), mul(-3, sq(y)), mul(4, x), mul(8, y), -5)).regularPoint())).toBe('(4/7, 9/7)');
    expect(() => ImplicitRegion([x, y], add(sq(x), mul(-2, x, y), mul(3, sq(y)), mul(-2, x), mul(-5, y), new Float(1.5))).regularPoint()).toThrow('Rational Point on the conic does not exist');
    expect(tuple(ImplicitRegion([x, y], add(mul(x, y), -1)).regularPoint())).toBe('(-1, -1)');
    expect(tuple(ImplicitRegion([x, y], add(mul(x, y), x, -3)).regularPoint())).toBe('(-3, -2)');
    expect(tuple(ImplicitRegion([x, y], add(sq(x), mul(-4, x, y), mul(4, sq(y)), x, y)).regularPoint())).toBe('(-1/3, 1/12)');
    expect(tuple(ImplicitRegion([x, y], add(sq(y), x)).regularPoint())).toBe('(0, 0)');
    for (const e of [add(sq(x), mul(3, x), -5), add(sq(x), sq(y), 1), add(sq(y), 1)]) {
      expect(() => ImplicitRegion([x, y], e).regularPoint()).toThrow('Rational Point on the conic does not exist');
    }
    expect(() => ImplicitRegion([x, y], add(pow(x, 3), pow(y, 3), -1)).regularPoint()).toThrow('no regular point');
    // SymPy raises TypeError (list[self.singular_points()][0]); the singular point (0, 0) is on the region
    expect(tuple(ImplicitRegion([x, y], add(pow(x, 3), mul(-1, sq(y)))).regularPoint())).toBe('(0, 0)');
    const r = ImplicitRegion([x, y, z], Eq(z, add(sq(x), sq(y))));
    expect(tuple(r.regularPoint())).toBe('(-10, -10, 200)');
    expect(tuple(ImplicitRegion([x, y, z], pow(add(x, y, z), 4)).regularPoint())).toBe('(-10, -10, 20)');
    expect(tuple(ImplicitRegion([x, y], add(sq(add(x, 2)), sq(add(y, -3)), -16)).regularPoint())).toBe('(-2, -1)');
    expect(tuple(ImplicitRegion([x, y], add(sq(x), mul(-4, y))).regularPoint())).toBe('(0, 0)');
  });

  it('singular_points and multiplicity', () => {
    const r1 = ImplicitRegion([x, y, z], Eq(add(x, y, z), 0));
    expect(str(r1.singularPoints())).toBe('EmptySet');
    const r2 = ImplicitRegion([x, y, z], add(mul(x, y, z), pow(y, 4), mul(-1, sq(x), sq(z))));
    expect(str(r2.singularPoints())).toBe('{(0, 0, z), (x, 0, 0)}');
    expect(r2.multiplicity([0, 0, 0])).toBe(3);
    expect(r2.multiplicity([0, 0, 6])).toBe(2);
    const r3 = ImplicitRegion([x, y, z], add(sq(z), mul(-1, sq(x)), mul(-1, sq(y))));
    expect(str(r3.singularPoints())).toBe('{(0, 0, 0)}');
    expect(r3.multiplicity(Tuple(0, 0, 0))).toBe(2);
    const r4 = ImplicitRegion([x, y], add(sq(x), sq(y), mul(-2, x)));
    expect(str(r4.singularPoints())).toBe('EmptySet');
    expect(r4.multiplicity(Point(1, 3))).toBe(0);
    expect(str(ImplicitRegion([x, y], add(sq(add(y, -1)), mul(-1, pow(x, 3)), mul(2, sq(x)), mul(-1, x))).singularPoints())).toBe('{(1, 1)}');
    // SymPy: 1 (it takes the factors of the single term x*y as terms); (0, 0) is a double point of x*y = 0
    expect(ImplicitRegion([x, y], mul(x, y)).multiplicity([0, 0])).toBe(2);
  });

  it('rational_parametrization', () => {
    expect(tuple(ImplicitRegion([x], add(x, -2)).rationalParametrization())).toBe('(x - 2)');
    expect(tuple(ImplicitRegion([x, y], Eq(y, add(mul(3, x), 2))).rationalParametrization())).toBe('(x, 3*x + 2)');
    expect(tuple(ImplicitRegion([x, y], add(sq(add(x, -2)), sq(add(y, 3)), -4)).rationalParametrization(t))).toBe('(4*t/(t**2 + 1) + 2, 4*t**2/(t**2 + 1) - 5)');
    expect(tuple(ImplicitRegion([x, y], add(sq(add(x, S.Half.neg())), sq(y), Rational.of(-1, 4))).rationalParametrization(t))).toBe('(t/(t**2 + 1) + 1/2, t**2/(t**2 + 1) - 1/2)');
    expect(tuple(ImplicitRegion([x, y], Eq(add(sq(x), sq(y)), mul(2, x))).rationalParametrization([t]))).toBe('(2*t/(t**2 + 1) + 1, 2*t**2/(t**2 + 1) - 1)');
  });

  it('rational_parametrization of curves with a double point and quadrics', () => {
    expect(tuple(ImplicitRegion([x, y], add(sq(add(y, -3)), mul(-4, add(x, 6)))).rationalParametrization(t))).toBe('(-6 + 4/t**2, 3 + 4/t)');
    expect(tuple(ImplicitRegion([x, y], add(mul(x, y), -1)).rationalParametrization(t))).toBe('(-1 + (t + 1)/t, t)');
    expect(tuple(ImplicitRegion([x, y], add(pow(x, 3), sq(x), mul(-1, sq(y)))).rationalParametrization(t))).toBe('(t**2 - 1, t*(t**2 - 1))');
    expect(tuple(ImplicitRegion([x, y], add(pow(x, 3), mul(-1, sq(y)))).rationalParametrization(t))).toBe('(t**2, t**3)');
    expect(tuple(ImplicitRegion([x, y, z], Eq(add(sq(x), sq(y), sq(z)), mul(2, x))).rationalParametrization([s, t]))).toBe('(2/(s**2 + t**2 + 1), 2*t/(s**2 + t**2 + 1), 2*s/(s**2 + t**2 + 1))');
    expect(tuple(ImplicitRegion([x, y], Eq(add(sq(x), mul(4, x, y), mul(3, sq(y)), x, mul(-1, y), 10), 0)).rationalParametrization(t))).toBe('(17/2 + 4/(3*t**2 + 4*t + 1), 4*t/(3*t**2 + 4*t + 1) - 11/2)');
    expect(tuple(ImplicitRegion([x, y], add(sq(x), sq(y), -4)).rationalParametrization('s'))).toBe('(4*s/(s**2 + 1), 4*s**2/(s**2 + 1) - 2)');
    expect(tuple(ImplicitRegion([x, y, z], add(sq(x), sq(y), sq(z), -4)).rationalParametrization(['r', 's']))).toBe('(-2 + 4/(r**2 + s**2 + 1), 4*s/(r**2 + s**2 + 1), 4*r/(r**2 + s**2 + 1))');
    expect(() => ImplicitRegion([x, y], add(sq(y), mul(-1, pow(x, 3)), x)).rationalParametrization()).toThrow('the region is not a monoid');
    expect(() => ImplicitRegion([x, y], add(sq(y), mul(-1, pow(x, 3)), mul(-1, sq(x)), 1)).rationalParametrization()).toThrow('the region is not a monoid');
    expect(() => ImplicitRegion([x, y, z], add(x, y, z)).rationalParametrization()).toThrow('linear region in 3 variables');
    expect(() => ImplicitRegion([x, y, z, s], add(sq(x), sq(y), sq(z), sq(s), -1)).rationalParametrization()).toThrow();
  });

  it('more points and parametrizations', () => {
    expect(tuple(ImplicitRegion([x, y], add(sq(x), mul(x, y), -3)).regularPoint())).toBe('(3, -2)');
    expect(tuple(ImplicitRegion([x, y], add(sq(x), mul(3, x, y), mul(-1, y), 2)).regularPoint())).toBe('(-6, 2)');
    expect(() => ImplicitRegion([x, y], add(sq(add(x, y)), x, y, 1)).regularPoint()).toThrow('Rational Point on the conic does not exist');
    // SymPy loops over the solutions of sin(x) = 0; symjs needs a finite set
    expect(() => ImplicitRegion([x], sin(x)).regularPoint()).toThrow('are not a finite set');
    // SymPy: TypeError (cannot determine truth value of Relational: 16*a < 0)
    expect(() => ImplicitRegion([x, y], add(sq(x), sq(y), mul(-1, symbol('a')))).regularPoint()).toThrow('16*a is not a number');
    // SymPy crashes (AttributeError) on these degenerate conics through their double point
    expect(tuple(ImplicitRegion([x, y], add(sq(x), mul(-1, sq(y)))).rationalParametrization())).toBe('(0, 0)');
    expect(tuple(ImplicitRegion([x, y], mul(x, y)).rationalParametrization())).toBe('(0, 0)');
    expect(() => ImplicitRegion([x, y, z], add(mul(x, y, z), pow(y, 4), mul(-1, sq(x), sq(z)))).rationalParametrization()).toThrow('the region is not a monoid');
    expect(() => ImplicitRegion([x, y, z, s], add(sq(x), sq(y), -1)).rationalParametrization(undefined, { regPoint: [1, 0, 0, 0] })).toThrow('rational parametrization in more than 3 variables');
    expect(tuple(ImplicitRegion([x, y], add(sq(add(x, -0.5)), sq(y), -0.0625)).rationalParametrization(undefined, { regPoint: [0.75, 0] }))).toBe('(0.75 - 0.5/(t**2 + 1), -0.5*t/(t**2 + 1))');
    expect(tuple(ImplicitRegion([x, y], add(pow(y, 2), mul(-4, x))).rationalParametrization())).toBe('(4/t**2, 4/t)');
    expect(str(ImplicitRegion([x, y], x).withArgs([Tuple(y), y]))).toBe('ImplicitRegion((y,), y)');
  });
});
