// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/parametricregion.ts (SymPy
// sympy/vector/parametricregion.py and
// sympy/vector/tests/test_parametricregion.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Tuple, add, cos, mul, pi, pow, sin, str, symbol } from '../../src';
import type { Expr, Sym } from '../../src';
import { Curve, Ellipse, Line, Parabola, Point, Polygon, Segment } from '../../src/geometry';
import { ImplicitRegion, ParametricRegion, parametricRegionList } from '../../src/vector';

const [a, b, r, t, x, y, z, theta, phi] = ['a', 'b', 'r', 't', 'x', 'y', 'z', 'theta', 'phi'].map((n) => symbol(n)) as [Sym, Sym, Sym, Sym, Sym, Sym, Sym, Sym, Sym];
const lim = (m: Map<Expr, [Expr, Expr]>): string[] => [...m].map(([k, [lo, hi]]) => `${str(k)}: (${str(lo)}, ${str(hi)})`);
const list = (rs: readonly Expr[]): string => `[${rs.map(str).join(', ')}]`;

describe('ParametricRegion (SymPy test_parametricregion)', () => {
  it('constructs regions', () => {
    const point = ParametricRegion([3, 4]);
    expect(point.definition.map(str)).toEqual(['3', '4']);
    expect(point.parameters).toEqual([]);
    expect(point.limits.size).toBe(0);
    expect(point.dimensions).toBe(0);
    const lineXY = ParametricRegion([y, y], [y, 1, 5]);
    expect(lineXY.parameters).toEqual([y]);
    expect(lineXY.dimensions).toBe(1);
    const lineYZ = ParametricRegion([x, t, t], x, [t, 1, 2]);
    expect(lineYZ.parameters).toEqual([x, t]);
    expect(lim(lineYZ.limits)).toEqual(['t: (1, 2)']);
    expect(lineYZ.dimensions).toBe(1);
    const p1 = ParametricRegion([mul(9, a), mul(-16, b)], [a, 0, 2], [b, -1, 5]);
    expect(lim(p1.limits)).toEqual(['a: (0, 2)', 'b: (-1, 5)']);
    expect(p1.dimensions).toBe(2);
    const p2 = ParametricRegion([t, pow(t, 3)], t);
    expect(p2.parameters).toEqual([t]);
    expect(p2.dimensions).toBe(0);
    const circle = ParametricRegion([mul(r, cos(theta)), mul(r, sin(theta))], r, [theta, 0, mul(2, pi)]);
    expect(circle.dimensions).toBe(1);
    const cylinder = ParametricRegion([mul(r, cos(theta)), mul(r, sin(theta)), z], [r, 0, 1], [theta, 0, mul(2, pi)], [z, 0, 4]);
    expect(cylinder.parameters).toEqual([r, theta, z]);
    expect(cylinder.dimensions).toBe(3);
    expect(() => ParametricRegion([mul(a, pow(t, 2)), mul(2, a, t)], [a, -2] as never)).toThrow('Tuple should be in the form (parameter, lowerbound, upperbound)');
    expect(() => ParametricRegion([a, b], [pow(a, 2), sin(b)] as never, [a, 2, 4, 6] as never)).toThrow(RangeError);
    expect(str(ParametricRegion([t, pow(t, 2)], [t, -1, 2]))).toBe('ParametricRegion((t, t**2), (t, -1, 2))');
    expect(str(ParametricRegion([mul(a, cos(t)), mul(b, sin(t))], t))).toBe('ParametricRegion((a*cos(t), b*sin(t)), t)');
    expect(str(ParametricRegion(x))).toBe('ParametricRegion((x,))');
    expect(str(ParametricRegion(Tuple(x, y), Tuple(x, 0, 1)).withArgs([Tuple(y, x), Tuple(y, 1, 2)]))).toBe('ParametricRegion((y, x), (y, 1, 2))');
  });

  it('parametric_region_list', () => {
    expect(list(parametricRegionList(Point(-5, 12)))).toBe('[ParametricRegion((-5, 12))]');
    expect(list(parametricRegionList(Ellipse(Point(2, 8), 2, 6), t))).toBe('[ParametricRegion((2*cos(t) + 2, 6*sin(t) + 8), (t, 0, 2*pi))]');
    expect(list(parametricRegionList(Curve([t, pow(t, 3)], [t, 5, 3])))).toBe('[ParametricRegion((t, t**3), (t, 5, 3))]');
    expect(list(parametricRegionList(Segment(Point(2, 11, -6), Point(0, 2, 5)), t))).toBe('[ParametricRegion((2 - 2*t, 11 - 9*t, 11*t - 6), (t, 0, 1))]');
    expect(list(parametricRegionList(Segment(Point(0, 0), [1, 0]), t))).toBe('[ParametricRegion((t, 0), (t, 0, 1))]');
    expect(list(parametricRegionList(Segment(Point(1, 2, 3), Point(1, 2, 5)), t))).toBe('[ParametricRegion((1, 2, 2*t + 3), (t, 0, 1))]');
    expect(list(parametricRegionList(Segment(Point(12, 56), Point(12, 56))))).toBe('[ParametricRegion((12, 56))]');
    expect(list(parametricRegionList(Polygon([1, 3], [-3, 8], [2, 4]), t))).toBe(
      '[ParametricRegion((1 - 4*t, 5*t + 3), (t, 0, 1)), ParametricRegion((5*t - 3, 8 - 4*t), (t, 0, 1)), ParametricRegion((2 - t, 4 - t), (t, 0, 1))]',
    );
    expect(() => parametricRegionList(Parabola(Point(0, 0), Line(Point(5, 8), Point(7, 8))))).toThrow('SymPy cannot determine parametric representation of the region.');
  });

  it('parametric_region_list of implicit regions', () => {
    expect(list(parametricRegionList(ImplicitRegion([x, y], add(pow(add(x, -2), 2), pow(add(y, -1), 2), -9))))).toBe('[ParametricRegion((3*sin(t) + 2, 1 - 3*cos(t)), (t, 0, 2*pi))]');
    expect(list(parametricRegionList(ImplicitRegion([x, y], add(pow(x, 2), pow(y, 2), -4)), 's'))).toBe('[ParametricRegion((2*sin(s), -2*cos(s)), (s, 0, 2*pi))]');
    expect(list(parametricRegionList(ImplicitRegion([x, y, z], add(pow(x, 2), pow(y, 2), pow(z, 2), -4)), ['u', 'v']))).toBe(
      '[ParametricRegion((-2 + 4/(tan(v/2)**2 + 2/(cos(u) + 1)), 4*tan(v/2)/(tan(v/2)**2 + 2/(cos(u) + 1)), 4*sin(u)/(cos(u)*tan(v/2)**2 + tan(v/2)**2 + 2)), (u, 0, 2*pi), (v, 0, 2*pi))]',
    );
    expect(phi).toBeDefined();
  });
});
