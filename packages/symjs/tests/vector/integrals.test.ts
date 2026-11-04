// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/integrals.ts (SymPy sympy/vector/integrals.py and
// sympy/vector/tests/test_integrals.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Float, Rational, Tuple, add, cos, doit, exp, mul, pi, pow, sin, sqrt, str, symbol } from '../../src';
import type { Expr, Sym } from '../../src';
import { Circle, Curve, Plane, Point, Polygon, Segment, Triangle } from '../../src/geometry';
import { CoordSys3D, ImplicitRegion, ParametricIntegral, ParametricRegion, vectorIntegrate } from '../../src/vector';

const C = CoordSys3D('C');
const [x, y, z, u, v, r, t, theta, phi] = ['x', 'y', 'z', 'u', 'v', 'r', 't', 'theta', 'phi'].map((n) => symbol(n)) as [Sym, Sym, Sym, Sym, Sym, Sym, Sym, Sym, Sym];
const sq = (e: Expr): Expr => pow(e, 2);

describe('ParametricIntegral (SymPy test_integrals)', () => {
  it('line integrals', () => {
    const halfcircle = ParametricRegion([mul(4, cos(theta)), mul(4, sin(theta))], [theta, mul(-1, pi, Rational.of(1, 2)), mul(pi, Rational.of(1, 2))]);
    expect(str(ParametricIntegral(mul(C.x, pow(C.y, 4)), halfcircle))).toBe('8192/5');
    const curve = ParametricRegion([t, sq(t), pow(t, 3)], [t, 0, 1]);
    const field1 = add(mul(8, sq(C.x), C.y, C.z, C.i), mul(5, C.z, C.j), mul(-4, C.x, C.y, C.k));
    expect(str(ParametricIntegral(field1, curve))).toBe('1');
    const line = ParametricRegion([add(mul(4, t), -1), add(2, mul(-2, t)), t], [t, 0, 1]);
    expect(str(ParametricIntegral(add(mul(C.x, C.z, C.i), mul(-1, C.y, C.z, C.k)), line))).toBe('3');
    expect(str(ParametricIntegral(mul(4, pow(C.x, 3)), ParametricRegion([1, t], [t, 0, 2])))).toBe('8');
    const helix = ParametricRegion([cos(t), sin(t), mul(3, t)], [t, 0, mul(4, pi)]);
    expect(str(ParametricIntegral(mul(C.x, C.y, C.z), helix))).toBe('-3*sqrt(10)*pi');
    const field2 = add(mul(C.y, C.i), mul(C.z, C.j), mul(C.z, C.k));
    expect(str(ParametricIntegral(field2, ParametricRegion([cos(t), sin(t), sq(t)], [t, 0, pi])))).toBe('-5*pi/2 + pi**4/2');
  });

  it('surface integrals', () => {
    const semisphere = ParametricRegion([mul(2, sin(phi), cos(theta)), mul(2, sin(phi), sin(theta)), mul(2, cos(phi))], [theta, 0, mul(2, pi)], [phi, 0, mul(pi, Rational.of(1, 2))]);
    expect(str(ParametricIntegral(C.z, semisphere))).toBe('8*pi');
    const cylinder = ParametricRegion([mul(sqrt(3), cos(theta)), mul(sqrt(3), sin(theta)), z], [z, 0, 6], [theta, 0, mul(2, pi)]);
    expect(str(ParametricIntegral(C.y, cylinder))).toBe('0');
    const cone = ParametricRegion([mul(v, cos(u)), mul(v, sin(u)), v], [u, 0, mul(2, pi)], [v, 0, 1]);
    expect(str(ParametricIntegral(add(mul(C.x, C.i), mul(C.y, C.j), mul(pow(C.z, 4), C.k)), cone))).toBe('pi/3');
    const triangle1 = ParametricRegion([x, y], [x, 0, 2], [y, 0, add(10, mul(-5, x))]);
    const triangle2 = ParametricRegion([x, y], [y, 0, add(10, mul(-5, x))], [x, 0, 2]);
    const f = mul(new Float(-15.6), C.y, C.k);
    expect(ParametricIntegral(f, triangle1).key).toBe(ParametricIntegral(f, triangle2).key);
    expect(str(ParametricIntegral(C.z, triangle1))).toBe('10*C.z');
  });

  it('volume integrals', () => {
    expect(str(ParametricIntegral(1, ParametricRegion([x, y, z], [x, 0, 1], [y, 0, 1], [z, 0, 1])))).toBe('1');
    const def = [mul(r, sin(phi), cos(theta)), mul(r, sin(phi), sin(theta)), mul(r, cos(phi))];
    const s1 = ParametricRegion(def, [r, 0, 2], [theta, 0, mul(2, pi)], [phi, 0, pi]);
    const s2 = ParametricRegion(def, [r, 0, 2], [phi, 0, pi], [theta, 0, mul(2, pi)]);
    expect(str(ParametricIntegral(add(sq(C.x), sq(C.y)), s1))).toBe('-256*pi/15');
    expect(str(ParametricIntegral(add(sq(C.x), sq(C.y)), s2))).toBe('256*pi/15');
    const p1 = ParametricRegion([x, y, z], [x, 0, 3], [y, 0, add(mul(-2, x, Rational.of(1, 3)), 2)], [z, 0, add(6, mul(-2, x), mul(-3, y))]);
    const p2 = ParametricRegion([x, y, z], [x, 0, 3], [z, 0, add(6, mul(-2, x), mul(-3, y))], [y, 0, add(mul(-2, x, Rational.of(1, 3)), 2)]);
    const g = add(mul(C.x, C.i), C.j, mul(-100, C.k));
    expect(ParametricIntegral(g, p1).key).toBe(ParametricIntegral(g, p2).key);
    expect(str(ParametricIntegral(mul(2, C.x), p2))).toBe('-9');
  });

  it('keeps the integrals it cannot compute', () => {
    const region = ParametricRegion([t, exp(sq(t))], [t, 0, 1]);
    const pi0 = ParametricIntegral(C.x, region);
    expect(str(pi0)).toBe('ParametricIntegral(C.x, ParametricRegion((t, exp(t**2)), (t, 0, 1)))');
    const node = pi0 as InstanceType<typeof ParametricIntegral>;
    expect(node.field).toBe(C.x);
    expect(node.parametricregion.key).toBe(region.key);
    expect(node.withArgs(node.args).key).toBe(pi0.key);
    expect(() => node.withArgs([C.x, C.x])).toThrow('ParametricRegion');
    expect(() => ParametricIntegral(add(C.x, CoordSys3D('D').x), region)).toThrow('several coordinate systems');
    expect(str(ParametricIntegral(add(C.j, C.k), ParametricRegion([mul(r, cos(theta)), mul(r, sin(theta))], r, theta)))).toBe('0');
  });
});

describe('vector_integrate (SymPy test_integrals)', () => {
  it('integrates over regions and variables', () => {
    const halfdisc = ParametricRegion([mul(r, cos(theta)), mul(r, sin(theta))], [r, -2, 2], [theta, 0, pi]);
    expect(str(vectorIntegrate(sq(C.x), halfdisc))).toBe('4*pi');
    expect(str(vectorIntegrate(C.x, ParametricRegion([t, sq(t)], [t, 2, 3])))).toBe('-17*sqrt(17)/12 + 37*sqrt(37)/12');
    expect(str(vectorIntegrate(mul(pow(C.y, 3), C.z), [C.x, 0, 3], [C.y, -1, 4]))).toBe('765*C.z/4');
    expect(str(vectorIntegrate(mul(-15, C.y), Segment(Point(0, 0), Point(0, 1))))).toBe('-15/2');
    expect(str(vectorIntegrate(mul(C.y, C.i), Segment(Point(4, 3, 9), Point(1, 1, 7))))).toBe('-6');
    expect(str(vectorIntegrate(mul(5, C.z), Curve([sin(t), cos(t)], [t, 0, 2])))).toBe('10*C.z');
    expect(str(vectorIntegrate(mul(C.x, C.y), Circle(Point(2, 3), 6)))).toBe('72*pi');
    const c2 = Circle(Point(0, 0), Point(1, 1), Point(1, 0)) as InstanceType<typeof Circle>;
    expect(vectorIntegrate(1, c2).key).toBe(c2.circumference.key);
    expect(str(vectorIntegrate(add(mul(C.x, C.i), mul(-14, C.y, C.j)), Polygon([0, 0], [1, 0], [1, 1])))).toBe('0');
    expect(str(vectorIntegrate(mul(-23, C.z), Polygon([0, 0], [1, 0], [5, 1], [0, 1])))).toBe('-161*C.z - 23*sqrt(17)*C.z');
    expect(str(vectorIntegrate(mul(C.i, C.y), Point(2, 3)))).toBe('0');
    expect(str(vectorIntegrate(45, ImplicitRegion([x, y], add(sq(x), sq(y), -4))))).toBe('180*pi');
    expect(str(vectorIntegrate(1, ImplicitRegion([x, y], add(sq(add(x, -3)), sq(add(y, -4)), -9))))).toBe('6*pi');
    expect(() => vectorIntegrate(add(mul(C.x, C.z, C.i), C.k), Plane(Point(1, 1, 1), Point(2, 3, 4), Point(2, 2, 2)))).toThrow(RangeError);
    expect(str(vectorIntegrate(mul(3, sq(C.x), C.y, C.i).add(C.j), Triangle(Point(-2, 3), Point(2, 3), Point(0, 5))))).toBe('-8');
  });

  it('integrates with respect to base scalars', () => {
    expect(str(vectorIntegrate(mul(12, pow(C.y, 3)), [C.y, 1, 3]))).toBe('240');
    expect(str(vectorIntegrate(mul(12, pow(C.y, 3)), Tuple(C.y, 1, 3)))).toBe('240');
    expect(str(vectorIntegrate(mul(sq(C.x), C.z), C.x))).toBe('C.x**3*C.z/3');
    const w = vectorIntegrate(add(mul(C.x, C.i), mul(-1, C.y, C.k)), C.x);
    expect(str(w)).toBe('(Integral(C.x, C.x))*C.i + (Integral(-C.y, C.x))*C.k');
    expect(str(doit(w))).toBe('C.x**2/2*C.i + (-C.x*C.y)*C.k');
    expect(() => vectorIntegrate(C.x, [C.x, 1] as never)).toThrow('is not a variable with limits');
    expect(() => vectorIntegrate(C.x, add(C.x, 1))).toThrow('is not a variable with limits');
  });
});
