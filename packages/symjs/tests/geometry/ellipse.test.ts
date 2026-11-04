// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/ellipse.ts (SymPy sympy/geometry/ellipse.py and
// sympy/geometry/tests/test_ellipse.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Expr, Rational, S, Sym, parse, pi, sqrt, symbols } from '../../src';
import { Circle, Ellipse, GeometryError, Line, Plane, Point, Point3D, Polygon, Ray, RegularPolygon, Segment, Triangle, intersection } from '../../src/geometry';

const planeLike = (): GeometryEntity => Plane([0, 0, 0], { normalVector: [0, 0, 1] });
import type { CircleNode, EllipseNode, GeometryEntity, Line2DNode } from '../../src/geometry';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : e instanceof Map ? `{${[...e].map(([k, v]) => `${s(k)}: ${s(v)}`).join(', ')}}` : String(e));
const real = (n: string): Sym => new Sym(n, { real: true });
const half = S.Half;
const R = (p: bigint, q = 1n): Expr => Rational.of(p, q);
const E = (...a: unknown[]): EllipseNode => (Ellipse as unknown as (...b: unknown[]) => EllipseNode)(...a);
const C = (...a: unknown[]): CircleNode => (Circle as unknown as (...b: unknown[]) => CircleNode)(...a);

describe('construction', () => {
  it('ellipses and circles from equations (SymPy test_object_from_equation)', () => {
    const p = parse;
    expect(s(Circle(p('x**2 + y**2 + 3*x + 4*y - 8')))).toBe('Circle(Point2D(-3/2, -2), sqrt(57)/2)');
    expect(s(Circle(p('x**2 + y**2 + 6*x + 8*y + 25')))).toBe('Point2D(-3, -4)');
    expect(s(Circle(p('a**2 + b**2 + 6*a + 8*b + 25'), { x: 'a', y: 'b' }))).toBe('Point2D(-3, -4)');
    expect(s(Circle(p('x**2 + y**2 - 25')))).toBe('Circle(Point2D(0, 0), 5)');
    expect(s(Circle(p('x**2 + y**2 + 6*x + 8')))).toBe('Circle(Point2D(-3, 0), 1)');
    expect(s(Circle(p('(x - 1)**2 + y**2 - 9')))).toBe('Circle(Point2D(1, 0), 3)');
    expect(s(Circle(p('6*(x**2) + 6*(y**2) + 6*x + 8*y - 25')))).toBe('Circle(Point2D(-1/2, -2/3), 5*sqrt(7)/6)');
    expect(s(Circle(Eq(p('a**2 + b**2'), 25), { x: 'a', y: new Sym('b') }))).toBe('Circle(Point2D(0, 0), 5)');
    expect(() => Circle(p('x**2 + y**2 + 3*x + 4*y + 26'))).toThrow(GeometryError);
    expect(() => Circle(p('x**2 + y**2 + 25'))).toThrow(GeometryError);
    expect(() => Circle(p('x**2 + 6*y + 8'))).toThrow(GeometryError);
    expect(() => Circle(p('6*(x ** 2) + 4*(y**2) + 6*x + 8*y + 25'))).toThrow(GeometryError);
    expect(() => Circle(p('x**3 + y**2'))).toThrow(GeometryError);
    expect(() => Circle(p('x*y + x**2 + y**2'))).toThrow(GeometryError);
    expect(() => Circle(p('sin(x) + y**2'))).toThrow(GeometryError);
    expect(() => Circle(p('a**2 + b**2 + 3*a + 4*b - 8'))).toThrow(RangeError);
    const [x, y] = symbols('x y', { real: true }) as [Sym, Sym];
    expect(s(Circle(p('a*x**2 + a*y**2 + c*x + d*y + e').subs(new Sym('x'), x).subs(new Sym('y'), y)).toString())).toContain('Circle(Point2D(-c/(2*a), -d/(2*a))');
  });

  it('three points, radii, eccentricities and degenerate cases', () => {
    expect(s(Circle(Point(0, 0), Point(3, 0), Point(0, 4)))).toBe(s(Circle(Point(R(3n, 2n), 2), R(5n, 2n))));
    expect(s(Circle(Point(0, 0), Point(1, 1), Point(2, 2)))).toBe('Segment2D(Point2D(0, 0), Point2D(2, 2))');
    expect(() => Ellipse(undefined, undefined, undefined, 1)).toThrow(RangeError);
    expect(() => Ellipse()).toThrow(RangeError);
    expect(() => Circle(Point(0, 0))).toThrow(GeometryError);
    expect(() => Circle(parse('x*y'))).toThrow(RangeError);
    expect(() => Circle([0, 0], parse('I'))).toThrow('Circle with imaginary radius is not permitted');
    expect(() => Ellipse([0, 0, 0], 1, 2)).toThrow('The center of "Ellipse" must be a two dimensional point');
    expect(s(E(undefined, 1, 1).center)).toBe('Point2D(0, 0)');
    expect(s(Ellipse([1, 1], 0, 0))).toBe('Point2D(1, 1)');
    expect(s(Ellipse([1, 1], 1, 0))).toBe('Segment2D(Point2D(0, 1), Point2D(2, 1))');
    expect(s(Ellipse([1, 1], 0, 1))).toBe('Segment2D(Point2D(1, 0), Point2D(1, 2))');
    expect(s(E({ hradius: 2, vradius: 1 }).eccentricity)).toBe('sqrt(3)/2');
    expect(s(E({ hradius: 2, eccentricity: sqrt(3).div(2) }).vradius)).toBe('1');
    expect(s(E({ vradius: 1, eccentricity: sqrt(3).div(2) }).hradius)).toBe('2');
    expect(s(E(Point(0, 0), { hradius: 1, eccentricity: 0 }).vradius)).toBe('1');
    expect(() => Ellipse(Point(3, 1), { hradius: 3, eccentricity: R(3n, 2n) })).toThrow(GeometryError);
    expect(() => Ellipse(Point(3, 1), { hradius: 3, eccentricity: pi.sub(2) })).toThrow(GeometryError);
    expect(s((Ellipse(undefined, 1, undefined, 1) as GeometryEntity & { length: Expr }).length)).toBe('2');
    expect(() => Ellipse(undefined, undefined, 1, 1)).toThrow(GeometryError);
    expect(() => Ellipse(Point(3, 1), { hradius: 3, eccentricity: -3 })).toThrow('Eccentricity of ellipse/circle should lie between [0, 1)');
    expect(() => Ellipse([0, 0], parse('I + 1'), 2)).toThrow('Invalid value encountered when computing hradius / vradius.');
    expect(s(Circle([1, 2], 0))).toBe('Point2D(1, 2)');
    expect(s(Circle([0, 1], 2))).toBe('Circle(Point2D(0, 1), 2)');
    // SymPy test_issue_15797_equals: Floats become Rationals unless evaluate=False
    const c = C([0.0864931002830291, 0.0819863295239654], 0.024127189424130748);
    expect(c.center.x instanceof Rational && c.radius instanceof Rational).toBe(true);
    const u = C([0.0864931002830291, 0.0819863295239654], 0.024127189424130748, { evaluate: false });
    expect(s(u.radius)).toBe('0.0241271894241307');
    expect(s(Circle([0, 0], 1).subs(S.One, 2))).toBe('Circle(Point2D(0, 0), 2)');
    expect(s(Ellipse([0, 0], 1, 2).subs(S.One, 3))).toBe('Ellipse(Point2D(0, 0), 3, 2)');
    expect(s(C([pi, pi], pi).n(2))).toBe('Circle(Point2D(3.1, 3.1), 3.1)');
    expect(s(E([pi, pi], pi, pi.neg()).n(2))).toBe('Ellipse(Point2D(3.1, 3.1), 3.1, -3.1)');
  });
});

describe('Ellipse (SymPy test_ellipse_geom)', () => {
  const y1 = real('y1');
  const t = real('t');
  const p1 = Point(0, 0);
  const p2 = Point(1, 1);
  const p4 = Point(0, 1);
  const e1 = E(p1, 1, 1);
  const e2 = E(p2, half, 1);
  const e3 = E(p1, y1, y1);
  const c1 = C(p1, 1);
  const c2 = C(p2, 1);
  const c3 = C(Point(sqrt(2), sqrt(2)), 1);

  it('basic properties', () => {
    expect(e1.equals(c1)).toBe(true);
    expect(e1.equals(e2)).toBe(false);
    expect(e1.contains(p4)).toBe(true);
    expect(e1.contains(e1)).toBe(true);
    expect(e2.contains(1)).toBe(false);
    expect(e2.contains(p2)).toBe(false);
    expect(s(e1.area)).toBe('pi');
    expect(s(e2.area)).toBe('pi/2');
    expect(s(e3.area)).toBe('pi*y1*Abs(y1)');
    expect(s(c1.circumference)).toBe(s(e1.circumference));
    expect(s(e3.circumference)).toBe('2*pi*y1');
    expect(s(e1.plotInterval())).toBe(s([t, pi.neg(), pi]));
    expect(s(e2.plotInterval('x'))).toBe('[x, -pi, pi]');
    expect([c1.minor, c1.major, c1.hradius, c1.vradius].map(s)).toEqual(['1', '1', '1', '1']);
    expect(e1.ambientDimension).toBe(2);
    expect(c1.key).toBe(C(Point(1, 0), Point(0, 1), Point(0, -1)).key);
    expect(e1.contains(Line(p1, p2))).toBe(false);
    expect(s(E(Point(0, 0), 4, 2).foci)).toBe('[Point2D(-2*sqrt(3), 0), Point2D(2*sqrt(3), 0)]');
    expect(s(E(Point(0, 0), 2, 4).foci)).toBe('[Point2D(0, -2*sqrt(3)), Point2D(0, 2*sqrt(3))]');
    expect(s(c1.foci)).toBe('[Point2D(0, 0), Point2D(0, 0)]');
    const [a, b] = symbols('a b') as [Sym, Sym];
    expect(s(E(Point(0, 0), a, b).major)).toBe('a');
    expect(s(E(Point(0, 0), a, b).minor)).toBe('b');
    expect(s(E(Point(0, 0), a.add(b), b.mul(2)).foci)).toBe('[Point2D(-sqrt(-4*b**2 + (a + b)**2), 0), Point2D(sqrt(-4*b**2 + (a + b)**2), 0)]');
    expect(s(E(Point(0, 0), 5, 4).circumference)).toBe('20*elliptic_e(9/25)');
    expect(s(E(undefined, 1, undefined, 0).circumference)).toBe('2*pi');
    expect(s(E(Point(0, 0), new Sym('M'), new Sym('m')).circumference)).toBe('4*M*elliptic_e((M**2 - m**2)/M**2)');
    expect(Math.abs(E(undefined, { hradius: 5, vradius: 3 }).circumference.evalf(16).toNumber() - 25.52699886339813)).toBeLessThan(1e-10);
    expect(s(E(Point(0, 0), 3, 5).bounds)).toBe('[-3, -5, 3, 5]');
    expect(s(C(Point(-2, 0), Point(0, 2), Point(2, 0)).bounds)).toBe('[-2, -2, 2, 2]');
  });

  it('properties of the orbit (focus distance, eccentricity, apsides)', () => {
    for (const e4 of [E(p2, 1, 3), E(p2, 3, 1)]) {
      expect(s(e4.focusDistance)).toBe('2*sqrt(2)');
      expect(s(e4.eccentricity)).toBe('2*sqrt(2)/3');
      expect(s(e4.periapsis)).toBe('3 - 2*sqrt(2)');
      expect(s(e4.apoapsis)).toBe('2*sqrt(2) + 3');
      expect(s(e4.semilatusRectum)).toBe('1/3');
    }
  });

  it('encloses', () => {
    expect(e1.encloses(Segment(Point(-0.5, -0.5), Point(0.5, 0.5)))).toBe(true);
    expect(e1.encloses(Line(p1, p2))).toBe(false);
    expect(e1.encloses(e1)).toBe(false);
    expect(e1.encloses(Polygon(Point(-0.5, -0.5), Point(-0.5, 0.5), Point(0.5, 0.5)))).toBe(true);
    expect(e1.encloses(RegularPolygon(p1, 0.5, 3))).toBe(true);
    expect(e1.encloses(RegularPolygon(p1, 5, 3))).toBe(false);
    expect(e1.encloses(RegularPolygon(p2, 5, 3))).toBe(false);
    expect(e1.encloses(C(p1, half))).toBe(true);
    expect(e1.encloses(C(p1, 2))).toBe(false);
    expect(() => e1.encloses(Point3D(0, 0, 0).add([1, 2, 3]) as never)).toThrow();
    let e = E([0, 0], 1, 2);
    expect(e.enclosesPoint(e.center)).toBe(true);
    expect(e.enclosesPoint(e.center.add([0, e.vradius.sub(R(1n, 10n))]))).toBe(true);
    expect(e.enclosesPoint(e.center.add([e.hradius, 0]))).toBe(false);
    expect(e.enclosesPoint(e.center.add([e.hradius.add(R(1n, 10n)), 0]))).toBe(false);
    e = E([0, 0], 2, 1);
    expect(e.enclosesPoint(e.center.add([e.hradius.sub(R(1n, 10n)), 0]))).toBe(true);
    expect(c1.enclosesPoint(Point(1, 0))).toBe(false);
    expect(c1.enclosesPoint(Point(0.3, 0.4))).toBe(true);
    expect(c1.enclosesPoint(Point(new Sym('q'), 0))).toBe('unknown');
    expect(E([0, 0], 2, 1).enclosesPoint(Point(new Sym('q'), 0))).toBe('unknown');
    expect(e2.contains(e2.arbitraryPoint())).toBe(true);
    expect(() => E(Point(real('x'), real('y')), 1, 2).arbitraryPoint('x')).toThrow('Symbol x already appears in object and cannot be used as a parameter.');
  });

  it('tangents and normals', () => {
    const v = sqrt(2).div(2);
    const p11 = Point(v, v);
    const p12 = p2.add(Point(half, 0));
    const p13 = p2.add(Point(0, 1));
    expect(s(e1.tangentLines(p4))).toBe(s(c1.tangentLines(p4)));
    expect(s(e2.tangentLines(p12))).toBe(s([Line(Point(R(3n, 2n), 1), Point(R(3n, 2n), half))]));
    expect(s(e2.tangentLines(p13))).toBe(s([Line(Point(1, 2), Point(R(5n, 4n), 2))]));
    expect(s(c1.tangentLines(p1))).toBe('[]');
    expect(e2.isTangent(Line(p12, p2.add(Point(half, 1))))).toBe(true);
    expect(e2.isTangent(Line(p13, p2.add(Point(half, 1))))).toBe(true);
    expect(c1.isTangent(Line(p11, Point(0, sqrt(2))))).toBe(true);
    expect(e1.isTangent(Line(Point(0, 0), Point(1, 1)))).toBe(false);
    expect(c1.isTangent(e1)).toBe(true);
    expect(c1.isTangent(E(Point(2, 0), 1, 1))).toBe(true);
    expect(c1.isTangent(Polygon(Point(1, 1), Point(1, -1), Point(2, 0)))).toBe(false);
    expect(C(Point(5, 5), 3).isTangent(C(Point(0, 5), 1))).toBe(false);
    expect(s(E(Point(5, 5), 2, 1).tangentLines(Point(0, 0)))).toBe(s([Line(Point(0, 0), Point(R(77n, 25n), R(132n, 25n))), Line(Point(0, 0), Point(R(33n, 5n), R(22n, 5n)))]));
    expect(s(E(Point(5, 5), 2, 1).tangentLines(Point(3, 4)))).toBe(s([Line(Point(3, 4), Point(4, 4)), Line(Point(3, 4), Point(3, 5))]));
    expect(s(C(Point(5, 5), 2).tangentLines(Point(3, 3)))).toBe(s([Line(Point(3, 3), Point(4, 3)), Line(Point(3, 3), Point(3, 4))]));
    expect(s(C(Point(5, 5), 5).tangentLines(Point(4, 0)))).toBe(s([Line(Point(4, 0), Point(R(40n, 13n), R(5n, 13n))), Line(Point(4, 0), Point(5, 0))]));
    expect(s(C(Point(5, 5), 5).tangentLines(Point(0, 6)))).toBe(s([Line(Point(0, 6), Point(0, 7)), Line(Point(0, 6), Point(R(5n, 13n), R(90n, 13n)))]));
    expect(s(C(Point(5, 5), 5).tangentLines(Point(5, 5)))).toBe('[]');
    expect(s(E([1, 2], 3, 2).tangentLines(Point(10, 0)))).toBe(s([Line(Point(10, 0), Point(1, 0)), Line(Point(10, 0), Point(R(14n, 5n), R(18n, 5n)))]));
    expect(s(E(Point(0, 0), 5, 20).tangentLines(Point(0, 0)))).toBe('[]');
    expect(s(E(Point(0, 0), 3, 2).tangentLines(Point(3, 0)))).toBe(s([Line(Point(3, 0), Point(3, -12))]));
    expect(e3.isTangent(e3.tangentLines(p1.add(Point(y1, 0)))[0] as Line2DNode)).toBe(true);
    const e = E(Point(0, 0), 2, 1);
    expect(s(e.normalLines(Point(0, 0)))).toBe(s([Line(Point(0, 0), Point(0, 1)), Line(Point(0, 0), Point(1, 0))]));
    expect(s(e.normalLines(Point(1, 0)))).toBe(s([Line(Point(0, 0), Point(1, 0))]));
    expect(s(e.normalLines([0, 1]))).toBe(s([Line(Point(0, 0), Point(0, 1))]));
    // SymPy: [Line2D(Point2D(-2.0, -0.20), Point2D(-0.96, 0.21)), Line2D(Point2D(0.97, -0.88), Point2D(2.0, -4.5))]
    const nl = e.normalLines(Point(1, 1), 2).map((l) => [l.p1, l.p2].flatMap((p) => p.args.map((c) => c.toNumber())));
    const want = [
      [-1.96, -0.2, -0.96, 0.21],
      [0.97, -0.88, 1.97, -4.5],
    ];
    nl.forEach((row, i) => row.forEach((v, j) => expect(Math.abs(v - (want[i]?.[j] ?? 0))).toBeLessThan(0.06)));
    const x = real('x');
    const eg = E([0, 0], x, 1);
    expect(s(eg.normalLines([x.add(1), 0]))).toBe(s([Line(Point(0, 0), Point(1, 0))]));
    expect(() => eg.normalLines([x.add(1), 1])).toThrow('intersections for the general ellipse are not supported');
    expect(s(E([0, 0], 2, sqrt(3).mul(2).div(3)).normalLines([1, 1], 2))).toBe('[Line2D(Point2D(-1.9, -0.28), Point2D(-0.94, 0.15)), Line2D(Point2D(1.0, -1.0), Point2D(2.0, -4.0))]');
  });

  it('is_tangent (SymPy test_is_tangent)', () => {
    const f1 = E(Point(0, 0), 3, 5);
    const g1 = C(Point(2, -2), 7);
    expect(f1.isTangent(Point(0, 0))).toBe(false);
    expect(f1.isTangent(f1)).toBe(true);
    expect(f1.isTangent(E([0, 0], 1, 2))).toBe(false);
    expect(f1.isTangent(E([0, 0], 3, 2))).toBe(true);
    expect(g1.isTangent(E([2, -2], 7, 1))).toBe(true);
    expect(g1.isTangent(C([11, -2], 2))).toBe(true);
    expect(g1.isTangent(Ray([-5, -2], [-15, -20]))).toBe(false);
    expect(g1.isTangent(Ray([9, 20], [9, -20]))).toBe(true);
    expect(g1.isTangent(Segment([2, 5], [9, 5]))).toBe(true);
    expect(f1.isTangent(Segment([2, 2], [-7, 7]))).toBe(false);
    expect(f1.isTangent(Segment([-3, 5], [3, 5]))).toBe(true);
    expect(f1.isTangent(Line([10, 0], [10, 10]))).toBe(false);
    expect(f1.isTangent(Line([-3, 0], [-2.99, -0.001]))).toBe(false);
    expect(f1.isTangent(Line([-3, 0], [-3, 1]))).toBe(true);
    expect(f1.isTangent(Polygon([-3, -5], [-3, 5], [3, 5], [3, -5]))).toBe(true);
    expect(g1.isTangent(Polygon([-3, -5], [-3, 5], [3, 5], [3, -5]))).toBe(false);
    expect(f1.isTangent(Polygon([3, 0], [5, 7], [6, -5]))).toBe(false);
    expect(() => f1.isTangent(Point(0, 0, 0))).toThrow('Entity must be two dimensional, not three dimensional');
    expect(() => f1.isTangent(Rational.of(5n) as never)).toThrow(TypeError);
  });

  it('intersections', () => {
    const l1 = Line(Point(1, -5), Point(1, 5));
    const l2 = Line(Point(-5, -1), Point(5, -1));
    const l3 = Line(Point(-1, -1), Point(1, 1));
    const l4 = Line(Point(-10, 0), Point(0, 10));
    expect(s(intersection(e2, l4))).toBe('[]');
    expect(s(intersection(c1, Point(1, 0)))).toBe('[Point2D(1, 0)]');
    expect(s(intersection(c1, l1))).toBe('[Point2D(1, 0)]');
    expect(s(intersection(c1, l2))).toBe('[Point2D(0, -1)]');
    expect(s(intersection(c1, l3))).toBe('[Point2D(-sqrt(2)/2, -sqrt(2)/2), Point2D(sqrt(2)/2, sqrt(2)/2)]');
    expect(s(intersection(c1, c2))).toBe('[Point2D(0, 1), Point2D(1, 0)]');
    expect(s(intersection(c1, c3))).toBe('[Point2D(sqrt(2)/2, sqrt(2)/2)]');
    expect(s(e1.intersection(Circle(Point(0, 2), 1)))).toBe('[Point2D(0, 1)]');
    expect(s(e1.intersection(Circle(Point(5, 0), 1)))).toBe('[]');
    expect(s(e1.intersection(Point(2, 0)))).toBe('[]');
    // SymPy returns the ellipse itself (not a list) for e1.intersection(e1)
    expect(s(e1.intersection(e1))).toBe(s([e1]));
    expect(s(intersection(E(Point(0, 0), 2, 1), E(Point(3, 0), 1, 2)))).toBe('[Point2D(2, 0)]');
    expect(s(intersection(C(Point(0, 0), 2), C(Point(7, 0), 1)))).toBe('[]');
    expect(s(intersection(E(Point(0, 0), 5, 17), E(Point(4, 0), 1, 0.2)))).toBe('[Point2D(5.0, 0)]');
    expect(s(intersection(E(Point(0, 0), 5, 17), E(Point(4, 0), 0.999, 0.2)))).toBe('[]');
    expect(s(C([0, 0], half).intersection(Triangle([-1, 0], [1, 0], [0, 1])))).toBe('[Point2D(-1/2, 0), Point2D(1/2, 0)]');
    expect(() => intersection(e2, Line([0, 0, 0], [0, 0, 1]))).toThrow(TypeError);
    expect(() => e2.intersection(1)).toThrow(TypeError);
    expect(s(C(p1, 3).intersection(C(p1, 5)))).toBe('[]');
    expect(s(C(p1, 3).intersection(C(Point(5, 5), 1)))).toBe('[]');
    const v = sqrt(2);
    expect(intersection(Triangle(Point(0, v), Point(0, v.neg()), Point(v, 0)), c1).length).toBe(4);
    expect(s(intersection(C(Point(0, 0), 5), E(Point(0, 0), 5, 20)))).toBe('[Point2D(-5, 0), Point2D(5, 0)]');
    const f1 = E(Point(0, 0), 5, 10);
    const a = R(53n, 17n);
    const c = sqrt(3991).mul(2).div(17);
    expect(s(f1.intersection(E(Point(2, 1), 4, 8)))).toBe(s([Point(a.sub(c.div(8)), a.div(2).add(c)), Point(a.add(c.div(8)), a.div(2).sub(c))]));
    expect(s(c1.intersection(Ray(p1, p2)))).toBe('[Point2D(sqrt(2)/2, sqrt(2)/2)]');
    expect(s(c1.intersection(Segment(p1, Point(0, 2))))).toBe('[Point2D(0, 1)]');
  });

  it('transformations', () => {
    const e = E([0, 0], 2, 1);
    expect(s(e.scale(2, 3))).toBe(s(Ellipse([0, 0], 4, 3)));
    expect(s(e.scale(3, 6))).toBe(s(Ellipse([0, 0], 6, 6)));
    expect(s(e.rotate(pi))).toBe(s(e));
    expect(s(e.rotate(pi, [1, 2]))).toBe(s(Ellipse(Point(2, 4), 2, 1)));
    expect(s(e.rotate(pi.div(2)))).toBe(s(Ellipse(Point(0, 0), 1, 2)));
    expect(() => e.rotate(pi.div(3))).toThrow('Only rotations of pi/2 are currently supported for Ellipse.');
    const cir = C(Point(1, 0), 1);
    expect(s(cir.rotate(pi.div(2)))).toBe(s(Circle(Point(0, 1), 1)));
    expect(s(cir.rotate(pi.div(3), Point(0, 1)))).toBe(s(Circle(Point(half.add(sqrt(3).div(2)), half.add(sqrt(3).div(2))), 1)));
    const c = C([1, 1], 2);
    expect(s(c.scale(-1))).toBe(s(Circle([-1, 1], 2)));
    expect(s(c.scale(1, -1))).toBe(s(Circle([1, -1], 2)));
    expect(s(c.scale(2))).toBe(s(Ellipse([2, 1], 4, 2)));
    expect(s(E([0, 0], 2, 3).scale(2, 3, [4, 5]))).toBe(s(Ellipse(Point(-4, -10), 4, 9)));
    expect(s(C([0, 0], 2).scale(3, 3, [4, 5]))).toBe(s(Circle(Point(-8, -10), 6)));
    expect(s(C([0, 0], 2).translate(4, 5))).toBe(s(Circle([4, 5], 2)));
    const [b, m] = [new Sym('b'), new Sym('m')];
    const f = E([1, 0], 1, 2);
    expect(s(f.reflect(Line([1, 0], { slope: 0 }) as Line2DNode))).toBe('Ellipse(Point2D(1, 0), -1, 2)');
    expect(s(f.reflect(Line([1, 0], { slope: S.Infinity }) as Line2DNode))).toBe('Ellipse(Point2D(1, 0), -1, 2)');
    expect(() => f.reflect(Line([1, 0], { slope: m }) as Line2DNode)).toThrow('General Ellipse is not supported but the equation of the reflected Ellipse is given by the zeros of');
    expect(s(Circle([0, 1], 1).reflect(Line([0, 0], [1, 1]) as Line2DNode))).toBe('Circle(Point2D(1, 0), -1)');
    expect(b.name).toBe('b');
  });

  it('equations and other properties', () => {
    const [x, y] = [new Sym('x'), new Sym('y')];
    expect(s(E(Point(1, 0), 3, 2).equation(x, y, 1))).toBe('(-x + y + 1)**2/8 + (x + y - 1)**2/18 - 1');
    expect(s(E(Point(1, 5), 6, 2).equation(x, y, 2))).toBe('(-2*x + y - 3)**2/20 + (x + 2*y - 11)**2/180 - 1');
    expect(s(E(Point(1, 1), 6, 3).evolute())).toBe('(6*x - 6)**(2/3) + (3*y - 3)**(2/3) - 9');
    expect(() => C(Point(1, 1), 6).evolute()).toThrow('Evolute of arbitrary Ellipse is not supported.');
    const [a, bb] = symbols('a b') as [Sym, Sym];
    const e = E([x, y], a, bb);
    expect(s(e.auxiliaryCircle())).toBe('Circle(Point2D(x, y), Max(a, b))');
    expect(s(C([3, 4], 8).auxiliaryCircle())).toBe('Circle(Point2D(3, 4), 8)');
    expect(s(e.directorCircle())).toBe('Circle(Point2D(x, y), sqrt(a**2 + b**2))');
    expect(s(C([3, 4], 8).directorCircle())).toBe('Circle(Point2D(3, 4), 8*sqrt(2))');
    const tt = new Sym('t');
    expect(s(E(Point(0, 0), 3, 5).parameterValue([3, 0], tt))).toBe('{t: 0}');
    expect(() => E(Point(0, 0), 3, 5).parameterValue([4, 0], tt)).toThrow(RangeError);
    const er = E(Point(0, 0), real('y1'), real('y1'));
    const [rx, ry] = [new Sym('rx'), new Sym('ry')];
    for (const r of [er.randomPoint(), er.randomPoint(1)]) {
      expect(s(er.equation(rx, ry).subs(rx, r.coordinate(0)).subs(ry, r.coordinate(1)).simplify())).toBe('0');
    }
    expect(s(E(Point(0, 0), 3, 2).randomPoint(0).n(2))).toBe('Point2D(2.1, 1.4)');
  });

  it('more cases', () => {
    expect(s(E([0, 0], 2, 1).arbitraryPoint(null))).toBe('Point2D(2*cos(t), sin(t))');
    expect(s(E([0, 0], 2, 1).intersection(RegularPolygon([0, 0], 3, 4)))).toBe('[]');
    expect(() => C([0, 0], 1).intersection(Point(0, 0).sub([1, 1]).add([1, 1]) as never)).not.toThrow();
    expect(() => C([0, 0], 1).intersection(new Sym('q') as never)).toThrow('Intersection not handled for Sym'.replace('Sym', 'object'));
    expect(() => C([0, 0], 1).intersection(planeLike())).toThrow('Intersection not handled for Plane');
    expect(E([0, 0], 2, 1).normalLines(Point(1, 1)).length).toBe(2);
    expect(() => Circle([0, 0], Point(1, 2) as never)).toThrow('Coordinates must be valid SymPy expressions.');
    expect(s(Circle([0, 0], 2n))).toBe('Circle(Point2D(0, 0), 2)');
    expect(() => Circle([0, 0], 'r' as never)).toThrow(TypeError);
  });

  it('moments of area (SymPy test_second_moment_of_area, test_section_modulus_and_polar_second_moment_of_area)', () => {
    const e = E(Point(0, 0), 5, 4);
    expect(s(e.secondMomentOfArea())).toBe('[80*pi, 125*pi, 0]');
    expect(s(e.secondMomentOfArea(Point(6, 5)))).toBe('[580*pi, 845*pi, 600*pi]');
    const d = new Sym('d', { positive: true });
    let c = C([3, 7], 8);
    expect(s(c.polarSecondMomentOfArea())).toBe('2048*pi');
    expect(s(c.sectionModulus())).toBe('[128*pi, 128*pi]');
    c = C([2, 9], d.div(2));
    expect(s(c.sectionModulus())).toBe('[pi*d**3/32, pi*d**3/32]');
    const [a, b] = symbols('a b', { positive: true }) as [Sym, Sym];
    let f = E([4, 6], a, b);
    expect(s(f.sectionModulus())).toBe('[pi*a*b**2/4, pi*a**2*b/4]');
    expect(s(f.polarSecondMomentOfArea())).toBe('pi*a**3*b/4 + pi*a*b**3/4');
    f = f.rotate(pi.div(2)) as EllipseNode;
    expect(s(f.sectionModulus())).toBe('[pi*a**2*b/4, pi*a*b**2/4]');
    f = E([a, b], 2, 6);
    expect(s(f.sectionModulus())).toBe('[18*pi, 6*pi]');
    expect(s(f.polarSecondMomentOfArea())).toBe('120*pi');
    f = E(Point(0, 0), 2, 2);
    expect(s(f.sectionModulus(Point(2, 2)))).toBe('[2*pi, 2*pi]');
    expect(s(f.sectionModulus([2, 2]))).toBe('[2*pi, 2*pi]');
  });
});
