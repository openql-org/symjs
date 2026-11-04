// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/polygon.ts (SymPy sympy/geometry/polygon.py and
// sympy/geometry/tests/test_polygon.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { And as and, Expr, Le, Lt, Rational, S, Sym, cos, pi, sqrt, symbols } from '../../src';
import { conditionHolds } from '../../src/geometry/polygon';
import {
  Circle,
  Ellipse,
  GeometryError,
  Line,
  Point,
  Point2D,
  Polygon,
  Ray,
  RegularPolygon,
  Segment,
  Triangle,
  areSimilar,
  convexHull,
  deg,
  intersection,
  rad,
} from '../../src/geometry';
import type { GeometryEntity, Line2DNode, PolygonNode, RegularPolygonNode, TriangleNode } from '../../src/geometry';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : e instanceof Map ? `{${[...e].map(([k, v]) => `${s(k)}: ${s(v)}`).join(', ')}}` : String(e));
const real = (n: string): Sym => new Sym(n, { real: true });
const R = (p: bigint, q = 1n): Expr => Rational.of(p, q);
const half = S.Half;
const P = (...a: unknown[]): PolygonNode => (Polygon as unknown as (...b: unknown[]) => PolygonNode)(...a);
const T = (...a: unknown[]): TriangleNode => (Triangle as unknown as (...b: unknown[]) => TriangleNode)(...a);
const RP = (...a: unknown[]): RegularPolygonNode => (RegularPolygon as unknown as (...b: unknown[]) => RegularPolygonNode)(...a);
const get = <V>(m: Map<Expr, V>, k: Expr): V => {
  const v = (m as unknown as { get(k: Expr): V | undefined }).get(k);
  if (v === undefined) throw new RangeError(`no key ${String(k)}`);
  return v;
};

describe('Polygon (SymPy test_polygon)', () => {
  const [x, y, q, u, v, w] = ['x', 'y', 'q', 'u', 'v', 'w'].map(real) as [Sym, Sym, Sym, Sym, Sym, Sym];
  const [a, b, c] = [Point(0, 0), Point(2, 0), Point(3, 3)];
  const t = T(a, b, c);

  it('construction', () => {
    expect(s(Polygon(Point(0, 0)))).toBe('Point2D(0, 0)');
    expect(s(Polygon(a, Point(1, 0), b, c))).toBe(s(t));
    expect(Polygon(Point(1, 0), b, c, a).equals(t)).toBe(true);
    expect(Polygon(b, c, a, Point(1, 0)).equals(t)).toBe(true);
    expect(Polygon(a, Point(3, 0), b, c).equals(t)).toBe(true);
    expect(Polygon(a, b, Point(3, -1), b, c).equals(t)).toBe(true);
    expect(s(Polygon(a, b, a))).toBe('Segment2D(Point2D(0, 0), Point2D(2, 0))');
    const big = Polygon(...[[-4, 15], [-11, 15], [-15, 15], [-15, 33 / 5], [-15, -87 / 10], [-15, -15], [-42 / 5, -15], [-2, -15], [7, -15], [15, -15], [15, -3], [15, 10], [15, 15]].map((p) => Point(...p)));
    expect(big.equals(Polygon(Point(-15, -15), Point(15, -15), Point(15, 15), Point(-15, 15)))).toBe(true);
    expect(s(Polygon(Point(0, 0), 1, { n: 3 }))).toBe('RegularPolygon(Point2D(0, 0), 1, 3, 0)');
    expect(s(Polygon(Point(0, 0), 1, 0, { n: 3 }))).toBe('RegularPolygon(Point2D(0, 0), 1, 3, 0)');
    expect(s(Polygon([0.5, 0], [1, 1], [0, 1], { evaluate: false }))).toBe('Triangle(Point2D(0.5, 0), Point2D(1, 1), Point2D(0, 1))');
    expect(s(Polygon(Point(0, 0), Point(1, 0), Point(1, 1), Point(0, 1)).subs(S.One, 2))).toBe('Polygon(Point2D(0, 0), Point2D(2, 0), Point2D(2, 2), Point2D(0, 2))');
    expect(() => Polygon(Point(0, 0), 'r' as never, { n: 3 })).toThrow(TypeError);
    expect(s(P([0, 0], [0, pi], [pi, 0], [pi, pi]).n(2))).toBe('Polygon(Point2D(0, 0), Point2D(0, 3.1), Point2D(3.1, 0), Point2D(3.1, 3.1))');
  });

  it('general polygons', () => {
    const p1 = P(Point(0, 0), Point(3, -1), Point(6, 0), Point(4, 5), Point(2, 3), Point(0, 3));
    const p2 = P(Point(6, 0), Point(3, -1), Point(0, 0), Point(0, 3), Point(2, 3), Point(4, 5));
    const p3 = P(Point(0, 0), Point(3, 0), Point(5, 2), Point(4, 4));
    const p4 = P(Point(0, 0), Point(4, 4), Point(5, 2), Point(3, 0));
    const p5 = P(Point(0, 0), Point(4, 4), Point(0, 4));
    const p6 = P(Point(-11, 1), Point(-9, 6.6), Point(-4, -3), Point(-8.4, -8.7));
    const p7 = P(Point(x, y), Point(q, u), Point(v, w));
    const p8 = P(Point(x, y), Point(v, w), Point(q, u));
    const p9 = P(Point(0, 0), Point(4, 4), Point(3, 0), Point(5, 2));
    const p10 = P(Point(0, 2), Point(2, 2), Point(0, 0), Point(2, 0));
    expect(p1.equals(p2)).toBe(true);
    expect(p1.key).toBe(p2.key);
    expect(p7.key).toBe(p8.key);
    expect(p3.key === p9.key).toBe(false);
    expect(p1.args.length).toBe(6);
    expect(p1.sides.length).toBe(6);
    expect(s(p1.perimeter)).toBe('2*sqrt(2) + 5 + sqrt(29) + 2*sqrt(10)');
    expect(s(p1.area)).toBe('22');
    expect(p1.isConvex()).toBe(false);
    expect(P([-1, 1], [2, -1], [2, 1], [-1, -1], [3, 0]).isConvex()).toBe(false);
    expect(p3.isConvex()).toBe(true);
    expect(p4.isConvex()).toBe(true);
    const d5 = p5.angles;
    expect(s(get(d5, Point(0, 0)))).toBe('pi/4');
    expect(s(get(d5, Point(0, 4)))).toBe('pi/2');
    expect(p5.enclosesPoint(Point(x, y))).toBe('unknown');
    expect(p5.enclosesPoint(Point(1, 3))).toBe(true);
    expect(p5.enclosesPoint(Point(0, 0))).toBe(false);
    expect(p5.enclosesPoint(Point(4, 0))).toBe(false);
    expect(p1.encloses(Circle(Point(2.5, 2.5), 5))).toBe(false);
    expect(p1.encloses(Ellipse(Point(2.5, 2), 5, 6))).toBe(false);
    expect(s(p5.plotInterval('x'))).toBe('[x, 0, 1]');
    expect(s(p5.distance(Polygon(Point(10, 10), Point(14, 14), Point(10, 14))))).toBe('6*sqrt(2)');
    expect(s(p5.distance(Polygon(Point(1, 8), Point(5, 8), Point(8, 12), Point(1, 12))))).toBe('4');
    expect(p5.equals(Polygon(Point(4, 4), Point(0, 4), Point(0, 0)))).toBe(true);
    expect(p5.contains(Polygon(Point(4, 4), Point(0, 4), Point(0, 0)))).toBe(true);
    expect(p5.equals(Point(0, 4))).toBe(false);
    expect(p5.contains(Point(0, 1))).toBe(true);
    expect(p5.contains(Point(0, 0))).toBe(true);
    expect(p5.contains(Point(1, 3))).toBe(false);
    expect(p5.contains(Segment([0, 1], [0, 2]))).toBe(true);
    expect(p5.contains(Circle([0, 0], 1))).toBe(false);
    expect(s(p5.arbitraryPoint('t').subs(real('t'), 0))).toBe('Point2D(0, 0)');
    expect(() => P(Point(x, 0), Point(0, y), Point(x, y)).arbitraryPoint('x')).toThrow(RangeError);
    expect(s(p6.intersection(Ray(Point(-9, 6.6), Point(-9, 5.5))))).toBe('[Point2D(-9, -84/13), Point2D(-9, 33/5)]');
    expect(s(p10.area)).toBe('0');
    expect(s(p5.bounds)).toBe('[0, 0, 4, 4]');
    expect(s(p5.centroid)).toBe('Point2D(4/3, 8/3)');
    expect(p5.ambientDimension).toBe(2);
    expect(() => p5.distance(Line([0, 0], [1, 1]))).toThrow('distance between a Polygon and');
    // SymPy issue 24885: the angles of a polygon sum to (n - 2)*pi
    const p13 = P(Point(0, 0), Point(8, 8), Point(23, 20), Point(0, 20));
    expect([...p13.angles.values()].reduce((acc, e) => acc + e.toNumber(), 0)).toBeCloseTo(2 * Math.PI, 10);
    const p14 = P(Point(8, 8), Point(23, 20), Point(0, 20), Point(0, 0));
    expect([...p14.angles.values()].reduce((acc, e) => acc + e.toNumber(), 0)).toBeCloseTo(2 * Math.PI, 10);
    const ang4 = p4.angles;
    expect(get(ang4, Point(0, 0)).toNumber()).toBeCloseTo(Math.PI / 4, 12);
    expect(get(ang4, Point(4, 4)).toNumber()).toBeCloseTo(Math.atan2(3, 1), 12);
    expect(get(ang4, Point(5, 2)).toNumber()).toBeCloseTo(1.8925468811915387, 12);
    expect(get(ang4, Point(3, 0)).toNumber()).toBeCloseTo((3 * Math.PI) / 4, 12);
    expect(get(p3.angles, Point(5, 2)).toNumber()).toBeCloseTo(1.8925468811915387, 12);
    expect(() => P(Point(0, 0), Point(x, 0), Point(x, y)).angles).toThrow("Can't determine orientation");
  });

  it('regular polygons', () => {
    const p1 = RP(Point(0, 0), 10, 5);
    const p2 = RP(Point(0, 0), 5, 5);
    expect(() => RegularPolygon(Point(0, 0), Point(0, 1) as never, Point(1, 1) as never)).toThrow();
    expect(() => RegularPolygon(Point(0, 0), 1, 2)).toThrow(GeometryError);
    expect(() => RegularPolygon(Point(0, 0), 1, 2.5)).toThrow(RangeError);
    expect(p1.equals(p2)).toBe(false);
    expect(s(p1.interiorAngle)).toBe('3*pi/5');
    expect(s(p1.exteriorAngle)).toBe('2*pi/5');
    expect(s(p2.apothem)).toBe('5/4 + 5*sqrt(5)/4');
    expect(s(p2.circumcenter)).toBe('Point2D(0, 0)');
    expect(s([p1.circumradius, p1.radius])).toBe('[10, 10]');
    expect(s(p2.circumcircle)).toBe('Circle(Point2D(0, 0), 5)');
    expect(s(p2.incircle)).toBe(s(Circle(Point(0, 0), p2.apothem)));
    expect(s(p2.inradius)).toBe(s(p2.apothem));
    expect(s(p2.centroid)).toBe('Point2D(0, 0)');
    p2.spin(pi.div(10));
    expect(s(get(p2.angles, Point(0, 5)))).toBe('3*pi/5');
    expect(p1.isConvex()).toBe(true);
    expect(s(p1.rotation)).toBe('0');
    expect(p1.enclosesPoint(Point(0, 0))).toBe(true);
    expect(p1.enclosesPoint(Point(11, 0))).toBe(false);
    expect(p2.enclosesPoint(Point(0, 4.9))).toBe(true);
    expect(RP(Point(0, 0), 2, 4).enclosesPoint(Point(1.5, 0))).toBe(true);
  });

  it('regular polygons: spin, rotate, area and transformations', () => {
    const p1 = RP(Point(0, 0), 10, 5);
    p1.spin(pi.div(3));
    expect(s(p1.rotation)).toBe('pi/3');
    expect(s(p1.vertices[0])).toBe('Point2D(5, 5*sqrt(3))');
    expect(s(p1)).toBe('RegularPolygon(Point2D(0, 0), 10, 5, pi/3)');
    expect(s(p1.rotate(pi.div(3)))).toBe(s(RegularPolygon(Point(0, 0), 10, 5, pi.mul(2).div(3))));
    expect(s(p1)).toBe('RegularPolygon(Point2D(0, 0), 10, 5, pi/3)');
    expect(s(p1.area)).toBe('(1250 - 250*sqrt(5))/(4*sqrt(5 - 2*sqrt(5)))');
    expect(s(p1.length)).toBe('20*sqrt(5/8 - sqrt(5)/8)');
    expect(s(p1.scale(2, 2))).toBe(s(RegularPolygon(p1.center, p1.radius.mul(2), 5, p1.rotation)));
    expect(s(RegularPolygon([0, 0], 1, 4).scale(2, 3))).toBe(s(Polygon(Point(2, 0), Point(0, 3), Point(-2, 0), Point(0, -3))));
    expect(s(RegularPolygon([0, 0], 1, 4).scale(2, 3, [4, 5]))).toBe(s(Polygon(Point(-2, -10), Point(-4, -7), Point(-6, -10), Point(-4, -13))));
    expect(s(RegularPolygon([0, 0], 1, 4).scale(2, 2))).toBe('RegularPolygon(Point2D(0, 0), 2, 4, 0)');
    expect(s(RegularPolygon([0, 0], 1, 4).reflect(Line([0, 1], { slope: -2 }) as Line2DNode))).toBe('RegularPolygon(Point2D(4/5, 2/5), -1, 4, atan(4/3))');
    expect(RegularPolygon([0, 0], 1, 4).equals(Polygon([1, 0], [0, 1], [-1, 0], [0, -1]))).toBe(true);
    expect(Polygon([1, 0], [0, 1], [-1, 0], [0, -1]).equals(RegularPolygon([0, 0], 1, 4))).toBe(true);
    expect(RegularPolygon([0, 0], 1, 4).equals(RegularPolygon([0, 0], 1, 4))).toBe(true);
    expect(s(RP([0, 0], 1, 4, x).rotation)).toBe('x');
    expect(s(RP([0, 0], 1, 4).subs(S.One, 2))).toBe('RegularPolygon(Point2D(0, 0), 2, 4, 0)');
    expect(s(RP([0, pi], pi, 4, pi).n(2))).toBe('RegularPolygon(Point2D(0, 3.1), 3.1, 4, 0)');
    const r = RP(Point(0, 0), 5, 3);
    expect(s(r.secondMomentOfArea())).toBe('[1875*sqrt(3)/32, 1875*sqrt(3)/32, 0]');
    const hex = RP([0, 0], 1, 6);
    expect(s(hex.sectionModulus())).toBe('[5/8, 5*sqrt(3)/16]');
    expect(s(hex.polarSecondMomentOfArea())).toBe('5*sqrt(3)/8');
    expect(RP([0, 0], new Sym('n'), new Sym('k')).radius.key).toBe(new Sym('n').key);
  });

  it('triangles', () => {
    const x1 = real('x1');
    const p1 = Point(0, 0);
    const p2 = Point(5, 0);
    const p3 = Point(0, 5);
    const t1 = T(p1, p2, p3);
    const t2 = T(p1, p2, Point(R(5n, 2n), sqrt(R(75n, 4n))));
    const t3 = T(p1, Point(x1, 0), Point(0, x1));
    expect(s(Triangle(p1, p2, p1))).toBe('Segment2D(Point2D(0, 0), Point2D(5, 0))');
    expect(() => Triangle(Point(0, 0))).toThrow(GeometryError);
    expect(s(Triangle(p1, p1, p1))).toBe('Point2D(0, 0)');
    expect(s(Triangle(p2, p2.mul(2), p2.mul(3)))).toBe('Segment2D(Point2D(5, 0), Point2D(15, 0))');
    expect(s(t1.area)).toBe('25/2');
    expect(t1.isRight()).toBe(true);
    expect(t2.isRight()).toBe(false);
    expect(t3.isRight()).toBe(true);
    expect(t1.contains(p1)).toBe(true);
    expect(t1.contains(t1.sides[0])).toBe(true);
    expect(t2.contains(Point(5, 5))).toBe(false);
    expect(t1.isConvex()).toBe(true);
    expect(get(t1.angles, p1).toNumber()).toBeCloseTo(Math.PI / 2, 12);
    expect(t1.isEquilateral()).toBe(false);
    expect(t2.isEquilateral()).toBe(true);
    expect(areSimilar(t1, t2)).toBe(false);
    expect(areSimilar(t1, t3)).toBe(true);
    expect(areSimilar(t2, t3)).toBe(false);
    expect(t1.isSimilar(Point(0, 0))).toBe(false);
    const bis = t1.bisectors();
    expect(s(get(bis, p1))).toBe('Segment2D(Point2D(0, 0), Point2D(5/2, 5/2))');
    expect(s(get(t2.bisectors(), p2))).toBe('Segment2D(Point2D(5, 0), Point2D(5/4, 5*sqrt(3)/4))');
    expect(s(get(t3.bisectors(), Point(0, x1)))).toBe(s(Segment(Point(0, x1), Point(x1.mul(sqrt(2).sub(1)), 0))));
    expect(s(t1.incenter)).toBe('Point2D(5 - 5*sqrt(2)/2, 5 - 5*sqrt(2)/2)');
    expect(s(t1.inradius)).toBe('5 - 5*sqrt(2)/2');
    expect(s((t1.incircle as GeometryEntity & { radius: Expr }).radius)).toBe('5 - 5*sqrt(2)/2');
    expect(s(t2.inradius)).toBe('5*sqrt(3)/6');
    expect(s(t3.inradius)).toBe('x1**2/((sqrt(2) + 2)*Abs(x1))');
    expect(s(get(t1.exradii, t1.sides[2] as Expr))).toBe('5*sqrt(2)/2');
    expect(s(get(t1.excenters, t1.sides[2] as Expr))).toBe('Point2D(25*sqrt(2), -5*sqrt(2)/2)');
    expect(s((t1.circumcircle as GeometryEntity & { center: Expr }).center)).toBe('Point2D(5/2, 5/2)');
    expect(s(t1.circumradius)).toBe('5*sqrt(2)/2');
    const m = t1.medians;
    expect(s(t1.centroid)).toBe('Point2D(5/3, 5/3)');
    expect(s(get(m, p1))).toBe('Segment2D(Point2D(0, 0), Point2D(5/2, 5/2))');
    expect(s(get(t3.medians, p1))).toBe('Segment2D(Point2D(0, 0), Point2D(x1/2, x1/2))');
    expect(s(intersection(get(m, p1) as GeometryEntity, get(m, p2) as GeometryEntity, get(m, p3) as GeometryEntity))).toBe(s([t1.centroid]));
    expect((t1.medial as PolygonNode).equals(Triangle(Point(2.5, 0), Point(0, 2.5), Point(2.5, 2.5)))).toBe(true);
    expect(s(t1.ninePointCircle)).toBe(s(Circle(Point(2.5, 0), Point(0, 2.5), Point(2.5, 2.5))));
    const alt = t1.altitudes;
    expect(s(get(alt, p1))).toBe('Segment2D(Point2D(0, 0), Point2D(5/2, 5/2))');
    expect((get(alt, p2) as GeometryEntity).equals(t1.sides[0] as Expr)).toBe(true);
    expect(s(get(alt, p3))).toBe(s(t1.sides[2]));
    expect(s(t1.orthocenter)).toBe('Point2D(0, 0)');
    expect(intersection(...([...bis.values()] as GeometryEntity[])).length).toBe(1);
    expect(intersection(...([...alt.values()] as GeometryEntity[])).length).toBe(1);
    expect(s(T(Point(0, 0), Point(4, 0), Point(0, 3)).inradius)).toBe('1');
    expect(s(T(Point(0, 0), Point(2, 0), Point(0, 2)).incircle)).toBe(s(Circle(Point(sqrt(2).neg().add(2), sqrt(2).neg().add(2)), sqrt(2).neg().add(2))));
    const t6 = T(Point(0, 0), Point(6, 0), Point(0, 2));
    expect(s(get(t6.exradii, t6.sides[2] as Expr))).toBe('-2 + sqrt(10)');
    expect(s(T(Point(0, 0), Point(1, 0), Point(0, 1)).medial)).toBe(s(Triangle(Point(half, 0), Point(half, half), Point(0, half))));
    expect(s(T(Point(0, 0), Point(1, 0), Point(0, 1)).ninePointCircle)).toBe('Circle(Point2D(1/4, 1/4), sqrt(2)/4)');
    expect(s(T(Point(0, 0), Point(1, 0), Point(0, 1)).eulerline)).toBe('Line2D(Point2D(0, 0), Point2D(1/2, 1/2))');
    expect(s(T(Point(0, 0), Point(10, 0), Point(5, sqrt(3).mul(5))).eulerline)).toBe('Point2D(5, 5*sqrt(3)/3)');
    expect(s(T(Point(4, -6), Point(4, -1), Point(-3, 3)).eulerline)).toBe('Line2D(Point2D(64/7, 3), Point2D(-29/14, -7/2))');
    expect(s(get(T(Point(0, 0), Point(1, 0), Point(0, 1)).bisectors(), Point(1, 0)))).toBe('Segment2D(Point2D(1, 0), Point2D(0, -1 + sqrt(2)))');
    expect(s(T(Point(0, 0), Point(1, 0), Point(0, 1)).incenter)).toBe('Point2D(1 - sqrt(2)/2, 1 - sqrt(2)/2)');
    expect(s(T(Point(0, 0), Point(1, 0), Point(0, 1)).subs(S.One, 2))).toBe('Triangle(Point2D(0, 0), Point2D(2, 0), Point2D(0, 2))');
    // the types of triangles (SymPy test_type_of_triangle)
    const i1 = T(Point(0, 0), Point(5, 0), Point(2, 4));
    expect([i1.isIsosceles(), i1.isScalene(), i1.isEquilateral()]).toEqual([true, false, false]);
    const i2 = T(Point(0, 0), Point(0, 2), Point(4, 0));
    expect([i2.isIsosceles(), i2.isScalene(), i2.isEquilateral()]).toEqual([false, true, false]);
    const i3 = T(Point(0, 0), Point(6, 0), Point(3, sqrt(27)));
    expect([i3.isIsosceles(), i3.isScalene(), i3.isEquilateral()]).toEqual([true, false, true]);
  });

  it('triangles from sides and angles (SymPy test_triangle_kwargs)', () => {
    expect(s(Triangle({ sss: [3, 4, 5] }))).toBe('Triangle(Point2D(0, 0), Point2D(3, 0), Point2D(3, 4))');
    expect(s(Triangle({ asa: [30, 2, 30] }))).toBe(s(Triangle(Point(0, 0), Point(2, 0), Point(1, sqrt(3).div(3)))));
    expect(s(Triangle({ sas: [1, 45, 2] }))).toBe(s(Triangle(Point(0, 0), Point(2, 0), Point(sqrt(2).div(2), sqrt(2).div(2)))));
    // SymPy Triangle(sss=(1, 2, 5)) is None
    expect(() => Triangle({ sss: [1, 2, 5] })).toThrow('There is no triangle with these sides.');
    expect(s(deg(rad(180)))).toBe('180');
  });

  it('distances (SymPy test_polygon, test_do_poly_distance)', () => {
    const p1 = P(Point(0, 0), Point(1, 0), Point(1, 1), Point(0, 1));
    const p2 = P(Point(0, R(5n, 4n)), Point(1, R(5n, 4n)), Point(1, R(9n, 4n)), Point(0, R(9n, 4n)));
    const p3 = P(Point(1, 2), Point(2, 2), Point(2, 1));
    const p4 = P(Point(1, 1), Point(R(6n, 5n), 1), Point(1, R(6n, 5n)));
    expect(s(p1.distance(Point(half, half)))).toBe('1/2');
    expect(s(p1.distance(Point(1, 1)))).toBe('0');
    expect(s(p2.distance(Point(half, half)))).toBe('3/4');
    expect(s(p3.distance(Point(1, 1)))).toBe('sqrt(2)/2');
    // SymPy warns "Polygons may intersect producing erroneous output"
    expect(s(p1.distance(p2))).toBe('1/4');
    expect(s(p1.distance(p3))).toBe('sqrt(2)/2');
    expect(s(p3.distance(p4))).toBe('2*sqrt(2)/5');
    const sq1 = P(Point(0, 0), Point(0, 1), Point(1, 1), Point(1, 0));
    expect(s(sq1.distance(P(Point(1, 2), Point(2, 2), Point(2, 1))))).toBe('sqrt(2)/2');
    expect(s(sq1.distance(P(Point(1, 0), Point(2, 0), Point(2, 1), Point(1, 1))))).toBe('0');
    expect(s(P(Point(0, -1), Point(2, -1), Point(half, half)).distance(sq1))).toBe('0');
  });

  it('convex hulls and enclosing (SymPy test_convex_hull, test_encloses)', () => {
    const p = [[-5, -1], [-2, 1], [-2, -1], [-1, -3], [0, 0], [1, 1], [2, 2], [2, -1], [3, 1], [4, -1], [6, 2]].map((xy) => Point(...xy));
    const at = (i: number): Expr => p[i] as Expr;
    const ch = Polygon(at(0), at(3), at(9), at(10), at(6), at(1));
    p.push(Point(-1, -3));
    const another = [[-45, -85], [-45, 85], [-45, 26], [-45, -24]].map((xy) => Point(...xy));
    expect(s(convexHull(...another))).toBe(s(Segment(another[0] as Expr, another[1] as Expr)));
    expect((convexHull(...p) as PolygonNode).equals(ch)).toBe(true);
    expect(s(convexHull(at(0)))).toBe(s(at(0)));
    expect(s(convexHull(at(0), at(1)))).toBe(s(Segment(at(0), at(1))));
    expect(s(convexHull(at(3), at(3), at(3)))).toBe(s(at(3)));
    expect(s(convexHull(Point(0, 0), Segment(Point(1, 0), Point(1, 1)), RegularPolygon(Point(2, 0), 2, 4)))).toBe(s(Polygon(Point(0, 0), Point(2, -2), Point(4, 0), Point(2, 2))));
    const sq = P(Point(0, 0), Point(1, 0), Point(1, 1), Point(0, 1), Point(half, half));
    expect(sq.encloses(Point(0, half))).toBe(false);
    expect(sq.encloses(Point(half, half))).toBe(false);
    expect(sq.encloses(Point(R(3n, 4n), half))).toBe(true);
    expect(sq.encloses(Polygon(Point(0.6, 0.6), Point(0.7, 0.6), Point(0.7, 0.7)))).toBe(true);
    expect(Circle([0, 0], 5).encloses(RegularPolygon([0, 0], 1, 4))).toBe(true);
    expect(Circle([0, 0], 5).encloses(RegularPolygon([8, 8], 1, 3))).toBe(false);
  });

  it('transformations (SymPy test_transform, test_reflect)', () => {
    const pts = [Point(0, 0), Point(half, R(1n, 4n)), Point(1, 1)];
    const out = [Point(-4, -10), Point(-3, R(-37n, 4n)), Point(-2, -7)];
    expect(s(Triangle(...pts).scale(2, 3, [4, 5]))).toBe(s(Triangle(...out)));
    const tri = Polygon([1, 0], [2, 0], [2, 2]);
    expect((tri.reflect(Line([3, 0], { slope: S.Infinity }) as Line2DNode) as PolygonNode).equals(Triangle(Point(5, 0), Point(4, 0), Point(4, 2)))).toBe(true);
    expect((tri.reflect(Line([0, 3], { slope: S.Infinity }) as Line2DNode) as PolygonNode).equals(Triangle(Point(-1, 0), Point(-2, 0), Point(-2, 2)))).toBe(true);
    expect((tri.reflect(Line([0, 3], { slope: 0 }) as Line2DNode) as PolygonNode).equals(Triangle(Point(1, 6), Point(2, 6), Point(2, 4)))).toBe(true);
    expect((tri.reflect(Line([3, 0], { slope: 0 }) as Line2DNode) as PolygonNode).equals(Triangle(Point(1, 0), Point(2, 0), Point(2, -2)))).toBe(true);
    expect(s(tri.reflect(Line([0, 0], { slope: 0 }) as Line2DNode))).toBe('Triangle(Point2D(1, 0), Point2D(2, 0), Point2D(2, -2))');
    expect(s(tri.reflect(Line([0, 0], { slope: S.Infinity }) as Line2DNode))).toBe('Triangle(Point2D(-1, 0), Point2D(-2, 0), Point2D(-2, 2))');
    const [bb, mm] = [new Sym('b'), new Sym('m')];
    const t1 = T([0, 0], [1, 0], [2, 3]);
    expect(s(t1.area.add((t1.reflect(Line([0, bb], { slope: mm }) as Line2DNode) as PolygonNode).area).simplify())).toBe('0');
  });

  it('bisectors (SymPy test_bisectors)', () => {
    // (the polygon of SymPy's test, whose angles are acos of radicals, takes several seconds; its
    // bisectors(2) is a doctest of the compatibility corpus)
    const p = P(Point(0, 0), Point(2, 0), Point(2, 2), Point(0, 2));
    expect(s(get(p.bisectors(), Point2D(2, 2)))).toBe('Ray2D(Point2D(2, 2), Point2D(2 - sqrt(2)/2, 2 - sqrt(2)/2))');
    expect(s(get(p.bisectors(2), Point2D(2, 2)))).toBe('Ray2D(Point2D(2, 2), Point2D(1.3, 1.3))');
  });

  it('intersections (SymPy test_intersection)', () => {
    const poly1 = T(Point(0, 0), Point(1, 0), Point(0, 1));
    const poly2 = P(Point(0, 1), Point(-5, 0), Point(0, -4), Point(0, R(1n, 5n)), Point(half, -0.1), Point(1, 0), Point(0, 1));
    expect(s(poly1.intersection(poly2))).toBe('[Point2D(1/3, 0), Segment2D(Point2D(0, 1/5), Point2D(0, 0)), Segment2D(Point2D(1, 0), Point2D(0, 1))]');
    expect(s(poly2.intersection(poly1))).toBe('[Point2D(1/3, 0), Segment2D(Point2D(0, 0), Point2D(0, 1/5)), Segment2D(Point2D(1, 0), Point2D(0, 1))]');
    expect(s(poly1.intersection(Point(0, 0)))).toBe('[Point2D(0, 0)]');
    expect(s(poly1.intersection(Point(-12, -43)))).toBe('[]');
    expect(s(poly2.intersection(Line([-12, 0], [12, 0])))).toBe('[Point2D(-5, 0), Point2D(0, 0), Point2D(1/3, 0), Point2D(1, 0)]');
    expect(s(poly2.intersection(Ray([-3, 4], [1, 0])))).toBe('[Segment2D(Point2D(1, 0), Point2D(0, 1))]');
    expect(s(poly2.intersection(Circle([0, -1], 1)))).toBe('[Point2D(0, -2), Point2D(0, 0)]');
    expect(s(poly1.intersection(poly1))).toBe('[Segment2D(Point2D(0, 0), Point2D(1, 0)), Segment2D(Point2D(0, 1), Point2D(0, 0)), Segment2D(Point2D(1, 0), Point2D(0, 1))]');
    expect(s(poly2.intersection(Triangle(Point(0, 1), Point(1, 0), Point(-1, 1))))).toBe('[Point2D(-5/7, 6/7), Segment2D(Point2D(0, 1), Point2D(1, 0))]');
    expect(s(poly1.intersection(RegularPolygon([-12, -15], 3, 3)))).toBe('[]');
  });

  it('parameter values and arbitrary points (SymPy test_parameter_value, test_issue_12966)', () => {
    const t = new Sym('t');
    const sq = P([0, 0], [0, 1], [1, 1], [1, 0]);
    expect(s(sq.parameterValue([0.5, 1], t))).toBe('{t: 3/8}');
    const qq = P([0, 0], [2, 1], [2, 4], [4, 0]);
    expect(s(qq.parameterValue([4, 0], t))).toBe('{t: -6 + 3*sqrt(5)}');
    expect(() => sq.parameterValue([5, 6], t)).toThrow(RangeError);
    expect(() => sq.parameterValue([-1, 6], t)).toThrow('Given point is not on Polygon');
    expect(() => sq.parameterValue(Circle(Point(0, 0), 1), t)).toThrow('other must be a point');
    expect(() => sq.parameterValue(Point(x, 0), t)).toThrow('non-numeric coordinates');
    expect(() => sq.parameterValue([2, 0], t)).toThrow('Given point may not be on Polygon');
    const poly = P(Point(0, 0), Point(0, 10), Point(5, 10), Point(5, 5), Point(10, 5), Point(10, 0));
    const tt = real('t');
    const pt = poly.arbitraryPoint(tt);
    const DELTA = R(5n).div(poly.perimeter);
    expect(s([0, 1, 2, 3, 4, 5, 6, 7].map((i) => pt.subs(tt, DELTA.mul(i))))).toBe('[Point2D(0, 0), Point2D(0, 5), Point2D(0, 10), Point2D(5, 10), Point2D(5, 5), Point2D(10, 5), Point2D(10, 0), Point2D(5, 0)]');
  });

  it('moments of area (SymPy test_second_moment_of_area, test_first_moment, test_section_modulus_and_polar_second_moment_of_area)', () => {
    const tri = P([0, 0], [4, 0], [0, 2]);
    expect(s(tri.secondMomentOfArea([0, 0]))).toBe('[8/3, 32/3, 8/3]');
    const rect = P([0, 0], [4, 0], [4, 2], [0, 2]);
    expect(s(rect.secondMomentOfArea([0, 0]))).toBe('[32/3, 128/3, 16]');
    const [a, b] = symbols('a b', { positive: true }) as [Sym, Sym];
    let p1 = P([0, 0], [a, 0], [a, b], [0, b]);
    expect(s(p1.firstMomentOfArea())).toBe('[a*b**2/8, a**2*b/8]');
    expect(s(p1.firstMomentOfArea([a.div(3), b.div(4)]))).toBe('[-3*a*b**2/32, -a**2*b/9]');
    p1 = P([0, 0], [40, 0], [40, 30], [0, 30]);
    expect(s(p1.firstMomentOfArea())).toBe('[4500, 6000]');
    let p2 = P([0, 0], [a, 0], [a.div(2), b]);
    expect(s(p2.firstMomentOfArea())).toBe('[4*a*b**2/81, a**2*b/24]');
    expect(s(p2.firstMomentOfArea([a.div(8), b.div(6)]))).toBe('[-25*a*b**2/648, -5*a**2*b/768]');
    p2 = P([0, 0], [12, 0], [12, 30]);
    expect(s(p2.firstMomentOfArea())).toBe('[1600/3, -640/3]');
    const [xx, yy] = symbols('x y') as [Sym, Sym];
    const rectangle = P([0, b], [0, 0], [a, 0], [a, b]);
    expect(s(rectangle.sectionModulus(Point(xx, yy)))).toBe('[a*b**3/(12*(-b/2 + y)), a**3*b/(12*(-a/2 + x))]');
    expect(s(rectangle.polarSecondMomentOfArea())).toBe('a**3*b/12 + a*b**3/12');
    expect(s(rectangle.sectionModulus())).toBe('[a*b**2/6, a**2*b/6]');
    const concave = P([0, 0], [1, 8], [3, 4], [4, 6], [7, 1]);
    expect(s(concave.sectionModulus())).toBe('[-6371/429, -9778/519]');
    expect(s(concave.polarSecondMomentOfArea())).toBe('-38669/252');
  });

  it('more cases', () => {
    const [a, b, c] = symbols('a b c', { positive: true }) as [Sym, Sym, Sym];
    expect(() => P(Point(0, 0), Point(a, 0), Point(b, c)).angles).toThrow('could not determine Polygon orientation.');
    const sq = P(Point(0, 0), Point(1, 0), Point(1, 1), Point(0, 1), Point(half, half));
    expect([[0.6, 0.3], [0.25, 0.5], [0.9, 0.9], [0.5, 0.1], [0.1, 0.5]].map((q) => sq.enclosesPoint(q))).toEqual([true, false, true, true, false]);
  });

  it('bisectors of a clockwise polygon', () => {
    const cw = P(Point(0, 0), Point(0, 2), Point(2, 2), Point(2, 0));
    expect(s(get(cw.bisectors(), Point2D(0, 0)))).toBe('Ray2D(Point2D(0, 0), Point2D(sqrt(2)/2, sqrt(2)/2))');
  });

  it('more cases 2', () => {
    const a = new Sym('a', { positive: true });
    expect(s(P([0, 0], [1, 0], [1, 1], [0, 1]).arbitraryPoint(null))).toBe('Piecewise((Point2D(4*t, 0), (t >= 0) & (t < 1/4)), (Point2D(1, 4*t - 1), (t >= 1/4) & (t < 1/2)), (Point2D(3 - 4*t, 1), (t >= 1/2) & (t < 3/4)), (Point2D(0, 4 - 4*t), (t >= 3/4) & (t < 1)))');
    expect(s(P([0, 0], [1, 0], [1, 1], [0, 1]).plotInterval(new Sym('u')))).toBe('[u, 0, 1]');
    expect(P(Point(0, 0), Point(a, 0), Point(a, a), Point(0, a)).isConvex()).toBe(true);
    const tt = real('t');
    expect(conditionHolds(and(Lt(sqrt(2), tt.add(2)), Le(1, tt)).subs(tt, 1))).toBe(true);
    expect(conditionHolds(Lt(sqrt(2), 1))).toBe(false);
    // both comparisons are equalities in disguise, decided once the differences are simplified
    const T0 = new Sym('T0', { real: true });
    const both = and(Le(sqrt(2).add(sqrt(3)).pow(2), T0), Le(T0, sqrt(6).add(1).pow(2).sub(2)));
    expect(conditionHolds(both.subs(T0, sqrt(6).mul(2).add(5)))).toBe(true);
  });

  it('cut sections (SymPy test_cut_section)', () => {
    const p = P([-1, -1], [1, R(5n, 2n)], [2, 1], [3, R(5n, 2n)], [4, 2], [5, 3], [-1, 3]);
    const l = Line([0, 0], [R(9n, 2n), 3]) as Line2DNode;
    const [c1, c2] = p.cutSection(l);
    expect(s(c1)).toBe('Polygon(Point2D(-9/13, -6/13), Point2D(1, 5/2), Point2D(24/13, 16/13), Point2D(12/5, 8/5), Point2D(3, 5/2), Point2D(24/7, 16/7), Point2D(9/2, 3), Point2D(-1, 3), Point2D(-1, -2/3))');
    expect(s(c2)).toBe('Polygon(Point2D(-1, -1), Point2D(-9/13, -6/13), Point2D(24/13, 16/13), Point2D(2, 1), Point2D(12/5, 8/5), Point2D(24/7, 16/7), Point2D(4, 2), Point2D(5, 3), Point2D(9/2, 3), Point2D(-1, -2/3))');
    const hx = RP(Point2D(0, 0), 6, 6);
    const [h1, h2] = hx.cutSection(Line([0, 0], { slope: 1 }) as Line2DNode);
    expect((h1 as PolygonNode).equals(Polygon(Point2D(sqrt(3).mul(-3).add(9), sqrt(3).mul(-3).add(9)), Point2D(3, sqrt(3).mul(3)), Point2D(-3, sqrt(3).mul(3)), Point2D(-6, 0), Point2D(sqrt(3).mul(3).sub(9), sqrt(3).mul(3).sub(9))))).toBe(true);
    expect((h2 as PolygonNode).equals(Polygon(Point2D(6, 0), Point2D(sqrt(3).mul(-3).add(9), sqrt(3).mul(-3).add(9)), Point2D(sqrt(3).mul(3).sub(9), sqrt(3).mul(3).sub(9)), Point2D(-3, sqrt(3).mul(-3)), Point2D(3, sqrt(3).mul(-3))))).toBe(true);
    const rect = P([0, 10], [0, 0], [20, 0], [20, 10]);
    // SymPy gives None for the side without a polygon
    expect(s(rect.cutSection(Line([0, 10], { slope: 0 }) as Line2DNode))).toBe('[EmptySet, Polygon(Point2D(0, 10), Point2D(0, 0), Point2D(20, 0), Point2D(20, 10))]');
    expect(s(rect.cutSection(Line([0, 0], { slope: 0 }) as Line2DNode))).toBe('[Polygon(Point2D(0, 10), Point2D(0, 0), Point2D(20, 0), Point2D(20, 10)), EmptySet]');
    expect(() => rect.cutSection(Line([0, 20], { slope: 0 }) as Line2DNode)).toThrow('This line does not intersect the polygon');
    expect(s(rect.cutSection(Line([10, 0], { slope: S.Infinity }) as Line2DNode))).toBe('[Polygon(Point2D(10, 0), Point2D(20, 0), Point2D(20, 10), Point2D(10, 10)), Polygon(Point2D(0, 10), Point2D(0, 0), Point2D(10, 0), Point2D(10, 10))]');
    expect(s(cos(0))).toBe('1');
  });
});
