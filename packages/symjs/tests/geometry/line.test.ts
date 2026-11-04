// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/line.ts (SymPy sympy/geometry/line.py and
// sympy/geometry/tests/test_line.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Expr, Float, Rational, S, Sym, Tuple, cos, parse, pi, simplify, sin, sqrt, symbols, tan } from '../../src';
import {
  Circle,
  GeometryError,
  Line,
  Line2D,
  Line3D,
  LinearEntity,
  Plane,
  Point,
  Point2D,
  Point3D,
  Ray,
  Ray2D,
  Ray3D,
  Segment,
  Segment2D,
  Segment3D,
  Undecidable,
  intersection,
} from '../../src/geometry';
import type { GeometryEntity, Line2DNode, Ray2DNode, Segment2DNode, SegmentNode } from '../../src/geometry';
import { pyMax, pyMin } from '../../src/geometry/line';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : String(e));
const real = (n: string): Sym => new Sym(n, { real: true });
const [x, y, z, x1, y1, t, m] = ['x', 'y', 'z', 'x1', 'y1', 't', 'm'].map(real) as [Sym, Sym, Sym, Sym, Sym, Sym, Sym];
const half = S.Half;
const l2d = (e: GeometryEntity): Line2DNode => e as Line2DNode;

describe('construction', () => {
  it('lines from equations (SymPy test_object_from_equation)', () => {
    const [a, b] = symbols('a b') as [Sym, Sym];
    const [px, py] = symbols('x y') as [Sym, Sym];
    expect(s(Line(parse('3*x + y + 18')))).toBe('Line2D(Point2D(0, -18), Point2D(1, -21))');
    expect(s(Line(parse('3*x + 5*y + 1')))).toBe('Line2D(Point2D(0, -1/5), Point2D(1, -4/5))');
    expect(s(Line(parse('3*a + b + 18'), { x: 'a', y: 'b' }))).toBe('Line2D(Point2D(0, -18), Point2D(1, -21))');
    expect(s(Line(Eq(parse('3*a + b'), -18), { x: 'a', y: b }))).toBe('Line2D(Point2D(0, -18), Point2D(1, -21))');
    expect(s(Line(parse('x - 1')))).toBe('Line2D(Point2D(1, 0), Point2D(1, 1))');
    expect(s(Line(parse('2*x - 2'), { y: px }))).toBe('Line2D(Point2D(0, 1), Point2D(1, 1))');
    expect(s(Line(py))).toBe('Line2D(Point2D(0, 0), Point2D(1, 0))');
    expect(s(Line(parse('2*y'), { x: py }))).toBe('Line2D(Point2D(0, 0), Point2D(0, 1))');
    expect(() => Line(parse('x/y'))).toThrow(RangeError);
    expect(() => Line(parse('a/b'), { x: 'a', y: 'b' })).toThrow(RangeError);
    expect(() => Line(parse('(x + 1)**2 + y'))).toThrow(RangeError);
    expect(() => Line(parse('x*y + x'))).toThrow(RangeError);
    expect(() => Line(parse('z'))).toThrow("not found in equation: {'x', 'y'}");
    expect(() => Line(parse('x + a + 1'), { x: 'x', y: a, z: 1 } as never)).toThrow('expecting only x and y as keywords');
    // a symbol of the name that is ambiguous: SymPy raises ValueError("ambiguous x"), then treats it as missing
    expect(s(Line(parse('x + 2*y').add(new Sym('x', { real: true })), {}))).toBe('Line2D(Point2D(0, -x/2 - x/2), Point2D(1, -x/2 - x/2))');
    expect(a.name).toBe('a');
  });

  it('lines, rays and segments of points', () => {
    expect(s(Line([0, 0], { slope: 0 }))).toBe('Line2D(Point2D(0, 0), Point2D(1, 0))');
    expect(s(Line([1, 1], { slope: 1 }))).toBe(s(Line([1, 1], [2, 2])));
    expect(s(Line([1, 1], { slope: S.Infinity }))).toBe(s(Line([1, 1], [1, 2])));
    expect(s(Line([1, 1], { slope: S.NegativeInfinity }))).toBe(s(Line([1, 1], [1, 2])));
    expect(s(Line([1, 1], { slope: S.Infinity }).bounds)).toBe('[1, 1, 1, 2]');
    expect(s(Line(Point(1, 2, 3, 4), Point(2, 2, 2, 2)))).toBe('Line(Point(1, 2, 3, 4), Point(2, 2, 2, 2))');
    expect(s(Line(Line(Point(1, 2, 3, 4), Point(2, 2, 2, 2))))).toBe('Line(Point(1, 2, 3, 4), Point(2, 2, 2, 2))');
    expect(s(Line(Segment([0, 0], [1, 1]) as Segment2DNode))).toBe('Line2D(Point2D(0, 0), Point2D(1, 1))');
    expect(s(Line(Segment([0, 0, 0], [1, 1, 1]) as LinearEntity))).toBe('Line3D(Point3D(0, 0, 0), Point3D(1, 1, 1))');
    expect(s(Line3D([1, 1, 1], { directionRatio: [2, 3, 4] }))).toBe('Line3D(Point3D(1, 1, 1), Point3D(3, 4, 5))');
    expect(s(Line3D(Line3D(Point3D(0, 0, 0), Point3D(0, 1, 0))))).toBe('Line3D(Point3D(0, 0, 0), Point3D(0, 1, 0))');
    expect(s(Ray3D(Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0))))).toBe('Ray3D(Point3D(0, 0, 0), Point3D(1, 0, 0))');
    expect(s(Ray3D([1, 1, 1], { directionRatio: [4, 4, 4] }))).toBe('Ray3D(Point3D(1, 1, 1), Point3D(5, 5, 5))');
    expect(s(Ray([1, 1], [2, 1, 2]))).toBe('Ray3D(Point3D(1, 1, 0), Point3D(2, 1, 2))');
    expect(s(Ray(Point(1, 2, 3, 4), Point(2, 2, 2, 2)))).toBe('Ray(Point(1, 2, 3, 4), Point(2, 2, 2, 2))');
    expect(s(Segment([1, 0], [1, 1]))).toBe('Segment2D(Point2D(1, 0), Point2D(1, 1))');
    expect(s(Segment([1, 0, 0], [1, 1, 1]))).toBe('Segment3D(Point3D(1, 0, 0), Point3D(1, 1, 1))');
    expect(s(Segment(Point(1, 2, 3, 4), Point(2, 2, 2, 2)))).toBe('Segment(Point(1, 2, 3, 4), Point(2, 2, 2, 2))');
    expect(s(Segment([1, 1], [1, 1]))).toBe('Point2D(1, 1)');
    expect(s(Segment2D([1, 1], [1, 1]))).toBe('Point2D(1, 1)');
    expect(s(Segment3D([1, 1, 1], [1, 1, 1]))).toBe('Point3D(1, 1, 1)');
    expect(s(Line2D([0, 0], [1, 1]).withArgs([Point(0, 0), Point(2, 3)]))).toBe('Line2D(Point2D(0, 0), Point2D(2, 3))');
    expect(s(Line(Point(0, 0), Point(1, 1)).subs(S.One, 5))).toBe('Line2D(Point2D(0, 0), Point2D(5, 5))');
    expect(s(Ray(Point(0, 0), Point(1, 1)).subs(S.One, 5))).toBe('Ray2D(Point2D(0, 0), Point2D(5, 5))');
    expect(s(Segment3D([0, 0, 0], [1, 1, 1]).subs(S.One, 5))).toBe('Segment3D(Point3D(0, 0, 0), Point3D(5, 5, 5))');
    expect(s(Line3D([0, 0, 0], [1, 1, 1]).subs(S.One, 5))).toBe('Line3D(Point3D(0, 0, 0), Point3D(5, 5, 5))');
    expect(s(Ray3D([0, 0, 0], [1, 1, 1]).subs(S.One, 5))).toBe('Ray3D(Point3D(0, 0, 0), Point3D(5, 5, 5))');
    expect(s(Ray2D([0, 0], [1, 1]).subs(S.One, 5))).toBe('Ray2D(Point2D(0, 0), Point2D(5, 5))');
    expect(s(Segment2D([0, 0], [1, 1]).subs(S.One, 5))).toBe('Segment2D(Point2D(0, 0), Point2D(5, 5))');
    expect(s(Segment(Point(1, 2, 3, 4), Point(2, 2, 2, 2)).subs(S.One, 5))).toBe('Segment(Point(5, 2, 3, 4), Point(2, 2, 2, 2))');
  });

  it('rebuilds, encloses and reads keywords', () => {
    const L4 = Line(Point(1, 2, 3, 4), Point(2, 2, 2, 2));
    expect(s(L4.subs(S.One, 5))).toBe('Line(Point(5, 2, 3, 4), Point(2, 2, 2, 2))');
    expect(s(Ray(Point(1, 2, 3, 4), Point(2, 2, 2, 2)).subs(S.One, 5))).toBe('Ray(Point(5, 2, 3, 4), Point(2, 2, 2, 2))');
    const c = Circle([0, 0], 5);
    // SymPy GeometryEntity.encloses
    expect(c.encloses(Line([0, 0], [1, 1]))).toBe(false);
    expect(c.encloses(Ray([0, 0], [1, 1]))).toBe(false);
    expect(c.encloses(Segment([0, 0], [1, 1]))).toBe(true);
    expect(c.encloses(Segment([0, 0], [6, 0]))).toBe(false);
    expect(s((Segment([0, 0], [1, 1]) as Segment2DNode).perpendicularLine([0, 0]))).toBe('Line2D(Point2D(0, 0), Point2D(-1, 1))');
    expect(s((Ray([0, 0], [1, 1]) as Ray2DNode).perpendicularLine([0, 0]))).toBe('Line2D(Point2D(0, 0), Point2D(-1, 1))');
    expect(s(Line3D([1, 1, 1], { directionRatio: Tuple(2, 3, 4) }))).toBe('Line3D(Point3D(1, 1, 1), Point3D(3, 4, 5))');
    expect(s(Ray3D([1, 1, 1], { directionRatio: Tuple(2, 3, 4) }))).toBe('Ray3D(Point3D(1, 1, 1), Point3D(3, 4, 5))');
    expect(() => Segment([0, 0], [2, 2]).contains(Point(new Sym('u'), new Sym('u')))).toThrow(Undecidable);
    expect(() => Segment([0, 0], [0, 2]).contains(Point(0, new Sym('u')))).toThrow(Undecidable);
    expect(() => Line3D([0, 0, 0], [1, 0, 0]).distance([Point(1, 2), 1, 2])).toThrow(TypeError);
    // SymPy Point(Line2D, dim=3): TypeError
    expect(() => Line3D(Line([0, 0], [1, 1]))).toThrow(TypeError);
    // SymPy Point3D((1, 2, 3, 4)) raises ValueError, then the tuple is not a supported entity
    expect(() => Line3D([0, 0, 0], [1, 0, 0]).distance([1, 2, 3, 4])).toThrow('which is unsupported');
    expect(s(Line([0, 0], [1, 0]).bisectors(Line3D([0, 0, 0], [0, 0, 1])))).toBe('[Line3D(Point3D(0, 0, 0), Point3D(1, 0, 1)), Line3D(Point3D(0, 0, 0), Point3D(-1, 0, 1))]');
    // SymPy Ray((0, 0), angle=pi*x) simplifies the conditions to x > 1/2, x < 3/2, Eq(x, 1/2), Eq(x, 3/2)
    // (Relational._eval_simplify), which symjs's simplify keeps as 1 < 2*x, ...
    expect(s(Ray([0, 0], { angle: pi.mul(x) }))).toBe('Ray2D(Point2D(0, 0), Point2D(Piecewise((-1, (1 < 2*x) & (2*x < 3)), (Piecewise((0, Eq(Mod(2*x, 1), 0)), (1, True)), True)), Piecewise((-tan(pi*x), (1 < 2*x) & (2*x < 3)), (Piecewise((1, Eq(2*x, 1)), (-1, Eq(2*x, 3)), (tan(pi*x), True)), True))))');
    expect(s(Ray([1, 1], { angle: pi.mul(new Float(3)) }))).toBe(s(Ray([1, 1], [0, 1])));
    expect(s(Ray([1, 1], { angle: pi.mul(3).div(2) }))).toBe(s(Ray([1, 1], [1, 0])));
    // SymPy: Ray2D(Point2D(1, 1), Point2D(Piecewise((0, (n > 1/2) & (n < 3/2)), (1, True)), 1)); symjs keeps tan(pi*n)
    // (0 for an integer n) and the unsimplified conditions
    const rn = Ray([1, 1], { angle: pi.mul(new Sym('n', { integer: true })) });
    expect(s(rn.p2.coordinate(0))).toBe('Piecewise((-1, (1 < 2*n) & (2*n < 3)), (0, True)) + 1');
  });

  it('raises like SymPy (test_raises)', () => {
    const [d, e] = [real('a'), real('b')];
    const sg = Segment([d, 0], [e, 0]);
    expect(() => Line([1, 1], 1 as never)).toThrow(TypeError);
    expect(() => Line(Point(0, 0), Point(0, 0))).toThrow('Line2D.__new__ requires two unique Points.');
    expect(() => sg.contains(Point(d.mul(2), 0))).toThrow(Undecidable);
    expect(() => Ray3D(Point(1.0, 1.0))).toThrow(RangeError);
    expect(() => Line3D(Point3D(0, 0, 0), Point3D(0, 0, 0))).toThrow(RangeError);
    expect(() => Line3D([1, 1], 1 as never)).toThrow(TypeError);
    expect(() => Line3D(Point3D(0, 0, 0))).toThrow('A 2nd Point or keyword "direction_ratio" must be used.');
    expect(() => Ray([1, 1], 1 as never)).toThrow(TypeError);
    expect(() => Line(Point(0, 0), Point(1, 0)).projection(Circle(Point(0, 0), 1))).toThrow(GeometryError);
    expect(() => Line()).toThrow(TypeError);
    expect(() => Line(Point(1, 2, 3, 4))).toThrow('Line requires two points.');
    expect(() => Ray(Point(1, 2, 3, 4))).toThrow('Ray requires two points.');
    expect(() => Line(Line([0, 0], [1, 1]), [1, 2])).toThrow('If p1 is a LinearEntity, p2 must be None.');
    expect(() => Line2D(Line([0, 0], [1, 1]), [1, 2])).toThrow('When p1 is a LinearEntity, pt should be None');
    expect(() => Line2D([0, 0], [1, 2, 3])).toThrow('The 2nd argument was not a valid Point. If it was a slope, enter it with keyword "slope".');
    expect(() => Line2D([0, 0])).toThrow('A 2nd Point or keyword "slope" must be used.');
    expect(() => Line3D(Line3D([0, 0, 0], [1, 1, 1]), [1, 2, 3])).toThrow('if p1 is a LinearEntity, pt must be None.');
    expect(() => Ray3D(Line3D([0, 0, 0], [1, 1, 1]), [1, 2, 3])).toThrow('If p1 is a LinearEntity, pt must be None');
    expect(() => Ray2D([0, 0], [1, 2, 3])).toThrow('it should be given with keyword "angle"');
    expect(() => Ray2D([0, 0], [0, 0])).toThrow('A Ray requires two distinct points.');
    expect(() => Ray2D([0, 0])).toThrow('A 2nd point or keyword "angle" must be used.');
    expect(() => Line([0, 0], [1, 1]).bisectors(Point(1, 1) as never)).toThrow(GeometryError);
    expect(() => Line([0, 0], [1, 1]).bisectors(Line([0, 1], [1, 2]))).toThrow('The lines do not intersect');
  });

  it('rays by angle (SymPy test_ray_generation)', () => {
    const r = (angle: unknown): string => s(Ray([1, 1], { angle: angle as Expr }));
    expect(r(pi.div(4))).toBe(s(Ray([1, 1], [2, 2])));
    expect(r(pi.div(2))).toBe(s(Ray([1, 1], [1, 2])));
    expect(r(pi.div(-2))).toBe(s(Ray([1, 1], [1, 0])));
    expect(r(pi.mul(-3).div(2))).toBe(s(Ray([1, 1], [1, 2])));
    expect(r(pi.mul(5).div(2))).toBe(s(Ray([1, 1], [1, 2])));
    expect(r(pi.mul(2.5))).toBe(s(Ray([1, 1], [1, 2])));
    expect(r(pi)).toBe(s(Ray([1, 1], [0, 1])));
    expect(r(pi.mul(3.0))).toBe(s(Ray([1, 1], [0, 1])));
    expect(r(pi.mul(4.0))).toBe(s(Ray([1, 1], [2, 1])));
    expect(r(0)).toBe(s(Ray([1, 1], [2, 1])));
    // SymPy: Point2D(2, -sqrt(5)*sqrt(2*sqrt(5) + 10)/4 - sqrt(2*sqrt(5) + 10)/4 + 2 + sqrt(5)), the same number 1 + tan(pi/20)
    const r405 = Ray([1, 1], { angle: pi.mul(4.05) });
    expect(s(r405.p2.coordinate(0))).toBe('2');
    expect(r405.p2.coordinate(1).toNumber()).toBeCloseTo(1 + Math.tan(Math.PI / 20), 14);
    expect(r(pi.mul(4.02))).toBe(s(Ray(Point(1, 1), Point(2, tan(pi.mul(4.02)).add(1)))));
    expect(r(5)).toBe(s(Ray([1, 1], [2, tan(5).add(1)])));
    const ra = Ray([0, 0], { angle: x });
    expect(s(ra.subs(x, pi.mul(3).div(4)))).toBe(s(Ray([0, 0], [-1, 1])));
    expect(s(ra.subs(x, pi.mul(5).div(4)))).toBe(s(Ray([0, 0], [-1, -1])));
    expect(s(ra.subs(x, pi.div(-4)))).toBe(s(Ray([0, 0], [1, -1])));
    expect(s(ra.subs(x, pi.div(2)))).toBe(s(Ray([0, 0], [0, 1])));
    expect(s(ra.subs(x, pi.div(-2)))).toBe(s(Ray([0, 0], [0, -1])));
  });
});

describe('basic properties (SymPy test_basic_properties_2d/3d)', () => {
  const p1 = Point(0, 0);
  const p2 = Point(1, 1);
  const p10 = Point(2000, 2000);
  const l1 = Line(p1, p2);
  const l3 = Line(Point(x1, x1), Point(x1, x1.add(1)));
  const l4 = Line(p1, Point(1, 0));
  const r1 = Ray(p1, Point(0, 1));
  const r2 = Ray(Point(0, 1), p1);
  const s1 = Segment(p1, p10) as Segment2DNode;

  it('2D', () => {
    expect(s(Line(p1, p2).scale(2, 1))).toBe(s(Line(p1, Point(2, 1))));
    expect(l1.key === Line(p2, p1).key).toBe(false);
    expect(l1.contains(p1)).toBe(true);
    expect(l3.contains(p1)).toBe(false);
    expect(Line(p1, p10).contains(s1)).toBe(true);
    expect(Ray(Point(0, 0), Point(0, 2)).contains(Ray(Point(0, 0), Point(0, 1)))).toBe(true);
    expect(s((Ray(Point(0, 0), Point(0, 2)) as Ray2DNode).xdirection)).toBe('0');
    expect(s((Ray(Point(0, 0), Point(1, 2)) as Ray2DNode).xdirection)).toBe('oo');
    expect(s((Ray(Point(0, 0), Point(-1, 2)) as Ray2DNode).xdirection)).toBe('-oo');
    expect(s((Ray(Point(0, 0), Point(2, 0)) as Ray2DNode).ydirection)).toBe('0');
    expect(s((Ray(Point(0, 0), Point(2, 2)) as Ray2DNode).ydirection)).toBe('oo');
    expect(s((Ray(Point(0, 0), Point(2, -2)) as Ray2DNode).ydirection)).toBe('-oo');
    expect(s1.contains(r1)).toBe(false);
    expect(s1.contains(Segment(p1, p2))).toBe(true);
    expect(s((Segment(p1, p2) as Segment2DNode).midpoint)).toBe('Point2D(1/2, 1/2)');
    expect(s((Segment(p1, Point(x1.neg(), x1)) as Segment2DNode).length)).toBe('sqrt(2)*Abs(x1)');
    expect(s(l2d(l1).slope)).toBe('1');
    expect(s(l2d(l3).slope)).toBe('oo');
    expect(s(l2d(l4).slope)).toBe('0');
    expect(s((r1 as Ray2DNode).slope)).toBe('oo');
    expect(s(s1.slope)).toBe('1');
    expect(s(l2d(l4).coefficients)).toBe('[0, 1, 0]');
    expect(s(l2d(Line([x.neg(), x], [x.neg().add(1), x.add(-1)])).coefficients)).toBe('[1, 1, 0]');
    expect(s(l2d(Line(p1, Point(0, 1))).coefficients)).toBe('[1, 0, 0]');
    expect(s(l2d(Line(p1, Point(1, 2))).coefficients)).toBe('[-2, 1, 0]');
    expect(s(s1.plotInterval())).toBe('[t, 0, 1]');
    expect(s(Line(p1, p10).plotInterval())).toBe('[t, -5, 5]');
    expect(s(Ray([0, 0], { angle: pi.div(4) }).plotInterval('u'))).toBe('[u, 0, 10]');
    expect(s(s1.bounds)).toBe('[0, 0, 2000, 2000]');
    expect(s((r2 as Ray2DNode).bounds)).toBe('[0, 0, 0, 1]');
    expect(s(l1.length)).toBe('oo');
    expect(s(l1.points)).toBe('[Point2D(0, 0), Point2D(1, 1)]');
    expect(s(l1.direction)).toBe('Point2D(1, 1)');
    expect(l1.ambientDimension).toBe(2);
    expect(s((r1 as Ray2DNode).source)).toBe('Point2D(0, 0)');
    // random points with a seed (SymPy random_point(seed=...), Python's Mersenne Twister)
    expect(s(Ray(p1, p2).randomPoint(42).n(3))).toBe('Point2D(0.144, 0.144)');
    expect(s((Segment(p1, p2) as SegmentNode).randomPoint(42).n(3))).toBe('Point2D(0.639, 0.639)');
    expect(s(Line(p1, p2).randomPoint(42).n(3))).toBe('Point2D(-0.144, -0.144)');
    expect(l3.contains(l3.randomPoint())).toBe(true);
  });

  it('3D', () => {
    const q1 = Point3D(0, 0, 0);
    const q2 = Point3D(1, 1, 1);
    const L1 = Line3D(q1, q2);
    expect(s(Line3D(q1, Point3D(1, 0, 0)).directionCosine)).toBe('[1, 0, 0]');
    expect(s(L1.directionRatio)).toBe('[1, 1, 1]');
    expect(s(Ray3D(q1, q2).directionRatio)).toBe('[1, 1, 1]');
    expect(s(Ray3D(q1, q2).directionCosine)).toBe('[sqrt(3)/3, sqrt(3)/3, sqrt(3)/3]');
    expect(s((Segment3D(q1, q2) as LinearEntity & { directionRatio: Expr[] }).directionRatio)).toBe('[1, 1, 1]');
    expect(s((Segment3D(q1, q2) as LinearEntity & { directionCosine: Expr[] }).directionCosine)).toBe('[sqrt(3)/3, sqrt(3)/3, sqrt(3)/3]');
    expect(Ray3D(Point3D(0, 0, 0), Point3D(2, 2, 2)).contains(Ray3D(Point3D(0, 0, 0), Point3D(1, 1, 1)))).toBe(true);
    const r = (a: number[], b: number[]) => Ray3D(a, b);
    expect([r([0, 0, 0], [2, 2, 2]).xdirection, r([0, 0, 0], [2, 2, 2]).ydirection, r([0, 0, 0], [2, 2, 2]).zdirection].map(s)).toEqual(['oo', 'oo', 'oo']);
    expect([r([0, 0, 0], [-2, 2, 2]).xdirection, r([0, 0, 0], [2, -2, 2]).ydirection, r([0, 0, 0], [2, 2, -2]).zdirection].map(s)).toEqual(['-oo', '-oo', '-oo']);
    expect([r([0, 0, 0], [0, 2, 2]).xdirection, r([0, 0, 0], [2, 0, 2]).ydirection, r([0, 0, 0], [2, 2, 0]).zdirection].map(s)).toEqual(['0', '0', '0']);
    expect(s((Segment3D(q1, q2) as SegmentNode).midpoint)).toBe('Point3D(1/2, 1/2, 1/2)');
    expect(s(Line3D([0, 0, 0], [1, 1, 1]).length)).toBe('oo');
  });
});

describe('contains, distance and equals', () => {
  it('contains (SymPy test_contains)', () => {
    const [a, b] = [real('a'), real('b')];
    const p1 = Point(0, 0);
    const r = Ray(p1, Point(4, 4));
    const r1 = Ray3D(p1, Point3D(0, 0, -1));
    const r3 = Ray3D(p1, Point3D(0, 0, 1));
    const l = Line(Point(0, 1), Point(3, 4));
    expect(Segment([0, a], [0, b]).contains(Point(0, a.add(b).div(2)))).toBe(true);
    expect(Segment([a, 0], [b, 0]).contains(Point(a.add(b).div(2), 0))).toBe(true);
    expect(Segment3D([0, 0, 0], [1, 0, 0]).contains([])).toBe(true);
    expect(Segment3D(Point3D(0, 0, 0), Point3D(1, 0, 0)).contains(Segment3D(Point3D(2, 2, 2), Point3D(3, 2, 2)))).toBe(false);
    expect(l.contains(Point(0, 1))).toBe(true);
    expect(l.contains([0, 1])).toBe(true);
    expect(l.contains([0, 0])).toBe(false);
    expect(l.contains(Circle([0, 0], 1))).toBe(false);
    expect(r.contains(p1)).toBe(true);
    expect(r.contains([1, 1])).toBe(true);
    expect(r.contains([1, 3])).toBe(false);
    expect(r.contains(Segment([1, 1], [2, 2]))).toBe(true);
    expect(r.contains(Segment([1, 2], [2, 5]))).toBe(false);
    expect(r.contains(Ray([2, 2], [3, 3]))).toBe(true);
    expect(r.contains(Ray([2, 2], [3, 5]))).toBe(false);
    expect(r.contains(Line([0, 0], [1, 1]))).toBe(false);
    expect(r1.contains(Segment3D(p1, Point3D(0, 0, -10)))).toBe(true);
    expect(r1.contains(Segment3D(Point3D(1, 1, 1), Point3D(2, 2, 2)))).toBe(false);
    expect(r3.contains(Point3D(0, 0, 0))).toBe(true);
    expect(Line3D([0, 0, 0], [x, y, z]).contains([x.mul(2), y.mul(2), z.mul(2)])).toBe(true);
    expect(Line3D(p1, Point3D(0, 1, 0)).contains(Point(1.0, 1.0))).toBe(false);
    expect(r3.contains(Point(1.0, 1.0))).toBe(false);
    const [u, v, w, zz] = symbols('u v w z') as [Sym, Sym, Sym, Sym];
    expect(Segment(Point(u, w), Point(v, zz)).contains(Point(u.mul(Rational.of(2n, 3n)).add(v.div(3)), w.mul(Rational.of(2n, 3n)).add(zz.div(3))))).toBe(true);
    // SymPy test_line_intersection
    const x0 = tan(pi.mul(Rational.of(13n, 45n)));
    const xs = sqrt(3);
    const x2 = x0.pow(2);
    const px = x0.mul(8).div(x0.add(xs));
    const py = x0.mul(24).sub(xs.mul(x2).mul(8)).div(x2.sub(3));
    expect(Line(Point(0, 0), Point(1, sqrt(3).neg())).contains(Point(px, py))).toBe(true);
    expect(Segment(Point(0, 0), Point(1, 1)).contains(Point(1, 1))).toBe(true);
    expect(Segment(Point(0, 0), Point(0, 1)).contains(Point(0, 2))).toBe(false);
    expect(Segment(Point(0, 0), Point(1, 2, 3, 4)).contains(Point(2, 4, 6, 8))).toBe(false);
    expect(Segment(Point(0, 0, 0, 0), Point(1, 2, 3, 4)).contains(Point(Rational.of(1n, 2n), 1, Rational.of(3n, 2n), 2))).toBe(true);
    expect(Segment(Point(0, 0), Point(x, 0)).contains(Point(x.div(2), 0))).toBe(true);
    expect(Segment(Point(0, 0), Point(0, x)).contains(Point(0, x.div(2)))).toBe(true);
  });

  it('distances (SymPy test_distance_2d/3d)', () => {
    const p1 = Point(0, 0);
    const p2 = Point(1, 1);
    const s1 = Segment(Point(0, 0), Point(1, 1));
    const s2 = Segment(Point(half, half), Point(1, 0));
    const r = Ray(p1, p2);
    expect(s(s1.distance(Point(0, 0)))).toBe('0');
    expect(s(s1.distance([0, 0]))).toBe('0');
    expect(s(s2.distance(Point(0, 0)))).toBe('sqrt(2)/2');
    expect(s(s2.distance(Point(Rational.of(3n, 2n), Rational.of(3n, 2n))))).toBe('sqrt(2)');
    expect(s(Segment([0, 0], [1, 1]).distance(Point(-1, -1)))).toBe('sqrt(2)');
    expect(s(Segment([0, 0], [1, 1]).distance(Point(3, 3)))).toBe('2*sqrt(2)');
    expect(s(Line(p1, p2).distance(Point(-1, 1)))).toBe('sqrt(2)');
    expect(s(Line(p1, p2).distance(Point(2, 2)))).toBe('0');
    expect(s(Line(p1, p2).distance([-1, 1]))).toBe('sqrt(2)');
    expect(s(Line([0, 0], [0, 1]).distance(p2))).toBe('1');
    expect(s(r.distance(Point(-1, -1)))).toBe('sqrt(2)');
    expect(s(r.distance(Point(1, 1)))).toBe('0');
    expect(s(r.distance(Point(-1, 1)))).toBe('sqrt(2)');
    expect(s(Ray([1, 1], [2, 2]).distance(Point(1.5, 3)))).toBe('3*sqrt(2)/4');
    expect(s(r.distance([1, 1]))).toBe('0');
    const q1 = Point3D(0, 0, 0);
    const q2 = Point3D(1, 1, 1);
    const q3 = Point3D(Rational.of(3n, 2n), Rational.of(3n, 2n), Rational.of(3n, 2n));
    const t2 = Segment3D(Point3D(half, half, half), Point3D(1, 0, 1));
    expect(s(t2.distance(q1))).toBe('sqrt(3)/2');
    expect(s(t2.distance(q3))).toBe('2*sqrt(6)/3');
    expect(s(t2.distance([0, 0, 0]))).toBe('sqrt(3)/2');
    expect(s(Line3D(q1, q2).distance(Point3D(-1, 1, 1)))).toBe('2*sqrt(6)/3');
    expect(s(Line3D(q1, q2).distance([2, 2, 2]))).toBe('0');
    expect(s(Line3D(q1, q2).distance([1, -1, 1]))).toBe('2*sqrt(6)/3');
    expect(s(Line3D([0, 0, 0], [0, 1, 0]).distance(q2))).toBe('sqrt(2)');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Line3D([0, 0, 0], [0, 1, 2])))).toBe('0');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Line3D([0, 0, 0], [1, 0, 0])))).toBe('0');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Line3D([10, 0, 0], [10, 1, 2])))).toBe('0');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Line3D([0, 1, 0], [0, 1, 1])))).toBe('1');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Line3D([0, 1, 0], [1, 1, 0])))).toBe('1');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Plane([2, 0, 0], { normalVector: [0, 0, 1] })))).toBe('0');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance(Plane([0, 1, 0], { normalVector: [0, 1, 0] })))).toBe('1');
    expect(() => Line3D([0, 0, 0], [1, 0, 0]).distance(Circle([0, 0], 1))).toThrow('which is unsupported');
    expect(s(Line3D([0, 0, 0], [1, 0, 0]).distance([1, 2]))).toBe('2');
    expect(s(Ray3D([0, 0, 0], [1, 1, 2]).distance([-1, -1, 2]))).toBe('4*sqrt(3)/3');
    expect(s(Ray3D([1, 1, 1], [2, 2, 2]).distance(Point3D(1.5, -3, -1)))).toBe('9/2');
    expect(s(Ray3D([1, 1, 1], [2, 2, 2]).distance(Point3D(1.5, 3, 1)))).toBe('sqrt(78)/6');
    expect(() => Segment([0, 0], [1, 1]).distance(Line([0, 1], [1, 2]))).toThrow('distance between a Segment and Line2D');
  });

  it('equals (SymPy test_equals)', () => {
    const p1 = Point(0, 0);
    const p2 = Point(1, 1);
    const l1 = Line(p1, p2);
    const l2 = Line([0, 5], { slope: m });
    const l3 = Line(Point(x1, x1), Point(x1, x1.add(1)));
    expect(l1.perpendicularLine(p1.args).equals(Line(Point(0, 0), Point(1, -1)))).toBe(true);
    expect(Line(Point(x1, x1), Point(y1, y1)).parallelLine(Point(x1.neg(), x1)).equals(Line(Point(x1.neg(), x1), Point(y1.neg(), x1.mul(2).sub(y1))))).toBe(true);
    expect(l3.parallelLine(p1).equals(Line(Point(0, 0), Point(0, -1)))).toBe(true);
    // SymPy: sqrt((3 - (3*m**2 + 2*m + 5)/(m**2 + 1))**2 + (-2*(1 - m)/(m**2 + 1) + 2)**2), equal to 2*Abs(m + 1)/sqrt(m**2 + 1)
    expect(l2.distance(Point(2, 3)).subs(m, Rational.of(3n, 10n)).toNumber()).toBeCloseTo((2 * 1.3) / Math.sqrt(1.09), 12);
    expect(Line3D(p1, Point3D(0, 1, 0)).equals(Point(1.0, 1.0))).toBe(false);
    expect(Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0)).equals(Line3D(Point3D(-5, 0, 0), Point3D(-1, 0, 0)))).toBe(true);
    expect(Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0)).equals(Line3D(p1, Point3D(0, 1, 0)))).toBe(false);
    expect(Ray3D(p1, Point3D(0, 0, -1)).equals(Point(1.0, 1.0))).toBe(false);
    expect(Ray3D(p1, Point3D(0, 0, -1)).equals(Ray3D(p1, Point3D(0, 0, -1)))).toBe(true);
    expect(Line3D([0, 0], [t, t]).perpendicularLine(Point(0, 1, 0)).equals(Line3D(Point3D(0, 1, 0), Point3D(half, half, 0)))).toBe(true);
    expect(Line3D([0, 0], [t, t]).perpendicularSegment(Point(0, 1, 0)).equals(Segment3D([0, 1], [half, half]))).toBe(true);
    expect(Segment([0, 0], [1, 1]).equals(Segment([1, 1], [0, 0]))).toBe(true);
    expect(Segment([0, 0], [1, 1]).equals(Line([1, 1], [0, 0]))).toBe(false);
    expect(Segment([0, 0], [1, 1]).equals(Segment([1, 1], [0, 2]))).toBe(false);
  });

  it('equations (SymPy test_equation)', () => {
    const p1 = Point(0, 0);
    const p2 = Point(1, 1);
    expect(s(simplify(l2d(Line(p1, p2)).equation()))).toBe('-x + y');
    expect(s(l2d(Line(Point(x1, x1), Point(x1, x1.add(1)))).equation())).toBe('x - x1');
    expect(s(l2d(Line(p1, Point(1, 0))).equation(x, y))).toBe('y');
    expect(s(l2d(Line(p1, Point(0, 1))).equation())).toBe('x');
    expect(s(l2d(Line(Point(2, 0), Point(2, 1))).equation())).toBe('x - 2');
    expect(s(l2d(Line(p2, Point(2, 1))).equation())).toBe('y - 1');
    expect(s(Line3D(Point(x1, x1, x1), Point(y1, y1, y1)).equation())).toBe('(-x + y, -x + z)');
    expect(s(Line3D(Point(1, 2, 3), Point(2, 3, 4)).equation())).toBe('(-x + y - 1, -x + z - 2)');
    expect(s(Line3D(Point(1, 2, 3), Point(1, 3, 4)).equation())).toBe('(x - 1, -y + z - 1)');
    expect(s(Line3D(Point(1, 2, 3), Point(2, 2, 4)).equation())).toBe('(y - 2, -x + z - 2)');
    expect(s(Line3D(Point(1, 2, 3), Point(2, 3, 3)).equation())).toBe('(-x + y - 1, z - 3)');
    expect(s(Line3D(Point(1, 2, 3), Point(1, 2, 4)).equation())).toBe('(x - 1, y - 2)');
    expect(s(Line3D(Point(1, 2, 3), Point(1, 3, 3)).equation())).toBe('(x - 1, z - 3)');
    expect(s(Line3D(Point(1, 2, 3), Point(2, 2, 3)).equation())).toBe('(y - 2, z - 3)');
  });
});

describe('intersection (SymPy test_intersection_2d/3d)', () => {
  const p1 = Point(0, 0);
  const p2 = Point(1, 1);
  const l1 = Line(p1, p2);
  const l3 = Line(Point(0, 0), Point(3, 4));
  const r1 = Ray(Point(1, 1), Point(2, 2));
  const r2 = Ray(Point(0, 0), Point(3, 4));
  const r4 = Ray(p1, p2);
  const r6 = Ray(Point(0, 1), Point(1, 2));
  const r7 = Ray(Point(0.5, 0.5), Point(1, 1));
  const s1 = Segment(p1, p2);
  const s2 = Segment(Point(0.25, 0.25), Point(0.5, 0.5));
  const s3 = Segment(Point(0, 0), Point(3, 4));

  it('2D', () => {
    const i = (a: unknown, b: unknown): string => s(intersection(a as GeometryEntity, b as GeometryEntity));
    expect(i(l1, p1)).toBe('[Point2D(0, 0)]');
    expect(i(l1, Point(x1, x1.add(1)))).toBe('[]');
    expect(i(l1, Line(Point(x1, x1), Point(y1, y1)))).toBe(s([Line(Point(x1, x1), Point(y1, y1))]));
    expect(i(l1, l1.parallelLine(Point(x1, x1.add(1))))).toBe('[]');
    expect(i(l3, l3)).toBe(s([l3]));
    expect(i(l3, r2)).toBe(s([r2]));
    expect(i(l3, s3)).toBe(s([s3]));
    expect(i(s3, l3)).toBe(s([s3]));
    expect(i(Segment(Point(-10, 10), Point(10, 10)), Segment(Point(-5, -5), Point(-5, 5)))).toBe('[]');
    expect(i(r2, l3)).toBe(s([r2]));
    expect(i(r1, Ray(Point(2, 2), Point(0, 0)))).toBe('[Segment2D(Point2D(1, 1), Point2D(2, 2))]');
    expect(i(r1, Ray(Point(1, 1), Point(-1, -1)))).toBe('[Point2D(1, 1)]');
    expect(i(r1, Ray(Point(3, 3), Point(4, 4)))).toBe('[Ray2D(Point2D(3, 3), Point2D(4, 4))]');
    expect(i(Ray(Point(3, 3), Point(4, 4)), r1)).toBe('[Ray2D(Point2D(3, 3), Point2D(4, 4))]');
    expect(i(Ray(Point(0, 0), Point(-1, -1)), r1)).toBe('[]');
    expect(i(r1, Segment(Point(0, 0), Point(2, 2)))).toBe('[Segment2D(Point2D(1, 1), Point2D(2, 2))]');
    expect(s(r4.intersection(s2))).toBe(s([s2]));
    expect(s(r4.intersection(Segment(Point(2, 3), Point(3, 4))))).toBe('[]');
    expect(s(r4.intersection(Segment(Point(-1, -1), Point(0.5, 0.5))))).toBe('[Segment2D(Point2D(0, 0), Point2D(1/2, 1/2))]');
    expect(s(r4.intersection(Segment(Point(0.5, 0.5), Point(-1, -1))))).toBe('[Segment2D(Point2D(0, 0), Point2D(1/2, 1/2))]');
    expect(s(r4.intersection(Segment(Point(-1, -1), Point(-2, -2))))).toBe('[]');
    expect(s(r4.intersection(Ray(p2, p1)))).toBe(s([s1]));
    expect(s(Ray(p2, p1).intersection(r6))).toBe('[]');
    expect(s(r4.intersection(r7))).toBe(s([r7]));
    expect(s(r7.intersection(r4))).toBe(s([r7]));
    expect(s(Ray(Point(0, 0), Point(0, 4)).intersection(Ray(Point(0, 1), Point(0, -1))))).toBe('[Segment2D(Point2D(0, 0), Point2D(0, 1))]');
    expect(s(Ray(Point(0, 0), Point(0, 4)).intersection(Ray(Point(0, 0), Point(0, -1))))).toBe('[Point2D(0, 0)]');
    expect(s(s1.intersection(Segment(Point(1, 1), Point(2, 2))))).toBe('[Point2D(1, 1)]');
    expect(s(s1.intersection(Segment(Point(0.5, 0.5), Point(1.5, 1.5))))).toBe('[Segment2D(Point2D(1/2, 1/2), Point2D(1, 1))]');
    expect(s(s1.intersection(Segment(Point(1.5, 1.5), Point(0.5, 0.5))))).toBe('[Segment2D(Point2D(1/2, 1/2), Point2D(1, 1))]');
    expect(s(s1.intersection(Segment(Point(4, 4), Point(5, 5))))).toBe('[]');
    expect(s(s1.intersection(Segment(Point(-1, -1), p1)))).toBe('[Point2D(0, 0)]');
    expect(s(s1.intersection(Line(Point(1, 0), Point(2, 1))))).toBe('[]');
    expect(s(s1.intersection(s2))).toBe(s([s2]));
    expect(s(s2.intersection(s1))).toBe(s([s2]));
    expect(s(Line([0, 0], [1, 1]).intersection(Ray([1, 0], [1, 2])))).toBe('[Point2D(1, 1)]');
    expect(s(Line([0, 0], [1, 1]).intersection(Segment([1, 0], [1, 2])))).toBe('[Point2D(1, 1)]');
    expect(s(Ray([0, 0], [1, 1]).intersection(Ray([1, 0], [1, 2])))).toBe('[Point2D(1, 1)]');
    expect(s(Ray([0, 0], [1, 1]).intersection(Segment([1, 0], [1, 2])))).toBe('[Point2D(1, 1)]');
    expect(s(Segment([0, 0], [1, 1]).intersection(Segment([3, 0], [3, 2])))).toBe('[]');
    expect(s(s1.intersection(Ray([1, 1], [4, 4])))).toBe('[Point2D(1, 1)]');
    expect(s(l1.intersection([1, 1]))).toBe('[Point2D(1, 1)]');
    expect(s(l1.intersection(Line([0, 1], [1, 0])))).toBe('[Point2D(1/2, 1/2)]');
    expect(s(l1.intersection(Circle([0, 0], 1)))).toBe('[Point2D(-sqrt(2)/2, -sqrt(2)/2), Point2D(sqrt(2)/2, sqrt(2)/2)]');
    expect(s(Line([0, 0, 0, 0], [1, 1, 1, 1]).intersection(Line([0, 0, 0, 1], [1, 1, 1, 0])))).toBe('[Point(1/2, 1/2, 1/2, 1/2)]');
    expect(s(Line([0, 0, 0, 0], [1, 0, 0, 0]).intersection(Line([0, 1, 0, 0], [0, 0, 1, 0])))).toBe('[]');
    // SymPy test_issue_7814
    const [k] = [real('k')];
    const circle = Circle(Point(x, 0), y);
    const line = Line(Point(k, z), { slope: 0 });
    expect(s(line.intersection(circle))).toBe('[Point2D(x + sqrt((y - z)*(y + z)), z), Point2D(x - sqrt((y - z)*(y + z)), z)]');
    // SymPy test_issue_12598: Float coordinates
    const ra = Ray(Point(0, 1), Point(0.98, 0.79).n(2) as never);
    const rb = Ray(Point(0, 0), Point(0.71, 0.71).n(2) as never);
    expect(s(at0(ra.intersection(rb)))).toBe('Point2D(0.82, 0.82)');
    expect(s(at0(Line([0, 0], [1, 1]).intersection(Segment([-1, 1], [0, -1]).n(2))))).toBe('Point2D(-0.33, -0.33)');
    expect(s(Line([0, 0], [1, 1]).intersection(Segment([-1, 1], [-0.5, 0.5]).n(2)))).toBe('[]');
    expect(s(Ray(Point(0, 1), Point(0.5, 0.5)).intersection(Ray(Point(0, 0), Point(-0.5, -0.5))))).toBe('[]');
  });

  it('commutes for lines, rays and segments (SymPy test_issue_2941)', () => {
    const makers = [Line, Ray, Segment] as unknown as ((a: number[], b: number[]) => LinearEntity)[];
    for (const [c, d] of [
      [
        [-2, -2],
        [-2, 0],
      ],
      [
        [-2, -3],
        [-2, 0],
      ],
    ]) {
      for (const f of makers) {
        for (const g of makers) {
          const a1 = f([0, 0], [1, 1]);
          const a2 = g(c as number[], d as number[]);
          expect(s(a1.intersection(a2))).toBe(s(a2.intersection(a1)));
        }
      }
    }
  });

  it('3D', () => {
    const q1 = Point3D(0, 0, 0);
    const q2 = Point3D(1, 1, 1);
    const L1 = Line3D(q1, q2);
    const L2 = Line3D(Point3D(0, 0, 0), Point3D(3, 4, 0));
    const R1 = Ray3D(Point3D(1, 1, 1), Point3D(2, 2, 2));
    const R2 = Ray3D(Point3D(0, 0, 0), Point3D(3, 4, 0));
    const S1 = Segment3D(Point3D(0, 0, 0), Point3D(3, 4, 0));
    expect(s(intersection(L1, q1))).toBe('[Point3D(0, 0, 0)]');
    expect(s(intersection(L1, Point3D(x1, x1.add(1), 1)))).toBe('[]');
    expect(s(intersection(L1, L1.parallelLine(q1)))).toBe('[Line3D(Point3D(0, 0, 0), Point3D(1, 1, 1))]');
    expect(s(intersection(L2, R2))).toBe(s([R2]));
    expect(s(intersection(L2, S1))).toBe(s([S1]));
    expect(s(intersection(R1, Ray3D(Point3D(1, 1, 1), Point3D(-1, -1, -1))))).toBe('[Point3D(1, 1, 1)]');
    expect(s(intersection(R1, Segment3D(Point3D(0, 0, 0), Point3D(2, 2, 2))))).toBe('[Segment3D(Point3D(1, 1, 1), Point3D(2, 2, 2))]');
    expect(s(intersection(Ray3D(Point3D(1, 0, 0), Point3D(-1, 0, 0)), Ray3D(Point3D(0, 1, 0), Point3D(0, -1, 0))))).toBe('[Point3D(0, 0, 0)]');
    expect(s(Line3D(Point3D(4, 0, 1), Point3D(0, 4, 1)).intersection(Line3D(Point3D(0, 0, 1), Point3D(4, 4, 1))))).toBe('[Point3D(2, 2, 1)]');
    expect(s(Line3D([0, 1, 2], [0, 2, 3]).intersection(Line3D([0, 1, 2], [0, 1, 1])))).toBe('[Point3D(0, 1, 2)]');
    expect(s(Line3D([0, 0], [t, t]).intersection(Line3D([0, 1], [t, t])))).toBe('[Point3D(t, t, 0)]');
    expect(s(Ray3D(Point3D(0, 0, 0), Point3D(0, 4, 0)).intersection(Ray3D(Point3D(0, 1, 1), Point3D(0, -1, 1))))).toBe('[]');
    expect(s(Segment3D([0, 0], [3, 0]).intersection(Segment3D([1, 0], [2, 0])))).toBe('[Segment3D(Point3D(1, 0, 0), Point3D(2, 0, 0))]');
    expect(s(Segment3D([1, 0], [2, 0]).intersection(Segment3D([0, 0], [3, 0])))).toBe('[Segment3D(Point3D(1, 0, 0), Point3D(2, 0, 0))]');
    expect(s(Segment3D([0, 0], [3, 0]).intersection(Segment3D([3, 0], [4, 0])))).toBe('[Point3D(3, 0, 0)]');
    expect(s(Segment3D([0, 0], [3, 0]).intersection(Segment3D([2, 0], [5, 0])))).toBe('[Segment3D(Point3D(2, 0, 0), Point3D(3, 0, 0))]');
    expect(s(Segment3D([0, 0], [3, 0]).intersection(Segment3D([-2, 0], [1, 0])))).toBe('[Segment3D(Point3D(0, 0, 0), Point3D(1, 0, 0))]');
    expect(s(Segment3D([0, 0], [3, 0]).intersection(Segment3D([-2, 0], [0, 0])))).toBe('[Point3D(0, 0, 0)]');
    expect(s(Segment3D([0, 0], [3, 0]).intersection(Segment3D([4, 0], [5, 0])))).toBe('[]');
    expect(s(Ray3D([0, 0], [3, 0]).intersection(Ray3D([1, 0], [3, 0])))).toBe('[Ray3D(Point3D(1, 0, 0), Point3D(3, 0, 0))]');
    expect(s(Line3D(Point3D(6, 5, 0), Point3D(6, -6, 0)).intersection(Line3D(Point3D(6, -1, 1.9), Point3D(6, -1, 0))))).toBe('[Point3D(6, -1, 0)]');
  });

  it('areConcurrent (SymPy test_are_concurrent_2d/3d)', () => {
    const c1 = Line(Point(0, 0), Point(1, 1));
    const c2 = Line(Point(x1, x1), Point(x1, x1.add(1)));
    expect(LinearEntity.areConcurrent(c1)).toBe(false);
    expect(LinearEntity.areConcurrent(c1, c2)).toBe(true);
    expect(LinearEntity.areConcurrent(c1, c1, c1, c2)).toBe(true);
    expect(LinearEntity.areConcurrent(c1, c2, Line(Point(5, x1), Point(Rational.of(-3n, 5n), x1)))).toBe(true);
    expect(LinearEntity.areConcurrent(c1, Line(Point(0, 0), Point(x1.neg(), x1)), c2)).toBe(false);
    const p1 = Point3D(0, 0, 0);
    const d1 = Line(p1, Point3D(1, 1, 1));
    expect(LinearEntity.areConcurrent(d1, Line(Point3D(x1, x1, x1), Point3D(y1, y1, y1)))).toBe(false);
    expect(LinearEntity.areConcurrent(Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0)), Line3D(Point3D(0, 1, 0), Point3D(1, 1, 0)))).toBe(false);
  });
});

describe('angles, parallels and projections', () => {
  it('angles (SymPy test_angle_between, test_closing_angle, test_smallest_angle)', () => {
    const a = Point(1, 2, 3, 4);
    const b = a.orthogonalDirection;
    const o = a.origin;
    expect(s(Line(Point(0, 0), Point(1, 1)).angleBetween(Line(Point(0, 0), Point(5, 0))))).toBe('pi/4');
    expect(s(Line(a, o).angleBetween(Line(b, o)))).toBe('pi/2');
    const zp = Point3D(0, 0, 0);
    expect(s(Line3D(zp, Point3D(1, 1, 1)).angleBetween(Line3D(zp, Point3D(5, 0, 0))))).toBe('acos(sqrt(3)/3)');
    expect(s(Line3D(zp, Point3D(1, 1, 1)).angleBetween(Line3D(Point3D(5, 0, 0), zp)))).toBe('acos(-sqrt(3)/3)');
    const ra = Ray([0, 0], { angle: 0 }) as Ray2DNode;
    const rb = Ray([1, 2], { angle: pi.div(2) }) as Ray2DNode;
    expect(s(ra.closingAngle(rb))).toBe('-pi/2');
    expect(s(rb.closingAngle(ra))).toBe('pi/2');
    expect(s(ra.closingAngle(ra))).toBe('0');
    expect(s((Ray([0, 0], [-1, -1]) as Ray2DNode).closingAngle(Ray([0, 0], [-1, 1]) as Ray2DNode))).toBe('pi/2');
    expect(s((Ray([0, 0], [-1, 1]) as Ray2DNode).closingAngle(Ray([0, 0], [-1, -1]) as Ray2DNode))).toBe('-pi/2');
    expect(() => ra.closingAngle(Ray3D([0, 0, 0], [1, 1, 1]) as never)).toThrow('Both arguments must be Ray2D objects.');
    expect(s(Line(Point(1, 1), Point(1, 2)).smallestAngleBetween(Line(Point(1, 1), Point(2, 3))))).toBe('acos(2*sqrt(5)/5)');
  });

  it('parallel and perpendicular (SymPy test_is_parallel, test_is_perpendicular, test_is_similar)', () => {
    const l2 = Line(Point(x1, x1), Point(y1, y1));
    const l21 = Line(Point(x1, x1), Point(x1, x1.add(1)));
    expect(Line(Point(0, 0), Point(1, 1)).isParallel(l2)).toBe(true);
    expect(l2.isParallel(l21)).toBe(false);
    expect(l2.isParallel(l2.parallelLine(Point(x1.neg(), x1)))).toBe(true);
    expect(l21.isParallel(l21.parallelLine(Point(0, 0)))).toBe(true);
    expect(Line3D(Point3D(4, 0, 1), Point3D(0, 4, 1)).isParallel(Line3D(Point3D(0, 0, 1), Point3D(4, 4, 1)))).toBe(false);
    expect(s(Line3D(Point3D(0, 0, 0), Point3D(1, 1, 1)).parallelLine(Point3D(x1, x1, x1)))).toBe('Line3D(Point3D(x1, x1, x1), Point3D(x1 + 1, x1 + 1, x1 + 1))');
    const l1 = Line(Point(0, 0), Point(1, 1));
    expect(l1.isPerpendicular(Line(Point(0, 0), Point(x1.neg(), x1)))).toBe(true);
    expect(l1.isPerpendicular(l2)).toBe(false);
    const p = l1.randomPoint();
    expect(l1.perpendicularSegment(p).key).toBe(p.key);
    expect(Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0)).isPerpendicular(Line3D(Point3D(0, 0, 0), Point3D(0, 1, 0)))).toBe(true);
    expect(Line3D(Point3D(0, 0, 0), Point3D(1, 1, 1)).isPerpendicular(Line3D(Point3D(x1, x1, x1), Point3D(y1, y1, y1)))).toBe(false);
    const q1 = Point(2000, 2000);
    const q2 = q1.scale(2, 2);
    const sg = Segment(Point(0, 0), q1);
    expect(sg.isSimilar(Segment(q1, q2))).toBe(true);
    expect(sg.isSimilar(Ray(Point(0, 0), Point(0, 1)))).toBe(false);
    expect(Ray3D(Point3D(1, 1, 1), Point3D(1, 0, 0)).isSimilar(Line3D(Point3D(1, 1, 1), Point3D(1, 0, 0)))).toBe(true);
    expect(Ray3D(Point3D(1, 1, 1), Point3D(1, 0, 0)).isSimilar(Line3D(Point3D(0, 0, 0), Point3D(0, 1, 0)))).toBe(false);
  });

  it('projections (SymPy test_projection)', () => {
    const p1 = Point(0, 0);
    const p2 = Point3D(0, 0, 0);
    const p3 = Point(x1.neg(), x1);
    const l1 = Line(p1, Point(1, 1));
    const l2 = Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0));
    const l3 = Line3D(p2, Point3D(1, 1, 1));
    const r1 = Ray(Point(1, 1), Point(2, 2));
    expect(s(Line(Point(x1, x1), Point(y1, y1)).projection(Point(y1, y1)))).toBe('Point2D(y1, y1)');
    expect(s(Line(Point(x1, x1), Point(x1, x1.add(1))).projection(Point(1, 1)))).toBe('Point2D(x1, 1)');
    expect(s((Segment(Point(-2, 2), Point(0, 4)) as SegmentNode).projection(r1))).toBe('Segment2D(Point2D(-1, 3), Point2D(0, 4))');
    expect(s((Segment(Point(0, 4), Point(-2, 2)) as SegmentNode).projection(r1))).toBe('Segment2D(Point2D(0, 4), Point2D(-1, 3))');
    expect(s((Segment(Point2D(1, 0), Point2D(2, 0.5)) as SegmentNode).projection(Segment(Point2D(0, 0), Point2D(0, 1))))).toBe('EmptySet');
    expect(s(l1.projection(p3))).toBe('Point2D(0, 0)');
    expect(s(l1.projection(Ray(p1, Point(-1, 5))))).toBe('Ray2D(Point2D(0, 0), Point2D(2, 2))');
    expect(s(l1.projection(Ray(p1, Point(-1, 1))))).toBe('Point2D(0, 0)');
    expect(s(r1.projection(Ray(Point(1, 1), Point(-1, -1))))).toBe('Point2D(1, 1)');
    expect(s(r1.projection(Ray(Point(0, 4), Point(-1, -5))))).toBe('Segment2D(Point2D(1, 1), Point2D(2, 2))');
    expect(s(r1.projection(Segment(Point(-1, 5), Point(-5, -10))))).toBe('Segment2D(Point2D(1, 1), Point2D(2, 2))');
    expect(s(l3.projection(Ray3D(p2, Point3D(-1, 5, 0))))).toBe('Ray3D(Point3D(0, 0, 0), Point3D(4/3, 4/3, 4/3))');
    expect(s(l2.projection(Point3D(5, 5, 0)))).toBe('Point3D(5, 0, 0)');
    expect(s(l2.projection([5, 5, 0]))).toBe('Point3D(5, 0, 0)');
    expect((l2.projection(Line3D(Point3D(0, 1, 0), Point3D(1, 1, 0))) as LinearEntity).equals(l2)).toBe(true);
  });

  it('perpendicular lines and bisectors (SymPy test_perpendicular_line, test_perpendicular_bisector, test_bisectors)', () => {
    const l = Line(Point(0, 0, 0), Point(2, 3, 4));
    const p = l.perpendicularLine(Point(-2, 2, 0));
    expect(s(p.p1)).toBe('Point3D(-2, 2, 0)');
    expect(l.contains(p.p2)).toBe(true);
    expect(s(l.perpendicularLine(Point(2, 3, 4)))).toBe('Line3D(Point3D(-1, 5, 4), Point3D(2, 3, 4))');
    const l2 = Line(Point(0, 0), Point(2, 3));
    const q = l2.perpendicularLine(Point(-2, 2));
    expect(s(q.p1)).toBe('Point2D(-2, 2)');
    expect(s(q.direction.unit)).toBe(s(Point(-2, 2).sub(l2.projection(Point(-2, 2)) as never).unit));
    const s1 = Segment(Point(0, 0), Point(1, 1)) as Segment2DNode;
    const aline = Line(Point(half, half), Point(Rational.of(3n, 2n), Rational.of(-1n, 2n)));
    const onLine = (Segment(Point(half, half), Point(Rational.of(3n, 2n), Rational.of(-1n, 2n))) as Segment2DNode).midpoint;
    expect((s1.perpendicularBisector() as LinearEntity).equals(aline)).toBe(true);
    expect((s1.perpendicularBisector(onLine) as LinearEntity).equals(Segment(s1.midpoint, onLine))).toBe(true);
    expect((s1.perpendicularBisector(onLine.add([1, 0])) as LinearEntity).equals(aline)).toBe(true);
    expect(s(Line(Point(0, 0), Point(1, 1)).perpendicularSegment([1, 1]))).toBe('Point2D(1, 1)');
    expect(s(Line(Point(0, 0), Point(1, 1)).perpendicularSegment([0, 2]))).toBe('Segment2D(Point2D(0, 2), Point2D(1, 1))');
    const b1 = Line3D(Point3D(0, 0, 0), Point3D(1, 0, 0));
    const b2 = Line3D(Point3D(0, 0, 0), Point3D(0, 1, 0));
    expect(s(b1.bisectors(b2))).toBe('[Line3D(Point3D(0, 0, 0), Point3D(1, 1, 0)), Line3D(Point3D(0, 0, 0), Point3D(1, -1, 0))]');
    const ans = '[Line3D(Point3D(0, 0, 0), Point3D(1, 0, 1)), Line3D(Point3D(0, 0, 0), Point3D(-1, 0, 1))]';
    const makers = [Line, Segment, Ray] as unknown as ((a: number[], b: number[]) => LinearEntity)[];
    for (const f of makers) for (const g of makers) expect(s(f([0, 0, 0], [0, 0, 1]).bisectors(g([0, 0], [1, 0])))).toBe(ans);
    expect(s(Line([0, 0], [1, 0]).bisectors(Line([0, 0], [1, 0])))).toBe('[Line2D(Point2D(0, 0), Point2D(1, 0))]');
  });

  it('arbitrary points and parameter values (SymPy test_arbitrary_point, test_parameter_value)', () => {
    const L1 = Line3D(Point3D(0, 0, 0), Point3D(1, 1, 1));
    const L2 = Line(Point(x1, x1), Point(y1, y1));
    expect(L2.contains(L2.arbitraryPoint())).toBe(true);
    expect(s(Ray([1, 1], { angle: pi.div(4) }).arbitraryPoint())).toBe('Point2D(t + 1, t + 1)');
    expect(s(Segment([1, 1], [2, 3]).arbitraryPoint())).toBe('Point2D(t + 1, 2*t + 1)');
    expect(s(L1.perpendicularSegment(L1.arbitraryPoint()))).toBe(s(L1.arbitraryPoint()));
    expect(s(Ray3D([1, 1, 1], { directionRatio: [1, 2, 3] }).arbitraryPoint())).toBe('Point3D(t + 1, 2*t + 1, 3*t + 1)');
    expect(s(L1.arbitraryPoint(null))).toBe('Point3D(t, t, t)');
    expect(() => Line([x, 1], [2, 3]).arbitraryPoint(x)).toThrow('Symbol x already appears in object and cannot be used as a parameter.');
    const tt = new Sym('t');
    const l = Line(Point(0, 1), Point(5, 6));
    expect([...(l.parameterValue([5, 6], tt) as Map<Expr, Expr>)].map(([k, v]) => `${s(k)}: ${s(v)}`)).toEqual(['t: 1']);
    expect(() => l.parameterValue([0, 0], tt)).toThrow('Given point is not on Line2D');
    expect(() => l.parameterValue(Line([0, 0], [1, 1]), tt)).toThrow('other must be a point');
  });

  it('python comparisons', () => {
    expect(s(pyMin([S.One, S.Zero, Rational.of(2n)]))).toBe('0');
    expect(s(pyMax([S.One, S.Zero, Rational.of(2n)]))).toBe('2');
    expect(() => pyMin([x, y])).toThrow('cannot determine truth value of Relational');
    expect(s(cos(0).add(sin(0)))).toBe('1');
  });
});

const at0 = <T>(xs: readonly T[]): T => {
  const v = xs[0];
  if (v === undefined) throw new RangeError('empty');
  return v;
};
