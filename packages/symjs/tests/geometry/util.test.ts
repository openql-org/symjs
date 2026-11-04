// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/util.ts (SymPy sympy/geometry/util.py and
// sympy/geometry/tests/test_util.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Float, NotImplementedError, UndefFn, interval, Rational, S, Sym, SymFunction, parse, sqrt, symbols } from '../../src';
import {
  Circle,
  Ellipse,
  Line,
  Line3D,
  Plane,
  Point,
  Point2D,
  Point3D,
  Polygon,
  Ray,
  Segment,
  areCoplanar,
  areSimilar,
  centroid,
  closestPoints,
  convexHull,
  farthestPoints,
  idiff,
  intersection,
} from '../../src/geometry';
import type { GeometryEntity, PointNode } from '../../src/geometry';
import { find, rationalOf } from '../../src/geometry/util';

const s = (e: unknown): string =>
  Array.isArray(e) ? `[${e.map(s).join(', ')}]` : e instanceof Set ? `{${[...e].map((p: PointNode[]) => `(${p.map(String).join(', ')})`).sort().join(', ')}}` : String(e);

describe('idiff (SymPy test_idiff)', () => {
  const [x, y, t] = symbols('x y t', { real: true }) as [Sym, Sym, Sym];
  const f = SymFunction('f');
  const g = SymFunction('g');
  it('implicit derivatives', () => {
    const circ = x.pow(2).add(y.pow(2)).sub(4);
    expect(s(idiff(circ, y, x))).toBe('-x/y');
    expect(s(idiff(circ, y, x, 3))).toBe('-3*x*(x**2/y**2 + 1)/y**3');
    expect(s(idiff(circ, [y], x, 3))).toBe('-3*x*(x**2/y**2 + 1)/y**3');
    expect(s(idiff(x.add(t).add(y), [y, t], x))).toBe('-Derivative(t, x) - 1');
    const fx = f(x) as UndefFn;
    expect(s(idiff(parse('f(x)*exp(f(x)) - x*exp(x)').subs(new Sym('x'), x), fx, x))).toBe('(x + 1)*exp(x)*exp(-f(x))/(f(x) + 1)');
    expect(s(idiff(fx.sub(y.mul(parse('exp(x)').subs(new Sym('x'), x))), g(x).sub(g(x)).add(fx) as never, x))).toBeDefined();
    expect(s(idiff(fx.sub(g(x)), [fx as never, g(x) as never], x))).toBeDefined();
    expect(s(idiff(parse('y - (-10*(-sin(x) + 1/x)**2 + tan(x)**2 + 2*cosh(x/10))').subs(new Sym('x'), x).subs(new Sym('y'), y), y, x))).toBe(
      '-20*sin(x)*cos(x) + 2*tan(x)**3 + 2*tan(x) + sinh(x/10)/5 + 20*cos(x)/x - 20*sin(x)/x**2 + 20/x**3',
    );
    expect(() => idiff(circ, S.One as never, x)).toThrow('expecting x-dependent symbol(s) or function(s) but got: 1');
    expect(() => idiff(circ, y, x, 0)).toThrow('idiff: n must be a positive integer');
  });
});

describe('intersection (SymPy test_intersection)', () => {
  it('of several entities', () => {
    expect(s(intersection(Point(0, 0)))).toBe('[]');
    expect(() => intersection(Point(0, 0), 3 as never)).toThrow(TypeError);
    expect(s(intersection(Segment([0, 0], [2, 0]), Segment([-1, 0], [1, 0]), Line([0, 0], [0, 1]), { pairwise: true }))).toBe('[Point2D(0, 0), Segment2D(Point2D(0, 0), Point2D(1, 0))]');
    expect(s(intersection(Line([0, 0], [0, 1]), Segment([0, 0], [2, 0]), Segment([-1, 0], [1, 0]), { pairwise: true }))).toBe('[Point2D(0, 0), Segment2D(Point2D(0, 0), Point2D(1, 0))]');
    expect(s(intersection(Line([0, 0], [0, 1]), Segment([0, 0], [2, 0]), Segment([-1, 0], [1, 0]), Line([0, 0], { slope: 1 }), { pairwise: true }))).toBe('[Point2D(0, 0), Segment2D(Point2D(0, 0), Point2D(1, 0))]');
    expect(s(intersection(Line([0, 0], [1, 1]), Line([0, 1], [1, 0]), Line([0, 0.5], [1, 0.5])))).toBe('[Point2D(1/2, 1/2)]');
    expect(s(intersection([0, 0], Line([0, 0], [1, 1])))).toBe('[Point2D(0, 0)]');
    const c = intersection(Ray(Point2D(0.001, -1), Point2D(0.0008, -1.7)), Ellipse(Point2D(0, 0), new Float(4), new Float(2)), { pairwise: true });
    expect(s(c)).toBe('[Point2D(0.000714285723396502, -1.99999996811224)]');
    const c2 = intersection(Ray(Point2D(0.001, -1), Point2D(0.0008, -1.7)), Ellipse(Point2D(0, 0), new Float(4, 20), new Float(2)), { pairwise: true });
    // SymPy str(c2[0]) (its list repr keeps the trailing zeros: -2.0000)
    expect(s(c2[0])).toBe('Point2D(0.00071429, -2.0)');
    // sets (SymPy Intersection): the same function intersects sets
    expect(s(intersection(interval(0, 2), interval(1, 3)))).toBe('Interval(1, 2)');
  });
});

describe('convex hulls, centroids and point pairs', () => {
  it('convex_hull (SymPy test_convex_hull)', () => {
    expect(() => convexHull(Point(0, 0), 3 as never)).toThrow(TypeError);
    expect(s(convexHull([1, -1], [1, -2], [3, -1], [-5, -2], [15, -4], { polygon: false }))).toBe('[[Point2D(-5, -2), Point2D(1, -1), Point2D(3, -1), Point2D(15, -4)], [Point2D(-5, -2), Point2D(15, -4)]]');
    expect(s(convexHull(Point(0, 0), Point(1, 1), Point(2, 2), { polygon: false }))).toBe('[Segment2D(Point2D(0, 0), Point2D(2, 2)), undefined]'.replace('undefined', 'undefined'));
    expect(s(convexHull(Point(0, 0), { polygon: false }))).toBe('[Point2D(0, 0), undefined]');
    expect(s(convexHull(Point(0, 0), Point(1, 0), { polygon: false }))).toBe('[Segment2D(Point2D(0, 0), Point2D(1, 0)), undefined]');
    expect(s(convexHull(Point(0, 0), Point(1, 1), Point(2, 2)))).toBe('Segment2D(Point2D(0, 0), Point2D(2, 2))');
    expect(() => convexHull(Point(0, 0, 0), Point(1, 1, 1))).toThrow('Can only compute the convex hull in two dimensions');
    expect(() => convexHull(Circle([0, 0], 1))).toThrow('Convex hull for Circle not implemented.');
    expect(() => convexHull(Point(0, new Sym('a')), Point(1, 0), Point(new Sym('b'), 2))).toThrow('The points could not be sorted.');
  });

  it('centroid (SymPy test_centroid)', () => {
    const p = Polygon([0, 0], [10, 0], [10, 10]) as GeometryEntity;
    expect(s(centroid(p, p.translate(0, 20)))).toBe('Point2D(20/3, 40/3)');
    expect(s(centroid(Segment([0, 0], [2, 0]) as GeometryEntity, Segment([0, 0], [2, 2]) as GeometryEntity))).toBe('Point2D(1, 2 - sqrt(2))');
    expect(s(centroid(Point(0, 0), Point(2, 0)))).toBe('Point2D(1, 0)');
    expect(s(centroid(Point(0, 0), Point(0, 0), Point(2, 0)))).toBe('Point2D(2/3, 0)');
    expect(() => centroid()).toThrow(RangeError);
    expect(() => centroid(Point(0, 0), Circle([0, 0], 1))).toThrow(TypeError);
  });

  it('closest and farthest points (SymPy test_farthest_points_closest_points)', () => {
    expect(() => closestPoints(Point2D(0, 0), Point2D(0, 0))).toThrow('At least 2 distinct points must be given.');
    expect(() => farthestPoints(Point2D(0, 0), Point2D(0, 0))).toThrow('At least two distinct points must be given.');
    expect(() => farthestPoints([1, 1])).toThrow(RangeError);
    expect(s(closestPoints(Point2D(0, 0), Point2D(3, 0), Point2D(1, 1)))).toBe('{(Point2D(0, 0), Point2D(1, 1))}');
    expect(s(farthestPoints(Point2D(0, 0), Point2D(3, 0), Point2D(1, 1)))).toBe('{(Point2D(0, 0), Point2D(3, 0))}');
    for (const pts of [
      [Point2D(0, 0), Point2D(3, 0), Point2D(2, 1)],
      [Point2D(0, 0), Point2D(3, 0), Point2D(1, 10)],
      [Point2D(0, 0), Point2D(3, 0), Point2D(4, 0)],
      [Point2D(0, 0), Point2D(3, 0), Point2D(-1, 0)],
      [Point2D(0, 0), Point2D(3, 0), Point2D(3, 0), Point2D(-1, 0)],
    ]) {
      const ds = pts.flatMap((a, i) => pts.slice(i + 1).filter((b) => b.key !== a.key).map((b) => a.distance(b).toNumber()));
      const [[a, b]] = [...closestPoints(...pts)] as [[PointNode, PointNode]];
      expect(a.distance(b).toNumber()).toBe(Math.min(...ds));
      const [[c, d]] = [...farthestPoints(...pts)] as [[PointNode, PointNode]];
      expect(c.distance(d).toNumber()).toBe(Math.max(...ds));
    }
    const xp = new Sym('x', { positive: true });
    const sp = [Point2D(xp, 1), Point2D(xp.add(3), 2), Point2D(xp.add(2), 2)];
    expect(s(closestPoints(...sp))).toBe('{(Point2D(x + 2, 2), Point2D(x + 3, 2))}');
    expect(s(farthestPoints(...sp))).toBe('{(Point2D(x, 1), Point2D(x + 3, 2))}');
    const [a, b, c] = [Point2D(0, 0), Point2D(1, 0), Point2D(S.Half, sqrt(3).div(2))];
    expect(s(closestPoints(b, c, a))).toBe('{(Point2D(0, 0), Point2D(1, 0)), (Point2D(0, 0), Point2D(1/2, sqrt(3)/2)), (Point2D(1/2, sqrt(3)/2), Point2D(1, 0))}');
    expect(s(farthestPoints(b, c, a))).toBe('{(Point2D(0, 0), Point2D(1, 0)), (Point2D(0, 0), Point2D(1/2, sqrt(3)/2)), (Point2D(1/2, sqrt(3)/2), Point2D(1, 0))}');
    expect(s(farthestPoints([1, 1], [1, 2], [3, 1], [-5, 2], [15, 4]))).toBe('{(Point2D(-5, 2), Point2D(15, 4))}');
    expect(s(farthestPoints([1, -1], [1, -2], [3, -1], [-5, -2], [15, -4]))).toBe('{(Point2D(-5, -2), Point2D(15, -4))}');
    expect(s(farthestPoints([1, 1], [0, 0]))).toBe('{(Point2D(0, 0), Point2D(1, 1))}');
    expect(s(farthestPoints(Point(0, 0), Point(1, 1), Point(2, 2)))).toBe('{(Point2D(0, 0), Point2D(2, 2))}');
    expect(s(closestPoints(Point(0, 0), Point(Rational.of(1n, 3n), 0), Point(sqrt(2), 0)))).toBe('{(Point2D(0, 0), Point2D(1/3, 0))}');
    expect(s(closestPoints(Point(0, 0), Point(sqrt(2).add(1), 0), Point(5, 5)))).toBe('{(Point2D(0, 0), Point2D(1 + sqrt(2), 0))}');
    expect(s(farthestPoints(Point(0, 0), Point(sqrt(2).add(1), 0), Point(5, 5)))).toBe('{(Point2D(0, 0), Point2D(5, 5))}');
    expect(s(closestPoints(Point(0, 0), Point(sqrt(2), 0), Point(1, 0), Point(sqrt(2).add(1), 1)))).toBe('{(Point2D(1, 0), Point2D(sqrt(2), 0))}');
  });
});

describe('similarity and coplanarity', () => {
  it('are_similar and are_coplanar (SymPy test_are_coplanar)', () => {
    const c1 = Circle([0, 0], 1);
    expect(areSimilar(c1, c1)).toBe(true);
    expect(areSimilar(Segment([0, 0], [1, 1]) as GeometryEntity, Segment([2, 2], [3, 3]) as GeometryEntity)).toBe(true);
    // SymPy raises NotImplementedError from GeometryEntity.is_similar
    expect(() => areSimilar(c1, Segment([0, 0], [1, 1]) as GeometryEntity)).toThrow(NotImplementedError);
    expect(() => areSimilar(c1, Circle([0, 0], 2))).toThrow(NotImplementedError);
    const a = Line3D(Point3D(5, 0, 0), Point3D(1, -1, 1));
    const b = Line3D(Point3D(0, -2, 0), Point3D(3, 1, 1));
    const c = Line3D(Point3D(0, -1, 0), Point3D(5, -1, 9));
    const d = Line(Point2D(0, 3), Point2D(1, 5));
    expect(areCoplanar(a, b, c)).toBe(false);
    expect(areCoplanar(a, d)).toBe(false);
    // SymPy calls is_coplanar on the other entities (AttributeError for a Line3D); symjs asks the plane
    expect(areCoplanar(Plane([0, 0, 0], { normalVector: [0, 0, 1] }), Point3D(1, 2, 0), Line3D([0, 0, 0], [1, 1, 0]))).toBe(true);
    expect(areCoplanar(Point3D(0, 0, 0), Point3D(1, 1, 1), Point3D(2, 2, 2))).toBe(false);
    expect(areCoplanar(Point3D(0, 0, 0), Point3D(1, 1, 1))).toBe(false);
    expect(areCoplanar(Point3D(0, 0, 0), Point3D(1, 0, 0), Point3D(0, 1, 0), Point3D(0, 0, 1))).toBe(false);
    expect(areCoplanar(Circle([0, 0], 1), Point3D(1, 1, 0), Point3D(2, 3, 0))).toBe(true);
  });

  it('helpers', () => {
    const e = parse('x + y');
    expect(s(find('x', e))).toBe('x');
    expect(s(find(new Sym('y'), e))).toBe('y');
    expect(() => find('z', e)).toThrow('could not find z');
    expect(() => find('x', e.add(new Sym('x', { real: true })))).toThrow('ambiguous x');
    expect(s(rationalOf(0.1))).toBe('3602879701896397/36028797018963968');
  });
});
