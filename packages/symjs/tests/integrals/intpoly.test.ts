// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/intpoly.ts (SymPy sympy/integrals/intpoly.py and
// sympy/integrals/tests/test_intpoly.py). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Expr, ExprMap, NotImplementedError, PolynomialError, Rational, S, Sym, parse, sqrt, symbols } from '../../src';
import { Point, Polygon, Segment2D } from '../../src/geometry';
import type { Polygon as PolygonT } from '../../src/geometry';
import type { Face, Hyperplane, MonomialRecord2D, PointLike, SegmentLike } from '../../src/integrals/intpoly';
import {
  bestOrigin,
  crossProduct,
  decompose,
  distanceToSide,
  gradientTerms,
  hyperplaneParameters,
  integrationReduction,
  integrationReductionDynamic,
  intersection,
  isVertex,
  leftIntegral2D,
  leftIntegral3D,
  linesegIntegrate,
  mainIntegrate,
  mainIntegrate3d,
  norm,
  pointSort,
  polygonIntegrate,
  polytopeIntegrate,
} from '../../src/integrals/intpoly';

const [x, y, z] = symbols('x y z');
const P = (s: string): Expr => parse(s, { symbols: [x!, y!, z!] });
const str = (v: unknown): string => {
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${String(k)}: ${String(w)}`).sort().join(', ')}}`;
  if (v instanceof Set) return `{${[...v].map(String).sort().join(', ')}}`;
  if (Array.isArray(v)) return `[${v.map(str).join(', ')}]`;
  return String(v);
};
const polygon = (...pts: [number, number][]): PolygonT => Polygon(...pts.map(([a, b]) => Point(a, b))) as PolygonT;
const square = polygon([0, 0], [0, 1], [1, 1], [1, 0]);
const triangle = polygon([0, 3], [5, 3], [1, 1]);
const cubeVertices: [number, number, number][] = [
  [0, 0, 0],
  [0, 0, 5],
  [0, 5, 0],
  [0, 5, 5],
  [5, 0, 0],
  [5, 0, 5],
  [5, 5, 0],
  [5, 5, 5],
];
const cubeFaces: Face[] = [
  [2, 6, 7, 3],
  [3, 7, 5, 1],
  [7, 6, 4, 5],
  [1, 5, 4, 0],
  [3, 1, 0, 2],
  [0, 4, 6, 2],
];
const cube2Faces: Face[] = [
  [3, 7, 6, 2],
  [1, 5, 7, 3],
  [5, 4, 6, 7],
  [0, 4, 5, 1],
  [2, 0, 1, 3],
  [2, 6, 4, 0],
];

describe('decompose', () => {
  it('splits a polynomial into homogeneous components', () => {
    expect(str(decompose(x!))).toBe('{1: x}');
    expect(str(decompose(P('x**2')))).toBe('{2: x**2}');
    expect(str(decompose(P('x*y')))).toBe('{2: x*y}');
    expect(str(decompose(P('x + y')))).toBe('{1: x + y}');
    expect(str(decompose(P('x**2 + y')))).toBe('{1: y, 2: x**2}');
    expect(str(decompose(P('8*x**2 + 4*y + 7')))).toBe('{0: 7, 1: 4*y, 2: 8*x**2}');
    expect(str(decompose(P('x**2 + 3*y*x')))).toBe('{2: x**2 + 3*x*y}');
    expect(str(decompose(P('9*x**2 + y + 4*x + x**3 + y**2*x + 3')))).toBe('{0: 3, 1: 4*x + y, 2: 9*x**2, 3: x**3 + x*y**2}');
    expect(str(decompose(P('x**2 + x*y + x + y + x**3*y**2 + y**5')))).toBe('{1: x + y, 2: x**2 + x*y, 5: x**3*y**2 + y**5}');
    expect(str(decompose(2))).toBe('{0: 2}');
    expect(str(decompose(P('3*x**2*y')))).toBe('{3: 3*x**2*y}');
  });
  it('lists the terms with separate', () => {
    expect(str(decompose(x!, true))).toBe('{x}');
    expect(str(decompose(P('x*y'), true))).toBe('{x*y}');
    expect(str(decompose(P('8*x**2 + 4*y + 7'), true))).toBe('{4*y, 7, 8*x**2}');
    expect(str(decompose(P('x**2 + x*y + x + y + x**3*y**2 + y**5'), true))).toBe('{x, x**2, x**3*y**2, x*y, y, y**5}');
  });
  it('needs integer exponents', () => {
    // SymPy keys sqrt(x) by the degree 1/2; symjs keeps degrees integers (the algorithm needs polynomials)
    expect(() => decompose(sqrt(x!))).toThrow(PolynomialError);
    expect(() => decompose(P('x*y**z'))).toThrow(PolynomialError);
  });
});

describe('bestOrigin', () => {
  const l1 = Segment2D(Point(0, 3), Point(1, 1)) as SegmentLike;
  const expr1 = P('y**2*x**5 + y**5*x**7 + 7*x + x**12 + y**7*x');
  it("matches SymPy's test_best_origin", () => {
    // SymPy divides Python integers to floats ((0, 3.0), (1.5, 0)); symjs divides exactly
    expect(str(bestOrigin([2, 1], 3, l1, expr1))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, P('x**3*y**7')))).toBe('[0, 3]');
    const l2 = Segment2D(Point(Rational.of(3n, 2n), 0), Point(Rational.of(3n, 2n), 3)) as SegmentLike;
    const l3 = Segment2D(Point(0, Rational.of(3n, 2n)), Point(3, Rational.of(3n, 2n))) as SegmentLike;
    expect(str(bestOrigin([2, 0], 3, l2, P('x**7')))).toBe('[3/2, 0]');
    expect(str(bestOrigin([0, 2], 3, l3, P('x**7')))).toBe('[0, 3/2]');
    const l4 = Segment2D(Point(0, 2), Point(2, 0)) as SegmentLike;
    expect(str(bestOrigin([1, 1], 2, l4, P('x**7*y**3')))).toBe('[0, 2]');
    expect(str(bestOrigin([1, 1], 2, l4, P('x**3*y**7')))).toBe('[2, 0]');
    expect(str(bestOrigin([1, 1], 2, Segment2D(Point(0, 2), Point(1, 1)) as SegmentLike, P('x**2*y**9')))).toBe('[0, 2]');
    expect(str(bestOrigin([1, 1], 2, Segment2D(Point(2, 0), Point(1, 1)) as SegmentLike, P('x**9*y**2')))).toBe('[2, 0]');
  });
  it('covers the other cases', () => {
    expect(str(bestOrigin([1, 0], 1, Segment2D(Point(1, 1), Point(1, 3)) as SegmentLike, x!))).toBe('[1, 1]');
    expect(str(bestOrigin([0, 1], 1, Segment2D(Point(1, 1), Point(3, 1)) as SegmentLike, x!))).toBe('[1, 1]');
    expect(str(bestOrigin([2, 1], 3, l1, 5))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, P('x**2 + y**3 + x*y')))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, P('y**4')))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, y!))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, P('x + y')))).toBe('[0, 3]');
    const far = Segment2D(Point(1, 1), Point(2, 3)) as SegmentLike;
    expect(str(bestOrigin([-2, 1], -1, far, x!))).toBe('[1, 1]');
    expect(str(bestOrigin([-2, 1], -1, far, P('y**3')))).toBe('[1, 1]');
    expect(str(bestOrigin([2, 1], 3, Segment2D(Point(1, 1), Point(2, -1)) as SegmentLike, y!))).toBe('[3/2, 0]');
    expect(str(bestOrigin([2, 1], 3, Segment2D(Point(-1, 5), Point(1, 1)) as SegmentLike, x!))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, P('x**3*sin(y)')))).toBe('[0, 3]');
    expect(str(bestOrigin([2, 1], 3, l1, P('x**3*y*z + y**9')))).toBe('[0, 3]');
  });
});

describe('polytopeIntegrate', () => {
  it('integrates over polygons in vertex representation', () => {
    expect(str(polytopeIntegrate(polygon([0, 0], [0, 2], [4, 0]), 1))).toBe('4');
    expect(str(polytopeIntegrate(square, P('x*y')))).toBe('1/4');
    expect(str(polytopeIntegrate(triangle, P('6*x**2 - 40*y')))).toBe('-935/3');
    const r3 = sqrt(3);
    const sq3 = Polygon(Point(0, 0), Point(0, r3), Point(r3, r3), Point(r3, 0)) as PolygonT;
    expect(str(polytopeIntegrate(sq3, 1))).toBe('3');
    expect(str(polytopeIntegrate(polygon([-1, -1], [-1, 1], [1, 1], [0, 0], [1, -1]), 1))).toBe('3');
  });
  it('integrates over polygons in hyperplane representation', () => {
    const h = (a: number, b: number, c: number): Hyperplane => [[a, b], c];
    expect(str(polytopeIntegrate([h(-1, 0, 0), h(1, 2, 4), h(0, -1, 0)], 1))).toBe('4');
    expect(str(polytopeIntegrate([h(-1, 0, 0), h(0, 1, 1), h(1, 0, 1), h(0, -1, 0)], P('x*y')))).toBe('1/4');
    expect(str(polytopeIntegrate([h(0, 1, 3), h(1, -2, -1), h(-2, -1, -3)], P('6*x**2 - 40*y')))).toBe('-935/3');
    expect(str(polytopeIntegrate([h(-1, 0, 1), h(0, 1, 1), h(1, -1, 0), h(1, 1, 0), h(0, -1, 1)], 1))).toBe('3');
    expect(() => polytopeIntegrate([[[1, 0, 0], 1] as Hyperplane, [[0, 1, 0], 1] as Hyperplane], 1)).toThrow(NotImplementedError);
  });
  it('sorts the vertices clockwise on request', () => {
    const fig6 = polygon([0, 0], [1, 0], [1, 1]);
    expect(str(polytopeIntegrate(fig6, P('x*y')))).toBe('-1/8');
    expect(str(polytopeIntegrate(fig6, P('x*y'), { clockwise: true }))).toBe('1/8');
    expect(() => polytopeIntegrate([[[1, 0], 0]], 1, { clockwise: true })).toThrow(TypeError);
  });
  it('integrates lists of polynomials up to a maximum degree', () => {
    const polys = [1, x!, y!, P('x*y'), P('x**2*y'), P('x*y**2')];
    expect(str(polytopeIntegrate(square, polys, { maxDegree: 3 }))).toBe('{1: 1, x**2*y: 1/6, x*y**2: 1/6, x*y: 1/4, x: 1/2, y: 1/2}');
    expect(str(polytopeIntegrate(square, polys, { maxDegree: 2 }))).toBe('{1: 1, x*y: 1/4, x: 1/2, y: 1/2}');
    expect(str(polytopeIntegrate(square, polys, { maxDegree: 1 }))).toBe('{1: 1, x: 1/2, y: 1/2}');
    expect(str(polytopeIntegrate(square, [x!, P('2*x*y + 1'), 0, 0], { maxDegree: 2 }))).toBe('{0: 0, 2*x*y + 1: 3/2, x: 1/2}');
    expect(str(polytopeIntegrate(square, undefined, { maxDegree: 1 }))).toBe('{0: 0, 1: 1, x: 1/2, y: 1/2}');
    // SymPy integrates 0 for maxDegree 0 (`if max_degree:`); the table of degree 0 is the area
    expect(str(polytopeIntegrate(square, undefined, { maxDegree: 0 }))).toBe('{0: 0, 1: 1}');
    const tri = triangle;
    const e1 = P('x**7*y + 2*x**2*y**6');
    expect(str(polytopeIntegrate(tri, [e1, P('x**10 + y**10')], { maxDegree: 9 }))).toBe('{x**7*y + 2*x**2*y**6: 489262/9}');
    expect(() => polytopeIntegrate(square, x!, { maxDegree: 2 })).toThrow(TypeError);
    // SymPy raises KeyError: z is not a monomial of the 2D table
    expect(() => polytopeIntegrate(square, [z!], { maxDegree: 1 })).toThrow(RangeError);
  });
  it('integrates lists of polynomials without a maximum degree (issue 19234)', () => {
    const polys = [1, x!, y!, P('x*y'), P('3 + x**2*y'), P('x + x*y**2')];
    expect(str(polytopeIntegrate(square, polys))).toBe('{1: 1, x**2*y + 3: 19/6, x*y**2 + x: 2/3, x*y: 1/4, x: 1/2, y: 1/2}');
  });
  it('integrates over 3-polytopes', () => {
    const cube1: [readonly PointLike[], ...Face[]] = [
      [
        [0, 0, 0],
        [0, 6, 6],
        [6, 6, 6],
        [3, 6, 0],
        [0, 6, 0],
        [6, 0, 6],
        [3, 0, 0],
        [0, 0, 6],
      ],
      [1, 2, 3, 4],
      [3, 2, 5, 6],
      [1, 7, 5, 2],
      [0, 6, 5, 7],
      [1, 4, 0, 7],
      [0, 4, 3, 6],
    ];
    expect(str(polytopeIntegrate(cube1, 1))).toBe('162');
    const cube2: [readonly PointLike[], ...Face[]] = [cubeVertices, ...cube2Faces];
    expect(str(polytopeIntegrate(cube2, P('x**2 + y**2 + x*y + z**2')))).toBe('15625/4');
    // SymPy 1.14 returns nan for polynomials that are not homogeneous; the sums of the homogeneous parts are
    // 8125/6 (the integral over [0, 5]**3) and 1674
    expect(str(polytopeIntegrate(cube2, P('x**2 + y')))).toBe('8125/6');
    expect(str(polytopeIntegrate(cube1, P('x*y + z')))).toBe('1674');
    const cube4: [readonly PointLike[], ...Face[]] = [
      [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1], [S.One.div(4), S.One.div(4), S.One.div(4)]],
      [0, 2, 1],
      [1, 3, 0],
      [4, 2, 3],
      [4, 3, 1],
      [0, 1, 2],
      [2, 4, 1],
      [0, 3, 2],
    ];
    expect(str(polytopeIntegrate(cube4, P('x**2 + y**2 + x*y + z**2')))).toBe('37/960');
    expect(str(polytopeIntegrate(cube2, [P('x**2'), P('y*z'), 3], { maxDegree: 2 }))).toBe('{3: 375, x**2: 3125/3, y*z: 3125/4}');
    expect(str(polytopeIntegrate(cube2, undefined, { maxDegree: 2 }))).toBe(
      '{1: 125, x**2: 3125/3, x*y: 3125/4, x*z: 3125/4, x: 625/2, y**2: 3125/3, y*z: 3125/4, y: 625/2, z**2: 3125/3, z: 625/2}',
    );
    expect(() => polytopeIntegrate(cube2)).toThrow(TypeError);
    expect(() => polytopeIntegrate(cube2, [x!])).toThrow(TypeError);
  });
  it('needs an expression in 2D', () => {
    expect(() => polytopeIntegrate(square)).toThrow(TypeError);
  });
  it('handles polygons with collinear vertices', () => {
    // a square [0, 2]**2 with the extra vertex (1, 0): SymPy's Polygon drops it and gives -4 (anticlockwise)
    const vs = [Point(0, 0), Point(1, 0), Point(2, 0), Point(2, 2), Point(0, 2)];
    const poly = { vertices: vs, sides: vs.map((v, i) => ({ points: [v, vs[(i + 1) % vs.length]!] })) };
    expect(str(polytopeIntegrate(poly, P('x*y')))).toBe('-4');
    expect(str(polytopeIntegrate(poly, 1))).toBe('-4');
  });
});

describe('point_sort', () => {
  it('sorts clockwise or anticlockwise', () => {
    expect(str(pointSort([Point(0, 0), Point(1, 0), Point(1, 1)]))).toBe('[Point2D(1, 1), Point2D(1, 0), Point2D(0, 0)]');
    expect(str(pointSort([Point(0, 0), Point(1, 0), Point(1, 1)], undefined, false))).toBe('[Point2D(0, 0), Point2D(1, 0), Point2D(1, 1)]');
    expect(str(pointSort(polygon([0, 0], [1, 0], [1, 1])))).toBe('[Point2D(1, 1), Point2D(1, 0), Point2D(0, 0)]');
    expect(str(pointSort([Point(1, 1)]))).toBe('[Point2D(1, 1)]');
    expect(str(pointSort([Point(0, 0), Point(0, 1), Point(0, -1), Point(0, 2)]))).toBe('[Point2D(0, 2), Point2D(0, 1), Point2D(0, -1), Point2D(0, 0)]');
    expect(str(pointSort([Point(0, 0), Point(1, 0), Point(2, 0), Point(1, 1)]))).toBe('[Point2D(1, 1), Point2D(2, 0), Point2D(1, 0), Point2D(0, 0)]');
  });
  it('sorts points in every relative position', () => {
    const sorted = (pts: [number, number][]): string => str(pointSort(pts.map(([a, b]) => Point(a, b))));
    expect(sorted([[-1, 1], [2, 0], [0, 0], [2, 2], [0, 2], [1, 3]])).toBe('[Point2D(1, 3), Point2D(2, 2), Point2D(2, 0), Point2D(0, 0), Point2D(-1, 1), Point2D(0, 2)]');
    expect(sorted([[0, 0], [1, 1], [3, 3], [-2, 0], [4, -1]])).toBe('[Point2D(3, 3), Point2D(4, -1), Point2D(0, 0), Point2D(-2, 0), Point2D(1, 1)]');
    expect(sorted([[3, 0], [-3, 0], [1, 0], [-1, 0], [0, 5], [0, -5]])).toBe('[Point2D(0, 5), Point2D(3, 0), Point2D(1, 0), Point2D(0, -5), Point2D(-3, 0), Point2D(-1, 0)]');
    expect(sorted([[0, -1], [0, -2], [1, 5], [-1, 5]])).toBe('[Point2D(1, 5), Point2D(0, -2), Point2D(0, -1), Point2D(-1, 5)]');
    expect(sorted([[0, -2], [0, -1], [1, 5], [-1, 5]])).toBe('[Point2D(1, 5), Point2D(0, -2), Point2D(0, -1), Point2D(-1, 5)]');
    expect(sorted([[1, 1], [-1, -1], [2, 2], [-2, -2], [1, -1], [-1, 1]])).toBe('[Point2D(2, 2), Point2D(1, 1), Point2D(1, -1), Point2D(-2, -2), Point2D(-1, -1), Point2D(-1, 1)]');
  });
  it('sorts 3D points around a normal', () => {
    expect(str(pointSort([Point(0, 0, 0), Point(1, 0, 0), Point(0, 1, 0)], [0, 0, 1]))).toBe('[Point3D(0, 1, 0), Point3D(1, 0, 0), Point3D(0, 0, 0)]');
    // collinear points compare equal and keep their order (SymPy's comparator returns None and fails)
    expect(str(pointSort([Point(0, 0, 0), Point(2, 0, 0), Point(1, 0, 0)], [0, 0, 1]))).toBe('[Point3D(0, 0, 0), Point3D(2, 0, 0), Point3D(1, 0, 0)]');
  });
  it('needs decidable comparisons', () => {
    const a = new Sym('a');
    expect(() => pointSort([Point(a, 0), Point(1, 0), Point(1, 1)])).toThrow(TypeError);
  });
});

describe('helpers', () => {
  it('norm', () => {
    expect(str(norm(Point(2, 7)))).toBe('sqrt(53)');
    expect(str(norm([3, 4]))).toBe('5');
    expect(str(norm(new Map([[1, 3], [2, 4]])))).toBe('5');
    // SymPy 1.14 gives sqrt(7) (it adds z instead of z**2)
    expect(str(norm(Point(1, 2, 2)))).toBe('3');
  });
  it('intersection', () => {
    expect(str(intersection(Segment2D(Point(1, 1), Point(3, 5)) as SegmentLike, Segment2D(Point(2, 0), Point(2, 5)) as SegmentLike, 'segment2D'))).toBe('[2, 3]');
    expect(str(intersection([[-1, 0], 0], [[0, 1], 1], 'plane2D'))).toBe('[0, 1]');
    expect(str(intersection(Segment2D(Point(0, 0), Point(1, 0)) as SegmentLike, Segment2D(Point(0, 1), Point(1, 1)) as SegmentLike, 'segment2D'))).toBe('[]');
    expect(str(intersection([[1, 0], 1], [[2, 0], 3], 'plane2D'))).toBe('[]');
    expect(str(intersection({ points: [[0, 0, 0], [1, 1, 1]] }, { points: [[1, 0, 0], [0, 1, 0]] }, 'segment3D'))).toBe('[1/2, 1/2]');
    expect(str(intersection([[1, 0], 1], [[0, 1], 1], 'segment2D'))).toBe('[]');
  });
  it('isVertex', () => {
    expect(isVertex(2)).toBe(false);
    expect(isVertex([2, 3])).toBe(true);
    expect(isVertex(Point(2, 3))).toBe(true);
    expect(isVertex([2, 3, 4])).toBe(true);
    expect(isVertex([2, 3, 4, 5])).toBe(false);
    expect(isVertex(x)).toBe(false);
  });
  it('gradientTerms', () => {
    expect(str(gradientTerms(2))).toBe('[[1, 0, 0, 0], [y, 0, 1, 0], [y**2, 0, 2, 0], [x, 1, 0, 0], [x*y, 1, 1, 0], [x**2, 2, 0, 0]]');
    expect(str(gradientTerms())).toBe('[[1, 0, 0, 0]]');
    expect(str(gradientTerms(1, 3))).toBe('[[[[1, 0, 0, 0, 0, 0, 0, 0]]], [[[y, 0, 1, 0, 1, 0, 0, 0], [z, 0, 0, 1, 1, 0, 1, 0]], [[x, 1, 0, 0, 1, 1, 0, 0]]]]');
  });
  it('hyperplaneParameters and crossProduct', () => {
    expect(str(hyperplaneParameters(triangle))).toBe('[[[0, 1], 3], [[1, -2], -1], [[-2, -1], -3]]');
    expect(str(hyperplaneParameters(cubeFaces, cubeVertices))).toBe(
      '[[[0, -1, 0], -5], [[0, 0, -1], -5], [[-1, 0, 0], -5], [[0, 1, 0], 0], [[1, 0, 0], 0], [[0, 0, 1], 0]]',
    );
    // a degenerate face: the normal is 0 (SymPy divides Python integers: [0.0, 0.0, 0.0], 0.0)
    expect(str(hyperplaneParameters([[0, 1, 2]], [[0, 0, 0], [1, 1, 1], [2, 2, 2]]))).toBe('[[[0, 0, 0], 0]]');
    expect(str(crossProduct([0, 0, 0], [1, 0, 0], [0, 1, 0]))).toBe('[0, 0, 1]');
  });
});

describe('the integration steps', () => {
  const facets = triangle.sides as readonly SegmentLike[];
  const hp = hyperplaneParameters(triangle);
  const [a, b] = hp[0]!;
  it('main_integrate', () => {
    expect(str(mainIntegrate(P('x**2 + y**2'), facets, hp))).toBe('325/6');
    expect(str(mainIntegrate(P('x**2 + y**2'), facets, hp, 1))).toBe('{0: 0, 1: 5, x: 10, y: 35/3}');
    expect(str(mainIntegrate([x!, 1], facets, hp))).toBe('{1: 5, x: 10}');
  });
  it('main_integrate3d', () => {
    const hp3 = hyperplaneParameters(cubeFaces, cubeVertices);
    expect(str(mainIntegrate3d(1, cubeFaces, cubeVertices, hp3))).toBe('-125');
    expect(str(mainIntegrate3d(1, cubeFaces, cubeVertices, hp3, 1))).toBe('{1: -125, x: -625/2, y: -625/2, z: -625/2}');
  });
  it('polygon_integrate, distance_to_side and lineseg_integrate', () => {
    expect(str(polygonIntegrate(cubeFaces[0]!, [[0, 1, 0], 5], 0, cubeFaces, cubeVertices, 1, 0))).toBe('-25');
    expect(str(polygonIntegrate(cubeFaces[0]!, [[0, 1, 0], 5], 0, cubeFaces, cubeVertices, 0, 0))).toBe('0');
    expect(str(distanceToSide([0, 0, 0], [[0, 0, 1], [0, 1, 0]], [1, 0, 0]))).toBe('-sqrt(2)/2');
    const poly = [[0, 5, 0], [5, 5, 0], [5, 5, 5], [0, 5, 5]];
    expect(str(linesegIntegrate(poly, 0, [[0, 5, 0], [5, 5, 0]], 1, 0))).toBe('5');
    expect(str(linesegIntegrate(poly, 0, [[0, 5, 0], [5, 5, 0]], 0, 0))).toBe('0');
  });
  it('integration_reduction and left_integral2D', () => {
    expect(str(integrationReduction(facets, 0, a, b, 1, [x!, y!], 0))).toBe('5');
    expect(str(integrationReduction(facets, 0, a, b, 0, [x!, y!], 0))).toBe('0');
    expect(str(leftIntegral2D(3, 0, facets, facets[0]!.points[0]!, 1, [x!, y!]))).toBe('5');
  });
  it('integration_reduction_dynamic', () => {
    const x0 = facets[0]!.points[0]!;
    const values: MonomialRecord2D[] = [
      [S.Zero, 0, 0, 0],
      [S.One, 0, 0, 5],
      [y!, 0, 1, 15],
      [x!, 1, 0, 0],
    ];
    expect(str(integrationReductionDynamic(facets, 0, a, b, x!, 1, [x!, y!], 1, 0, 1, x0, values, 3))).toBe('25/2');
    expect(str(integrationReductionDynamic(facets, 0, a, b, 0, 1, [x!, y!], 1, 0, 1, x0, values, 3))).toBe('0');
  });
  it('left_integral3D', () => {
    expect(str(leftIntegral3D(cubeFaces, 3, 1, cubeVertices, [[0, -1, 0], -5], 0))).toBe('-50');
  });
});

describe('results', () => {
  it('are expression maps', () => {
    expect(polytopeIntegrate(square, [x!], { maxDegree: 1 })).toBeInstanceOf(ExprMap);
    expect(polytopeIntegrate(square, x!)).toBeInstanceOf(Expr);
  });
});
