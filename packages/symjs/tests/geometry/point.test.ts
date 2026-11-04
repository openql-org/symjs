// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/point.ts (SymPy sympy/geometry/point.py and
// sympy/geometry/tests/test_point.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { I, Matrix, Mod, Rational, S, Sym, latex, parse, pi, sqrt } from '../../src';
import { GeometryError, Line, Line3D, Plane, Point, Point2D, Point3D, Undecidable } from '../../src/geometry';
import { matrixRank, newPoint, normalizeDimension, pointOptions, exprEquals, toInput } from '../../src/geometry/point';
import { rotate, scale, translate } from '../../src/geometry/entity';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : String(e));
const real = (n: string): Sym => new Sym(n, { real: true });
const [x, y, x1, x2, x3, y1, y2, y3] = ['x', 'y', 'x1', 'x2', 'x3', 'y1', 'y2', 'y3'].map(real) as [Sym, Sym, Sym, Sym, Sym, Sym, Sym, Sym];

describe('Point (SymPy test_point)', () => {
  const p1 = Point(x1, x2);
  const p2 = Point(y1, y2);
  const p3 = Point(0, 0);
  const p4 = Point(1, 1);
  const p5 = Point(0, 1);
  const line = Line(Point(1, 0), { slope: 1 });

  it('constructs points', () => {
    expect(s(Point(1, 2, 3))).toBe('Point3D(1, 2, 3)');
    expect(s(Point([1, 2]))).toBe('Point2D(1, 2)');
    expect(s(Point({ dim: 4 }))).toBe('Point(0, 0, 0, 0)');
    expect(s(Point(0.5, 0.25))).toBe('Point2D(1/2, 1/4)');
    expect(s(Point(0.5, 0.25, { evaluate: false }))).toBe('Point2D(0.5, 0.25)');
    expect(s(Point(34.05, sqrt(3)))).toBe('Point2D(681/20, sqrt(3))');
    expect(s(Point2D([1, 2]))).toBe('Point2D(1, 2)');
    expect(s(Point3D(0.5, 0.25, 2))).toBe('Point3D(1/2, 1/4, 2)');
    expect(Point(p4)).toBe(p4);
    expect(s(Point(p4, { dim: 3 }))).toBe('Point3D(1, 1, 0)');
    expect(s(Point(Point(0.1, 0.2, { evaluate: false }), { dim: 4 }))).toBe('Point(0.1, 0.2, 0, 0)');
    expect(s(Point({ dim: 3, onMorph: 'error' }))).toBe('Point3D(0, 0, 0)');
    expect(() => Point(1)).toThrow(TypeError);
    expect(() => Point([1])).toThrow(RangeError);
    expect(() => Point(3, I)).toThrow('Imaginary coordinates are not permitted.');
    expect(() => Point(1, 1, { dim: 3, onMorph: 'error' })).toThrow(RangeError);
    expect(() => Point(1, 1, { dim: 3, onMorph: 'unknown' as 'error' })).toThrow("on_morph value should be 'error', 'warn' or 'ignore'.");
    expect(() => Point(1, 2, { dim: 1 })).toThrow('Nonzero coordinates cannot be removed.');
    expect(() => Point(Point(1, 2), 3)).toThrow('Coordinates must be valid SymPy expressions.');
    expect(() => newPoint(parse('x + 1'))).toThrow('Expecting sequence of coordinates, not `Add`');
    expect(() => toInput('a')).toThrow(TypeError);
    // SymPy Point(1, 2, dim=Integer(3)): the dimension may be an Integer
    expect(pointOptions({ dim: Rational.of(3n) })).toEqual({ dim: 3 });
    expect(s(Point(1, 2, 0, { dim: 2 }))).toBe('Point2D(1, 2)');
  });

  it('membership, arithmetic and properties', () => {
    expect(p1.contains(p1)).toBe(true);
    expect(p1.contains(p2)).toBe(false);
    expect(Point(0, 0, 0, 0).contains(S.Zero)).toBe(true);
    expect(Point(0, 0, 0, 0).contains(S.One)).toBe(false);
    expect(Point(0, 0, 0, 0).contains(0)).toBe(false);
    expect(p1.contains(1)).toBe(false);
    expect(s(p3.add(p4))).toBe('Point2D(1, 1)');
    expect(s(p2.sub(p1))).toBe('Point2D(-x1 + y1, -x2 + y2)');
    expect(s(p2.sub([1, 2]))).toBe('Point2D(y1 - 1, y2 - 2)');
    expect(s(p2.neg())).toBe('Point2D(-y1, -y2)');
    expect(s(p4.mul(5))).toBe('Point2D(5, 5)');
    expect(s(p4.div(5))).toBe('Point2D(1/5, 1/5)');
    expect(() => p3.add(10)).toThrow(GeometryError);
    expect(() => p3.add([1, I])).toThrow('Imaginary coordinates are not permitted.');
    expect(s(Point.project([0, 1], [1, 0]))).toBe('Point2D(0, 0)');
    expect(s(Point.project([1, 1], [1, 0]))).toBe('Point2D(1, 0)');
    expect(() => Point.project(p1, Point(0, 0))).toThrow('Cannot project to the zero vector.');
    expect(() => Point(1, 2).add(Point(1, 2, 3, 4, 5, 6).mul(Point(1, 1)))).toThrow();
    expect(s(Point(parse('x*(x - 1)'), parse('y')).sub(Point(parse('x**2 - x'), parse('y + 1'))))).toBe('Point2D(0, -1)');
    expect(s(p4.abs())).toBe('sqrt(2)');
    expect(s(p4.length)).toBe('0');
    expect(s(p1.origin)).toBe('Point2D(0, 0)');
    expect(s(Point(0, 1).orthogonalDirection)).toBe('Point2D(1, 0)');
    expect(s(Point(1, 0).orthogonalDirection)).toBe('Point2D(0, 1)');
    expect(s(Point(1, 2, 3).orthogonalDirection)).toBe('Point3D(-2, 1, 0)');
    expect(s(Point(1, 1).unit)).toBe('Point2D(sqrt(2)/2, sqrt(2)/2)');
    expect(p1.isZero).toBe('unknown');
    expect(p3.isZero).toBe(true);
    expect(p4.isZero).toBe(false);
    expect(p1.isNonzero).toBe('unknown');
    expect(p3.isNonzero).toBe(false);
    expect(p4.isNonzero).toBe(true);
    expect(s(p4.coordinates)).toBe('[1, 1]');
    expect(s(p4.coordinate(-1))).toBe('1');
    expect(p4.isPoint).toBe(true);
    expect(s(Point2D(1, 5).bounds)).toBe('[1, 5, 1, 5]');
  });

  it('distances and products', () => {
    expect(s(p3.midpoint(p4))).toBe('Point2D(1/2, 1/2)');
    expect(s(p1.midpoint(p4))).toBe('Point2D(x1/2 + 1/2, x2/2 + 1/2)');
    expect(s(p2.midpoint(p2))).toBe('Point2D(y1, y2)');
    expect(s(p3.distance(p4))).toBe('sqrt(2)');
    expect(s(p1.distance(p1))).toBe('0');
    expect(s(p3.distance(p2))).toBe('sqrt(y1**2 + y2**2)');
    expect(s(p3.distance([3, 4]))).toBe('5');
    expect(() => p1.distance(0 as never)).toThrow(TypeError);
    expect(s(p1.distance(line))).toBe(s(line.distance(p1)));
    expect(s(p4.distance(line))).toBe('sqrt(2)/2');
    expect(s(p4.taxicabDistance(p3))).toBe('2');
    expect(s(p4.canberraDistance(p5))).toBe('1');
    expect(() => p3.canberraDistance(p3)).toThrow(RangeError);
    expect(s(Point(1, 2).dot([3, 4]))).toBe('11');
    expect(s(Point2D(1, 5).distance(Point2D(4, 2.5)))).toBe('sqrt(61)/2');
    expect(s(Point2D(4, 2.5).distance([6, 3]))).toBe('sqrt(17)/2');
    // SymPy warns about the dimension change
    expect(s(Point3D(1, 0, 2).distance(Point2D(2, 0)))).toBe('sqrt(5)');
  });

  it('collinear, concyclic and scalar multiples', () => {
    expect(p3.isCollinear()).toBe(true);
    expect(p3.isCollinear(p4)).toBe(true);
    expect(p3.isCollinear(Point(p3, { dim: 4 }))).toBe(true);
    expect(p3.isCollinear(p4, Point(x1, x1), Point(y2, y2))).toBe(true);
    expect(p3.isCollinear(p4, Point(x1, x1), Point(parse('x1 + 1'), x1))).toBe(false);
    expect(p3.isCollinear(p3, p4, p5)).toBe(false);
    expect(Point(1, 1).isCollinear([2, 2], [3, 4])).toBe(false);
    const xp = new Sym('x', { positive: true });
    const [q1, q2, q3, q4, q5] = [Point(xp, 0), Point(0, xp), Point(xp.neg(), 0), Point(0, xp.neg()), Point(xp, 5)];
    expect(q1.isConcyclic()).toBe(true);
    expect(q1.isConcyclic(q2)).toBe(true);
    expect(q1.isConcyclic(q2, q3, q4)).toBe(true);
    expect(q1.isConcyclic(q2, q3, q5)).toBe(false);
    expect(p4.isConcyclic(p4.mul(2), p4.mul(3))).toBe(false);
    expect(Point(0, 0).isConcyclic([1, 1], [2, 2], [2, 1])).toBe(false);
    expect(Point(-1, 0).isConcyclic(Point(1, 0), Point(0, 1))).toBe(true);
    expect(Point(-1, 0).isConcyclic(Point(1, 0), Point(0, 1), Point(-1, 2))).toBe(false);
    expect(Point(0, 0, 0, 0).isConcyclic(Point(1, 0, 0, 0), Point(1, 1, 0, 0), Point(1, 1, 1, 0))).toBe(false);
    expect(p1.isScalarMultiple(p1)).toBe(true);
    expect(p1.isScalarMultiple(p1.mul(2))).toBe(true);
    expect(p1.isScalarMultiple(p2)).toBe(false);
    expect(Point(1, 1).isScalarMultiple([-1, -1])).toBe(true);
    expect(Point(0, 0).isScalarMultiple([0, -1])).toBe(true);
    expect(Point(1, 2, 3).isScalarMultiple([2, 4, 6])).toBe(true);
    expect(() => Point(Mod(x1, y1), Mod(x2, y2)).isScalarMultiple(Point(0, 1))).toThrow(Undecidable);
    expect(Point.affineRank()).toBe(-1);
    expect(Point.affineRank([0, 0], [1, 1], [2, 3])).toBe(2);
    // an entry that cannot be evaluated numerically is tested by is_zero
    expect(Point.affineRank([0, 0], [parse('f(1)'), 0])).toBe(1);
    expect(Point.areCoplanar()).toBe(true);
    expect(Point.areCoplanar([1, 2, 0], [1, 2, 0], [1, 3, 0])).toBe(true);
    expect(Point.areCoplanar([1, 2, 0], [1, 2, 3])).toBe(true);
    expect(Point.areCoplanar([0, 0, 0], [1, 1, 0], [1, 1, 1], [1, 2, 1])).toBe(false);
    expect(Point.areCoplanar(Point(x, y), Point(x, parse('x + y')), Point(y, parse('x + 2')))).toBe(true);
    const plane = Plane([1, 2, 1], [2, 1, 0], [3, 1, 2]);
    expect(Point.areCoplanar(...[0, 1, 2, 3].map((i) => plane.projection([(-1) ** i, i])))).toBe(true);
  });

  it('intersections and equality', () => {
    expect(s(p3.intersection(Point(0, 0)))).toBe('[Point2D(0, 0)]');
    expect(s(p3.intersection(p4))).toBe('[]');
    expect(s(p3.intersection(line))).toBe('[]');
    expect(s(p3.intersection([0, 0]))).toBe('[Point2D(0, 0)]');
    expect(s(Point(0, 0, 0).intersection(Point(0, 0)))).toBe('[]');
    expect(s(Point(0, 0).intersection(Point(0, 0, 0)))).toBe('[]');
    // SymPy Point.intersection(Point(0, 0, 0, 0), Point(0, 0)) (with a dimension warning)
    expect(s(Point(0, 0, 0, 0).intersection(Point(0, 0)))).toBe('[Point(0, 0, 0, 0)]');
    expect(p4.equals(Point(1, 1))).toBe(true);
    expect(Point(1, parse('sqrt(2)**2 - 1')).equals(Point(1, 1))).toBe(true);
    expect(p4.equals(Point(1, 1, 1))).toBe(false);
    expect(p4.equals(x1)).toBe(false);
  });

  it('transformations', () => {
    expect(s(Point(1, 0).rotate(pi.div(2)))).toBe('Point2D(0, 1)');
    expect(s(Point(1, 0).rotate(pi.div(2), Point(1, 0)))).toBe('Point2D(1, 0)');
    expect(s(p4.rotate(pi, Point(0.5, 0.5)))).toBe('Point2D(0, 0)');
    expect(s(Point(1, 1).scale(2, 3))).toBe('Point2D(2, 3)');
    expect(s(Point(1, 1).scale())).toBe('Point2D(1, 1)');
    expect(s(Point(1, 1).scale(2, 3, [4, 5]))).toBe('Point2D(-2, -7)');
    expect(s(Point(1, 1).translate(1, 2))).toBe('Point2D(2, 3)');
    expect(s(Point(1, 1).translate(1))).toBe('Point2D(2, 1)');
    expect(s(Point(1, 1).translate())).toBe('Point2D(1, 1)');
    expect(s(Point2D(1, 1).transform(rotate(pi.div(2))))).toBe('Point2D(-1, 1)');
    expect(s(Point2D(1, 1).transform(scale(3, 2)))).toBe('Point2D(3, 2)');
    expect(s(Point2D(1, 1).transform(translate(1, 2)))).toBe('Point2D(2, 3)');
    expect(s(scale(1, 2, [3, 4]))).toBe('Matrix([[1, 0, 0], [0, 2, 0], [0, -4, 1]])');
    expect(() => Point2D(0, 0).transform(p3 as never)).toThrow('matrix must be a 3x3 matrix');
    expect(() => Point2D(1, 1).transform(Matrix.of([[1, 0], [0, 1]]))).toThrow(RangeError);
    expect(s(Point(1, 1).subs(x, 2))).toBe('Point2D(1, 1)');
    expect(s(Point(x, 1).subs(x, 0.5))).toBe('Point2D(1/2, 1)');
    expect(s(Point(1, 2, 3, 4).subs(S.One, 5))).toBe('Point(5, 2, 3, 4)');
    expect(s(Point(S.Half, Rational.of(1n, 3n)).evalf(2))).toBe('Point2D(0.5, 0.33)');
    expect(s(Point(1, 2).evalf())).toBe('Point2D(1.0, 2.0)');
    expect(latex(Point(1, 2))).toBe('\\operatorname{Point2D}\\left(1, 2\\right)');
  });
});

describe('Point3D (SymPy test_point3D)', () => {
  const p1 = Point3D(x1, x2, x3);
  const p2 = Point3D(y1, y2, y3);
  const p3 = Point3D(0, 0, 0);
  const p4 = Point3D(1, 1, 1);
  const p5 = Point3D(0, 1, 2);
  const p = Point3D(1, 1, 1);

  it('works like SymPy', () => {
    expect(p1.contains(p1)).toBe(true);
    expect(p1.contains(p2)).toBe(false);
    expect(s(p2.y)).toBe('y2');
    expect(s(p2.sub(p1))).toBe('Point3D(-x1 + y1, -x2 + y2, -x3 + y3)');
    expect(s(p3.midpoint(p4))).toBe('Point3D(1/2, 1/2, 1/2)');
    expect(s(p3.distance(p4))).toBe('sqrt(3)');
    expect(Point3D.areCollinear()).toBe(true);
    expect(Point3D.areCollinear(p3, p4)).toBe(true);
    expect(Point3D.areCollinear(p3, p4, Point3D(x1, x1, x1), Point3D(y2, y2, y2))).toBe(true);
    expect(Point3D.areCollinear(p3, p3, p4, p5)).toBe(false);
    expect(Point3D.areCollinear(Point3D(4, -2, 6), Point3D(1, 2, 3), Point3D(7, 2, 3))).toBe(false);
    expect(s(p3.intersection(Point3D(0, 0, 0)))).toBe('[Point3D(0, 0, 0)]');
    expect(s(p3.intersection(p4))).toBe('[]');
    expect(s(p3.intersection([0, 0, 0]))).toBe('[Point3D(0, 0, 0)]');
    expect(s(p4.div(5))).toBe('Point3D(1/5, 1/5, 1/5)');
    expect(s(p5.coordinates)).toBe('[0, 1, 2]');
    expect(s([p5.x, p5.y, p5.z])).toBe('[0, 1, 2]');
    expect(s(Point3D(0.1, 0.2, { evaluate: false }))).toBe('Point3D(0.1, 0.2, 0)');
    expect(s(p.scale(2, 3))).toBe('Point3D(2, 3, 1)');
    expect(s(p.scale())).toBe('Point3D(1, 1, 1)');
    expect(s(p.translate(1, 2))).toBe('Point3D(2, 3, 1)');
    expect(s(p.translate(1))).toBe('Point3D(2, 1, 1)');
    expect(s(p.translate(0, 0, 1))).toBe('Point3D(1, 1, 2)');
    expect(s(p.translate())).toBe('Point3D(1, 1, 1)');
    const planar2 = Point3D(1, 1, 2);
    const planar3 = Point3D(1, 1, 3);
    expect(s(planar2.intersection(Line3D(p, planar3)))).toBe('[Point3D(1, 1, 2)]');
    expect(s(planar2.scale(1, 1, 1))).toBe('Point3D(1, 1, 2)');
    expect(s(planar2.scale(2, 2, 2, planar3))).toBe('Point3D(1, 1, 1)');
    expect(s(planar2.scale(1, 1, 1, p3))).toBe('Point3D(1, 1, 2)');
    // a point as the third argument is the center (the scale of z is 1), as GeometryEntity.scale(x, y, pt)
    expect(s(planar2.scale(2, 2, [1, 1, 3]))).toBe('Point3D(1, 1, 2)');
    const identity = Matrix.eye(4);
    expect(s(p.transform(identity))).toBe('Point3D(1, 1, 1)');
    const trans = Matrix.of([
      [1, 0, 0, 1],
      [0, 1, 0, 1],
      [0, 0, 1, 1],
      [0, 0, 0, 1],
    ]);
    expect(s(p.transform(trans))).toBe('Point3D(2, 2, 2)');
    expect(() => p.transform(Matrix.of([[1, 0], [0, 1]]))).toThrow('matrix must be a 4x4 matrix');
    expect(s(p.sub(Point(0, 0, 0, 1)))).toBe('Point(1, 1, 1, -1)');
    expect(s(p.directionRatio(Point3D(2, 3, 5)))).toBe('[1, 2, 4]');
    expect(s(p3.directionCosine(Point3D(0, 0, pi)))).toBe('[0, 0, 1]');
    expect(s(p3.directionCosine(Point3D(-12, -15, 0)))).toBe('[-4*sqrt(41)/41, -5*sqrt(41)/41, 0]');
    expect(s(Point3D(1, 2, 3).evalf(2))).toBe('Point3D(1.0, 2.0, 3.0)');
  });
});

describe('point helpers', () => {
  it('normalize dimensions and ranks', () => {
    expect(s(normalizeDimension([Point(1, 2), Point(3, 4)]))).toBe('[Point2D(1, 2), Point2D(3, 4)]');
    expect(s(normalizeDimension([Point(1, 2), Point(3, 4, 0)], { onMorph: 'ignore' }))).toBe('[Point3D(1, 2, 0), Point3D(3, 4, 0)]');
    const z = (e: { key: string }): boolean | undefined => (e.key === S.Zero.key ? true : undefined);
    expect(matrixRank([], z)).toBe(0);
    expect(matrixRank([[S.Zero, S.One]], (e) => e.key === S.Zero.key)).toBe(1);
    expect(matrixRank([[S.Zero], [S.Zero]], (e) => e.key === S.Zero.key)).toBe(0);
    expect(matrixRank([[S.Zero, S.Zero], [S.Zero, S.Zero]], (e) => e.key === S.Zero.key)).toBe(0);
    expect(matrixRank([[S.One, S.One], [S.One, S.One]], (e) => e.key === S.Zero.key)).toBe(1);
    expect(matrixRank([[S.One, S.Zero], [S.Zero, S.One]], (e) => e.key === S.Zero.key)).toBe(2);
    // undecided entries: simplified, then compared with zero
    const und = (e: { key: string }): boolean | undefined => (e.key === S.Zero.key ? true : e.key === S.One.key ? false : undefined);
    expect(matrixRank([[x, y, S.One], [x, y, S.One], [S.Zero, S.Zero, S.Zero]], und)).toBe(1);
    expect(matrixRank([[parse('x - x'), S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero]], und)).toBe(0);
    expect(matrixRank([[x, S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero]], (e) => (e.key === S.Zero.key ? true : undefined))).toBe(1);
    expect(matrixRank([[parse('(x + 1)**2 - x**2 - 2*x - 1'), S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero]], () => undefined)).toBe(0);
    expect(exprEquals(parse('sqrt(2)*sqrt(3) - sqrt(6)'), 0)).toBe(true);
    expect(exprEquals(parse('pi'), 3)).toBe(false);
    // SymPy (x - y).equals(0) and f(x1).equals(0) are False, Mod(x1, x2).equals(0) is None
    expect(exprEquals(x, y)).toBe(false);
    expect(exprEquals(parse('f(x1)'), 0)).toBe(false);
    expect(exprEquals(Mod(x1, x2), 0)).toBe(undefined);
    expect(exprEquals(parse('sin(x1)**2 + cos(x1)**2 - 1 + x1 - x1'), 0)).toBe(true);
    expect(exprEquals(parse('zoo'), 0)).toBe(false);
    // SymPy ((x + 1)**2 - x**2 - 2*x).equals(0), (sqrt(2) + sqrt(3) - pi).equals(0): False
    expect(exprEquals(parse('(x + 1)**2 - x**2 - 2*x'), 0)).toBe(false);
    expect(exprEquals(parse('sqrt(2) + sqrt(3) - pi'), 0)).toBe(false);
    // SymPy (cos(pi/7) + cos(3*pi/7) + cos(5*pi/7) - 1/2).equals(0): True (symjs: undecided)
    expect(exprEquals(parse('cos(pi/7) + cos(3*pi/7) + cos(5*pi/7) - 1/2'), 0)).toBe(undefined);
    expect(matrixRank([[parse('(x + 1)**2 - x**2 - 2*x'), S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero], [S.Zero, S.Zero, S.Zero]], und)).toBe(1);
  });
});
