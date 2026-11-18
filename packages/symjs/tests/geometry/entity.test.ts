// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/entity.ts (SymPy sympy/geometry/entity.py and
// sympy/geometry/tests/test_entity.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as setsApi from '../../src/sets';
import * as geometryApi from '../../src/geometry';
import { Expr, Gt, Lt, NotImplementedError, Rational, S, Sym, cos, pi, sin, symbols } from '../../src';
import {
  Circle,
  Curve,
  Ellipse,
  GeometryEntity,
  GeometrySet,
  Line,
  Line2D,
  Parabola,
  Plane,
  Point,
  Point3D,
  Polygon,
  Ray,
  RegularPolygon,
  Segment,
  Triangle,
} from '../../src/geometry';
import type { Line2DNode } from '../../src/geometry';
import { decide, realSymbol, rotate, scale, translate, tryDecide } from '../../src/geometry/entity';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : String(e));

/** SymPy GeometryEntity(x, y): an entity without any of the methods of the subclasses. */
class Bare extends GeometrySet {
  constructor(args: readonly Expr[]) {
    super('GeometryEntity', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Bare(args);
  }
  get ambientDimension(): number {
    return 2;
  }
}

describe('GeometryEntity (SymPy test_entity)', () => {
  const [x, y] = symbols('x y', { real: true }) as [Sym, Sym];

  it('the base class', () => {
    const g = new Bare([x, y]);
    expect(g.contains(new Bare([x, y]))).toBe(true);
    expect(g.contains(new Bare([y, x]))).toBe(false);
    expect(() => g.contains(Point(0, 0))).toThrow(NotImplementedError);
    expect(g.equals(new Bare([x, y]))).toBe(true);
    expect(g.equals(2)).toBe(false);
    expect(g.isPoint).toBe(false);
    expect(() => g.bounds).toThrow(NotImplementedError);
    expect(() => g.enclosesPoint([0, 0])).toThrow(NotImplementedError);
    expect(() => Circle([0, 0], 1).encloses(g)).toThrow(NotImplementedError);
    expect(() => g.distance(Point(0, 0))).toThrow(TypeError);
    expect(() => Point(0, 0).distance(g)).toThrow(TypeError);
    expect(() => g.intersection(g)).toThrow(NotImplementedError);
    expect(() => g.isSimilar(g)).toThrow(NotImplementedError);
    expect(() => g.arbitraryPoint()).toThrow(NotImplementedError);
    expect(s(g.translate(1, 2))).toBe('GeometryEntity(x, y)');
    expect(s(g.scale(2, 3))).toBe('GeometryEntity(x, y)');
    expect(s(g.rotate(pi))).toBe('GeometryEntity(x, y)');
    expect(s(g.evalf())).toBe('GeometryEntity(x, y)');
    expect(s(new Bare([pi, x]).evalf(3))).toBe('GeometryEntity(3.14, x)');
  });

  it('encloses (SymPy GeometryEntity.encloses)', () => {
    const c = Circle([0, 0], 5);
    expect(c.encloses(Point(0, 0))).toBe(true);
    expect(c.encloses(Segment([0, 0], [1, 1]) as GeometryEntity)).toBe(true);
    expect(c.encloses(Line([0, 0], [1, 1]))).toBe(false);
    expect(c.encloses(Circle([0, 0], 4))).toBe(true);
    expect(c.encloses(Polygon(Point(0, 0), Point(1, 0), Point(0, 1)))).toBe(true);
    expect(c.encloses(RegularPolygon(Point(8, 8), 1, 3))).toBe(false);
  });

  it('substitution (SymPy test_subs)', () => {
    const p = Point(x, 2);
    const q = Point(1, 1);
    const r = Point(3, 4);
    for (const o of [p, Segment(p, q), Ray(p, q), Line(p, q), Triangle(p, q, r), RegularPolygon(p, 3, 6), Polygon(p, q, r, Point(5, 4)), Circle(p, 3), Ellipse(p, 3, 4)]) {
      expect(s(o.subs(x, y))).toContain('y');
    }
    expect(s(p.subs(x, 1))).toBe('Point2D(1, 2)');
    expect(s(Point(1, 2).subs(Point(1, 2), Point(3, 4)))).toBe('Point2D(3, 4)');
  });

  it('transformation matrices (SymPy test_transform)', () => {
    expect(s(scale(1, 2, [3, 4]))).toBe('Matrix([[1, 0, 0], [0, 2, 0], [0, -4, 1]])');
    expect(s(scale(2, 3))).toBe('Matrix([[2, 0, 0], [0, 3, 0], [0, 0, 1]])');
    expect(s(translate(1, 2))).toBe('Matrix([[1, 0, 0], [0, 1, 0], [1, 2, 1]])');
    expect(s(rotate(pi.div(2)))).toBe('Matrix([[0, 1, 0], [-1, 0, 0], [0, 0, 1]])');
  });

  it('reflections (SymPy test_reflect_entity_overrides)', () => {
    const [b, m] = [new Sym('b'), new Sym('m')];
    const l = Line([0, b], { slope: m }) as Line2DNode;
    const p = Point(x, y);
    const r = p.reflect(l);
    const c = Circle([x, y], 3);
    const cr = c.reflect(l);
    expect(s(cr)).toBe(s(Circle(r, -3)));
    expect(s((c as GeometryEntity & { area: Expr }).area.add((cr as GeometryEntity & { area: Expr }).area))).toBe('0');
    expect(s(Point(1, 2).reflect(Line([0, 0], { slope: 0 }) as Line2DNode))).toBe('Point2D(1, -2)');
    expect(s(Point(1, 2).reflect(Line([0, 3], { slope: 0 }) as Line2DNode))).toBe('Point2D(1, 4)');
    expect(s(Point(1, 2).reflect(Line([0, 0], { slope: S.Infinity }) as Line2DNode))).toBe('Point2D(-1, 2)');
    expect(s(Point(1, 2).reflect(Line([3, 0], { slope: S.Infinity }) as Line2DNode))).toBe('Point2D(5, 2)');
    expect(s(Point(1, 2).reflect(Line([0, 0], [1, 1]) as Line2DNode))).toBe('Point2D(2, 1)');
    const pent = RegularPolygon([1, 2], 1, 4);
    const lp = Line(pent.vertices[1] as Expr, { slope: Rational.of(1n, 3n) }) as Line2DNode;
    const rpent = pent.reflect(lp) as typeof pent;
    expect(rpent.center.equals(pent.center.reflect(lp) as Expr)).toBe(true);
    expect(s(pent.area.add(rpent.area).simplify())).toBe('0');
  });

  it('numerical evaluation (SymPy test_geometry_EvalfMixin)', () => {
    const X = pi;
    const t = new Sym('t');
    for (const g of [
      Point(X, X),
      Plane(Point(0, X, 0), { normalVector: [0, 0, X] }),
      Curve([X.mul(t), X], [t, 0, X]),
      Ellipse([X, X], X, X.neg()),
      Circle([X, X], X),
      Line([0, X], [X, 0]),
      Segment([0, X], [X, 0]),
      Ray([0, X], [X, 0]),
      Parabola([0, X], Line([X.neg(), 0], [X, 0])),
      Polygon([0, 0], [0, X], [X, 0], [X, X]),
      RegularPolygon([0, X], X, 4, X),
      Triangle([0, 0], [X, 0], [X, X]),
    ]) {
      expect(s(g.n(2))).toBe(s(g).replace(/pi/g, '3.1'));
    }
  });

  it('python truth values', () => {
    expect(decide(true)).toBe(true);
    expect(decide(S.true)).toBe(true);
    expect(decide(Lt(1, 2))).toBe(true);
    // equal sides once the difference is simplified
    expect(decide(Gt(cos(x).pow(2).add(sin(x).pow(2)), 1))).toBe(false);
    expect(() => decide(Gt(x, 0))).toThrow('cannot determine truth value of Relational');
    expect(tryDecide(Gt(x, 0))).toBe(undefined);
    expect(decide(S.Zero)).toBe(false);
    expect(decide(x)).toBe(true);
    expect(s(realSymbol('t'))).toBe('t');
    expect(realSymbol(x)).toBe(x);
    expect(Point3D(1, 2, 3).ambientDimension).toBe(3);
  });
});

it('constructs a base geometry entity and leaves its ambient dimension unspecified', () => {
  const x = new Sym('x');
  const entity = new GeometryEntity('GeometryEntity', [x]);
  expect(String(entity)).toBe('GeometryEntity(x)');
  expect(entity.equals(new GeometryEntity('GeometryEntity', [x]))).toBe(true);
  expect(() => entity.ambientDimension).toThrow(NotImplementedError);
  expect(() => entity.contains(Point(0, 0))).toThrow(NotImplementedError);
});

it('transforms nested geometry arguments and solves their point parameters', () => {
  const x = new Sym('x');
  const g = new GeometryEntity('GeometryEntity', [Point(1, 2), x]);
  expect(String(g.scale(2, 3, [4, 5]))).toBe('GeometryEntity(Point2D(-2, -4), x)');
  expect(String(g.scale())).toBe(String(g));
  expect(String(g.rotate(pi))).toBe('GeometryEntity(Point2D(-1, -2), x)');
  expect(String(g.translate(2, 3))).toBe('GeometryEntity(Point2D(3, 5), x)');
  const axis = Line([0, 0], [1, 0]);
  if (!(axis instanceof Line2D)) throw new TypeError('expected a planar line');
  expect(String(g.reflect(axis))).toBe('GeometryEntity(Point2D(1, -2), x)');
  const t = new Sym('t');
  const line = Line([0, 0], [1, 1]);
  for (const point of [[2, 2], Point(2, 2)]) {
    const result = line.parameterValue(point, t);
    expect(result).toBeInstanceOf(Map);
    if (!(result instanceof Map)) throw new TypeError('expected parameter bindings');
    expect([...result].map(([k, v]) => [String(k), String(v)])).toEqual([['t', '2']]);
  }
  expect(() => line.parameterValue([1, 2], t)).toThrow(RangeError);
  expect(() => line.parameterValue(Circle([0, 0], 1), t)).toThrow('other must be a point');
});

describe('geometric sets in Union and Intersection (SymPy test_geometrysets)', () => {
  const sj = { ...setsApi, ...geometryApi };
  const P = sj.Point;
  const set = sj.geometrySet;
  const l1 = sj.Line(P(0, 0), P(1, 1));
  const l4 = sj.Line(P(5, 1), P(0, 1));
  const l3 = sj.Line(P(5, 1), P(1, -1));
  const poly1 = sj.Polygon(P(0, 0), P(1, 0), P(5, 1), P(0, 1));
  const poly2 = sj.Triangle(P(3, 2), P(1, -1), P(0, 2));
  const poly3 = sj.Triangle(P(0, 0), P(1, 0), P(3, 2));
  const show = (s: unknown) => String(s);
  it('intersects entities into their common points and entities', () => {
    expect(show(sj.Intersection(set(l1), set(l4)))).toBe('{Point2D(1, 1)}');
    expect(show(sj.Intersection(sj.Union(set(l1), set(l4)), set(l3)))).toBe('{Point2D(-3, -3), Point2D(5, 1)}');
    expect(sj.Intersection(set(l1), sj.finiteSet(P(7, -7)))).toBe(sj.EmptySet);
    expect(show(sj.Intersection(set(sj.Circle(P(0, 0), 3)), set(sj.Line(P(0, 0), P(1, 0)))))).toBe('{Point2D(-3, 0), Point2D(3, 0)}');
    expect(show(sj.Intersection(set(l1), sj.finiteSet(P(0, 0))))).toBe('{Point2D(0, 0)}');
    expect(show(sj.Intersection(set(poly1), set(poly2)))).toBe('{Point2D(1/3, 1), Point2D(2/3, 0), Point2D(9/5, 1/5), Point2D(7/3, 1)}');
    expect(show(sj.Intersection(set(poly1), set(poly3)))).toBe('Union({Point2D(3/2, 1), Point2D(2, 1)}, Segment2D(Point2D(0, 0), Point2D(1, 0)))');
  });
  it('absorbs the points and the sets an entity contains in a union', () => {
    const fs = sj.finiteSet(P(Rational.of(1, 3), 1), P(Rational.of(2, 3), 0), P(Rational.of(9, 5), Rational.of(1, 5)), P(Rational.of(7, 3), 1));
    expect(show(sj.Union(set(l1), sj.finiteSet(P(0, 0))))).toBe('Line2D(Point2D(0, 0), Point2D(1, 1))');
    expect(show(sj.Union(set(poly1), set(poly2), fs))).toBe('Union(Polygon(Point2D(0, 0), Point2D(1, 0), Point2D(5, 1), Point2D(0, 1)), Triangle(Point2D(3, 2), Point2D(1, -1), Point2D(0, 2)))');
    expect(show(sj.Union(set(poly1), sj.finiteSet(P(0, 0), P(3, 5))))).toBe('Union({Point2D(3, 5)}, Polygon(Point2D(0, 0), Point2D(1, 0), Point2D(5, 1), Point2D(0, 1)))');
    // no point of the finite set lies on the line: nothing combines
    expect(show(sj.Union(set(l1), sj.finiteSet(P(1, 5))))).toBe('Union({Point2D(1, 5)}, Line2D(Point2D(0, 0), Point2D(1, 1)))');
    // a segment of the line is absorbed
    expect(show(sj.Union(set(l1), set(sj.Segment(P(0, 0), P(2, 2)))))).toBe('Line2D(Point2D(0, 0), Point2D(1, 1))');
  });
  it('is a set of points', () => {
    const s = set(l1);
    expect(s).toBeInstanceOf(sj.GeometrySetNode);
    expect(s.className).toBe('Line2D');
    expect(s.key).toBe(`GeometrySet(${l1.key})`);
    expect(s.elementOf(P(2, 2))).toBe(true);
    expect(s.elementOf(sj.finiteSet(P(2, 2), P(3, 3)))).toBe(true);
    expect(s.elementOf(sj.finiteSet(P(2, 2), P(3, 4)))).toBe(false);
    expect(show(s.withArgs([l4]))).toBe(show(l4));
    // without a rule the intersection stays
    expect(show(sj.Intersection(s, sj.Reals))).toBe('Intersection(Line2D(Point2D(0, 0), Point2D(1, 1)), Reals)');
    const [t] = symbols('t');
    const curve = sj.Curve([t, t.pow(2)], [t, 0, 2]);
    expect(show(sj.Intersection(s, set(curve)))).toContain('Intersection(');
    // an error other than a missing implementation is passed on
    expect(() => sj.Intersection(set(sj.Circle(P(0, 0), 3)), set(sj.Plane(sj.Point3D(0, 0, 0), [0, 0, 1])))).toThrow(TypeError);
  });
});
