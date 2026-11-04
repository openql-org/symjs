// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/entity.ts (SymPy sympy/geometry/entity.py and
// sympy/geometry/tests/test_entity.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Expr, Gt, Lt, NotImplementedError, Rational, S, Sym, cos, pi, sin, symbols } from '../../src';
import {
  Circle,
  Curve,
  Ellipse,
  GeometryEntity,
  GeometrySet,
  Line,
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
