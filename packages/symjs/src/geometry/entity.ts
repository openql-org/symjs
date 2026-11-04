// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/entity.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.entity: GeometryEntity, the base class of the
 * geometric entities (points, lines, planes, polygons, ellipses, curves,
 * parabolas), and the 2D transformation matrices translate, scale and
 * rotate.
 *
 * Entities are expression nodes (SymPy Basic): their arguments define them,
 * so substitution, structural equality and printing work as for any other
 * expression. The modules that define the entities register their
 * constructors here (SymPy imports them locally to avoid import cycles).
 */

import { BoolAtom, Dummy, Expr, ExtensionExpr, Rel, S, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { rel } from '../core/logic';
import { simplify } from '../simplify/simplify';
import { xreplace } from '../core/traverse';
import { ExprMap } from '../core/exprmap';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined } from '../core/guard';
import { cos, sin, atan } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
import { solveEquations } from './solvehelp';

/** A point given as an entity or as a sequence of coordinates (SymPy accepts any sequence). */
export type PointInput = Expr | readonly ExprLike[];

/** A 2D line as the reflection axis: its slope, coefficients and first point (SymPy Line2D). */
export interface ReflectionLine {
  readonly slope: Expr;
  readonly coefficients: readonly [Expr, Expr, Expr];
  readonly args: readonly Expr[];
}

/**
 * The constructors of the entity modules, registered when they are loaded
 * (the geometry modules import each other only downwards).
 */
export const geometryClasses: {
  /** SymPy Point(coords, dim=dim, evaluate=evaluate). */
  point?: (coords: PointInput, opts?: { dim?: number; evaluate?: boolean }) => GeometryEntity;
} = {};

/** SymPy Point(coords, dim=...): the point class registered by geometry/point. */
export function makePoint(coords: PointInput, opts: { dim?: number; evaluate?: boolean } = {}): GeometryEntity {
  return defined(geometryClasses.point, 'Point')(coords, opts);
}

/**
 * Python bool() of a SymPy comparison: true or false when it is decided, a
 * TypeError (SymPy "cannot determine truth value of Relational") otherwise.
 */
export function decide(e: Expr | boolean): boolean {
  const r = tryDecide(e);
  if (r === undefined) throw new TypeError('cannot determine truth value of Relational');
  return r;
}

/** The truth value of a SymPy comparison, or undefined when it is not decided (SymPy `isin in (True, False)`). */
export function tryDecide(e: Expr | boolean): boolean | undefined {
  if (typeof e === 'boolean') return e;
  if (e instanceof BoolAtom) return e.value;
  if (e instanceof Rel) {
    // SymPy compares with the simplified difference when the relation is not decided at once
    const r = rel(e.op, simplify(add(e.lhs, mul(-1, e.rhs))), 0);
    return r instanceof BoolAtom ? r.value : undefined;
  }
  // Python truth value of an expression: nonzero
  return !(e.key === S.Zero.key);
}

/** SymPy _symbol(name, real=True): a real symbol of that name, or the symbol itself. */
export function realSymbol(parameter: string | Sym): Sym {
  return typeof parameter === 'string' ? new Sym(parameter, { real: true }) : parameter;
}

/**
 * SymPy GeometryEntity: the base class of all geometric entities, an
 * expression node whose arguments define it.
 */
export abstract class GeometryEntity extends ExtensionExpr {
  /** The entity is a point (SymPy is_Point). */
  get isPoint(): boolean {
    return false;
  }

  /** The number of coordinates of the space the entity lives in (SymPy ambient_dimension). */
  abstract get ambientDimension(): number;

  /** The rectangle (xmin, ymin, xmax, ymax) bounding a 2D entity (SymPy bounds). */
  get bounds(): [Expr, Expr, Expr, Expr] {
    throw new NotImplementedError(`bounds of ${this.name} are not defined`);
  }

  /**
   * SymPy `o in self` (__contains__): o is a part of the entity. The base
   * rule only knows entities of the same class.
   */
  contains(o: unknown): boolean {
    if (o instanceof GeometryEntity && o.constructor === this.constructor) return o.key === this.key;
    throw new NotImplementedError(`${this.name} does not know whether it contains ${String(o)}`);
  }

  /**
   * SymPy encloses_point: the point lies inside the entity (true), outside
   * or on it (false), or it cannot be decided ('unknown').
   */
  enclosesPoint(_p: PointInput): boolean | 'unknown' {
    throw new NotImplementedError(`encloses_point is not defined for ${this.name}`);
  }

  /**
   * SymPy encloses: o lies inside this entity (no point of o is outside or
   * on the boundary).
   */
  encloses(o: GeometryEntity): boolean {
    return o.enclosedBy(this);
  }

  /**
   * The part of SymPy GeometryEntity.encloses that depends on the class of
   * the enclosed entity (points, segments, lines, ellipses and polygons
   * override it).
   */
  enclosedBy(_container: GeometryEntity): boolean {
    throw new NotImplementedError(`encloses is not defined for ${this.name}`);
  }

  /** SymPy equals: the entities are the same (structural equality unless a class knows better). */
  override equals(o: ExprLike): boolean {
    return o instanceof Expr && o.key === this.key;
  }

  /** The shortest distance to o (SymPy distance, defined by the entities that measure it). */
  distance(o: unknown): Expr {
    throw new TypeError(`distance between ${String(o)} and ${this.name} is not defined`);
  }

  /** The entities that this entity and o have in common (SymPy intersection). */
  intersection(_o: unknown): GeometryEntity[] {
    throw new NotImplementedError(`intersection of ${this.name} is not defined`);
  }

  /** The entities are similar: one can be scaled uniformly to the other (SymPy is_similar). */
  isSimilar(_other: GeometryEntity): boolean {
    throw new NotImplementedError(`is_similar of ${this.name} is not defined`);
  }

  /** A point on the entity as a function of a parameter (SymPy arbitrary_point). */
  arbitraryPoint(_parameter?: string | Sym | null): Expr {
    throw new NotImplementedError(`arbitrary_point of ${this.name} is not defined`);
  }

  /** The entity with each argument replaced (SymPy type(self)(*newargs)). */
  protected rebuildWith(args: readonly Expr[]): GeometryEntity {
    return cast(this.withArgs(args), GeometryEntity, 'geometry entity');
  }

  /** The reflection of the entity in a 2D line (SymPy reflect). */
  reflect(line: ReflectionLine): GeometryEntity {
    const g: GeometryEntity = this;
    const l = line;
    const slope = l.slope;
    const p0 = at(l.args, 0);
    const points = pointsOf(g);
    let reps: [Expr, Expr][];
    if (slope.key === S.Zero.key) {
      const v = at(p0.args, 1);
      if (v.key === S.Zero.key) return g.scale(1, -1);
      reps = points.map((p) => [p, p.translate(0, mul(2, add(v, mul(-1, at(p.args, 1)))))]);
    } else if (slope.key === S.Infinity.key) {
      const v = at(p0.args, 0);
      if (v.key === S.Zero.key) return g.scale(-1, 1);
      reps = points.map((p) => [p, p.translate(mul(2, add(v, mul(-1, at(p.args, 0)))), 0)]);
    } else {
      const a = atan(slope);
      const c = l.coefficients;
      const d = mul(-1, c[2], c[1].pow(-1));
      const o = makePoint([0, 0]);
      const [x, y] = [new Dummy('entity_dummy'), new Dummy('entity_dummy')];
      const xf = makePoint([x, y]).translate(0, mul(-1, d)).rotate(mul(-1, a), o).scale(1, -1).rotate(a, o).translate(0, d);
      reps = points.map((p) => [p, xreplace(xf, [[x, at(p.args, 0)], [y, at(p.args, 1)]])]);
    }
    return cast(xreplace(g, reps), GeometryEntity, 'geometry entity');
  }

  /** The entity rotated counterclockwise by angle about pt (the origin by default) (SymPy rotate). */
  rotate(angle: ExprLike, pt?: PointInput | null): GeometryEntity {
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.rotate(angle, pt) : a)));
  }

  /** The entity scaled by x and y about pt (the origin by default) (SymPy scale). */
  scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): GeometryEntity {
    if (pt !== undefined && pt !== null) {
      const p = makePoint(pt, { dim: 2 });
      return this.translate(...negated(p)).scale(x, y).translate(at(p.args, 0), at(p.args, 1));
    }
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.scale(x, y) : a)));
  }

  /** The entity shifted by x and y (SymPy translate). */
  translate(x: ExprLike = 0, y: ExprLike = 0): GeometryEntity {
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.translate(x, y) : a)));
  }

  /**
   * The value of the parameter t at which the arbitrary point of the entity
   * is the point other, as a map {t: value} (SymPy parameter_value; Plane gives
   * the point itself for its p1).
   */
  parameterValue(other: PointInput, t: Expr): ExprMap<Expr> | GeometryEntity {
    const o = other instanceof GeometryEntity ? other : makePoint(other, { dim: this.ambientDimension });
    if (!o.isPoint) throw new RangeError('other must be a point');
    const T = new Dummy('entity_dummy', { real: true });
    const ap = this.arbitraryPoint(T);
    const sol = solveEquations(ap.args.map((c, i) => add(c, mul(-1, at(o.args, i)))), [T]);
    const first = sol[0];
    if (first === undefined) throw new RangeError(`Given point is not on ${this.name}`);
    return new ExprMap([[t, at(first, 0)]]);
  }

  /** The entity with its coordinates evaluated numerically (SymPy evalf). */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr | undefined {
    const args = this.args.map(evalfArg);
    return args.every((a, i) => a === this.args[i]) ? this : this.withArgs(args);
  }
}

/** The points in an entity, the entity itself included (SymPy g.atoms(Point)). */
function pointsOf(g: GeometryEntity): GeometryEntity[] {
  const out = new Map<string, GeometryEntity>();
  const go = (e: Expr): void => {
    if (e instanceof GeometryEntity && e.isPoint) out.set(e.key, e);
    else e.args.forEach(go);
  };
  go(g);
  return [...out.values()];
}

/** The coordinates of -p as a pair (SymPy *(-pt).args). */
function negated(p: GeometryEntity): [Expr, Expr] {
  return [mul(-1, at(p.args, 0)), mul(-1, at(p.args, 1))];
}

/**
 * SymPy GeometrySet: a geometry entity that is also a set of points (lines,
 * planes, polygons, ellipses, curves and parabolas).
 */
export abstract class GeometrySet extends GeometryEntity {}

/** The matrix of the 2D translation by (x, y) acting on row vectors (SymPy entity.translate). */
export function translate(x: ExprLike, y: ExprLike): Matrix {
  return Matrix.of([
    [1, 0, 0],
    [0, 1, 0],
    [sympify(x), sympify(y), 1],
  ]);
}

/** The matrix of the 2D scaling by x and y about pt acting on row vectors (SymPy entity.scale). */
export function scale(x: ExprLike, y: ExprLike, pt?: PointInput): Matrix {
  const rv = Matrix.of([
    [sympify(x), 0, 0],
    [0, sympify(y), 0],
    [0, 0, 1],
  ]);
  if (pt === undefined) return rv;
  const p = makePoint(pt, { dim: 2 });
  const [px, py] = [at(p.args, 0), at(p.args, 1)];
  return translate(mul(-1, px), mul(-1, py)).mul(rv).mul(translate(px, py));
}

/** The matrix of the 2D rotation by th acting on row vectors (SymPy entity.rotate). */
export function rotate(th: ExprLike): Matrix {
  const s = sin(th);
  const c = cos(th);
  return Matrix.of([
    [c, s, 0],
    [mul(-1, s), c, 0],
    [0, 0, 1],
  ]);
}
