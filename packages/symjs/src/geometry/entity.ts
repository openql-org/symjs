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
import { FiniteSet, SetExpr, SetOp, finiteSet, intersection, union } from '../sets/sets';
import type { Truth } from '../core/truth';

/** A point given as an entity or as a sequence of coordinates. */
export type PointInput = Expr | readonly ExprLike[];

/** A 2D line as the reflection axis: its slope, coefficients and first point. */
export interface ReflectionLine {
  /** Slope of the reflection axis. */
  readonly slope: Expr;
  /**
   * Coefficients of the line equation in horizontal coordinate, vertical coordinate and constant
   * order.
   */
  readonly coefficients: readonly [Expr, Expr, Expr];
  /** Operands in their defining order. */
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
 * The base class of all geometric entities, an expression node whose arguments define it.
 *
 * @see SymPy `sympy.geometry.entity.GeometryEntity`
 */
export class GeometryEntity extends ExtensionExpr {
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new GeometryEntity(this.name, args);
  }
  /**
   * The entity is a point.
   *
   * @returns The entity is a point.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.is_Point`
   */
  get isPoint(): boolean {
    return false;
  }

  /**
   * The number of coordinates of the space the entity lives in.
   *
   * @returns The number of coordinates of the space the entity lives in.
   * @throws NotImplementedError when the entity does not specify its ambient dimension.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.ambient_dimension`
   */
  get ambientDimension(): number {
    throw new NotImplementedError(`ambient dimension of ${this.name} is not defined`);
  }

  /**
   * The rectangle (xmin, ymin, xmax, ymax) bounding a 2D entity.
   *
   * @returns The rectangle (xmin, ymin, xmax, ymax) bounding a 2D entity.
   * @throws NotImplementedError when the entity does not define bounds.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.bounds`
   */
  get bounds(): [Expr, Expr, Expr, Expr] {
    throw new NotImplementedError(`bounds of ${this.name} are not defined`);
  }

  /**
   * O is a part of the entity. The base rule only knows entities of the same class.
   *
   * @param o - Point or entity tested for containment.
   * @returns Whether the operand belongs to the entity.
   * @throws NotImplementedError when the entity has no containment rule for the operand.
   */
  contains(o: unknown): boolean {
    if (o instanceof GeometryEntity && o.constructor === this.constructor) return o.key === this.key;
    throw new NotImplementedError(`${this.name} does not know whether it contains ${String(o)}`);
  }

  /**
   * The point lies inside the entity (true), outside or on it (false), or it cannot be decided
   * ('unknown').
   *
   * @param _p - Point used in the geometric construction or comparison.
   * @returns The point lies inside the entity (true), outside or on it (false), or it cannot be decided ('unknown').
   * @throws NotImplementedError when the entity has no enclosure test.
   */
  enclosesPoint(_p: PointInput): boolean | 'unknown' {
    throw new NotImplementedError(`encloses_point is not defined for ${this.name}`);
  }

  /**
   * O lies inside this entity (no point of o is outside or on the boundary).
   *
   * @param o - Entity tested for strict enclosure.
   * @returns Whether the entity strictly encloses the operand.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.encloses`
   */
  encloses(o: GeometryEntity): boolean {
    return o.enclosedBy(this);
  }

  /**
   * The part of SymPy GeometryEntity.encloses that depends on the class of the enclosed entity
   * (points, segments, lines, ellipses and polygons override it).
   *
   * @param _container - Geometric entity tested for enclosure.
   * @returns Whether the supplied entity encloses this one.
   * @throws NotImplementedError when the entity has no enclosure test.
   */
  enclosedBy(_container: GeometryEntity): boolean {
    throw new NotImplementedError(`encloses is not defined for ${this.name}`);
  }

  /**
   * The entities are the same (structural equality unless a class knows better).
   *
   * @param o - Object to compare with this one.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.equals`
   */
  override equals(o: ExprLike): boolean {
    return o instanceof Expr && o.key === this.key;
  }

  /**
   * The shortest distance to o.
   *
   * @param o - Entity to measure the distance to.
   * @returns The shortest distance to o.
   * @throws TypeError when distance is undefined for the supplied entity.
   */
  distance(o: unknown): Expr {
    throw new TypeError(`distance between ${String(o)} and ${this.name} is not defined`);
  }

  /**
   * The entities that this entity and o have in common.
   *
   * @param _o - Entity to intersect with this one.
   * @returns The entities that this entity and o have in common.
   * @throws NotImplementedError when the entity has no intersection rule.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.intersection`
   */
  intersection(_o: unknown): GeometryEntity[] {
    throw new NotImplementedError(`intersection of ${this.name} is not defined`);
  }

  /**
   * The entities are similar: one can be scaled uniformly to the other.
   *
   * @param _other - Entity compared for similarity.
   * @returns The entities are similar: one can be scaled uniformly to the other.
   * @throws NotImplementedError when the entity has no similarity test.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.is_similar`
   */
  isSimilar(_other: GeometryEntity): boolean {
    throw new NotImplementedError(`is_similar of ${this.name} is not defined`);
  }

  /**
   * A point on the entity as a function of a parameter.
   *
   * @param _parameter - Symbol or name used for the parametrization.
   * @returns A point on the entity as a function of a parameter.
   * @throws NotImplementedError when the entity has no parametrization.
   */
  arbitraryPoint(_parameter?: string | Sym | null): Expr {
    throw new NotImplementedError(`arbitrary_point of ${this.name} is not defined`);
  }

  /** The entity with each argument replaced (SymPy type(self)(*newargs)). */
  protected rebuildWith(args: readonly Expr[]): GeometryEntity {
    return cast(this.withArgs(args), GeometryEntity, 'geometry entity');
  }

  /**
   * The reflection of the entity in a 2D line.
   *
   * @param line - Line defining the direction or reflection axis.
   * @returns The reflection of the entity in a 2D line.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.reflect`
   */
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

  /**
   * The entity rotated counterclockwise by angle about pt (the origin by default).
   *
   * @param angle - Rotation angle in radians.
   * @param pt - Center of rotation, defaulting to the origin.
   * @returns The entity rotated counterclockwise by angle about pt (the origin by default).
   * @see SymPy `sympy.geometry.entity.GeometryEntity.rotate`
   */
  rotate(angle: ExprLike, pt?: PointInput | null): GeometryEntity {
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.rotate(angle, pt) : a)));
  }

  /**
   * The entity scaled by x and y about pt (the origin by default).
   *
   * @param x - Scale factor along the x axis.
   * @param y - Scale factor along the y axis.
   * @param pt - Fixed point of the scaling, defaulting to the origin.
   * @returns The entity scaled by x and y about pt (the origin by default).
   * @see SymPy `sympy.geometry.entity.GeometryEntity.scale`
   */
  scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): GeometryEntity {
    if (pt !== undefined && pt !== null) {
      const p = makePoint(pt, { dim: 2 });
      return this.translate(...negated(p)).scale(x, y).translate(at(p.args, 0), at(p.args, 1));
    }
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.scale(x, y) : a)));
  }

  /**
   * The entity shifted by x and y.
   *
   * @param x - Displacement along the x axis.
   * @param y - Displacement along the y axis.
   * @returns The entity shifted by x and y.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.translate`
   */
  translate(x: ExprLike = 0, y: ExprLike = 0): GeometryEntity {
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.translate(x, y) : a)));
  }

  /**
   * Finds the parameter value at which the parametrization reaches the given point.
   *
   * @param other - Point on the entity for which to find the parameter values.
   * @param t - Parameter symbol.
   * @returns A map from `t` to its value at the given point.
   * @throws RangeError when the operand is not a point or the point does not belong to the entity.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.parameter_value`
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

  /**
   * The entity with its coordinates evaluated numerically.
   *
   * @param evalfArg - Function that evaluates an operand numerically.
   * @param _dps - Decimal digits of numerical precision.
   * @returns The numerically evaluated expression.
   * @see SymPy `sympy.geometry.entity.GeometryEntity._eval_evalf`
   */
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
 * A geometry entity that is also a set of points (lines, planes, polygons, ellipses, curves and
 * parabolas).
 *
 * @see SymPy `sympy.geometry.entity.GeometrySet`
 */
export abstract class GeometrySet extends GeometryEntity {}

/**
 * A geometric set as an operand of Union and Intersection (in SymPy a GeometrySet is itself a
 * Set): the points of the entity.
 */
export class GeometrySetNode extends SetExpr {
  /** Operands in their defining order. */
  readonly args: readonly Expr[];
  /**
   * Constructs an instance of `GeometrySetNode`.
   *
   * @param entity - Geometric entity whose points are considered.
   */
  constructor(
    /** Geometric entity whose points are considered. */
    readonly entity: GeometryEntity) {
    super();
    this.args = [entity];
  }
  /**
   * The class name used when printing the geometric set.
   *
   * @returns The class name used when printing the geometric set.
   */
  get className(): string {
    return this.entity.name;
  }
  protected computeKey(): string {
    return `GeometrySet(${this.entity.key})`;
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  printStr(print: (e: Expr) => string): string {
    return print(this.entity);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new GeometrySetNode(cast(at(args, 0), GeometryEntity));
  }
  /**
   * A finite set is contained when all its points are.
   *
   * @param x - Candidate point of the set.
   * @returns The truth value, or `'unknown'` when the relation cannot be decided.
   */
  override elementOf(x: Expr): Truth {
    return x instanceof FiniteSet ? x.args.every((point) => this.entity.contains(point)) : this.entity.contains(x);
  }
  /**
   * The common points as a finite set, with the other common entities.
   *
   * @param other - Set whose common points with this entity are sought.
   * @returns The common points as a finite set, with the other common entities.
   */
  override intersectSelf(other: SetExpr): SetExpr | undefined {
    // (SymPy distributes the intersection over a union before this rule applies)
    if (other instanceof SetOp && other.op === 'Union') return union(...other.args.map((part) => intersection(this, cast(part, SetExpr))));
    if (!(other instanceof GeometrySetNode)) return undefined;
    let common: GeometryEntity[];
    try {
      common = this.entity.intersection(other.entity);
    } catch (error) {
      if (error instanceof NotImplementedError) return undefined;
      throw error;
    }
    return union(...common.filter((e) => !e.isPoint).map((e) => new GeometrySetNode(e)), finiteSet(...common.filter((e) => e.isPoint)));
  }
  /**
   * The points and the sets that this set contains are absorbed.
   *
   * @param other - Set to combine with the points of this entity.
   * @returns The points and the sets that this set contains are absorbed.
   */
  override unionSelf(other: SetExpr): SetExpr | undefined {
    if (other instanceof FiniteSet) {
      const outside = other.args.filter((point) => !this.entity.contains(point));
      if (outside.length === other.args.length) return undefined;
      return outside.length ? new SetOp('Union', [this, finiteSet(...outside)]) : this;
    }
    return other instanceof GeometrySetNode && this.entity.contains(other.entity) ? this : undefined;
  }
}

/**
 * The set of the points of a geometric entity, for Union and Intersection.
 *
 * @param entity - Geometric entity whose points are considered.
 * @returns The set of the points of a geometric entity, for Union and Intersection.
 */
export function geometrySet(entity: GeometryEntity): SetExpr {
  return new GeometrySetNode(entity);
}

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
