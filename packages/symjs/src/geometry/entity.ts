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
   * Indicates whether this geometric entity represents a point.
   *
   * @returns The point flag.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.is_Point`
   */
  get isPoint(): boolean {
    return false;
  }

  /**
   * Counts the coordinates of the entity's ambient space.
   *
   * @returns The ambient dimension.
   * @throws NotImplementedError when the entity does not specify its ambient dimension.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.ambient_dimension`
   */
  get ambientDimension(): number {
    throw new NotImplementedError(`ambient dimension of ${this.name} is not defined`);
  }

  /**
   * Finds the axis-aligned bounding rectangle of a two-dimensional entity.
   *
   * @returns The bounds `[xmin, ymin, xmax, ymax]`.
   * @throws NotImplementedError when the entity does not define bounds.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.bounds`
   */
  get bounds(): [Expr, Expr, Expr, Expr] {
    throw new NotImplementedError(`bounds of ${this.name} are not defined`);
  }

  /**
   * Tests whether the operand is part of this entity.
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
   * Tests for strict interior membership, excluding the boundary.
   *
   * @param _p - Point used in the geometric construction or comparison.
   * @returns A truth value, possibly `'unknown'`.
   * @throws NotImplementedError when the entity has no enclosure test.
   */
  enclosesPoint(_p: PointInput): boolean | 'unknown' {
    throw new NotImplementedError(`encloses_point is not defined for ${this.name}`);
  }

  /**
   * Tests whether the entire operand lies strictly inside this entity.
   *
   * @param o - Entity tested for strict enclosure.
   * @returns Whether the entity strictly encloses the operand.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.encloses`
   */
  encloses(o: GeometryEntity): boolean {
    return o.enclosedBy(this);
  }

  /**
   * Tests enclosure using the geometry of the enclosed entity.
   *
   * @param _container - Geometric entity tested for enclosure.
   * @returns Whether the supplied entity encloses this one.
   * @throws NotImplementedError when the entity has no enclosure test.
   */
  enclosedBy(_container: GeometryEntity): boolean {
    throw new NotImplementedError(`encloses is not defined for ${this.name}`);
  }

  /**
   * Tests whether the two entities represent the same geometry.
   *
   * @param o - Object to compare with this one.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.equals`
   */
  override equals(o: ExprLike): boolean {
    return o instanceof Expr && o.key === this.key;
  }

  /**
   * Computes the minimum distance to the other entity.
   *
   * @param o - Entity to measure the distance to.
   * @returns The shortest distance.
   * @throws TypeError when distance is undefined for the supplied entity.
   */
  distance(o: unknown): Expr {
    throw new TypeError(`distance between ${String(o)} and ${this.name} is not defined`);
  }

  /**
   * Finds the geometry shared by this entity and the operand.
   *
   * @param _o - Entity to intersect with this one.
   * @returns The intersection entities.
   * @throws NotImplementedError when the entity has no intersection rule.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.intersection`
   */
  intersection(_o: unknown): GeometryEntity[] {
    throw new NotImplementedError(`intersection of ${this.name} is not defined`);
  }

  /**
   * Tests whether one entity can be scaled uniformly to the other.
   *
   * @param _other - Entity compared for similarity.
   * @returns The similarity test result.
   * @throws NotImplementedError when the entity has no similarity test.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.is_similar`
   */
  isSimilar(_other: GeometryEntity): boolean {
    throw new NotImplementedError(`is_similar of ${this.name} is not defined`);
  }

  /**
   * Parametrizes a point on the entity.
   *
   * @param _parameter - Symbol or name used for the parametrization.
   * @returns A point expressed in the parameter.
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
   * Reflects the entity across a line in the plane.
   *
   * @param line - Line defining the direction or reflection axis.
   * @returns The reflected entity.
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
   * Rotates the entity counterclockwise about the specified point, defaulting to the origin.
   *
   * @param angle - Rotation angle in radians.
   * @param pt - Center of rotation, defaulting to the origin.
   * @returns The rotated entity.
   * @see SymPy `sympy.geometry.entity.GeometryEntity.rotate`
   */
  rotate(angle: ExprLike, pt?: PointInput | null): GeometryEntity {
    return this.rebuildWith(this.args.map((a) => (a instanceof GeometryEntity ? a.rotate(angle, pt) : a)));
  }

  /**
   * Scales the entity along both axes about the specified point, defaulting to the origin.
   *
   * @param x - Scale factor along the x axis.
   * @param y - Scale factor along the y axis.
   * @param pt - Fixed point of the scaling, defaulting to the origin.
   * @returns The scaled entity.
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
   * Translates the entity by the given coordinate offsets.
   *
   * @param x - Displacement along the x axis.
   * @param y - Displacement along the y axis.
   * @returns The shifted entity.
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
   * Evaluates the entity's coordinates numerically.
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
   * Identifies the class name shown when the set is printed.
   *
   * @returns The display name.
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
   * Tests whether every point in the finite set belongs to the entity.
   *
   * @param x - Candidate point of the set.
   * @returns The truth value, or `'unknown'` when the relation cannot be decided.
   */
  override elementOf(x: Expr): Truth {
    return x instanceof FiniteSet ? x.args.every((point) => this.entity.contains(point)) : this.entity.contains(x);
  }
  /**
   * Combines common points into a finite set alongside other shared entities.
   *
   * @param other - Set whose common points with this entity are sought.
   * @returns The intersection as a set.
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
   * Absorbs points and sets already contained in this geometric set.
   *
   * @param other - Set to combine with the points of this entity.
   * @returns The simplified union when applicable.
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
 * Represents the points of a geometric entity as a set for set operations.
 *
 * @param entity - Geometric entity whose points are considered.
 * @returns A geometric set.
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
