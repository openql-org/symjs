// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/line.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.line: linear entities (Line, Ray and Segment,
 * with the Line2D, Ray2D, Segment2D, Line3D, Ray3D and Segment3D classes
 * of two and three dimensions).
 *
 * Line(...), Ray(...) and Segment(...) give the class of the dimension of
 * their points. A Line can also be given by a linear equation in x and y.
 */

import { Dummy, Expr, Float, Mul, Rational, Rel, S, Special, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, Lt, piecewise } from '../core/logic';
import { and } from '../core/boolalg';
import { NotImplementedError } from '../core/errors';
import { subs } from '../core/traverse';
import { atoms, asNumerDenom } from '../core/methods';
import { ordered } from '../core/match';
import { callableClass } from '../core/callable';
import { isIntegerQ, isNonNegative, isZero as isZeroQ } from '../core/assumptions';
import { at, cast, defined } from '../core/guard';
import { TupleNode } from '../core/containers';
import { diff } from '../calculus/diff';
import { acos, abs, tan } from '../functions/elementary/elementary';
import { atan2 } from '../functions/special/special';
import { EmptySet } from '../sets/sets';
import { Mod } from '../functions/mod';
import { Matrix } from '../matrices/matrix';
import { cross, rref } from '../matrices/linalg';
import { simplify } from '../simplify/simplify';
import { cancel } from '../simplify/rational';
import { solve } from '../solvers/solve';
import { Random } from '../ntheory/random';
import { GeometryEntity, GeometrySet, decide, realSymbol, tryDecide } from './entity';
import type { PointInput } from './entity';
import { GeometryError, Undecidable } from './exceptions';
import { Point2DNode, Point3DNode, PointNode, exprEquals, isOptions, newPoint, normalizeDimension, toInput, toPoint } from './point';
import { find, intersection as intersect, rationalOf } from './util';
import { solveEquations } from './solvehelp';

const lineT = new Dummy('line_dummy');
const lineU = new Dummy('line_dummy');

/** A Python comparison as a bool (TypeError when SymPy cannot decide it). */
const pyLt = (a: ExprLike, b: ExprLike): boolean => decide(Lt(a, b));
const pyGt = (a: ExprLike, b: ExprLike): boolean => decide(Gt(a, b));
const pyGe = (a: ExprLike, b: ExprLike): boolean => decide(Ge(a, b));
const pyLe = (a: ExprLike, b: ExprLike): boolean => decide(Le(a, b));

/** Python min/max of expressions compared with < (SymPy raises when a comparison is undecided). */
export function pyMin(xs: readonly Expr[]): Expr {
  return xs.reduce((m, x) => (pyLt(x, m) ? x : m));
}
export function pyMax(xs: readonly Expr[]): Expr {
  return xs.reduce((m, x) => (pyGt(x, m) ? x : m));
}

/**
 * The base class of lines, rays and segments, given by two distinct points p1 and p2.
 *
 * @see SymPy `sympy.geometry.line.LinearEntity`
 */
export abstract class LinearEntity extends GeometrySet {
  /**
   * Identifies the first point defining the linear entity.
   *
   * @returns The first endpoint or reference point.
   * @see SymPy `sympy.geometry.line.LinearEntity.p1`
   */
  get p1(): PointNode {
    return asPoint(at(this.args, 0));
  }
  /**
   * Identifies the second point defining the linear entity.
   *
   * @returns The second defining point.
   * @see SymPy `sympy.geometry.line.LinearEntity.p2`
   */
  get p2(): PointNode {
    return asPoint(at(this.args, 1));
  }
  /**
   * Collects the two points that determine the linear entity.
   *
   * @returns The defining point pair.
   * @see SymPy `sympy.geometry.line.LinearEntity.points`
   */
  get points(): [PointNode, PointNode] {
    return [this.p1, this.p2];
  }

  /**
   * Counts the coordinates needed to describe a point in the ambient space.
   *
   * @returns The ambient dimension.
   * @see SymPy `sympy.geometry.line.LinearEntity.ambient_dimension`
   */
  get ambientDimension(): number {
    return this.p1.args.length;
  }

  /**
   * Subtracts the first defining point from the second.
   *
   * @returns The direction vector.
   * @see SymPy `sympy.geometry.line.LinearEntity.direction`
   */
  get direction(): PointNode {
    return this.p2.sub(this.p1);
  }

  /**
   * Measures the extent of the linear entity, which is infinite for lines and rays.
   *
   * @returns The length.
   * @see SymPy `sympy.geometry.line.LinearEntity.length`
   */
  get length(): Expr {
    return S.Infinity;
  }

  /**
   * Classifies the point's position relative to the first defining point and the forward direction.
   *
   * @param other - Point to locate relative to the first defining point.
   * @returns `0` at the starting point, `1` ahead, or `-1` behind.
   * @see SymPy `sympy.geometry.line.LinearEntity._span_test`
   */
  spanTest(other: PointNode): number {
    if (this.p1.key === other.key) return 0;
    const rel = other.sub(this.p1);
    return pyGt(this.direction.dot(rel), 0) ? 1 : -1;
  }

  /**
   * Checks membership in the linear entity.
   *
   * @param other - Point or entity tested for containment.
   * @returns Whether the operand belongs to the entity.
   * @see SymPy `sympy.geometry.line.LinearEntity.contains`
   */
  override contains(other: unknown): boolean {
    return this.containsQ(other);
  }

  /**
   * Tests whether the entire point or linear entity lies in this entity.
   *
   * @param other - Point or entity to test for inclusion.
   * @returns True for containment.
   * @see SymPy `sympy.geometry.line.LinearEntity.contains`
   */
  abstract containsQ(other: unknown): boolean;

  /**
   * Computes the angle between the two direction vectors.
   *
   * @param l2 - Other line.
   * @returns The angle in radians.
   * @see SymPy `sympy.geometry.line.LinearEntity.angle_between`
   */
  angleBetween(l2: LinearEntity): Expr {
    const [v1, v2] = [this.direction, l2.direction];
    return acos(mul(v1.dot(v2), pow(mul(v1.abs(), v2.abs()), -1)));
  }

  /**
   * Selects the smaller angle formed by the lines.
   *
   * @param l2 - Other line.
   * @returns The minimum angle.
   * @see SymPy `sympy.geometry.line.LinearEntity.smallest_angle_between`
   */
  smallestAngleBetween(l2: LinearEntity): Expr {
    const [v1, v2] = [this.direction, l2.direction];
    return acos(mul(abs(v1.dot(v2)), pow(mul(v1.abs(), v2.abs()), -1)));
  }

  /**
   * Parametrizes the entity starting at the first point and following the direction vector.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns A point at parameter `t`.
   * @throws RangeError when the requested parameter name already occurs in the entity.
   * @see SymPy `sympy.geometry.line.LinearEntity.arbitrary_point`
   */
  override arbitraryPoint(parameter: string | Sym | null = 't'): PointNode {
    const t = realSymbol(parameter ?? 't');
    if ([...this.freeSymbols()].filter((s) => s instanceof Sym).some((f) => f.name === t.name)) {
      throw new RangeError(`Symbol ${t.name} already appears in object and cannot be used as a parameter.`);
    }
    return this.p1.add(this.direction.mul(t));
  }

  /**
   * Tests whether all the linear entities share exactly one point.
   *
   * @param lines - Linear entities to test.
   * @returns Whether the entities share a point.
   * @see SymPy `sympy.geometry.line.LinearEntity.are_concurrent`
   */
  static areConcurrent(...lines: LinearEntity[]): boolean {
    if (lines.length < 2) return false;
    let common: GeometryEntity[] = [at(lines, 0)];
    for (const l of lines.slice(1)) common = common.flatMap((c) => c.intersection(l));
    return common.length === 1 && at(common, 0).isPoint;
  }

  /**
   * Finds the geometry shared by the two entities.
   *
   * @param otherIn - Entity to intersect with this one.
   * @returns The intersection entities.
   * @see SymPy `sympy.geometry.line.LinearEntity.intersection`
   */
  override intersection(otherIn: unknown): GeometryEntity[] {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (other instanceof PointNode) return this.containsQ(other) ? [other] : [];
    if (!(other instanceof LinearEntity)) return other.intersection(this);
    const pts = normalizeDimension([this.p1, this.p2, other.p1, other.p2]);
    const rank = PointNode.affineRank(...pts);
    if (rank === 1) {
      if (this instanceof LineNode) return [other];
      if (other instanceof LineNode) return [this];
      if (this instanceof RayNode && other instanceof RayNode) return intersectParallelRays(this, other);
      if (this instanceof RayNode && other instanceof SegmentNode) return intersectParallelRayAndSegment(this, other);
      if (this instanceof SegmentNode && other instanceof RayNode) return intersectParallelRayAndSegment(other, this);
      return intersectParallelSegments(asSegment(this), asSegment(other));
    }
    if (rank !== 2) return [];
    const l1 = Line(at(pts, 0), at(pts, 1));
    const l2 = Line(at(pts, 2), at(pts, 3));
    if (l1.direction.isScalarMultiple(l2.direction)) return [];
    const m = Matrix.of([[...l1.direction.args], [...l2.direction.neg().args]]).transpose();
    const v = Matrix.of([[...at(pts, 2).sub(at(pts, 0)).args]]).transpose();
    // the directions are independent (not scalar multiples), so both columns are pivots
    const [mRref] = rref(m.hstack(v));
    const coeff = simplify(mRref.get(0, 2));
    const lineIntersection = l1.direction.mul(coeff).add(this.p1);
    if (this instanceof LineNode && other instanceof LineNode) return [lineIntersection];
    if ((this instanceof LineNode || this.containsQ(lineIntersection)) && other.containsQ(lineIntersection)) return [lineIntersection];
    if (!hasFloat(this) && !hasFloat(other)) return [];
    const sol = solveEquations(
      this.arbitraryPoint(lineT).sub(other.arbitraryPoint(lineU)).args,
      [lineT, lineU],
    );
    const tu = at(sol, 0);
    const ok = (p: Expr, l: LinearEntity): boolean => {
      if (l instanceof LineNode) return true;
      if (l instanceof RayNode) return isNonNegative(p) === true;
      return isNonNegative(p) === true && isNonNegative(add(1, mul(-1, p))) === true;
    };
    return ok(at(tu, 0), this) && ok(at(tu, 1), other) ? [lineIntersection] : [];
  }

  /**
   * Tests the direction vectors for parallelism.
   *
   * @param l2 - Other line.
   * @returns True for parallel directions.
   * @see SymPy `sympy.geometry.line.LinearEntity.is_parallel`
   */
  isParallel(l2: LinearEntity): boolean {
    return this.direction.isScalarMultiple(l2.direction);
  }

  /**
   * Tests the direction vectors for orthogonality.
   *
   * @param l2 - Other line.
   * @returns True for perpendicular directions.
   * @see SymPy `sympy.geometry.line.LinearEntity.is_perpendicular`
   */
  isPerpendicular(l2: LinearEntity): boolean {
    return exprEquals(S.Zero, this.direction.dot(l2.direction)) === true;
  }

  /**
   * Tests whether both linear entities lie on the same line.
   *
   * @param other - Entity compared for similarity.
   * @returns True for collinear entities.
   * @see SymPy `sympy.geometry.line.LinearEntity.is_similar`
   */
  override isSimilar(other: GeometryEntity): boolean {
    return Line(this.p1, this.p2).containsQ(other);
  }

  /**
   * Constructs the parallel to this entity through the given point.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @returns A line through the point.
   * @see SymPy `sympy.geometry.line.LinearEntity.parallel_line`
   */
  parallelLine(pIn: PointInput): LineNode {
    const p = toPoint(pIn, { dim: this.ambientDimension });
    return Line(p, p.add(this.direction));
  }

  /**
   * Constructs the perpendicular line through the given point.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @returns The perpendicular line through the given point.
   * @see SymPy `sympy.geometry.line.LinearEntity.perpendicular_line`
   */
  perpendicularLine(pIn: PointInput): LineNode {
    let p = toPoint(pIn, { dim: this.ambientDimension });
    if (this.contains(p)) p = p.add(this.direction.orthogonalDirection);
    return Line(p, this.projection(p));
  }

  /**
   * Drops a perpendicular from the point to this line.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @returns The segment or the point itself if on the line.
   * @see SymPy `sympy.geometry.line.LinearEntity.perpendicular_segment`
   */
  perpendicularSegment(pIn: PointInput): PointNode | SegmentNode {
    const p = toPoint(pIn, { dim: this.ambientDimension });
    if (this.contains(p)) return p;
    const l = this.perpendicularLine(p);
    const [p2] = Line(this.p1, this.p2).intersection(l);
    return Segment(p, asPoint(defined(p2)));
  }

  /**
   * Projects a point or linear entity orthogonally onto this line.
   *
   * @param otherIn - Operand to project.
   * @returns The projected geometry.
   * @throws GeometryError when the projection is undefined for the supplied entity.
   * @see SymPy `sympy.geometry.line.LinearEntity.projection`
   */
  projection(otherIn: unknown): GeometryEntity | typeof EmptySet {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    const projPoint = (p: PointNode): PointNode => PointNode.project(p.sub(this.p1), this.direction).add(this.p1);
    if (other instanceof PointNode) return projPoint(other);
    if (other instanceof LinearEntity) {
      const [p1, p2] = [projPoint(other.p1), projPoint(other.p2)];
      if (p1.key === p2.key) return p1;
      const projected = other.withArgs([p1, p2]);
      const common = this.intersection(projected);
      // SymPy Intersection(self, projected): an empty set, one point, or a linear entity
      if (common.length === 0) return EmptySet;
      const c = at(common, 0);
      if (c instanceof PointNode) return c;
      const le = asLinear(c);
      if (pyLt(this.direction.dot(le.direction), 0)) return asLinear(le.withArgs([le.p2, le.p1]));
      return le;
    }
    throw new GeometryError(`Do not know how to project ${String(other)} onto ${String(this)}`);
  }

  /**
   * Samples a point on the entity using the optional seed for repeatability.
   *
   * @param seed - Seed for reproducible sampling.
   * @returns The sampled point.
   * @see SymPy `sympy.geometry.line.LinearEntity.random_point`
   */
  randomPoint(seed?: number | bigint): PointNode {
    const rng = seed === undefined ? sharedRandom : new Random(seed);
    const pt = this.arbitraryPoint(lineT);
    let v: number;
    if (this instanceof RayNode) v = Math.abs(rng.gauss(0, 1));
    else if (this instanceof SegmentNode) v = rng.random();
    else v = rng.gauss(0, 1);
    return asPoint(subs(pt, [[lineT, rationalOf(v)]]));
  }

  /**
   * Bisects the angles at the intersection of the two lines.
   *
   * @param other - Second linear entity defining the angles.
   * @returns The angle-bisecting lines.
   * @throws GeometryError when the lines do not intersect or the argument is not a linear entity.
   * @see SymPy `sympy.geometry.line.LinearEntity.bisectors`
   */
  bisectors(other: LinearEntity): LineNode[] {
    if (!(other instanceof LinearEntity)) throw new GeometryError(`Expecting LinearEntity, not ${String(other)}`);
    let [l1, l2]: [LinearEntity, LinearEntity] = [this, other];
    if (l1.p1.ambientDimension !== l2.p1.ambientDimension) {
      if (l1 instanceof Line2DNode) [l1, l2] = [l2, l1];
      const [, p1] = normalizeDimension([l1.p1, l2.p1], { onMorph: 'ignore' });
      const [, p2] = normalizeDimension([l1.p2, l2.p2], { onMorph: 'ignore' });
      l2 = Line(defined(p1), defined(p2));
    }
    const point = intersect(l1, l2);
    const pt = point[0];
    if (pt === undefined) throw new GeometryError('The lines do not intersect');
    if (pt instanceof LineNode) return [asLineNode(this)];
    const p = asPoint(pt);
    const d1 = l1.direction.unit;
    const d2 = l2.direction.unit;
    return [Line(p, p.add(d1).add(d2)), Line(p, p.add(d1).sub(d2))];
  }

  /**
   * Specifies the parameter range used to plot a parametrized point.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The plotting variable and endpoints.
   */
  abstract plotInterval(parameter?: string | Sym): [Sym, Expr, Expr];
}


const asPoint = (e: Expr): PointNode => cast(e, PointNode, 'Point');
const asLinear = (e: Expr): LinearEntity => cast(e, LinearEntity, 'linear entity');
const asSegment = (e: Expr): SegmentNode => cast(e, SegmentNode, 'Segment');
const asLineNode = (e: Expr): LineNode => cast(e, LineNode, 'Line');

const hasFloat = (e: Expr): boolean => atoms(e, (a) => a instanceof Float).length > 0;

/** The generator of random_point without a seed (Python's module-level random). */
const sharedRandom = new Random();

function intersectParallelRays(ray1: RayNode, ray2: RayNode): GeometryEntity[] {
  if (pyGt(ray1.direction.dot(ray2.direction), 0)) return [ray1.spanTest(ray2.p1) >= 0 ? ray2 : ray1];
  const st = ray1.spanTest(ray2.p1);
  if (st < 0) return [];
  if (st === 0) return [ray2.p1];
  return [Segment(ray1.p1, ray2.p1)];
}

function intersectParallelRayAndSegment(ray: RayNode, seg: SegmentNode): GeometryEntity[] {
  const [st1, st2] = [ray.spanTest(seg.p1), ray.spanTest(seg.p2)];
  if (st1 < 0 && st2 < 0) return [];
  if (st1 >= 0 && st2 >= 0) return [seg];
  if (st1 >= 0) return [Segment(ray.p1, seg.p1)];
  return [Segment(ray.p1, seg.p2)];
}

function intersectParallelSegments(seg1In: SegmentNode, seg2In: SegmentNode): GeometryEntity[] {
  let [seg1, seg2] = [seg1In, seg2In];
  if (seg1.containsQ(seg2)) return [seg2];
  if (seg2.containsQ(seg1)) return [seg1];
  if (pyLt(seg1.direction.dot(seg2.direction), 0)) seg2 = asSegment(Segment(seg2.p2, seg2.p1));
  if (seg1.spanTest(seg2.p1) < 0) [seg1, seg2] = [seg2, seg1];
  if (seg2.spanTest(seg1.p2) < 0) return [];
  return [Segment(seg2.p1, seg1.p2)];
}

// ---------------------------------------------------------------------------
// Line, Ray, Segment
// ---------------------------------------------------------------------------

/**
 * An infinite line through two points.
 *
 * @see SymPy `sympy.geometry.line.Line`
 * @example
 * ```ts
 * import { Line } from '@symjs/symjs';
 *
 * Line([2, 3], [3, 5]); // => Line2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export class LineNode extends LinearEntity {
  /**
   * Constructs an instance of `LineNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   * @param name - Symbolic name.
   */
  constructor(p1: PointNode, p2: PointNode, name = 'Line') {
    super(name, [p1, p2]);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Line(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Tests whether the line contains the given point or linear entity.
   *
   * @param otherIn - Point or entity to test for inclusion.
   * @returns True for containment.
   * @see SymPy `sympy.geometry.line.Line.contains`
   */
  containsQ(otherIn: unknown): boolean {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (other instanceof PointNode) return other.isCollinear(this.p1, this.p2);
    if (other instanceof LinearEntity) return this.p1.isCollinear(this.p2, other.p1, other.p2);
    return false;
  }

  /**
   * Measures the minimum separation from the specified point.
   *
   * @param otherIn - Entity to measure the distance to.
   * @returns The shortest distance.
   * @see SymPy `sympy.geometry.line.Line.distance`
   */
  override distance(otherIn: unknown): Expr {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (this.containsQ(other)) return S.Zero;
    const ps = this.perpendicularSegment(asPoint(other));
    return ps.length;
  }

  /**
   * Tests whether both lines describe the same point set.
   *
   * @param other - Object to compare with this one.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.geometry.line.Line.equals`
   */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof LineNode)) return false;
    return this.p1.isCollinear(other.p1, this.p2, other.p2);
  }

  /**
   * Specifies the parameter and bounds for plotting the entity.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The triple `[parameter, lower, upper]`.
   * @see SymPy `sympy.geometry.line.Line.plot_interval`
   */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), Rational.of(-5n), Rational.of(5n)];
  }

  /**
   * Tests whether the given entity encloses this entity.
   *
   * @returns Whether the supplied entity encloses this one.
   */
  override enclosedBy(): boolean {
    return false;
  }
}

/**
 * A half-line from a source point through a second point.
 *
 * @see SymPy `sympy.geometry.line.Ray`
 * @example
 * ```ts
 * import { Ray } from '@symjs/symjs';
 *
 * Ray([2, 3], [3, 5]); // => Ray2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export class RayNode extends LinearEntity {
  /**
   * Constructs an instance of `RayNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   * @param name - Symbolic name.
   */
  constructor(p1: PointNode, p2: PointNode, name = 'Ray') {
    super(name, [p1, p2]);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Ray(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Identifies the endpoint from which the ray extends.
   *
   * @returns The ray's source.
   * @see SymPy `sympy.geometry.line.Ray.source`
   */
  get source(): PointNode {
    return this.p1;
  }

  /**
   * Tests whether the ray contains the given point or linear entity.
   *
   * @param otherIn - Point or entity to test for inclusion.
   * @returns True for containment.
   * @see SymPy `sympy.geometry.line.Ray.contains`
   */
  containsQ(otherIn: unknown): boolean {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (other instanceof PointNode) {
      if (this.p1.isCollinear(this.p2, other)) return pyGe(this.p2.sub(this.p1).dot(other.sub(this.p1)), S.Zero);
      return false;
    }
    if (other instanceof RayNode) {
      if (this.p1.isCollinear(this.p2, other.p1, other.p2)) return pyGt(this.p2.sub(this.p1).dot(other.p2.sub(other.p1)), S.Zero);
      return false;
    }
    if (other instanceof SegmentNode) return this.contains(other.p1) && this.contains(other.p2);
    return false;
  }

  /**
   * Measures the minimum separation from the specified point.
   *
   * @param otherIn - Entity to measure the distance to.
   * @returns The shortest distance.
   * @see SymPy `sympy.geometry.line.Ray.distance`
   */
  override distance(otherIn: unknown): Expr {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (this.containsQ(other)) return S.Zero;
    const o = asPoint(other);
    const proj = asPoint(Line(this.p1, this.p2).projection(o));
    if (this.containsQ(proj)) return o.sub(proj).abs();
    return o.sub(this.source).abs();
  }

  /**
   * Tests whether both rays share a source and direction.
   *
   * @param other - Object to compare with this one.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.geometry.line.Ray.equals`
   */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof RayNode)) return false;
    return this.source.key === other.source.key && this.contains(other.p2);
  }

  /**
   * Specifies the parameter and bounds for plotting the entity.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The triple `[parameter, lower, upper]`.
   * @see SymPy `sympy.geometry.line.Ray.plot_interval`
   */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), S.Zero, Rational.of(10n)];
  }

  /**
   * Tests whether the given entity encloses this entity.
   *
   * @returns Whether the supplied entity encloses this one.
   */
  override enclosedBy(): boolean {
    return false;
  }
}

/**
 * The line segment between two points.
 *
 * @see SymPy `sympy.geometry.line.Segment`
 * @example
 * ```ts
 * import { Segment } from '@symjs/symjs';
 *
 * Segment([2, 3], [3, 5]); // => Segment2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export class SegmentNode extends LinearEntity {
  /**
   * Constructs an instance of `SegmentNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   * @param name - Symbolic name.
   */
  constructor(p1: PointNode, p2: PointNode, name = 'Segment') {
    super(name, [p1, p2]);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Segment(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Tests whether the segment contains the point or the entire other segment.
   *
   * @param otherIn - Point or entity to test for inclusion.
   * @returns True for containment.
   * @throws Undecidable when the containment predicate is undecidable.
   * @see SymPy `sympy.geometry.line.Segment.contains`
   */
  containsQ(otherIn: unknown): boolean {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (other instanceof PointNode) {
      if (!other.isCollinear(this.p1, this.p2)) return false;
      if (this instanceof Segment2DNode) {
        const vert = exprEquals(pow(this.slope, -1), 0);
        if (vert === false) {
          const isin = tryDecide(Le(mul(add(this.p1.coordinate(0), mul(-1, other.coordinate(0))), add(this.p2.coordinate(0), mul(-1, other.coordinate(0)))), 0));
          if (isin !== undefined) return isin;
        }
        if (vert === true) {
          const isin = tryDecide(Le(mul(add(this.p1.coordinate(1), mul(-1, other.coordinate(1))), add(this.p2.coordinate(1), mul(-1, other.coordinate(1)))), 0));
          if (isin !== undefined) return isin;
        }
      }
      const [d1, d2] = [other.sub(this.p1), other.sub(this.p2)];
      const d = this.p2.sub(this.p1);
      const r = simplify(Eq(add(d1.abs(), d2.abs(), mul(-1, d.abs())), 0));
      if (r instanceof Rel) throw new Undecidable(`Cannot determine if ${String(other)} is in ${String(this)}`);
      return decide(r);
    }
    if (other instanceof SegmentNode) return this.contains(other.p1) && this.contains(other.p2);
    return false;
  }

  /**
   * Tests whether both segments have the same endpoints.
   *
   * @param other - Object to compare with this one.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.geometry.line.Segment.equals`
   */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof SegmentNode) || other.name !== this.name) return false;
    const a = ordered(this.args).map((e) => e.key);
    const b = ordered(other.args).map((e) => e.key);
    return a.every((k, i) => k === b[i]);
  }

  /**
   * Measures the minimum separation from the specified point.
   *
   * @param otherIn - Entity to measure the distance to.
   * @returns The shortest distance.
   * @throws NotImplementedError when the distance to the supplied entity is unsupported.
   * @see SymPy `sympy.geometry.line.Segment.distance`
   */
  override distance(otherIn: unknown): Expr {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (other instanceof PointNode) {
      const vp1 = other.sub(this.p1);
      const vp2 = other.sub(this.p2);
      const sign1 = pyGe(this.direction.dot(vp1), 0);
      const sign2 = pyLe(this.direction.dot(vp2), 0);
      if (sign1 && sign2) return Line(this.p1, this.p2).distance(other);
      if (sign1) return vp2.abs();
      return vp1.abs();
    }
    throw new NotImplementedError(`distance between a Segment and ${other.name}`);
  }

  /**
   * Measures the separation of the segment's endpoints.
   *
   * @returns The segment length.
   * @see SymPy `sympy.geometry.line.Segment.length`
   */
  override get length(): Expr {
    return this.p1.distance(this.p2);
  }

  /**
   * Finds the point halfway between the segment's endpoints.
   *
   * @returns The midpoint.
   * @see SymPy `sympy.geometry.line.Segment.midpoint`
   */
  get midpoint(): PointNode {
    return this.p1.midpoint(this.p2);
  }

  /**
   * Bisects the segment at right angles, optionally joining a point on the bisector to the midpoint.
   *
   * @param p - Point used in the geometric construction or comparison.
   * @returns The bisecting line or segment.
   * @see SymPy `sympy.geometry.line.Segment.perpendicular_bisector`
   */
  perpendicularBisector(p?: PointInput): LineNode | SegmentNode | PointNode {
    const l = this.perpendicularLine(this.midpoint);
    if (p !== undefined) {
      const p2 = toPoint(p, { dim: this.ambientDimension });
      if (l.contains(p2)) return Segment(p2, this.midpoint);
    }
    return l;
  }

  /**
   * Specifies the parameter and bounds for plotting the entity.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The triple `[parameter, lower, upper]`.
   * @see SymPy `sympy.geometry.line.Segment.plot_interval`
   */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), S.Zero, S.One];
  }

  /**
   * Checks whether the container encloses both endpoints.
   *
   * @param container - Geometric entity tested for enclosure.
   * @returns Whether the supplied entity encloses this one.
   */
  override enclosedBy(container: GeometryEntity): boolean {
    return this.points.every((p) => container.enclosesPoint(p) === true);
  }
}

// ---------------------------------------------------------------------------
// 2D and 3D classes
// ---------------------------------------------------------------------------

/** SymPy LinearEntity2D.bounds. */
function bounds2D(l: LinearEntity): [Expr, Expr, Expr, Expr] {
  const xs = l.points.map((p) => p.coordinate(0));
  const ys = l.points.map((p) => p.coordinate(1));
  return [pyMin(xs), pyMin(ys), pyMax(xs), pyMax(ys)];
}

/** SymPy LinearEntity2D.slope: oo for a vertical line. */
function slope2D(l: LinearEntity): Expr {
  const [d1, d2] = l.p1.sub(l.p2).args;
  if (d1 === undefined || d2 === undefined || d1.key === S.Zero.key) return S.Infinity;
  return simplify(mul(d2, pow(d1, -1)));
}

/** SymPy LinearEntity2D.perpendicular_line. */
function perpendicularLine2D(l: LinearEntity, pIn: PointInput): Line2DNode {
  const p = toPoint(pIn, { dim: l.ambientDimension });
  return as2DLine(Line(p, p.add(l.direction.orthogonalDirection)));
}

const as2DLine = (e: Expr): Line2DNode => cast(e, Line2DNode, 'Line2D');

/**
 * A line in the plane.
 *
 * @see SymPy `sympy.geometry.line.Line2D`
 * @example
 * ```ts
 * import { Line2D } from '@symjs/symjs';
 *
 * Line2D([2, 3], [3, 5]); // => Line2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export class Line2DNode extends LineNode {
  /**
   * Constructs an instance of `Line2DNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   */
  constructor(p1: Point2DNode, p2: Point2DNode) {
    super(p1, p2, 'Line2D');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Line2D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Finds the axis-aligned bounding rectangle.
   *
   * @returns The bounds `[xmin, ymin, xmax, ymax]`.
   * @see SymPy `sympy.geometry.line.Line2D.bounds`
   */
  override get bounds(): [Expr, Expr, Expr, Expr] {
    return bounds2D(this);
  }

  /**
   * Computes the rise over run of the line.
   *
   * @returns The slope or `oo` for a vertical line.
   * @see SymPy `sympy.geometry.line.Line2D.slope`
   */
  get slope(): Expr {
    return slope2D(this);
  }

  /**
   * Create a new Line perpendicular to this linear entity which passes through the point `p`.
   *
   * @param p - Point used in the geometric construction or comparison.
   * @returns The perpendicular line through the given point.
   * @see SymPy `sympy.geometry.line.Line2D.perpendicular_line`
   */
  override perpendicularLine(p: PointInput): Line2DNode {
    return perpendicularLine2D(this, p);
  }

  /**
   * Extracts the coefficients of the line equation `a*x + b*y + c = 0`.
   *
   * @returns The triple `[a, b, c]`.
   * @see SymPy `sympy.geometry.line.Line2D.coefficients`
   */
  get coefficients(): [Expr, Expr, Expr] {
    const [p1, p2] = this.points;
    if (p1.coordinate(0).key === p2.coordinate(0).key) return [S.One, S.Zero, mul(-1, p1.coordinate(0))];
    if (p1.coordinate(1).key === p2.coordinate(1).key) return [S.Zero, S.One, mul(-1, p1.coordinate(1))];
    const [x1, y1, x2, y2] = [p1.coordinate(0), p1.coordinate(1), p2.coordinate(0), p2.coordinate(1)];
    return [simplify(add(y1, mul(-1, y2))), simplify(add(x2, mul(-1, x1))), simplify(add(mul(x1, y2), mul(-1, y1, x2)))];
  }

  /**
   * Forms the Cartesian equation of the line in real coordinates.
   *
   * @param x - Symbol for the x coordinate.
   * @param y - Symbol for the y coordinate.
   * @returns The expression `a*x + b*y + c`.
   * @see SymPy `sympy.geometry.line.Line2D.equation`
   */
  equation(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const [p1, p2] = this.points;
    if (p1.coordinate(0).key === p2.coordinate(0).key) return add(X, mul(-1, p1.coordinate(0)));
    if (p1.coordinate(1).key === p2.coordinate(1).key) return add(Y, mul(-1, p1.coordinate(1)));
    const [a, b, c] = this.coefficients;
    return add(mul(a, X), mul(b, Y), c);
  }
}

/**
 * A ray in the plane.
 *
 * @see SymPy `sympy.geometry.line.Ray2D`
 * @example
 * ```ts
 * import { Ray2D } from '@symjs/symjs';
 *
 * Ray2D([2, 3], [3, 5]); // => Ray2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export class Ray2DNode extends RayNode {
  /**
   * Constructs an instance of `Ray2DNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   */
  constructor(p1: Point2DNode, p2: Point2DNode) {
    super(p1, p2, 'Ray2D');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Ray2D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Finds the axis-aligned bounding rectangle.
   *
   * @returns The bounds `[xmin, ymin, xmax, ymax]`.
   * @see SymPy `sympy.geometry.line.Ray2D.bounds`
   */
  override get bounds(): [Expr, Expr, Expr, Expr] {
    return bounds2D(this);
  }

  /**
   * Computes the rise over run of the ray.
   *
   * @returns The slope or `oo` for a vertical ray.
   * @see SymPy `sympy.geometry.line.Ray2D.slope`
   */
  get slope(): Expr {
    return slope2D(this);
  }

  /**
   * Create a new Line perpendicular to this linear entity which passes through the point `p`.
   *
   * @param p - Point used in the geometric construction or comparison.
   * @returns The perpendicular line through the given point.
   * @see SymPy `sympy.geometry.line.Ray2D.perpendicular_line`
   */
  override perpendicularLine(p: PointInput): Line2DNode {
    return perpendicularLine2D(this, p);
  }

  /**
   * Indicates the direction of travel along the x-axis.
   *
   * @returns Positive infinity, zero, or negative infinity.
   * @see SymPy `sympy.geometry.line.Ray2D.xdirection`
   */
  get xdirection(): Expr {
    return direction(this.p1.coordinate(0), this.p2.coordinate(0));
  }

  /**
   * Indicates the direction of travel along the y-axis.
   *
   * @returns Positive infinity, zero, or negative infinity.
   * @see SymPy `sympy.geometry.line.Ray2D.ydirection`
   */
  get ydirection(): Expr {
    return direction(this.p1.coordinate(1), this.p2.coordinate(1));
  }

  /**
   * Computes the counterclockwise rotation that aligns the other ray with this ray.
   *
   * @param r2 - Ray relative to which to measure the closing angle.
   * @returns The rotation angle.
   * @throws TypeError when either operand is not a two-dimensional ray.
   * @see SymPy `sympy.geometry.line.Ray2D.closing_angle`
   */
  closingAngle(r2: Ray2DNode): Expr {
    if (!(r2 instanceof Ray2DNode)) throw new TypeError('Both arguments must be Ray2D objects.');
    let a1 = atan2(this.direction.coordinate(1), this.direction.coordinate(0));
    let a2 = atan2(r2.direction.coordinate(1), r2.direction.coordinate(0));
    if (pyLt(mul(a1, a2), 0)) {
      if (pyLt(a1, 0)) a1 = add(mul(2, S.Pi), a1);
      if (pyLt(a2, 0)) a2 = add(mul(2, S.Pi), a2);
    }
    return add(a1, mul(-1, a2));
  }
}

/** oo, 0 or -oo as b is right of, equal to or left of a (SymPy xdirection). */
function direction(a: Expr, b: Expr): Expr {
  if (pyLt(a, b)) return S.Infinity;
  if (a.key === b.key) return S.Zero;
  return S.NegativeInfinity;
}

/**
 * A segment in the plane.
 *
 * @see SymPy `sympy.geometry.line.Segment2D`
 * @example
 * ```ts
 * import { Segment2D } from '@symjs/symjs';
 *
 * Segment2D([2, 3], [3, 5]); // => Segment2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export class Segment2DNode extends SegmentNode {
  /**
   * Constructs an instance of `Segment2DNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   */
  constructor(p1: Point2DNode, p2: Point2DNode) {
    super(p1, p2, 'Segment2D');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Segment2D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Finds the axis-aligned bounding rectangle.
   *
   * @returns The bounds `[xmin, ymin, xmax, ymax]`.
   * @see SymPy `sympy.geometry.line.Segment2D.bounds`
   */
  override get bounds(): [Expr, Expr, Expr, Expr] {
    return bounds2D(this);
  }

  /**
   * Computes the rise over run of the segment.
   *
   * @returns The slope or `oo` for a vertical segment.
   * @see SymPy `sympy.geometry.line.Segment2D.slope`
   */
  get slope(): Expr {
    return slope2D(this);
  }

  /**
   * Create a new Line perpendicular to this linear entity which passes through the point `p`.
   *
   * @param p - Point used in the geometric construction or comparison.
   * @returns The perpendicular line through the given point.
   * @see SymPy `sympy.geometry.line.Segment2D.perpendicular_line`
   */
  override perpendicularLine(p: PointInput): Line2DNode {
    return perpendicularLine2D(this, p);
  }
}

/** SymPy LinearEntity3D.direction_ratio. */
const directionRatio3D = (l: LinearEntity): Expr[] => as3DPoint(l.p1).directionRatio(as3DPoint(l.p2));
/** SymPy LinearEntity3D.direction_cosine. */
const directionCosine3D = (l: LinearEntity): Expr[] => as3DPoint(l.p1).directionCosine(as3DPoint(l.p2));

const as3DPoint = (e: Expr): Point3DNode => cast(e, Point3DNode, 'Point3D');

/**
 * A line in space.
 *
 * @see SymPy `sympy.geometry.line.Line3D`
 * @example
 * ```ts
 * import { Line3D } from '@symjs/symjs';
 *
 * Line3D([2, 3, 4], [3, 5, 1]); // => Line3D(Point3D(2, 3, 4), Point3D(3, 5, 1))
 * ```
 */
export class Line3DNode extends LineNode {
  /**
   * Constructs an instance of `Line3DNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   */
  constructor(p1: Point3DNode, p2: Point3DNode) {
    super(p1, p2, 'Line3D');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Line3D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Computes the coordinate ratios of the direction vector.
   *
   * @returns The direction ratios.
   * @see SymPy `sympy.geometry.line.Line3D.direction_ratio`
   */
  get directionRatio(): Expr[] {
    return directionRatio3D(this);
  }

  /**
   * Normalizes the direction vector to obtain its cosines with the axes.
   *
   * @returns The direction cosines.
   * @see SymPy `sympy.geometry.line.Line3D.direction_cosine`
   */
  get directionCosine(): Expr[] {
    return directionCosine3D(this);
  }

  /**
   * Describes the line as the intersection of two planes in real coordinates.
   *
   * @param x - Symbol for the x coordinate.
   * @param y - Symbol for the y coordinate.
   * @param z - Symbol for the z coordinate.
   * @returns The two plane equations.
   * @see SymPy `sympy.geometry.line.Line3D.equation`
   */
  equation(x: string | Sym = 'x', y: string | Sym = 'y', z: string | Sym = 'z'): TupleNode {
    const [X, Y, Z, k] = [realSymbol(x), realSymbol(y), realSymbol(z), realSymbol('k')];
    const [p1, p2] = this.points;
    const [d1, d2, d3] = as3DPoint(p1).directionRatio(as3DPoint(p2));
    const [x1, y1, z1] = p1.args;
    const eqs = [add(mul(-1, defd(d1), k), X, mul(-1, defd(x1))), add(mul(-1, defd(d2), k), Y, mul(-1, defd(y1))), add(mul(-1, defd(d3), k), Z, mul(-1, defd(z1)))];
    const i = eqs.findIndex((e) => e.has(k));
    const kk = at(solve(at(eqs, i), k), 0);
    eqs.splice(i, 1);
    return new TupleNode(eqs.map((e) => asNumerDenom(cancel(subs(e, [[k, kk]])))[0]));
  }

  /**
   * Measures the minimum separation from a point, line, or plane.
   *
   * @param otherIn - Entity to measure the distance to.
   * @returns The shortest distance.
   * @throws NotImplementedError when the operand type has no implementation of this operation.
   * @see SymPy `sympy.geometry.line.Line3D.distance`
   */
  override distance(otherIn: unknown): Expr {
    const other = Array.isArray(otherIn) ? tryPoint3D(otherIn) : otherIn;
    if (other instanceof Point3DNode) return super.distance(other);
    if (other instanceof Line3DNode) {
      if (this.key === other.key) return S.Zero;
      if (this.isParallel(other)) return super.distance(other.p1);
      const normal = cross(Matrix.col(...this.directionRatio), Matrix.col(...other.directionRatio));
      const plane = makePlane(this.p1, normal.data);
      return other.p1.distance(plane);
    }
    if (other instanceof GeometryEntity && other.name === 'Plane') return other.distance(this);
    throw new NotImplementedError(`${String(other)} has type ${typeof other}, which is unsupported`);
  }
}

const defd = <T>(e: T | undefined): T => defined(e, 'coordinate');

/** SymPy Point3D(other) of a sequence, or the sequence when it is not a 3D point. */
function tryPoint3D(o: readonly unknown[]): unknown {
  try {
    return toPoint(toInput(o), { dim: 3 });
  } catch (err) {
    if (err instanceof RangeError) return o;
    throw err;
  }
}

/** The Plane constructor, registered by geometry/plane. */
export const planeHook: { make?: (p1: PointNode, normal: readonly Expr[]) => GeometryEntity } = {};
const makePlane = (p1: PointNode, normal: readonly Expr[]): GeometryEntity => defined(planeHook.make, 'Plane')(p1, normal);

/**
 * A ray in space.
 *
 * @see SymPy `sympy.geometry.line.Ray3D`
 * @example
 * ```ts
 * import { Ray3D } from '@symjs/symjs';
 *
 * Ray3D([2, 3, 4], [3, 5, 1]); // => Ray3D(Point3D(2, 3, 4), Point3D(3, 5, 1))
 * ```
 */
export class Ray3DNode extends RayNode {
  /**
   * Constructs an instance of `Ray3DNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   */
  constructor(p1: Point3DNode, p2: Point3DNode) {
    super(p1, p2, 'Ray3D');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Ray3D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Computes the coordinate ratios of the direction vector.
   *
   * @returns The direction ratios.
   * @see SymPy `sympy.geometry.line.Ray3D.direction_ratio`
   */
  get directionRatio(): Expr[] {
    return directionRatio3D(this);
  }

  /**
   * Normalizes the direction vector to obtain its cosines with the axes.
   *
   * @returns The direction cosines.
   * @see SymPy `sympy.geometry.line.Ray3D.direction_cosine`
   */
  get directionCosine(): Expr[] {
    return directionCosine3D(this);
  }

  /**
   * Indicates the direction of travel along the x-axis.
   *
   * @returns Positive infinity, zero, or negative infinity.
   * @see SymPy `sympy.geometry.line.Ray3D.xdirection`
   */
  get xdirection(): Expr {
    return direction(this.p1.coordinate(0), this.p2.coordinate(0));
  }
  /**
   * Indicates the direction of travel along the y-axis.
   *
   * @returns Positive infinity, zero, or negative infinity.
   * @see SymPy `sympy.geometry.line.Ray3D.ydirection`
   */
  get ydirection(): Expr {
    return direction(this.p1.coordinate(1), this.p2.coordinate(1));
  }
  /**
   * Indicates the direction of travel along the z-axis.
   *
   * @returns Positive infinity, zero, or negative infinity.
   * @see SymPy `sympy.geometry.line.Ray3D.zdirection`
   */
  get zdirection(): Expr {
    return direction(this.p1.coordinate(2), this.p2.coordinate(2));
  }
}

/**
 * A segment in space.
 *
 * @see SymPy `sympy.geometry.line.Segment3D`
 * @example
 * ```ts
 * import { Segment3D } from '@symjs/symjs';
 *
 * Segment3D([2, 3, 4], [3, 5, 1]); // => Segment3D(Point3D(2, 3, 4), Point3D(3, 5, 1))
 * ```
 */
export class Segment3DNode extends SegmentNode {
  /**
   * Constructs an instance of `Segment3DNode`.
   *
   * @param p1 - First defining point.
   * @param p2 - Second defining point.
   */
  constructor(p1: Point3DNode, p2: Point3DNode) {
    super(p1, p2, 'Segment3D');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return Segment3D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /**
   * Computes the coordinate ratios of the direction vector.
   *
   * @returns The direction ratios.
   * @see SymPy `sympy.geometry.line.Segment3D.direction_ratio`
   */
  get directionRatio(): Expr[] {
    return directionRatio3D(this);
  }

  /**
   * Normalizes the direction vector to obtain its cosines with the axes.
   *
   * @returns The direction cosines.
   * @see SymPy `sympy.geometry.line.Segment3D.direction_cosine`
   */
  get directionCosine(): Expr[] {
    return directionCosine3D(this);
  }
}

// ---------------------------------------------------------------------------
// constructors
// ---------------------------------------------------------------------------

/** Keywords of Line(...): the slope (2D), direction ratios (3D), or the symbols of an equation. */
export interface LineOptions {
  /** The slope of a 2D line through the first point. */
  slope?: ExprLike;
  /** The direction ratios of a 3D line through the first point. */
  directionRatio?: readonly ExprLike[] | TupleNode;
  /** The x symbol (or its name) of an equation (default 'x'). */
  x?: string | Sym;
  /** The y symbol (or its name) of an equation (default 'y'). */
  y?: string | Sym;
}

/** Keywords of Ray(...): the angle (2D) or direction ratios (3D). */
export interface RayOptions {
  /** The angle of a 2D ray from the positive x axis. */
  angle?: ExprLike;
  /** The direction ratios of a 3D ray. */
  directionRatio?: readonly ExprLike[] | TupleNode;
}

/** The options as read from a call: the direction ratios as an array. */
type LineOpts = Omit<LineOptions, 'directionRatio'> & { directionRatio?: readonly ExprLike[] };
type RayOpts = Omit<RayOptions, 'directionRatio'> & { directionRatio?: readonly ExprLike[] };

/** SymPy linear_coeffs(eq, x, y): [a, b, c] with eq = a*x + b*y + c; RangeError when eq is not linear. */
function linearCoeffs(eq: Expr, x: Sym, y: Sym): [Expr, Expr, Expr] {
  const a = simplify(diff(eq, x));
  const b = simplify(diff(eq, y));
  if (a.has(x) || a.has(y) || b.has(x) || b.has(y)) throw new RangeError(`nonlinear term encountered: ${String(eq)}`);
  // with a and b free of x and y, the rest is free of them too
  return [a, b, simplify(add(eq, mul(-1, a, x), mul(-1, b, y)))];
}

/** SymPy Line(equation, x=..., y=...). */
function lineFromEquation(equationIn: Expr, opts: LineOpts): Line2DNode {
  const missing = new Sym('?');
  const equation = equationIn instanceof Rel && equationIn.op === 'Eq' ? add(equationIn.lhs, mul(-1, equationIn.rhs)) : equationIn;
  const findOrMissing = (v: string | Sym): Sym => {
    try {
      return find(v, equation);
    } catch {
      // not found or ambiguous (find raises RangeError)
      return missing;
    }
  };
  const x = findOrMissing(opts.x ?? (opts.y === undefined ? 'x' : missing));
  const y = findOrMissing(opts.y ?? (opts.x === undefined ? 'y' : missing));
  const [a, b, c] = linearCoeffs(equation, x, y);
  if (b.key !== S.Zero.key) return Line2D([0, mul(-1, c, pow(b, -1))], { slope: mul(-1, a, pow(b, -1)) });
  if (a.key !== S.Zero.key) return Line2D([mul(-1, c, pow(a, -1)), 0], { slope: S.Infinity });
  // SymPy set('xy') - {x, y}: the names are strings, never equal to the symbols
  throw new RangeError("not found in equation: {'x', 'y'}");
}

/** The positional arguments and trailing options of a constructor call. */
function splitCall<O>(args: readonly unknown[], read: (o: Record<string, unknown>) => O): [unknown[], O] {
  const last = args[args.length - 1];
  if (isOptions(last)) return [args.slice(0, -1), read(last)];
  return [[...args], read({})];
}

const readLineOptions = (o: Record<string, unknown>): LineOpts => {
  const r: { slope?: ExprLike; directionRatio?: readonly ExprLike[]; x?: string | Sym; y?: string | Sym } = {};
  const exprLike = (v: unknown): v is ExprLike => v instanceof Expr || typeof v === 'number' || typeof v === 'bigint';
  const name = (v: unknown): v is string | Sym => typeof v === 'string' || v instanceof Sym;
  if (exprLike(o['slope'])) r.slope = o['slope'];
  if (Array.isArray(o['directionRatio'])) r.directionRatio = o['directionRatio'];
  else if (o['directionRatio'] instanceof TupleNode) r.directionRatio = o['directionRatio'].args;
  if (name(o['x'])) r.x = o['x'];
  if (name(o['y'])) r.y = o['y'];
  const unknown = Object.keys(o).filter((k) => !['slope', 'directionRatio', 'x', 'y'].includes(k));
  if (unknown.length) throw new RangeError('expecting only x and y as keywords');
  return r;
};

const readRayOptions = (o: Record<string, unknown>): RayOpts => {
  const r: { angle?: ExprLike; directionRatio?: readonly ExprLike[] } = {};
  const a = o['angle'];
  if (a instanceof Expr || typeof a === 'number' || typeof a === 'bigint') r.angle = a;
  if (Array.isArray(o['directionRatio'])) r.directionRatio = o['directionRatio'];
  else if (o['directionRatio'] instanceof TupleNode) r.directionRatio = o['directionRatio'].args;
  return r;
};

/** An argument as a point input (a point, a Tuple or an array of coordinates). */
const pointArg = (a: unknown): PointInput => toInput(a);

/** SymPy Line.__new__. */
function newLine(args: unknown[], opts: LineOpts): LineNode {
  const first = args[0];
  if (args.length === 1 && first instanceof Expr && !(first instanceof GeometryEntity) && !(first instanceof TupleNode)) return lineFromEquation(first, opts);
  if (first === undefined) throw new TypeError('Line requires a point or an equation');
  const p2in = args[1];
  if (first instanceof LinearEntity) {
    if (p2in !== undefined) throw new RangeError('If p1 is a LinearEntity, p2 must be None.');
    const dim = first.p1.args.length;
    if (dim === 2) return line2D(first, undefined, opts);
    if (dim === 3) return line3D(first, undefined, opts);
    return newLinear(first.p1, first.p2, (a, b) => new LineNode(a, b), 'Line');
  }
  const p1 = toPoint(pointArg(first));
  const p2 = p2in === undefined ? undefined : toPoint(pointArg(p2in));
  const dim = p1.args.length;
  if (dim === 2) return line2D(p1, p2, opts);
  if (dim === 3) return line3D(p1, p2, opts);
  if (p2 === undefined) throw new RangeError('Line requires two points.');
  return newLinear(p1, p2, (a, b) => new LineNode(a, b), 'Line');
}

/** SymPy LinearEntity.__new__: two distinct points of one dimension. */
function newLinear<T>(p1In: PointNode, p2In: PointNode, make: (a: PointNode, b: PointNode) => T, cls: string): T {
  const [p1, p2] = normalizeDimension([p1In, p2In]);
  if (defd(p1).key === defd(p2).key) throw new RangeError(`${cls}.__new__ requires two unique Points.`);
  return make(defd(p1), defd(p2));
}

/** SymPy Line2D.__new__(p1, pt=None, slope=None). */
function line2D(p1In: PointInput | LinearEntity, ptIn: PointInput | undefined, opts: LineOpts): Line2DNode {
  let p1: PointNode;
  let pt: PointInput | undefined = ptIn;
  if (p1In instanceof LinearEntity) {
    if (pt !== undefined) throw new RangeError('When p1 is a LinearEntity, pt should be None');
    const [a, b] = normalizeDimension([p1In.p1, p1In.p2], { dim: 2 });
    p1 = defd(a);
    pt = defd(b);
  } else p1 = toPoint(p1In, { dim: 2 });
  let p2: PointNode;
  if (pt !== undefined && opts.slope === undefined) {
    try {
      p2 = toPoint(pt, { dim: 2 });
    } catch {
      throw new RangeError('The 2nd argument was not a valid Point. If it was a slope, enter it with keyword "slope".');
    }
  } else if (opts.slope !== undefined && pt === undefined) {
    const slope = sympify(opts.slope);
    const [dx, dy] = slope instanceof Special && slope.isInfinite ? [S.Zero, S.One] : [S.One, slope];
    p2 = newPoint([add(p1.coordinate(0), dx), add(p1.coordinate(1), dy)], { evaluate: false });
  } else throw new RangeError('A 2nd Point or keyword "slope" must be used.');
  return newLinear(p1, p2, (a, b) => new Line2DNode(as2D(a), as2D(b)), 'Line2D');
}

/** SymPy Line3D.__new__(p1, pt=None, direction_ratio=()). */
function line3D(p1In: PointInput | LinearEntity, ptIn: PointInput | undefined, opts: LineOpts): Line3DNode {
  const [p1, p2] = point3DPair(p1In, ptIn, opts.directionRatio, 'if p1 is a LinearEntity, pt must be None.');
  return newLinear(p1, p2, (a, b) => new Line3DNode(as3DPoint(a), as3DPoint(b)), 'Line3D');
}

/** The two points of Line3D / Ray3D (SymPy p1 and pt, or p1 + direction_ratio). */
function point3DPair(p1In: PointInput | LinearEntity, ptIn: PointInput | undefined, ratio: readonly ExprLike[] = [], entityMessage: string): [PointNode, PointNode] {
  let p1: PointNode;
  let pt: PointInput | undefined = ptIn;
  if (p1In instanceof LinearEntity && p1In.p1.args.length === 3) {
    if (pt !== undefined) throw new RangeError(entityMessage);
    [p1, pt] = [p1In.p1, p1In.p2];
  } else p1 = toPoint(p1In, { dim: 3 });
  if (pt !== undefined && ratio.length === 0) return [p1, toPoint(pt, { dim: 3 })];
  if (ratio.length === 3 && pt === undefined) {
    return [p1, newPoint(p1.args.map((c, i) => add(c, at(ratio, i))), { dim: 3 })];
  }
  throw new RangeError('A 2nd Point or keyword "direction_ratio" must be used.');
}

const as2D = (e: PointNode): Point2DNode => cast(e, Point2DNode, 'Point2D');

/** SymPy Ray.__new__. */
function newRay(args: unknown[], opts: RayOpts): RayNode {
  const p1 = toPoint(pointArg(args[0]));
  const p2in = args[1];
  let p2: PointNode | undefined;
  let q1 = p1;
  if (p2in !== undefined) {
    const [a, b] = normalizeDimension([p1, toPoint(pointArg(p2in))]);
    [q1, p2] = [defd(a), defd(b)];
  }
  const dim = q1.args.length;
  if (dim === 2) return ray2D(q1, p2, opts);
  if (dim === 3) return ray3D(q1, p2, opts);
  if (p2 === undefined) throw new RangeError('Ray requires two points.');
  return newLinear(q1, p2, (a, b) => new RayNode(a, b), 'Ray');
}

/**
 * SymPy _pi_coeff for the angle of a ray: c with angle = c*pi reduced to
 * [0, 2) for a numeric c, the coefficient itself for a symbolic one, or
 * undefined when the angle is not a multiple of pi.
 */
function piCoeff(angle: Expr): Expr | undefined {
  if (angle.key === S.Pi.key) return S.One;
  if (isZeroQ(angle) === true) return S.Zero;
  if (!(angle instanceof Mul) || !angle.args.some((a) => a.key === S.Pi.key)) return undefined;
  const rest = angle.args.filter((a) => a.key !== S.Pi.key);
  const head = rest[0];
  let c: Expr = head instanceof Rational || head instanceof Float ? head : S.One;
  const x = mul(...rest.filter((a) => a !== c));
  if (c instanceof Float) {
    // SymPy recasts exact binary fractions to Rationals
    const v = c.toNumber();
    const f = Math.abs(v) % 1;
    if (f !== 0) {
      const m = 2 ** -Math.round(Math.log2(f));
      if (Number.isInteger(v * m)) c = Rational.of(BigInt(v * m), BigInt(m));
    } else c = Rational.of(BigInt(Math.trunc(v)));
  }
  if (isIntegerQ(x) === true) return mul(Mod(c, 2), x);
  return mul(c, x);
}

/** SymPy Ray2D.__new__(p1, pt=None, angle=None). */
function ray2D(p1In: PointInput, pt: PointInput | undefined, opts: RayOpts): Ray2DNode {
  const p1 = toPoint(p1In, { dim: 2 });
  let p2: PointNode | undefined;
  if (pt !== undefined && opts.angle === undefined) {
    try {
      p2 = toPoint(pt, { dim: 2 });
    } catch {
      throw new RangeError('The 2nd argument was not a valid Point; if it was meant to be an angle it should be given with keyword "angle".');
    }
    if (p1.key === p2.key) throw new RangeError('A Ray requires two distinct points.');
  } else if (opts.angle !== undefined && pt === undefined) {
    const angle = sympify(opts.angle);
    let c = piCoeff(angle);
    if (c !== undefined) {
      if (c instanceof Rational) {
        // c is in [0, 2): 1/2 or 3/2, 0 or 1
        if (c.q === 2n) p2 = p1.add(c.p === 1n ? [0, 1] : [0, -1]);
        else if (c.q === 1n) p2 = p1.add(c.p === 0n ? [1, 0] : [-1, 0]);
      }
      if (p2 === undefined) c = mul(c, S.Pi);
    } else c = Mod(angle, mul(2, S.Pi));
    if (p2 === undefined) {
      const m = mul(2, c, pow(S.Pi, -1));
      const left = and(Lt(1, m), Lt(m, 3));
      const x = piecewise([-1, left], [piecewise([0, Eq(Mod(m, 1), 0)], [1, true]), true]);
      const y = piecewise([mul(-1, tan(c)), left], [piecewise([1, Eq(m, 1)], [-1, Eq(m, 3)], [tan(c), true]), true]);
      p2 = p1.add(toPoint([x, y]));
    }
  } else throw new RangeError('A 2nd point or keyword "angle" must be used.');
  return newLinear(p1, p2, (a, b) => new Ray2DNode(as2D(a), as2D(b)), 'Ray2D');
}

/** SymPy Ray3D.__new__(p1, pt=None, direction_ratio=()). */
function ray3D(p1In: PointInput | LinearEntity, ptIn: PointInput | undefined, opts: RayOpts): Ray3DNode {
  const [p1, p2] = point3DPair(p1In, ptIn, opts.directionRatio, 'If p1 is a LinearEntity, pt must be None');
  return newLinear(p1, p2, (a, b) => new Ray3DNode(as3DPoint(a), as3DPoint(b)), 'Ray3D');
}

/** SymPy Segment.__new__: a Segment2D, Segment3D or Segment (a Point when the end points coincide). */
function newSegment(p1In: PointInput, p2In: PointInput): SegmentNode | PointNode {
  const [p1, p2] = normalizeDimension([toPoint(p1In), toPoint(p2In)]);
  const dim = defd(p1).args.length;
  if (dim === 2) return segment2D(defd(p1), defd(p2));
  if (dim === 3) return segment3D(defd(p1), defd(p2));
  return newLinear(defd(p1), defd(p2), (a, b) => new SegmentNode(a, b), 'Segment');
}

function segment2D(p1In: PointInput, p2In: PointInput): Segment2DNode | PointNode {
  const p1 = toPoint(p1In, { dim: 2 });
  const p2 = toPoint(p2In, { dim: 2 });
  if (p1.key === p2.key) return p1;
  return new Segment2DNode(as2D(p1), as2D(p2));
}

function segment3D(p1In: PointInput, p2In: PointInput): Segment3DNode | PointNode {
  const p1 = toPoint(p1In, { dim: 3 });
  const p2 = toPoint(p2In, { dim: 3 });
  if (p1.key === p2.key) return p1;
  return new Segment3DNode(as3DPoint(p1), as3DPoint(p2));
}

type LineArg = PointInput | LinearEntity | LineOptions | Expr;

/**
 * Constructs the infinite line determined by two points, a direction or a linear equation.
 *
 * @param args - Two points, another linear entity, or a line equation with optional coordinate names or direction options.
 * @returns The resulting `Line` expression.
 * @throws RangeError when the points coincide or the equation does not define a line.
 * @see SymPy `sympy.geometry.line.Line`
 * @example
 * ```ts
 * import { Line } from '@symjs/symjs';
 *
 * Line([2, 3], [3, 5]); // => Line2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export const Line = /* @__PURE__ */ callableClass(LineNode, (...args: LineArg[]): LineNode => {
  const [pos, opts] = splitCall(args, readLineOptions);
  return newLine(pos, opts);
});
export type Line = LineNode;

/**
 * Constructs an infinite line in the plane.
 *
 * @param args - Defining points or a point with a slope.
 * @returns The resulting `Line2D` expression.
 * @throws RangeError when the points coincide or no second point or slope is supplied.
 * @see SymPy `sympy.geometry.line.Line2D`
 * @example
 * ```ts
 * import { Line2D } from '@symjs/symjs';
 *
 * Line2D([2, 3], [3, 5]); // => Line2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export const Line2D = /* @__PURE__ */ callableClass(Line2DNode, (...args: LineArg[]): Line2DNode => {
  const [pos, opts] = splitCall(args, readLineOptions);
  const first = pos[0];
  return line2D(first instanceof LinearEntity ? first : pointArg(first), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Line2D = Line2DNode;

/**
 * Constructs an infinite 3D line in space.
 *
 * @param args - Defining points or a point with direction ratios.
 * @returns The resulting `Line3D` expression.
 * @throws RangeError when the points coincide or no second point or direction ratios are supplied.
 * @see SymPy `sympy.geometry.line.Line3D`
 * @example
 * ```ts
 * import { Line3D } from '@symjs/symjs';
 *
 * Line3D([2, 3, 4], [3, 5, 1]); // => Line3D(Point3D(2, 3, 4), Point3D(3, 5, 1))
 * ```
 */
export const Line3D = /* @__PURE__ */ callableClass(Line3DNode, (...args: LineArg[]): Line3DNode => {
  const [pos, opts] = splitCall(args, readLineOptions);
  const first = pos[0];
  return line3D(first instanceof LinearEntity ? first : pointArg(first), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Line3D = Line3DNode;

type RayArg = PointInput | RayOptions;

/**
 * Constructs a half-line extending from its source through a second point or along a specified
 * direction.
 *
 * @param args - Source and second point, or source and direction options.
 * @returns The resulting `Ray` expression.
 * @throws RangeError when the source and direction do not determine a ray.
 * @see SymPy `sympy.geometry.line.Ray`
 * @example
 * ```ts
 * import { Ray } from '@symjs/symjs';
 *
 * Ray([2, 3], [3, 5]); // => Ray2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export const Ray = /* @__PURE__ */ callableClass(RayNode, (...args: RayArg[]): RayNode => {
  const [pos, opts] = splitCall(args, readRayOptions);
  return newRay(pos, opts);
});
export type Ray = RayNode;

/**
 * Constructs a half-line in the plane given by its source and direction.
 *
 * @param args - Source and second point or angular direction.
 * @returns The resulting `Ray2D` expression.
 * @throws RangeError when the defining points coincide or no direction is supplied.
 * @see SymPy `sympy.geometry.line.Ray2D`
 * @example
 * ```ts
 * import { Ray2D } from '@symjs/symjs';
 *
 * Ray2D([2, 3], [3, 5]); // => Ray2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export const Ray2D = /* @__PURE__ */ callableClass(Ray2DNode, (...args: RayArg[]): Ray2DNode => {
  const [pos, opts] = splitCall(args, readRayOptions);
  return ray2D(pointArg(pos[0]), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Ray2D = Ray2DNode;

/**
 * Constructs a half-line in three-dimensional space given by its source and direction.
 *
 * @param args - Source and second point or direction ratios.
 * @returns The resulting `Ray3D` expression.
 * @throws RangeError when the defining points coincide or no direction is supplied.
 * @see SymPy `sympy.geometry.line.Ray3D`
 * @example
 * ```ts
 * import { Ray3D } from '@symjs/symjs';
 *
 * Ray3D([2, 3, 4], [3, 5, 1]); // => Ray3D(Point3D(2, 3, 4), Point3D(3, 5, 1))
 * ```
 */
export const Ray3D = /* @__PURE__ */ callableClass(Ray3DNode, (...args: (RayArg | LinearEntity)[]): Ray3DNode => {
  const [pos, opts] = splitCall(args, readRayOptions);
  const first = pos[0];
  return ray3D(first instanceof LinearEntity ? first : pointArg(first), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Ray3D = Ray3DNode;

/**
 * Constructs the closed segment joining two points.
 *
 * @param p1 - First defining point.
 * @param p2 - Second defining point.
 * @returns The segment, or its endpoint when the two points coincide.
 * @see SymPy `sympy.geometry.line.Segment`
 * @example
 * ```ts
 * import { Segment } from '@symjs/symjs';
 *
 * Segment([2, 3], [3, 5]); // => Segment2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export const Segment = /* @__PURE__ */ callableClass(SegmentNode, (p1: PointInput, p2: PointInput): SegmentNode | PointNode => newSegment(p1, p2));
export type Segment = SegmentNode;

/**
 * Constructs a line segment in 2D space.
 *
 * @param p1 - First defining point.
 * @param p2 - Second defining point.
 * @returns The segment, or its endpoint when the two points coincide.
 * @see SymPy `sympy.geometry.line.Segment2D`
 * @example
 * ```ts
 * import { Segment2D } from '@symjs/symjs';
 *
 * Segment2D([2, 3], [3, 5]); // => Segment2D(Point2D(2, 3), Point2D(3, 5))
 * ```
 */
export const Segment2D = /* @__PURE__ */ callableClass(Segment2DNode, (p1: PointInput, p2: PointInput): Segment2DNode | PointNode => segment2D(p1, p2));
export type Segment2D = Segment2DNode;

/**
 * Constructs a line segment in a 3D space.
 *
 * @param p1 - First defining point.
 * @param p2 - Second defining point.
 * @returns The segment, or its endpoint when the two points coincide.
 * @see SymPy `sympy.geometry.line.Segment3D`
 * @example
 * ```ts
 * import { Segment3D } from '@symjs/symjs';
 *
 * Segment3D([2, 3, 4], [3, 5, 1]); // => Segment3D(Point3D(2, 3, 4), Point3D(3, 5, 1))
 * ```
 */
export const Segment3D = /* @__PURE__ */ callableClass(Segment3DNode, (p1: PointInput, p2: PointInput): Segment3DNode | PointNode => segment3D(p1, p2));
export type Segment3D = Segment3DNode;

/** Python bool() of expression comparisons, for the other geometry modules. */
export { pyGe, pyGt, pyLe, pyLt };
