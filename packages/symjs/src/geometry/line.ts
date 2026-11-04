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
 * SymPy LinearEntity: the base class of lines, rays and segments, given by
 * two distinct points p1 and p2.
 */
export abstract class LinearEntity extends GeometrySet {
  /** The first defining point. */
  get p1(): PointNode {
    return asPoint(at(this.args, 0));
  }
  /** The second defining point. */
  get p2(): PointNode {
    return asPoint(at(this.args, 1));
  }
  /** The defining points (SymPy points). */
  get points(): [PointNode, PointNode] {
    return [this.p1, this.p2];
  }

  get ambientDimension(): number {
    return this.p1.args.length;
  }

  /** The direction vector p2 - p1 (SymPy direction). */
  get direction(): PointNode {
    return this.p2.sub(this.p1);
  }

  /** The length: infinite unless a segment (SymPy length). */
  get length(): Expr {
    return S.Infinity;
  }

  /** SymPy _span_test: 0 for p1, 1 for a point in the direction of the entity, -1 behind it. */
  spanTest(other: PointNode): number {
    if (this.p1.key === other.key) return 0;
    const rel = other.sub(this.p1);
    return pyGt(this.direction.dot(rel), 0) ? 1 : -1;
  }

  /** SymPy `o in self`: contains, or Undecidable. */
  override contains(other: unknown): boolean {
    return this.containsQ(other);
  }

  /** SymPy contains: the entity contains the point or linear entity (SymPy contains). */
  abstract containsQ(other: unknown): boolean;

  /** The angle between the direction vectors (SymPy angle_between). */
  angleBetween(l2: LinearEntity): Expr {
    const [v1, v2] = [this.direction, l2.direction];
    return acos(mul(v1.dot(v2), pow(mul(v1.abs(), v2.abs()), -1)));
  }

  /** The smallest angle between the lines (SymPy smallest_angle_between). */
  smallestAngleBetween(l2: LinearEntity): Expr {
    const [v1, v2] = [this.direction, l2.direction];
    return acos(mul(abs(v1.dot(v2)), pow(mul(v1.abs(), v2.abs()), -1)));
  }

  /** The point p1 + t*(p2 - p1) with the real parameter t (SymPy arbitrary_point). */
  override arbitraryPoint(parameter: string | Sym | null = 't'): PointNode {
    const t = realSymbol(parameter ?? 't');
    if ([...this.freeSymbols()].some((f) => f.name === t.name)) {
      throw new RangeError(`Symbol ${t.name} already appears in object and cannot be used as a parameter.`);
    }
    return this.p1.add(this.direction.mul(t));
  }

  /** All the linear entities have exactly one point in common (SymPy are_concurrent). */
  static areConcurrent(...lines: LinearEntity[]): boolean {
    if (lines.length < 2) return false;
    let common: GeometryEntity[] = [at(lines, 0)];
    for (const l of lines.slice(1)) common = common.flatMap((c) => c.intersection(l));
    return common.length === 1 && at(common, 0).isPoint;
  }

  /** The entities this one has in common with other (SymPy intersection). */
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

  /** The direction vectors are parallel (SymPy is_parallel). */
  isParallel(l2: LinearEntity): boolean {
    return this.direction.isScalarMultiple(l2.direction);
  }

  /** The direction vectors are perpendicular (SymPy is_perpendicular). */
  isPerpendicular(l2: LinearEntity): boolean {
    return exprEquals(S.Zero, this.direction.dot(l2.direction)) === true;
  }

  /** The entities lie on the same line (SymPy is_similar). */
  override isSimilar(other: GeometryEntity): boolean {
    return Line(this.p1, this.p2).containsQ(other);
  }

  /** The line through p parallel to this one (SymPy parallel_line). */
  parallelLine(pIn: PointInput): LineNode {
    const p = toPoint(pIn, { dim: this.ambientDimension });
    return Line(p, p.add(this.direction));
  }

  /** The line through p perpendicular to this one (SymPy perpendicular_line). */
  perpendicularLine(pIn: PointInput): LineNode {
    let p = toPoint(pIn, { dim: this.ambientDimension });
    if (this.contains(p)) p = p.add(this.direction.orthogonalDirection);
    return Line(p, this.projection(p));
  }

  /** The segment from p perpendicular to this line, or p itself when it lies on the line (SymPy perpendicular_segment). */
  perpendicularSegment(pIn: PointInput): PointNode | SegmentNode {
    const p = toPoint(pIn, { dim: this.ambientDimension });
    if (this.contains(p)) return p;
    const l = this.perpendicularLine(p);
    const [p2] = Line(this.p1, this.p2).intersection(l);
    return Segment(p, asPoint(defined(p2)));
  }

  /** The projection of a point or linear entity onto this line (SymPy projection). */
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

  /** A random point of the entity; the same for the same integer seed (SymPy random_point). */
  randomPoint(seed?: number | bigint): PointNode {
    const rng = seed === undefined ? sharedRandom : new Random(seed);
    const pt = this.arbitraryPoint(lineT);
    let v: number;
    if (this instanceof RayNode) v = Math.abs(rng.gauss(0, 1));
    else if (this instanceof SegmentNode) v = rng.random();
    else v = rng.gauss(0, 1);
    return asPoint(subs(pt, [[lineT, rationalOf(v)]]));
  }

  /** The two perpendicular lines through the intersection that bisect the angles (SymPy bisectors). */
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

  /** The parameter interval of the arbitrary point used for plotting (SymPy plot_interval). */
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

/** SymPy Line: an infinite line through two points. */
export class LineNode extends LinearEntity {
  constructor(p1: PointNode, p2: PointNode, name = 'Line') {
    super(name, [p1, p2]);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Line(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /** The line contains the point or linear entity (SymPy Line.contains). */
  containsQ(otherIn: unknown): boolean {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (other instanceof PointNode) return other.isCollinear(this.p1, this.p2);
    if (other instanceof LinearEntity) return this.p1.isCollinear(this.p2, other.p1, other.p2);
    return false;
  }

  /** The shortest distance to a point (SymPy Line.distance). */
  override distance(otherIn: unknown): Expr {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (this.containsQ(other)) return S.Zero;
    const ps = this.perpendicularSegment(asPoint(other));
    return ps.length;
  }

  /** The lines are the same set of points (SymPy Line.equals). */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof LineNode)) return false;
    return this.p1.isCollinear(other.p1, this.p2, other.p2);
  }

  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), Rational.of(-5n), Rational.of(5n)];
  }

  override enclosedBy(): boolean {
    return false;
  }
}

/** SymPy Ray: a half-line from a source point through a second point. */
export class RayNode extends LinearEntity {
  constructor(p1: PointNode, p2: PointNode, name = 'Ray') {
    super(name, [p1, p2]);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Ray(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /** The source point (SymPy source). */
  get source(): PointNode {
    return this.p1;
  }

  /** The ray contains the point or linear entity (SymPy Ray.contains). */
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

  /** The shortest distance to a point (SymPy Ray.distance). */
  override distance(otherIn: unknown): Expr {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(toInput(otherIn), { dim: this.ambientDimension });
    if (this.containsQ(other)) return S.Zero;
    const o = asPoint(other);
    const proj = asPoint(Line(this.p1, this.p2).projection(o));
    if (this.containsQ(proj)) return o.sub(proj).abs();
    return o.sub(this.source).abs();
  }

  /** The rays have the same source and direction (SymPy Ray.equals). */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof RayNode)) return false;
    return this.source.key === other.source.key && this.contains(other.p2);
  }

  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), S.Zero, Rational.of(10n)];
  }

  override enclosedBy(): boolean {
    return false;
  }
}

/** SymPy Segment: the line segment between two points. */
export class SegmentNode extends LinearEntity {
  constructor(p1: PointNode, p2: PointNode, name = 'Segment') {
    super(name, [p1, p2]);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Segment(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /** The segment contains the point or segment (SymPy Segment.contains). */
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

  /** The segments have the same end points (SymPy Segment.equals). */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof SegmentNode) || other.name !== this.name) return false;
    const a = ordered(this.args).map((e) => e.key);
    const b = ordered(other.args).map((e) => e.key);
    return a.every((k, i) => k === b[i]);
  }

  /** The shortest distance to a point (SymPy Segment.distance). */
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

  /** The distance between the end points (SymPy length). */
  override get length(): Expr {
    return this.p1.distance(this.p2);
  }

  /** The midpoint (SymPy midpoint). */
  get midpoint(): PointNode {
    return this.p1.midpoint(this.p2);
  }

  /**
   * The perpendicular bisector; with a point p on it, the segment from p to
   * the midpoint (SymPy perpendicular_bisector).
   */
  perpendicularBisector(p?: PointInput): LineNode | SegmentNode | PointNode {
    const l = this.perpendicularLine(this.midpoint);
    if (p !== undefined) {
      const p2 = toPoint(p, { dim: this.ambientDimension });
      if (l.contains(p2)) return Segment(p2, this.midpoint);
    }
    return l;
  }

  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), S.Zero, S.One];
  }

  /** SymPy GeometryEntity.encloses for a segment: both end points are enclosed. */
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

/** SymPy Line2D: a line in the plane. */
export class Line2DNode extends LineNode {
  constructor(p1: Point2DNode, p2: Point2DNode) {
    super(p1, p2, 'Line2D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Line2D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  override get bounds(): [Expr, Expr, Expr, Expr] {
    return bounds2D(this);
  }

  /** The slope: oo for a vertical line (SymPy slope). */
  get slope(): Expr {
    return slope2D(this);
  }

  override perpendicularLine(p: PointInput): Line2DNode {
    return perpendicularLine2D(this, p);
  }

  /** The coefficients (a, b, c) of the equation a*x + b*y + c = 0 (SymPy coefficients). */
  get coefficients(): [Expr, Expr, Expr] {
    const [p1, p2] = this.points;
    if (p1.coordinate(0).key === p2.coordinate(0).key) return [S.One, S.Zero, mul(-1, p1.coordinate(0))];
    if (p1.coordinate(1).key === p2.coordinate(1).key) return [S.Zero, S.One, mul(-1, p1.coordinate(1))];
    const [x1, y1, x2, y2] = [p1.coordinate(0), p1.coordinate(1), p2.coordinate(0), p2.coordinate(1)];
    return [simplify(add(y1, mul(-1, y2))), simplify(add(x2, mul(-1, x1))), simplify(add(mul(x1, y2), mul(-1, y1, x2)))];
  }

  /** The equation a*x + b*y + c of the line in real symbols x and y (SymPy equation). */
  equation(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const [p1, p2] = this.points;
    if (p1.coordinate(0).key === p2.coordinate(0).key) return add(X, mul(-1, p1.coordinate(0)));
    if (p1.coordinate(1).key === p2.coordinate(1).key) return add(Y, mul(-1, p1.coordinate(1)));
    const [a, b, c] = this.coefficients;
    return add(mul(a, X), mul(b, Y), c);
  }
}

/** SymPy Ray2D: a ray in the plane. */
export class Ray2DNode extends RayNode {
  constructor(p1: Point2DNode, p2: Point2DNode) {
    super(p1, p2, 'Ray2D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Ray2D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  override get bounds(): [Expr, Expr, Expr, Expr] {
    return bounds2D(this);
  }

  /** The slope: oo for a vertical ray (SymPy slope). */
  get slope(): Expr {
    return slope2D(this);
  }

  override perpendicularLine(p: PointInput): Line2DNode {
    return perpendicularLine2D(this, p);
  }

  /** The x direction: oo, 0 or -oo (SymPy xdirection). */
  get xdirection(): Expr {
    return direction(this.p1.coordinate(0), this.p2.coordinate(0));
  }

  /** The y direction: oo, 0 or -oo (SymPy ydirection). */
  get ydirection(): Expr {
    return direction(this.p1.coordinate(1), this.p2.coordinate(1));
  }

  /** The angle by which r2 must be rotated counterclockwise to have the direction of this ray (SymPy closing_angle). */
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

/** SymPy Segment2D: a segment in the plane. */
export class Segment2DNode extends SegmentNode {
  constructor(p1: Point2DNode, p2: Point2DNode) {
    super(p1, p2, 'Segment2D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Segment2D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  override get bounds(): [Expr, Expr, Expr, Expr] {
    return bounds2D(this);
  }

  /** The slope: oo for a vertical segment (SymPy slope). */
  get slope(): Expr {
    return slope2D(this);
  }

  override perpendicularLine(p: PointInput): Line2DNode {
    return perpendicularLine2D(this, p);
  }
}

/** SymPy LinearEntity3D.direction_ratio. */
const directionRatio3D = (l: LinearEntity): Expr[] => as3DPoint(l.p1).directionRatio(as3DPoint(l.p2));
/** SymPy LinearEntity3D.direction_cosine. */
const directionCosine3D = (l: LinearEntity): Expr[] => as3DPoint(l.p1).directionCosine(as3DPoint(l.p2));

const as3DPoint = (e: Expr): Point3DNode => cast(e, Point3DNode, 'Point3D');

/** SymPy Line3D: a line in space. */
export class Line3DNode extends LineNode {
  constructor(p1: Point3DNode, p2: Point3DNode) {
    super(p1, p2, 'Line3D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Line3D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /** The direction ratios (SymPy direction_ratio). */
  get directionRatio(): Expr[] {
    return directionRatio3D(this);
  }

  /** The direction cosines (SymPy direction_cosine). */
  get directionCosine(): Expr[] {
    return directionCosine3D(this);
  }

  /**
   * The equations of the line as the two planes through it, in real
   * symbols x, y and z (SymPy equation).
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

  /** The shortest distance to a point, line or plane (SymPy Line3D.distance). */
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

/** SymPy Ray3D: a ray in space. */
export class Ray3DNode extends RayNode {
  constructor(p1: Point3DNode, p2: Point3DNode) {
    super(p1, p2, 'Ray3D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Ray3D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /** The direction ratios (SymPy direction_ratio). */
  get directionRatio(): Expr[] {
    return directionRatio3D(this);
  }

  /** The direction cosines (SymPy direction_cosine). */
  get directionCosine(): Expr[] {
    return directionCosine3D(this);
  }

  /** The x direction: oo, 0 or -oo (SymPy xdirection). */
  get xdirection(): Expr {
    return direction(this.p1.coordinate(0), this.p2.coordinate(0));
  }
  /** The y direction: oo, 0 or -oo (SymPy ydirection). */
  get ydirection(): Expr {
    return direction(this.p1.coordinate(1), this.p2.coordinate(1));
  }
  /** The z direction: oo, 0 or -oo (SymPy zdirection). */
  get zdirection(): Expr {
    return direction(this.p1.coordinate(2), this.p2.coordinate(2));
  }
}

/** SymPy Segment3D: a segment in space. */
export class Segment3DNode extends SegmentNode {
  constructor(p1: Point3DNode, p2: Point3DNode) {
    super(p1, p2, 'Segment3D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return Segment3D(asPoint(at(args, 0)), asPoint(at(args, 1)));
  }

  /** The direction ratios (SymPy direction_ratio). */
  get directionRatio(): Expr[] {
    return directionRatio3D(this);
  }

  /** The direction cosines (SymPy direction_cosine). */
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
 * SymPy Line(p1, p2), Line(p1, {slope}) (2D), Line(p1, {directionRatio})
 * (3D), Line(linearEntity) or Line(equation, {x, y}): a Line2D, Line3D or
 * Line.
 */
export const Line = /* @__PURE__ */ callableClass(LineNode, (...args: LineArg[]): LineNode => {
  const [pos, opts] = splitCall(args, readLineOptions);
  return newLine(pos, opts);
});
export type Line = LineNode;

/** SymPy Line2D(p1, pt=None, slope=None). */
export const Line2D = /* @__PURE__ */ callableClass(Line2DNode, (...args: LineArg[]): Line2DNode => {
  const [pos, opts] = splitCall(args, readLineOptions);
  const first = pos[0];
  return line2D(first instanceof LinearEntity ? first : pointArg(first), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Line2D = Line2DNode;

/** SymPy Line3D(p1, pt=None, direction_ratio=()). */
export const Line3D = /* @__PURE__ */ callableClass(Line3DNode, (...args: LineArg[]): Line3DNode => {
  const [pos, opts] = splitCall(args, readLineOptions);
  const first = pos[0];
  return line3D(first instanceof LinearEntity ? first : pointArg(first), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Line3D = Line3DNode;

type RayArg = PointInput | RayOptions;

/** SymPy Ray(p1, p2) or Ray(p1, {angle}) (2D) / Ray(p1, {directionRatio}) (3D). */
export const Ray = /* @__PURE__ */ callableClass(RayNode, (...args: RayArg[]): RayNode => {
  const [pos, opts] = splitCall(args, readRayOptions);
  return newRay(pos, opts);
});
export type Ray = RayNode;

/** SymPy Ray2D(p1, pt=None, angle=None). */
export const Ray2D = /* @__PURE__ */ callableClass(Ray2DNode, (...args: RayArg[]): Ray2DNode => {
  const [pos, opts] = splitCall(args, readRayOptions);
  return ray2D(pointArg(pos[0]), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Ray2D = Ray2DNode;

/** SymPy Ray3D(p1, pt=None, direction_ratio=()). */
export const Ray3D = /* @__PURE__ */ callableClass(Ray3DNode, (...args: (RayArg | LinearEntity)[]): Ray3DNode => {
  const [pos, opts] = splitCall(args, readRayOptions);
  const first = pos[0];
  return ray3D(first instanceof LinearEntity ? first : pointArg(first), pos[1] === undefined ? undefined : pointArg(pos[1]), opts);
});
export type Ray3D = Ray3DNode;

/** SymPy Segment(p1, p2): a Segment2D, Segment3D or Segment (the point when p1 == p2). */
export const Segment = /* @__PURE__ */ callableClass(SegmentNode, (p1: PointInput, p2: PointInput): SegmentNode | PointNode => newSegment(p1, p2));
export type Segment = SegmentNode;

/** SymPy Segment2D(p1, p2). */
export const Segment2D = /* @__PURE__ */ callableClass(Segment2DNode, (p1: PointInput, p2: PointInput): Segment2DNode | PointNode => segment2D(p1, p2));
export type Segment2D = Segment2DNode;

/** SymPy Segment3D(p1, p2). */
export const Segment3D = /* @__PURE__ */ callableClass(Segment3DNode, (p1: PointInput, p2: PointInput): Segment3DNode | PointNode => segment3D(p1, p2));
export type Segment3D = Segment3DNode;

/** Python bool() of expression comparisons, for the other geometry modules. */
export { pyGe, pyGt, pyLe, pyLt };
