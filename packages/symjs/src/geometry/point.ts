// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/point.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.point: points in n-dimensional Euclidean space
 * (Point, and Point2D and Point3D for two and three dimensions).
 *
 * Point(...) gives a Point2D or Point3D for two or three coordinates.
 * Floats among the coordinates are converted to Rationals unless
 * `evaluate: false` is given. Points add, subtract and scale like vectors
 * (add, sub, mul, div, neg); the coordinates of the results are simplified.
 */

import { BoolAtom, Expr, ExtensionExpr, Float, Fn, Rational, Rel, S } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { some, xreplace } from '../core/traverse';
import { atoms } from '../core/methods';
import { callableClass } from '../core/callable';
import { isNonZero, isZero as isZeroQ } from '../core/assumptions';
import type { Truth } from '../core/truth';
import { at, cast } from '../core/guard';
import { TupleNode } from '../core/containers';
import { abs, cos, sin } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
import { rref } from '../matrices/linalg';
import { nsimplify } from '../numeric/nfloat';
import { simplify } from '../simplify/simplify';
import { GeometryEntity, geometryClasses } from './entity';
import { isNonRealNumber } from './solvehelp';
import type { PointInput } from './entity';
import { GeometryError, Undecidable } from './exceptions';

/** Options of the Point constructors (SymPy keyword arguments). */
export interface PointOptions {
  /** Convert Floats to Rationals (default true). */
  evaluate?: boolean;
  /** The dimension: missing coordinates are zeros, extra zero coordinates are dropped. */
  dim?: number;
  /** What a change of dimension does: 'ignore' (default), 'warn' (as ignore) or 'error'. */
  onMorph?: 'ignore' | 'warn' | 'error';
}

/** A plain options object (not an expression or a sequence). */
export const isOptions = (x: unknown): x is Record<string, unknown> =>
  typeof x === 'object' && x !== null && !(x instanceof Expr) && !Array.isArray(x) && !(x instanceof Matrix);

/** The entry is a sequence of coordinates (SymPy is_sequence, not a Point). */
const isCoordSequence = (x: unknown): x is readonly ExprLike[] | TupleNode => Array.isArray(x) || x instanceof TupleNode;

/** SymPy is_number: no free symbols. */
const isNumberExpr = (e: Expr): boolean => e.freeSymbols().size === 0;

/** A value that is not a SymPy Expr (a geometry entity, container, set, boolean or relational). */
const isNotExpr = (e: Expr): boolean => e instanceof GeometryEntity || e instanceof TupleNode || e instanceof BoolAtom || e instanceof Rel || e.kind === 'Set';

/**
 * SymPy Point: a point in n-dimensional Euclidean space. Point2D and
 * Point3D are its subclasses for two and three dimensions.
 */
export class PointNode extends GeometryEntity {
  constructor(coords: readonly Expr[], name = 'Point') {
    super(name, coords);
  }

  override get isPoint(): boolean {
    return true;
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newPoint(args);
  }

  /** The number of coordinates (SymPy ambient_dimension). */
  get ambientDimension(): number {
    return this.args.length;
  }

  /** The coordinates (SymPy coordinates, the arguments). */
  get coordinates(): readonly Expr[] {
    return this.args;
  }

  /** The coordinate i (SymPy p[i]). */
  coordinate(i: number): Expr {
    return at(this.args, i < 0 ? this.args.length + i : i);
  }

  /** SymPy `item in p`: item is one of the coordinates (a Point2D or Point3D: item is the point). */
  override contains(item: unknown): boolean {
    if (this instanceof Point2DNode || this instanceof Point3DNode) return item instanceof Expr && item.key === this.key;
    return item instanceof Expr && this.args.some((a) => a.key === item.key);
  }

  /** SymPy GeometryEntity.encloses for a point: the container encloses it. */
  override enclosedBy(container: GeometryEntity): boolean {
    return container.enclosesPoint(this) === true;
  }

  // ---- arithmetic ----------------------------------------------------------

  /** SymPy p + q: the coordinatewise sum, simplified. */
  override add(other: ExprLike | PointInput): PointNode {
    let s: PointNode, o: PointNode;
    try {
      [s, o] = pair2(normalizeDimension([this, toPoint(toInput(other), { evaluate: false })]));
    } catch (err) {
      if (err instanceof TypeError) throw new GeometryError(`Don't know how to add ${String(other)} and a Point object`);
      throw err;
    }
    return newPoint(
      s.args.map((a, i) => simplify(add(a, at(o.args, i)))),
      { evaluate: false },
    );
  }

  /** SymPy p - q. */
  override sub(other: ExprLike | PointInput): PointNode {
    const o = toInput(other);
    const coords = o instanceof Expr ? o.args : o;
    return this.add(coords.map((c) => mul(-1, c)));
  }

  /** SymPy p*factor: the coordinates multiplied, simplified. */
  override mul(factor: ExprLike): PointNode {
    const f = sympify(factor);
    return newPoint(
      this.args.map((x) => simplify(mul(x, f))),
      { evaluate: false },
    );
  }

  /** SymPy p/divisor: the coordinates divided, simplified. */
  override div(divisor: ExprLike): PointNode {
    const d = sympify(divisor);
    return newPoint(
      this.args.map((x) => simplify(mul(x, pow(d, -1)))),
      { evaluate: false },
    );
  }

  /** SymPy -p. */
  override neg(): PointNode {
    return newPoint(
      this.args.map((x) => mul(-1, x)),
      { evaluate: false },
    );
  }

  /** SymPy abs(p): the distance from the origin. */
  abs(): Expr {
    return newPoint(this.args.map(() => S.Zero)).distance(this);
  }

  // ---- properties ----------------------------------------------------------

  /** The length of a point is zero (SymPy length). */
  get length(): Expr {
    return S.Zero;
  }

  /** The origin of the space of the point (SymPy origin). */
  get origin(): PointNode {
    return newPoint(
      this.args.map(() => S.Zero),
      { evaluate: false },
    );
  }

  /** A nonzero vector orthogonal to the point as a vector (SymPy orthogonal_direction). */
  get orthogonalDirection(): PointNode {
    const dim = this.ambientDimension;
    const zeros = (n: number): Expr[] => Array.from({ length: n }, () => S.Zero);
    if (isZeroQ(this.coordinate(0)) === true) return newPoint([S.One, ...zeros(dim - 1)]);
    if (isZeroQ(this.coordinate(1)) === true) return newPoint([S.Zero, S.One, ...zeros(dim - 2)]);
    return newPoint([mul(-1, this.coordinate(1)), this.coordinate(0), ...zeros(dim - 2)]);
  }

  /** The vector of length 1 in the direction of the point (SymPy unit). */
  get unit(): PointNode {
    return this.div(this.abs());
  }

  /** All coordinates are zero (SymPy is_zero; 'unknown' when undecided). */
  get isZero(): Truth {
    const nonzero = this.args.map(isNonZero);
    if (nonzero.some((v) => v === true)) return false;
    if (nonzero.some((v) => v === undefined)) return 'unknown';
    return true;
  }

  /** Some coordinate is nonzero (SymPy is_nonzero; 'unknown' when undecided). */
  get isNonzero(): Truth {
    const z = this.isZero;
    return z === 'unknown' ? z : !z;
  }

  // ---- metric --------------------------------------------------------------

  /** The Euclidean distance to a point or another entity (SymPy distance). */
  distance(other: PointInput): Expr {
    const o = other instanceof GeometryEntity ? other : toPoint(other, { dim: this.ambientDimension });
    if (o instanceof PointNode) {
      const [s, p] = pair2(normalizeDimension([this, o]));
      return sqrt(add(...s.args.map((a, i) => pow(add(a, mul(-1, at(p.args, i))), 2))));
    }
    return o.distance(this);
  }

  /** The dot product with p as vectors (SymPy dot). */
  dot(p: PointInput): Expr {
    const q = toPoint(p);
    return add(...this.args.map((a, i) => mul(a, q.coordinate(i))));
  }

  /** The points are the same, with coordinates that may differ in form (SymPy equals). */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof PointNode) || this.args.length !== other.args.length) return false;
    return this.args.every((a, i) => exprEquals(a, at(other.args, i)) === true);
  }

  /** The sum of the absolute differences of the coordinates (SymPy taxicab_distance). */
  taxicabDistance(p: PointInput): Expr {
    const [s, q] = pair2(normalizeDimension([this, toPoint(p)]));
    return add(...s.args.map((a, i) => abs(add(a, mul(-1, at(q.args, i))))));
  }

  /** The Canberra distance to p (SymPy canberra_distance). */
  canberraDistance(p: PointInput): Expr {
    const [s, q] = pair2(normalizeDimension([this, toPoint(p)]));
    if (this.isZero === true && q.isZero === true) throw new RangeError('Cannot project to the zero vector.');
    return add(...s.args.map((a, i) => mul(abs(add(a, mul(-1, at(q.args, i)))), pow(add(abs(a), abs(at(q.args, i))), -1))));
  }

  /** The midpoint of this point and p (SymPy midpoint). */
  midpoint(p: PointInput): PointNode {
    const [s, q] = pair2(normalizeDimension([this, toPoint(p)]));
    return newPoint(s.args.map((a, i) => simplify(mul(add(a, at(q.args, i)), S.Half))));
  }

  /** The intersection with another entity: [this] for the same point, [] for another one (SymPy intersection). */
  override intersection(other: unknown): GeometryEntity[] {
    const o = other instanceof GeometryEntity ? other : toPoint(toInput(other));
    if (o instanceof PointNode) {
      if (o.key === this.key) return [this];
      const [p1, p2] = pair2(normalizeDimension([this, o]));
      if (p1.key === this.key && p1.key === p2.key) return [this];
      return [];
    }
    return o.intersection(this);
  }

  /** The point and the others lie on one line (SymPy is_collinear). */
  isCollinear(...args: PointInput[]): boolean {
    const points = uniqPoints(normalizeDimension([this, ...args].map((a) => toPoint(a))));
    return affineRank(...points) <= 1;
  }

  /** The point and the others lie on one circle (SymPy is_concyclic). */
  isConcyclic(...args: PointInput[]): boolean {
    let points = uniqPoints(normalizeDimension([this, ...args].map((a) => toPoint(a))));
    if (!(affineRank(...points) <= 2)) return false;
    const origin = at(points, 0);
    points = points.map((p) => p.sub(origin));
    const mat = Matrix.of(points.map((p) => [...p.args, p.dot(p)]));
    const [, pivots] = rref(mat);
    return !pivots.includes(origin.args.length);
  }

  /** The point is a scalar multiple of p as vectors (SymPy is_scalar_multiple). */
  isScalarMultiple(p: PointInput): boolean {
    const [s, o] = pair2(normalizeDimension([this, toPoint(p)]));
    if (s.ambientDimension === 2) {
      const [x1, y1, x2, y2] = [s.coordinate(0), s.coordinate(1), o.coordinate(0), o.coordinate(1)];
      const rv = exprEquals(add(mul(x1, y2), mul(-1, x2, y1)), S.Zero);
      if (rv === undefined) throw new Undecidable(`Cannot determine if ${String(s)} is a scalar multiple of ${String(o)}`);
    }
    return matrixRank([s.args, o.args], (x) => isZeroQ(x)) < 2;
  }

  /** The point with its coordinates evaluated numerically (SymPy _eval_evalf). */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    return newPoint(this.args.map(evalfArg), { evaluate: false });
  }

  // ---- static methods ------------------------------------------------------

  /**
   * The affine rank of the points: the dimension of the smallest affine
   * subspace containing them (SymPy affine_rank).
   */
  static affineRank(...args: PointInput[]): number {
    return affineRank(...args.map((a) => toPoint(a)));
  }

  /** The points lie in one plane (SymPy are_coplanar). */
  static areCoplanar(...points: PointInput[]): boolean {
    if (points.length <= 1) return true;
    const ps = normalizeDimension(points.map((a) => toPoint(a)));
    if (at(ps, 0).ambientDimension === 2) return true;
    return affineRank(...uniqPoints(ps)) <= 2;
  }

  /** The projection of the vector a on the line through the origin and b (SymPy project). */
  static project(a: PointInput, b: PointInput): PointNode {
    const [p, q] = pair2(normalizeDimension([toPoint(a), toPoint(b)]));
    if (q.isZero === true) throw new RangeError('Cannot project to the zero vector.');
    return q.mul(mul(p.dot(q), pow(q.dot(q), -1)));
  }
}

/** SymPy Point2D: a point in the plane. */
export class Point2DNode extends PointNode {
  constructor(coords: readonly Expr[]) {
    super(coords, 'Point2D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newPoint(args, { dim: 2 });
  }

  /** The x coordinate. */
  get x(): Expr {
    return at(this.args, 0);
  }
  /** The y coordinate. */
  get y(): Expr {
    return at(this.args, 1);
  }

  override get bounds(): [Expr, Expr, Expr, Expr] {
    return [this.x, this.y, this.x, this.y];
  }

  /** The point rotated counterclockwise by angle about pt (the origin by default) (SymPy rotate). */
  override rotate(angle: ExprLike, pt?: PointInput | null): Point2DNode {
    const c = cos(angle);
    const s = sin(angle);
    let rv: PointNode = this;
    let p: PointNode | undefined;
    if (pt !== undefined && pt !== null) {
      p = toPoint(pt, { dim: 2 });
      rv = rv.sub(p);
    }
    const [x, y] = [rv.coordinate(0), rv.coordinate(1)];
    rv = newPoint([add(mul(c, x), mul(-1, s, y)), add(mul(s, x), mul(c, y))]);
    if (p !== undefined) rv = rv.add(p);
    return as2D(rv);
  }

  /** The point scaled by x and y about pt (the origin by default) (SymPy scale). */
  override scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): Point2DNode {
    if (pt !== undefined && pt !== null) {
      const p = toPoint(pt, { dim: 2 });
      return as2D(this.translate(...p.neg().args).scale(x, y).translate(...p.args));
    }
    return as2D(newPoint([mul(this.x, x), mul(this.y, y)]));
  }

  /** The point transformed by a 3x3 matrix acting on the row (x, y, 1) (SymPy transform). */
  transform(matrix: Matrix): Point2DNode {
    if (!(matrix instanceof Matrix) || matrix.rows !== 3 || matrix.cols !== 3) throw new RangeError('matrix must be a 3x3 matrix');
    const r = Matrix.of([[this.x, this.y, 1]]).mul(matrix);
    return as2D(newPoint([r.get(0, 0), r.get(0, 1)]));
  }

  /** The point shifted by x and y (SymPy translate). */
  override translate(x: ExprLike = 0, y: ExprLike = 0): Point2DNode {
    return as2D(newPoint([add(this.x, x), add(this.y, y)]));
  }
}

/** SymPy Point3D: a point in three-dimensional space. */
export class Point3DNode extends PointNode {
  constructor(coords: readonly Expr[]) {
    super(coords, 'Point3D');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newPoint(args, { dim: 3 });
  }

  /** The x coordinate. */
  get x(): Expr {
    return at(this.args, 0);
  }
  /** The y coordinate. */
  get y(): Expr {
    return at(this.args, 1);
  }
  /** The z coordinate. */
  get z(): Expr {
    return at(this.args, 2);
  }

  /** The points lie on one line (SymPy Point3D.are_collinear). */
  static areCollinear(...points: PointInput[]): boolean {
    const [p, ...rest] = points.map((a) => toPoint(a));
    return p === undefined ? true : p.isCollinear(...rest);
  }

  /** The direction cosines of the line from this point to point (SymPy direction_cosine). */
  directionCosine(point: Point3DNode): Expr[] {
    const a = this.directionRatio(point);
    const b = sqrt(add(...a.map((i) => pow(i, 2))));
    return a.map((i) => mul(i, pow(b, -1)));
  }

  /** The direction ratios of the line from this point to point (SymPy direction_ratio). */
  directionRatio(point: Point3DNode): Expr[] {
    return [add(point.x, mul(-1, this.x)), add(point.y, mul(-1, this.y)), add(point.z, mul(-1, this.z))];
  }

  /** The intersection with another entity (SymPy Point3D.intersection). */
  override intersection(other: unknown): GeometryEntity[] {
    const o = other instanceof GeometryEntity ? other : toPoint(toInput(other), { dim: 3 });
    if (o instanceof Point3DNode) return o.key === this.key ? [this] : [];
    return o.intersection(this);
  }

  /** The point scaled by x, y and z about pt (the origin by default) (SymPy scale). */
  override scale(x: ExprLike = 1, y: ExprLike = 1, zOrPt?: ExprLike | PointInput | null, pt?: PointInput | null): Point3DNode {
    // SymPy scale(x=1, y=1, z=1, pt=None)
    const zIsPoint = isCoordSequence(zOrPt) || zOrPt instanceof PointNode;
    const z = zOrPt === undefined || zOrPt === null || zIsPoint ? 1 : zOrPt;
    const center = pt ?? (zIsPoint ? zOrPt : undefined);
    if (center !== undefined) {
      const p = Point3D(center);
      return as3D(this.translate(...p.neg().args).scale(x, y, z).translate(...p.args));
    }
    return as3D(newPoint([mul(this.x, x), mul(this.y, y), mul(this.z, z)]));
  }

  /** The point transformed by a 4x4 matrix acting on the column (x, y, z, 1) (SymPy transform). */
  transform(matrix: Matrix): Point3DNode {
    if (!(matrix instanceof Matrix) || matrix.rows !== 4 || matrix.cols !== 4) throw new RangeError('matrix must be a 4x4 matrix');
    const r = Matrix.of([[this.x, this.y, this.z, 1]]).mul(matrix.transpose());
    return as3D(newPoint([r.get(0, 0), r.get(0, 1), r.get(0, 2)]));
  }

  /** The point shifted by x, y and z (SymPy translate). */
  override translate(x: ExprLike = 0, y: ExprLike = 0, z: ExprLike = 0): Point3DNode {
    return as3D(newPoint([add(this.x, x), add(this.y, y), add(this.z, z)]));
  }
}

// ---------------------------------------------------------------------------
// construction
// ---------------------------------------------------------------------------

/** A sequence argument of a geometry function as point coordinates (a Tuple or an array). */
export function toInput(x: unknown): PointInput {
  if (x instanceof Expr) return x;
  if (Array.isArray(x)) return x;
  throw new TypeError(`Expecting sequence of coordinates, not \`${typeof x}\``);
}

/** SymPy Point(coords, **kwargs) for one argument (a point or a sequence of coordinates). */
export function toPoint(coords: PointInput, opts: PointOptions = {}): PointNode {
  return newPoint(coords, opts);
}

/** SymPy Point.__new__: the coordinates checked, then a Point2D, Point3D or Point. */
export function newPoint(coordsIn: PointInput, opts: PointOptions = {}): PointNode {
  let evaluate = opts.evaluate ?? true;
  const onMorph = opts.onMorph ?? 'ignore';
  if (coordsIn instanceof PointNode) {
    evaluate = false;
    if (coordsIn.args.length === (opts.dim ?? coordsIn.args.length)) return coordsIn;
  }
  if (!(coordsIn instanceof PointNode) && !isCoordSequence(coordsIn)) {
    throw new TypeError(`Expecting sequence of coordinates, not \`${coordsIn.kind}\``);
  }
  let coords: Expr[] = (coordsIn instanceof Expr ? coordsIn.args : coordsIn).map((c) => sympify(c));
  if (coords.length === 0 && opts.dim !== undefined && opts.dim > 0) coords = Array.from({ length: opts.dim }, () => S.Zero);
  const dim = opts.dim ?? coords.length;
  if (coords.length < 2) throw new RangeError('Point requires 2 or more coordinates or keyword `dim` > 1.');
  if (coords.length !== dim) {
    if (onMorph === 'error') throw new RangeError(`Dimension of (${coords.map(String).join(', ')}) needs to be changed from ${coords.length} to ${dim}.`);
  }
  if (coords.slice(dim).some((c) => c.key !== S.Zero.key)) throw new RangeError('Nonzero coordinates cannot be removed.');
  if (coords.some((a) => isNumberExpr(a) && !(a instanceof GeometryEntity) && isNonRealNumber(a))) throw new RangeError('Imaginary coordinates are not permitted.');
  if (coords.some(isNotExpr)) throw new TypeError('Coordinates must be valid SymPy expressions.');
  coords = [...coords.slice(0, dim), ...Array.from({ length: Math.max(0, dim - coords.length) }, () => S.Zero)];
  if (evaluate) {
    const floats = atoms(new TupleNode(coords), (a) => a instanceof Float);
    if (floats.length) {
      const reps = floats.map((f): [Expr, Expr] => [f, simplify(nsimplify(f, { rational: true }))]);
      coords = coords.map((c) => xreplace(c, reps));
    }
  }
  if (coords.length === 2) return new Point2DNode(coords);
  if (coords.length === 3) return new Point3DNode(coords);
  return new PointNode(coords);
}

/** The Point keywords of an options object. */
export function pointOptions(o: Record<string, unknown>): PointOptions {
  const r: { evaluate?: boolean; dim?: number; onMorph?: PointOptions['onMorph'] } = {};
  if (typeof o['evaluate'] === 'boolean') r.evaluate = o['evaluate'];
  const dim = o['dim'];
  if (typeof dim === 'number') r.dim = dim;
  else if (dim instanceof Rational) r.dim = Number(dim.p);
  const m = o['onMorph'];
  if (m === 'ignore' || m === 'warn' || m === 'error') r.onMorph = m;
  else if (m !== undefined) throw new RangeError("on_morph value should be 'error', 'warn' or 'ignore'.");
  return r;
}

/** The arguments of a Point constructor call: the coordinates (or one sequence) and the options. */
function pointCall(args: readonly unknown[]): [PointInput, PointOptions] {
  const last = args[args.length - 1];
  const opts: PointOptions = isOptions(last) ? pointOptions(last) : {};
  const rest = isOptions(last) ? args.slice(0, -1) : args;
  const coords = rest.length === 1 ? toInput(rest[0]) : toInput(rest);
  return [coords, opts];
}

const as2D = (p: PointNode): Point2DNode => cast(p, Point2DNode, 'Point2D');
const as3D = (p: PointNode): Point3DNode => cast(p, Point3DNode, 'Point3D');

/**
 * SymPy Point(*coords, evaluate=True, dim=None, on_morph='ignore'): a
 * Point2D, Point3D or Point. Coordinates are given as arguments or as one
 * sequence; a trailing options object holds the keywords.
 */
export const Point = /* @__PURE__ */ callableClass(PointNode, (...args: (ExprLike | PointInput | PointOptions)[]): PointNode => {
  const [coords, opts] = pointCall(args);
  return newPoint(coords, opts);
});
export type Point = PointNode;

/** SymPy Point2D(*coords, evaluate=True): a point in the plane. */
export const Point2D = /* @__PURE__ */ callableClass(Point2DNode, (...args: (ExprLike | PointInput | PointOptions)[]): Point2DNode => {
  const [coords, opts] = pointCall(args);
  return as2D(newPoint(coords, { ...opts, dim: 2 }));
});
export type Point2D = Point2DNode;

/** SymPy Point3D(*coords, evaluate=True): a point in space. */
export const Point3D = /* @__PURE__ */ callableClass(Point3DNode, (...args: (ExprLike | PointInput | PointOptions)[]): Point3DNode => {
  const [coords, opts] = pointCall(args);
  return as3D(newPoint(coords, { ...opts, dim: 3 }));
});
export type Point3D = Point3DNode;

geometryClasses.point = (coords, opts) => newPoint(coords, opts);

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

const pair2 = (ps: readonly PointNode[]): [PointNode, PointNode] => [at(ps, 0), at(ps, 1)];

/** The distinct points in order (SymPy uniq). */
export function uniqPoints<T extends Expr>(ps: readonly T[]): T[] {
  const seen = new Set<string>();
  return ps.filter((p) => !seen.has(p.key) && Boolean(seen.add(p.key)));
}

/**
 * SymPy Point._normalize_dimension: the points in a common dimension (the
 * largest one, or `dim`), padded with zeros.
 */
export function normalizeDimension(points: readonly PointNode[], opts: { dim?: number; onMorph?: PointOptions['onMorph'] } = {}): PointNode[] {
  const dim = opts.dim ?? Math.max(...points.map((p) => p.ambientDimension));
  if (points.every((p) => p.ambientDimension === dim)) return [...points];
  return points.map((p) => newPoint(p.args, { dim, onMorph: opts.onMorph ?? 'warn' }));
}

/**
 * SymPy Expr.equals(other): true when the difference is zero, false when it
 * is not, undefined when it cannot be decided.
 */
export function exprEquals(a: Expr, b: ExprLike): boolean | undefined {
  const d = add(a, mul(-1, b));
  if (d.key === S.Zero.key) return true;
  const s = simplify(d);
  if (s.key === S.Zero.key) return true;
  const zs = isZeroQ(s);
  if (zs !== undefined) return zs;
  if (isNumberExpr(s)) {
    try {
      const v = s.toComplex();
      return Math.hypot(v.re, v.im) < 1e-12 ? undefined : false;
    } catch {
      return undefined;
    }
  }
  // SymPy is_constant: a piecewise constant function of the symbols is not decided
  if (some(s, (e) => (e instanceof Fn || e instanceof ExtensionExpr) && PIECEWISE_CONSTANT.has(e.name))) return undefined;
  // a difference that depends on the symbols is not zero (SymPy equals of a non-constant expression)
  return false;
}

/** Functions that are constant on intervals (SymPy is_constant cannot decide them). */
const PIECEWISE_CONSTANT = new Set(['Mod', 'floor', 'ceiling', 'frac', 'sign']);

/** The zero test of affine_rank: |x| < 1e-12 for a number, else x.is_zero. */
function affineZero(x: Expr): boolean | undefined {
  if (isNumberExpr(x)) {
    try {
      const v = x.toComplex();
      return Math.hypot(v.re, v.im) < 1e-12;
    } catch {
      return isZeroQ(x);
    }
  }
  return isZeroQ(x);
}

/** SymPy Point.affine_rank. */
function affineRank(...args: PointNode[]): number {
  if (args.length === 0) return -1;
  const points = normalizeDimension(args);
  const origin = at(points, 0);
  const rows = points.slice(1).map((p) => p.sub(origin).args);
  return matrixRank(rows, affineZero);
}

/** SymPy _find_reasonable_pivot: the first entry that is not zero (simplifying undecided ones). */
function reasonablePivot(col: readonly Expr[], iszero: (x: Expr) => boolean | undefined): number {
  const zs = col.map(iszero);
  const sure = zs.indexOf(false);
  if (sure >= 0) return sure;
  for (let i = 0; i < col.length; i++) {
    if (zs[i] !== undefined) continue;
    const z = iszero(simplify(at(col, i)));
    if (z === false) return i;
    zs[i] = z;
  }
  for (let i = 0; i < col.length; i++) if (zs[i] === undefined && exprEquals(at(col, i), S.Zero) === true) zs[i] = true;
  return zs.indexOf(undefined);
}

/** SymPy Matrix.rank(iszerofunc) of the matrix with the given rows. */
export function matrixRank(rowsIn: readonly (readonly Expr[])[], iszero: (x: Expr) => boolean | undefined): number {
  const nr = rowsIn.length;
  const nc = nr ? at(rowsIn, 0).length : 0;
  if (nr === 0 || nc === 0) return 0;
  const all = rowsIn.flat();
  if ((nr <= 1 || nc <= 1) && all.some((x) => iszero(x) === false)) return 1;
  if (nr === 2 && nc === 2) {
    const zs = all.map(iszero);
    if (zs.every((z) => z === true)) return 0;
    const [r0, r1] = [at(rowsIn, 0), at(rowsIn, 1)];
    const det = add(mul(at(r0, 0), at(r1, 1)), mul(-1, at(r0, 1), at(r1, 0)));
    const zd = iszero(det);
    if (zd === true && zs.includes(false)) return 1;
    if (zd === false) return 2;
  }
  // SymPy _permute_complexity_right: columns with undecided entries go to the right
  const order = Array.from({ length: nc }, (_, j) => j).sort(
    (i, j) => Number(rowsIn.some((r) => iszero(at(r, i)) === undefined)) - Number(rowsIn.some((r) => iszero(at(r, j)) === undefined)) || i - j,
  );
  const m = rowsIn.map((r) => order.map((j) => at(r, j)));
  let pivots = 0;
  let row = 0;
  for (let c = 0; c < nc && row < nr; c++) {
    const col = m.slice(row).map((r) => at(r, c));
    const k = reasonablePivot(col, iszero);
    if (k < 0) continue;
    const p = row + k;
    [m[row], m[p]] = [at(m, p), at(m, row)];
    const pr = at(m, row);
    const pv = at(pr, c);
    for (let i = row + 1; i < nr; i++) {
      const ri = at(m, i);
      const f = at(ri, c);
      m[i] = ri.map((v, j) => add(mul(pv, v), mul(-1, f, at(pr, j))));
    }
    pivots++;
    row++;
  }
  return pivots;
}
