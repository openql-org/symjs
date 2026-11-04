// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/plane.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.plane: planes in three-dimensional space,
 * given by a point and a normal vector or by three points.
 */

import { Dummy, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { subs, xreplace } from '../core/traverse';
import { isConstant } from '../core/methods';
import { callableClass } from '../core/callable';
import { isZero as isZeroQ } from '../core/assumptions';
import { ExprMap } from '../core/exprmap';
import { at, cast, defined, expectType } from '../core/guard';
import { TupleNode } from '../core/containers';
import { abs, acos, asin, cos, sin } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
import { cross } from '../matrices/linalg';
import { cancel } from '../simplify/rational';
import { linsolve } from '../matrices/linsys';
import { Random } from '../ntheory/random';
import { GeometryEntity, realSymbol } from './entity';
import type { PointInput } from './entity';
import { Point3DNode, PointNode, exprEquals, isOptions, newPoint, toInput, toPoint } from './point';
import type { Line3DNode} from './line';
import { Line3D, LineNode, LinearEntity, Ray3D, RayNode, Segment3D, Segment3DNode, SegmentNode, planeHook } from './line';
import { rationalOf, utilClasses } from './util';
import { solveEquations } from './solvehelp';

const [px, py, pz, pt] = [new Dummy('plane_dummy'), new Dummy('plane_dummy'), new Dummy('plane_dummy'), new Dummy('plane_dummy')];

/** Options of Plane (SymPy normal_vector and evaluate). */
export interface PlaneOptions {
  /** The normal vector (instead of two more points). */
  normalVector?: PointInput;
  /** Convert Floats of the normal vector to Rationals (default true). */
  evaluate?: boolean;
}

const as3D = (e: Expr): Point3DNode => cast(e, Point3DNode, 'Point3D');

/** SymPy Plane: a plane through p1 with a normal vector. */
export class PlaneNode extends GeometryEntity {
  constructor(p1: Point3DNode, normal: TupleNode) {
    super('Plane', [p1, normal]);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newPlane(at(args, 0), undefined, undefined, { normalVector: at(args, 1) });
  }

  /** The point defining the plane (SymPy p1). */
  get p1(): Point3DNode {
    return as3D(at(this.args, 0));
  }

  /** The normal vector as a Tuple (SymPy normal_vector). */
  get normalVector(): TupleNode {
    return cast(at(this.args, 1), TupleNode, 'normal vector');
  }

  get ambientDimension(): number {
    return this.p1.ambientDimension;
  }

  /** SymPy `o in plane`: the point or linear entity lies in the plane. */
  override contains(o: unknown): boolean {
    const k = this.equation(px, py, pz);
    if (o instanceof LinearEntity) {
      const d = toPoint(o.arbitraryPoint(pt), { dim: 3 });
      const e = subs(k, [
        [px, d.coordinate(0)],
        [py, d.coordinate(1)],
        [pz, d.coordinate(2)],
      ]);
      return exprEquals(e, 0) === true;
    }
    let p: PointNode;
    try {
      if (o instanceof GeometryEntity && !(o instanceof PointNode)) return false;
      p = toPoint(toInput(o), { dim: 3 });
    } catch {
      // not a point (SymPy catches the TypeError of Point(o, dim=3, strict=True))
      return false;
    }
    const d = xreplace(k, [
      [px, p.coordinate(0)],
      [py, p.coordinate(1)],
      [pz, p.coordinate(2)],
    ]);
    return exprEquals(d, 0) === true;
  }

  /** The point and normal vector evaluated numerically (SymPy _eval_evalf). */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    return newPlane(evalfArg(this.p1), undefined, undefined, { normalVector: this.normalVector.args.map(evalfArg), evaluate: false });
  }

  /** The angle with a 3D linear entity or another plane (SymPy angle_between). */
  angleBetween(o: GeometryEntity): Expr {
    const nv = this.normalVector.args;
    const norm = (v: readonly Expr[]): Expr => sqrt(add(...v.map((i) => pow(i, 2))));
    const dotv = (a: readonly Expr[], b: readonly Expr[]): Expr => add(...a.map((ai, i) => mul(ai, at(b, i))));
    if (isLinear3D(o)) {
      const dr = directionRatioOf(o);
      return asin(mul(dotv(nv, dr), pow(mul(norm(nv), norm(dr)), -1)));
    }
    if (o instanceof PlaneNode) {
      const on = o.normalVector.args;
      return acos(mul(dotv(nv, on), pow(mul(norm(nv), norm(on)), -1)));
    }
    throw new TypeError(`angle between a Plane and ${o.name} is not defined`);
  }

  /**
   * A point of the plane: on the circle of radius 1 about p1 as a function
   * of the angle u, or p1 + u*a + v*b with two parameters (SymPy arbitrary_point).
   */
  override arbitraryPoint(u?: string | Sym | null, v?: string | Sym | null): Point3DNode {
    const circle = v === undefined || v === null;
    const U = realSymbol(u ?? (circle ? 't' : 'u'));
    const [x, y, z] = this.normalVector.args.map((c) => c);
    const [a, b, c] = this.p1.args;
    const X = defd(x);
    const Y = defd(y);
    let [x1, y1, z1]: Expr[] = isZeroQ(X) === true && isZeroQ(Y) === true ? [S.One, S.Zero, S.Zero] : [mul(-1, Y), X, S.Zero];
    let [x2, y2, z2] = cross(Matrix.col(X, Y, defd(z)), Matrix.col(defd(x1), defd(y1), defd(z1))).data;
    if (circle) {
      const n1 = sqrt(add(pow(defd(x1), 2), pow(defd(y1), 2), pow(defd(z1), 2)));
      [x1, y1, z1] = [x1, y1, z1].map((w) => mul(defd(w), pow(n1, -1)));
      const n2 = sqrt(add(pow(defd(x2), 2), pow(defd(y2), 2), pow(defd(z2), 2)));
      [x2, y2, z2] = [x2, y2, z2].map((w) => mul(defd(w), pow(n2, -1)));
      return as3D(
        newPoint([
          add(defd(a), mul(defd(x1), cos(U)), mul(defd(x2), sin(U))),
          add(defd(b), mul(defd(y1), cos(U)), mul(defd(y2), sin(U))),
          add(defd(c), mul(defd(z1), cos(U)), mul(defd(z2), sin(U))),
        ]),
      );
    }
    const V = realSymbol(v);
    return as3D(
      newPoint([
        add(defd(a), mul(defd(x1), U), mul(defd(x2), V)),
        add(defd(b), mul(defd(y1), U), mul(defd(y2), V)),
        add(defd(c), mul(defd(z1), U), mul(defd(z2), V)),
      ]),
    );
  }

  /** The planes have a line in common (SymPy are_concurrent). */
  static areConcurrent(...planesIn: PlaneNode[]): boolean {
    const seen = new Set<string>();
    const planes = planesIn.filter((p) => !seen.has(p.key) && Boolean(seen.add(p.key)));
    for (const i of planes) if (!(i instanceof PlaneNode)) throw new RangeError(`All objects should be Planes but got ${String(i)}`);
    if (planes.length < 2) return false;
    const [first, ...rest] = planes;
    const f = defd(first);
    const sol = f.intersection(at(rest, 0));
    const line = sol[0];
    if (line === undefined) return false;
    for (const i of rest.slice(1)) {
      const l = f.intersection(i);
      const l0 = l[0];
      if (l0 === undefined || !line.contains(l0)) return false;
    }
    return true;
  }

  /** The shortest distance to a point, linear entity or plane (SymPy distance). */
  override distance(oIn: unknown): Expr {
    const o = oIn instanceof GeometryEntity ? oIn : toPoint(toInput(oIn), { dim: 3 });
    if (this.intersection(o).length) return S.Zero;
    if (o instanceof Segment3DNode || (o instanceof RayNode && o.name === 'Ray3D')) {
      const [a, b] = [o.p1, o.p2];
      // the plane does not meet o (checked above), so the nearer end point is the closest one
      const pi = at(this.intersection(Line3D(a, b)), 0);
      if (Segment3D(pi, b).contains(a)) return this.distance(a);
      return this.distance(b);
    }
    const a = o instanceof PointNode ? o : o instanceof PlaneNode ? o.p1 : cast(o, LinearEntity, 'linear entity').p1;
    const n = toPoint(this.normalVector, { dim: 3 }).unit;
    const d = a.sub(this.p1).dot(n);
    return abs(d);
  }

  /** The planes are the same (SymPy equals). */
  override equals(o: ExprLike): boolean {
    if (!(o instanceof PlaneNode)) return false;
    return isConstant(cancel(mul(this.equation(), pow(o.equation(), -1))));
  }

  /** The equation of the plane in real symbols x, y and z (SymPy equation). */
  equation(x?: Sym | string, y?: Sym | string, z?: Sym | string): Expr {
    const [X, Y, Z] = [x, y, z].map((s, i) => (s === undefined ? new Sym(at('xyz', i), { real: true }) : realSymbol(s)));
    const a = newPoint([defd(X), defd(Y), defd(Z)]);
    const b = this.p1.directionRatio(as3D(a));
    return add(...b.map((bi, i) => mul(bi, at(this.normalVector.args, i))));
  }

  /** The entities this plane has in common with o (SymPy intersection). */
  override intersection(oIn: unknown): GeometryEntity[] {
    const o0 = oIn instanceof GeometryEntity ? oIn : toPoint(toInput(oIn), { dim: 3 });
    if (o0 instanceof PointNode) return this.contains(o0) ? [o0] : [];
    if (o0 instanceof LinearEntity) {
      const [p1, p2] = [o0.p1, o0.p2];
      let o: LinearEntity;
      if (o0 instanceof SegmentNode) o = asLinear(Segment3D(p1, p2));
      else if (o0 instanceof RayNode) o = Ray3D(p1, p2);
      else o = Line3D(p1, p2);
      if (this.contains(o)) return [o];
      const a = toPoint(o.arbitraryPoint(pt), { dim: 3 });
      const n = toPoint(this.normalVector, { dim: 3 });
      // the equation is linear in the parameter: no solution (parallel) or one, which is real for real
      // coordinates (SymPy's Undecidable for several or non-real roots cannot occur)
      const c = solveEquations([a.sub(this.p1).dot(n)], [pt]);
      const c0 = c[0];
      if (c0 === undefined) return [];
      const p = subs(a, [[pt, at(c0, 0)]]);
      if (!o.contains(p)) return [];
      return [asPoint(p)];
    }
    if (o0 instanceof PlaneNode) {
      if (this.equals(o0)) return [this];
      if (this.isParallel(o0)) return [];
      const [x, y, z] = [new Dummy('x'), new Dummy('y'), new Dummy('z')];
      const c = cross(Matrix.row(...this.normalVector.args), Matrix.row(...o0.normalVector.args)).data;
      const d = this.equation(x, y, z);
      const e = o0.equation(x, y, z);
      // the planes are not parallel: the system has solutions
      const sol = expectType(linsolve([d, e], [x, y, z]), (v): v is Expr[] => Array.isArray(v), 'solution');
      const result = sol.map((r) => subs(subs(subs(r, [[x, 0]]), [[y, 0]]), [[z, 0]]));
      return [Line3D(result, { directionRatio: c })];
    }
    throw new TypeError(`intersection of a Plane and ${o0.name} is not defined`);
  }

  /** The entity lies in the plane (SymPy is_coplanar). */
  isCoplanar(o: GeometryEntity): boolean {
    if (o instanceof PlaneNode) {
      const r = cancel(mul(this.equation(px, py, pz), pow(o.equation(px, py, pz), -1)));
      return !(r.has(px) || r.has(py) || r.has(pz));
    }
    if (o instanceof Point3DNode) return this.contains(o);
    if (isLinear3D(o)) return this.contains(o);
    return this.normalVector.args.slice(0, 2).every((i) => i.key === S.Zero.key);
  }

  /** The plane and the 3D linear entity or plane are parallel (SymPy is_parallel). */
  isParallel(l: GeometryEntity): boolean {
    if (isLinear3D(l)) {
      const a = directionRatioOf(l);
      const b = this.normalVector.args;
      return add(...a.map((ai, i) => mul(ai, at(b, i)))).key === S.Zero.key;
    }
    if (l instanceof PlaneNode) {
      const c = cross(Matrix.col(...l.normalVector.args), Matrix.col(...this.normalVector.args));
      return c.data.every((e) => isZeroQ(e) === true);
    }
    return false;
  }

  /** The plane and the 3D linear entity or plane are perpendicular (SymPy is_perpendicular). */
  isPerpendicular(l: GeometryEntity): boolean {
    if (isLinear3D(l)) {
      const c = cross(Matrix.col(...directionRatioOf(l)), Matrix.col(...this.normalVector.args));
      return c.data.every((e) => isZeroQ(e) === true);
    }
    if (l instanceof PlaneNode) {
      const d = add(...l.normalVector.args.map((ai, i) => mul(ai, at(this.normalVector.args, i))));
      return d.key === S.Zero.key;
    }
    return false;
  }

  /** The parallel plane through pt (SymPy parallel_plane). */
  parallelPlane(p: PointInput): PlaneNode {
    return newPlane(p, undefined, undefined, { normalVector: this.normalVector });
  }

  /** The line through pt perpendicular to the plane (SymPy perpendicular_line). */
  perpendicularLine(p: PointInput): Line3DNode {
    return Line3D(p, { directionRatio: this.normalVector.args });
  }

  /** A plane through the given points (at most two) perpendicular to this one (SymPy perpendicular_plane). */
  perpendicularPlane(...ptsIn: PointInput[]): PlaneNode {
    if (ptsIn.length > 2) throw new RangeError('No more than 2 pts should be provided.');
    const pts: PointInput[] = [...ptsIn];
    const [x, y] = this.normalVector.args;
    const zeroXY = defd(x).key === S.Zero.key && defd(y).key === S.Zero.key;
    if (pts.length === 0) pts.push(this.p1);
    if (pts.length === 1) pts.push(toPoint(at(pts, 0), { dim: 3 }).add(zeroXY ? [0, 1, 0] : [0, 0, 1]));
    const [p1, p2] = pts.map((i) => toPoint(i, { dim: 3 }));
    const l = Line3D(defd(p1), defd(p2));
    const n = Line3D(defd(p1), { directionRatio: this.normalVector.args });
    let p3: PointNode;
    if (n.contains(l)) {
      p3 = toPoint(zeroXY ? [0, 1, 0] : [0, 0, 1]);
      if (l.contains(p3)) p3 = p3.mul(2);
    } else p3 = defd(p1).add(this.normalVector.args);
    return newPlane(defd(p1), defd(p2), p3);
  }

  /** The projection of a linear entity onto the plane: a point, or a 3D line, ray or segment (SymPy projection_line). */
  projectionLine(line: GeometryEntity): GeometryEntity {
    if (!(line instanceof LinearEntity)) throw new TypeError('Enter a linear entity only');
    const [a, b] = [this.projection(line.p1), this.projection(line.p2)];
    if (a.key === b.key) return a;
    if (line instanceof LineNode) return Line3D(a, b);
    if (line instanceof RayNode) return Ray3D(a, b);
    return Segment3D(a, b);
  }

  /** The orthogonal projection of a point onto the plane (SymPy projection). */
  projection(p: PointInput): Point3DNode {
    const rv = toPoint(p, { dim: 3 });
    if (this.contains(rv)) return as3D(rv);
    return as3D(at(this.intersection(Line3D(rv, rv.add(this.normalVector.args))), 0));
  }

  /** A random point of the plane; the same for the same integer seed (SymPy random_point). */
  randomPoint(seed?: number | bigint): Point3DNode {
    const rng = seed === undefined ? sharedRandom : new Random(seed);
    const a = add(mul(2, rationalOf(rng.gauss(0, 1))), -1);
    const b = add(mul(2, rationalOf(rng.gauss(0, 1))), -1);
    return as3D(subs(this.arbitraryPoint(px, py), [
      [px, a],
      [py, b],
    ]));
  }

  /**
   * The parameter values of the arbitrary point at the given point: {u: angle}
   * for one parameter, {u, v} for two (SymPy parameter_value).
   */
  override parameterValue(otherIn: PointInput, u: Expr, v?: ExprLike): ExprMap<Expr> | PointNode {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(otherIn, { dim: this.ambientDimension });
    if (!(other instanceof PointNode)) throw new RangeError('other must be a point');
    // SymPy returns the point itself for p1 (where the parameter is not defined)
    if (other.key === this.p1.key) return other;
    let sol: Expr[][];
    let syms: Sym[];
    if (u instanceof Sym && v === undefined) {
      const delta = this.arbitraryPoint(u).sub(this.p1);
      const eq = delta.sub(other.sub(this.p1).unit);
      syms = [u];
      sol = solveEquations(eq.args, syms);
    } else if (u instanceof Sym && v instanceof Sym) {
      const p = this.arbitraryPoint(u, v);
      syms = [u, v];
      sol = solveEquations(p.sub(other).args, syms);
    } else throw new RangeError('expecting 1 or 2 symbols');
    const s0 = sol[0];
    if (s0 === undefined) throw new RangeError('Given point is not on Plane');
    return new ExprMap(syms.map((s, i): [Expr, Expr] => [s, at(s0, i)]));
  }
}

const sharedRandom = new Random();

const defd = <T>(e: T | undefined): T => defined(e, 'coordinate');
const asPoint = (e: Expr): PointNode => cast(e, PointNode, 'Point');
const asLinear = (e: Expr): LinearEntity => cast(e, LinearEntity, 'linear entity');

const isLinear3D = (e: GeometryEntity): e is LinearEntity => e instanceof LinearEntity && e.ambientDimension === 3 && /3D$/.test(e.name);
const directionRatioOf = (l: LinearEntity): Expr[] => as3D(l.p1).directionRatio(as3D(l.p2));

/** SymPy Plane.__new__(p1, a=None, b=None, normal_vector=...). */
function newPlane(p1In: PointInput, a: PointInput | undefined, b: PointInput | undefined, opts: PlaneOptions = {}): PlaneNode {
  const p1 = as3D(toPoint(p1In, { dim: 3 }));
  let normal: Expr[];
  if (a !== undefined && b !== undefined) {
    const p2 = toPoint(a, { dim: 3 });
    const p3 = toPoint(b, { dim: 3 });
    if (Point3DNode.areCollinear(p1, p2, p3)) throw new RangeError('Enter three non-collinear points');
    const da = p1.directionRatio(as3D(p2));
    const db = p1.directionRatio(as3D(p3));
    normal = cross(Matrix.col(...da), Matrix.col(...db)).data.slice();
  } else {
    const nv = opts.normalVector ?? a;
    const evaluate = opts.evaluate ?? true;
    const seq = nv instanceof TupleNode || nv instanceof PointNode ? nv.args : Array.isArray(nv) ? nv.map(sympify) : undefined;
    if (seq?.length !== 3) {
      throw new RangeError('Either provide 3 3D points or a point with a normal vector expressed as a sequence of length 3');
    }
    normal = evaluate ? toPoint(seq, { dim: 3 }).args.slice() : [...seq];
    if (normal.every((c) => isZeroQ(c) === true)) throw new RangeError('Normal vector cannot be zero vector');
  }
  return new PlaneNode(p1, new TupleNode(normal));
}

type PlaneArg = PointInput | PlaneOptions;

/**
 * SymPy Plane(p1, p2, p3) or Plane(p1, {normalVector}): the plane through
 * three points, or through p1 with the given normal vector.
 */
export const Plane = /* @__PURE__ */ callableClass(PlaneNode, (...args: PlaneArg[]): PlaneNode => {
  const last = args[args.length - 1];
  const opts = isOptions(last) ? readPlaneOptions(last) : {};
  const pos = isOptions(last) ? args.slice(0, -1) : args;
  const [p1, a, b] = pos.map((x) => toInput(x));
  if (p1 === undefined) throw new TypeError('Plane requires a point');
  return newPlane(p1, a, b, opts);
});
export type Plane = PlaneNode;

function readPlaneOptions(o: Record<string, unknown>): PlaneOptions {
  const r: { normalVector?: PointInput; evaluate?: boolean } = {};
  const nv = o['normalVector'];
  if (nv !== undefined) r.normalVector = toInput(nv);
  if (typeof o['evaluate'] === 'boolean') r.evaluate = o['evaluate'];
  return r;
}

planeHook.make = (p1, normal) => newPlane(p1, undefined, undefined, { normalVector: [...normal] });
utilClasses.plane = (p1, p2, p3) => newPlane(p1, p2, p3);

