// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/ellipse.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.ellipse: ellipses with axes parallel to the
 * coordinate axes, and circles.
 *
 * Ellipse(center, hradius, vradius) gives a Circle when the radii are equal
 * and a Segment when one of them is zero.
 */

import { Dummy, Expr, Rational, Rel, S, Special, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { Lt } from '../core/logic';
import { subs } from '../core/traverse';
import { asNumerDenom } from '../core/methods';
import { ordered } from '../core/match';
import { callableClass } from '../core/callable';
import { isIntegerQ, isNegative, isPositive, isReal } from '../core/assumptions';
import { at, cast, defined } from '../core/guard';
import { abs, cos, sin } from '../functions/elementary/elementary';
import { Max } from '../functions/special/special';
import { ellipticE } from '../functions/special/ellipticintegrals';
import { Poly } from '../polys/sympoly';
import { expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';
import { trigsimp } from '../simplify/trigsimp';
import { solve } from '../solvers/solve';
import { NotImplementedError } from '../core/errors';
import { Random } from '../ntheory/random';
import { GeometryEntity, GeometrySet, decide, realSymbol } from './entity';
import type { PointInput } from './entity';
import { GeometryError } from './exceptions';
import { Point2DNode, PointNode, isOptions, newPoint, toInput, toPoint } from './point';
import { Line, Line2DNode, LinearEntity, Ray2DNode, Segment, Segment2DNode } from './line';
import { find, idiff, rationalOf } from './util';
import { isNonRealNumber, solveEquations } from './solvehelp';

const ex = new Dummy('ellipse_dummy', { real: true });
const ey = new Dummy('ellipse_dummy', { real: true });

/** Python `a == b` of two expressions: structural equality. */
const same = (a: Expr, b: ExprLike): boolean => a.key === sympify(b).key;

/** The comparison when it is decided (SymPy `o == True` / `o == False`), else undefined. */
const decided = (r: Expr): boolean | undefined => (r instanceof Rel ? undefined : decide(r));

const as2D = (e: Expr): Point2DNode => cast(e, Point2DNode, 'Point2DNode');

/**
 * The circumcircle of three points as [center, radius], or the Segment or
 * Point their Triangle degenerates to; registered by geometry/polygon.
 */
export const ellipseHooks: {
  circumcircle?: (a: PointNode, b: PointNode, c: PointNode) => GeometryEntity | [PointNode, Expr];
} = {};

/** Options of Ellipse (SymPy keyword arguments). */
export interface EllipseOptions {
  /** The horizontal radius. */
  hradius?: ExprLike;
  /** The vertical radius. */
  vradius?: ExprLike;
  /** The eccentricity, with one of the radii. */
  eccentricity?: ExprLike;
}

/** SymPy Ellipse: an ellipse with axes parallel to the coordinate axes. */
export class EllipseNode extends GeometrySet {
  constructor(args: readonly Expr[], name = 'Ellipse') {
    super(name, args);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newEllipse(at(args, 0), at(args, 1), at(args, 2));
  }

  get ambientDimension(): number {
    return 2;
  }

  /** The center (SymPy center). */
  get center(): Point2DNode {
    return as2D(at(this.args, 0));
  }
  /** The horizontal radius (SymPy hradius). */
  get hradius(): Expr {
    return at(this.args, 1);
  }
  /** The vertical radius (SymPy vradius). */
  get vradius(): Expr {
    return at(this.args, 2);
  }

  /** SymPy `o in ellipse`: a point on the ellipse, or the same ellipse. */
  override contains(o: unknown): boolean {
    if (o instanceof PointNode) {
      const res = subs(this.equation(ex, ey), [
        [ex, o.coordinate(0)],
        [ey, o.coordinate(1)],
      ]);
      return trigsimp(simplify(res)).key === S.Zero.key;
    }
    if (o instanceof EllipseNode) return o.key === this.key;
    return false;
  }

  /** The greatest distance from a focus to the ellipse (SymPy apoapsis). */
  get apoapsis(): Expr {
    return mul(this.major, add(1, this.eccentricity));
  }

  /** The point (cx + hradius*cos(t), cy + vradius*sin(t)) with a real parameter t (SymPy arbitrary_point). */
  override arbitraryPoint(parameter: string | Sym | null = 't'): Point2DNode {
    const t = realSymbol(parameter ?? 't');
    if ([...this.freeSymbols()].some((f) => f.name === t.name)) {
      throw new RangeError(`Symbol ${t.name} already appears in object and cannot be used as a parameter.`);
    }
    return as2D(newPoint([add(this.center.x, mul(this.hradius, cos(t))), add(this.center.y, mul(this.vradius, sin(t)))]));
  }

  /** The area pi*hradius*vradius (SymPy area). */
  get area(): Expr {
    return simplify(mul(S.Pi, this.hradius, this.vradius));
  }

  override get bounds(): [Expr, Expr, Expr, Expr] {
    const [h, v] = [this.hradius, this.vradius];
    const { x, y } = this.center;
    return [add(x, mul(-1, h)), add(y, mul(-1, v)), add(x, h), add(y, v)];
  }

  /** The perimeter (SymPy circumference). */
  get circumference(): Expr {
    // (SymPy's cases e == 1 and e == 0 are a Segment and a Circle, never an Ellipse)
    return mul(4, this.major, ellipticE(pow(this.eccentricity, 2)));
  }

  /** The eccentricity (SymPy eccentricity). */
  get eccentricity(): Expr {
    return mul(this.focusDistance, pow(this.major, -1));
  }

  /** The point lies inside the ellipse (SymPy encloses_point; 'unknown' when undecided). */
  override enclosesPoint(pIn: PointInput): boolean | 'unknown' {
    const p = toPoint(pIn, { dim: 2 });
    if (this.contains(p)) return false;
    const [f1, f2] = this.foci;
    const test = add(mul(2, this.major), mul(-1, add(f1.distance(p), f2.distance(p))));
    return isPositive(test) ?? 'unknown';
  }

  /** The equation of the ellipse in real symbols x and y (SymPy equation). */
  equation(x: string | Sym = 'x', y: string | Sym = 'y', slope?: ExprLike): Expr {
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const dx = add(X, mul(-1, this.center.x));
    const dy = add(Y, mul(-1, this.center.y));
    if (slope !== undefined) {
      const s = sympify(slope);
      const L = pow(add(dy, mul(-1, s, dx)), 2);
      const l = pow(add(mul(s, dy), dx), 2);
      const h = add(1, pow(s, 2));
      const b = mul(h, pow(this.major, 2));
      const a = mul(h, pow(this.minor, 2));
      return add(mul(l, pow(b, -1)), mul(L, pow(a, -1)), -1);
    }
    const t1 = pow(mul(dx, pow(this.hradius, -1)), 2);
    const t2 = pow(mul(dy, pow(this.vradius, -1)), 2);
    return add(t1, t2, -1);
  }

  /** The evolute of the ellipse (SymPy evolute). */
  evolute(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    if (this.args.length !== 3) throw new NotImplementedError('Evolute of arbitrary Ellipse is not supported.');
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const twoThirds = Rational.of(2n, 3n);
    const t1 = pow(mul(this.hradius, add(X, mul(-1, this.center.x))), twoThirds);
    const t2 = pow(mul(this.vradius, add(Y, mul(-1, this.center.y))), twoThirds);
    return add(t1, t2, mul(-1, pow(add(pow(this.hradius, 2), mul(-1, pow(this.vradius, 2))), twoThirds)));
  }

  /** The two foci (SymPy foci). */
  get foci(): [PointNode, PointNode] {
    const c = this.center;
    const [hr, vr] = [this.hradius, this.vradius];
    if (same(hr, vr)) return [c, c];
    const fd = sqrt(add(pow(this.major, 2), mul(-1, pow(this.minor, 2))));
    if (same(hr, this.minor)) return [c.add([0, mul(-1, fd)]), c.add([0, fd])];
    // hradius is the major radius (major gives the hradius when the order cannot be decided)
    return [c.add([mul(-1, fd), 0]), c.add([fd, 0])];
  }

  /** The distance from the center to a focus (SymPy focus_distance). */
  get focusDistance(): Expr {
    return this.center.distance(this.foci[0]);
  }

  /** The points or entities common to the ellipse and o (SymPy intersection). */
  override intersection(o: unknown): GeometryEntity[] {
    if (o instanceof PointNode) return this.contains(o) ? [o] : [];
    if (o instanceof Segment2DNode || o instanceof Ray2DNode) {
      const eq = this.equation(ex, ey);
      const leq = as2DLine(Line(o.p1, o.p2)).equation(ex, ey);
      const sols = solveEquations([eq, leq], [ex, ey]).map((s) => toPoint(s));
      return sortedPoints(sols.filter((p) => o.contains(p)));
    }
    if (o instanceof EllipseNode || o instanceof Line2DNode) {
      if (o.key === this.key) return [this];
      const sols = solveEquations([this.equation(ex, ey), o.equation(ex, ey)], [ex, ey]);
      return sortedPoints(sols.map((s) => toPoint(s)));
    }
    if (o instanceof LinearEntity && o.ambientDimension === 3) throw new TypeError('Entity must be two dimensional, not three dimensional');
    if (o instanceof GeometryEntity && (o.name === 'Polygon' || o.name === 'Triangle' || o.name === 'RegularPolygon')) return o.intersection(this);
    throw new TypeError(`Intersection not handled for ${o instanceof GeometryEntity ? o.name : typeof o}`);
  }

  /** The entity is tangent to the ellipse (SymPy is_tangent). */
  isTangent(o: GeometryEntity): boolean {
    if (o instanceof Point2DNode) return false;
    if (o instanceof EllipseNode) {
      const intersect = this.intersection(o);
      if (intersect.length === 1 && at(intersect, 0) instanceof EllipseNode) return true;
      if (intersect.length) {
        return intersect.every((i) => {
          const a = at(this.tangentLines(i), 0);
          return a.equals(at(o.tangentLines(i), 0));
        });
      }
      return false;
    }
    if (o instanceof Line2DNode) {
      const hit = this.intersection(o);
      if (hit.length === 0) return false;
      if (hit.length === 1) return true;
      return at(hit, 0).equals(at(hit, 1));
    }
    if (o instanceof Segment2DNode || o instanceof Ray2DNode) {
      const intersect = this.intersection(o);
      if (intersect.length === 1) return at(this.tangentLines(at(intersect, 0)), 0).contains(o);
      return false;
    }
    if (hasSides(o)) return o.sides.every((s) => this.isTangent(s));
    if (o.ambientDimension === 3) throw new TypeError('Entity must be two dimensional, not three dimensional');
    throw new TypeError(`Is_tangent not handled for ${o.name}`);
  }

  /** The major radius (SymPy major; the hradius when the order cannot be decided). */
  get major(): Expr {
    const [a, b] = [this.hradius, at(this.args, 2)];
    const o = decided(Lt(add(b, mul(-1, a)), 0));
    if (o === true) return a;
    if (o === false) return b;
    return this.hradius;
  }

  /** The minor radius (SymPy minor; the vradius when the order cannot be decided). */
  get minor(): Expr {
    const [a, b] = [this.hradius, at(this.args, 2)];
    const o = decided(Lt(add(a, mul(-1, b)), 0));
    if (o === true) return a;
    if (o === false) return b;
    return this.vradius;
  }

  /**
   * The lines through p normal to the ellipse; with `prec`, the points
   * and slopes evaluated to that many digits (SymPy normal_lines).
   */
  normalLines(pIn: PointInput, prec?: number): Line2DNode[] {
    const p = toPoint(pIn, { dim: 2 });
    const rv: Line2DNode[] = [];
    if (same(p.coordinate(0), this.center.x)) rv.push(as2DLine(Line(this.center, { slope: S.Infinity })));
    if (same(p.coordinate(1), this.center.y)) rv.push(as2DLine(Line(this.center, { slope: 0 })));
    if (rv.length) return rv;
    const eq = this.equation(ex, ey);
    const dydx = idiff(eq, ey, ex);
    const norm = mul(-1, pow(dydx, -1));
    const slope = as2DLine(Line(p, [ex, ey])).slope;
    const seq = add(slope, mul(-1, norm));
    const yis = at(solve(seq, ey), 0);
    const xeq = expand(asNumerDenom(subs(eq, [[ey, yis]]))[0]);
    if (xeq.freeSymbols().size !== 1) throw new NotImplementedError('intersections for the general ellipse are not supported');
    // (SymPy falls back to solve when real_roots fails; symjs's real roots handle the coefficients
    // the ellipse gives, as CRootOf when needed)
    const xsol = Poly.from(xeq, [ex]).realRoots();
    let points = xsol.map((i) => toPoint([i, at(solve(subs(eq, [[ex, i]]), ey), 0)]));
    let slopes = points.map((pt) => subs(norm, [
      [ex, pt.coordinate(0)],
      [ey, pt.coordinate(1)],
    ]));
    if (prec !== undefined) {
      // (a normal through p is not vertical: p is not on the vertical axis, so no slope is infinite)
      points = points.map((pt) => toPoint(pt.evalf(prec)));
      slopes = slopes.map((i) => i.evalf(prec));
    }
    return points.map((pt, i) => as2DLine(Line(pt, { slope: at(slopes, i) })));
  }

  /** The least distance from a focus to the ellipse (SymPy periapsis). */
  get periapsis(): Expr {
    return mul(this.major, add(1, mul(-1, this.eccentricity)));
  }

  /** The semi-latus rectum (SymPy semilatus_rectum). */
  get semilatusRectum(): Expr {
    return mul(this.major, add(1, mul(-1, pow(this.eccentricity, 2))));
  }

  /** The circle with the larger radius as its radius (SymPy auxiliary_circle). */
  auxiliaryCircle(): GeometryEntity {
    return newCircle(this.center, Max(this.hradius, this.vradius));
  }

  /** The circle of the points from which two perpendicular tangents can be drawn (SymPy director_circle). */
  directorCircle(): GeometryEntity {
    return newCircle(this.center, sqrt(add(pow(this.hradius, 2), pow(this.vradius, 2))));
  }

  /** The parameter interval of the arbitrary point used for plotting (SymPy plot_interval). */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), mul(-1, S.Pi), S.Pi];
  }

  /** A random point of the ellipse; the same for the same integer seed (SymPy random_point). */
  randomPoint(seed?: number | bigint): PointNode {
    const t = realSymbol('t');
    const [x, y] = this.arbitraryPoint(t).args;
    const rng = seed === undefined ? sharedRandom : new Random(seed);
    const r = rationalOf(rng.random());
    const c = add(mul(2, r), -1);
    const s = sqrt(add(1, mul(-1, pow(c, 2))));
    return toPoint([subs(defd(x), [[cos(t), c]]), subs(defd(y), [[sin(t), s]])]);
  }

  /** The reflection in a horizontal or vertical line (SymPy reflect). */
  override reflect(line: Line2DNode): GeometryEntity {
    if (same(line.slope, 0) || same(line.slope, S.Infinity)) {
      const c = this.center.reflect(line);
      return newEllipse(c, mul(-1, this.hradius), this.vradius);
    }
    const x = new Sym('_x', { real: true });
    const y = new Sym('_y', { real: true });
    const expr = this.equation(x, y);
    const p = toPoint([x, y]).reflect(line);
    const result = subs(expr, [
      [x, at(p.args, 0)],
      [y, at(p.args, 1)],
    ], { simultaneous: true });
    throw new NotImplementedError(`General Ellipse is not supported but the equation of the reflected Ellipse is given by the zeros of: f(${x.name}, ${y.name}) = ${String(result)}`);
  }

  /** The ellipse rotated by a multiple of pi/2 (SymPy rotate). */
  override rotate(angle: ExprLike = 0, pt?: PointInput | null): GeometryEntity {
    if (same(this.hradius, this.vradius)) return newEllipse(this.center.rotate(angle, pt), this.hradius, this.vradius);
    const a = sympify(angle);
    if (isIntegerQ(mul(a, pow(S.Pi, -1))) === true) return super.rotate(a, pt);
    if (isIntegerQ(mul(2, a, pow(S.Pi, -1))) === true) return newEllipse(this.center.rotate(a, pt), this.vradius, this.hradius);
    throw new NotImplementedError('Only rotations of pi/2 are currently supported for Ellipse.');
  }

  /** The ellipse scaled by x and y about pt (SymPy scale). */
  override scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): GeometryEntity {
    if (pt !== undefined && pt !== null) return super.scale(x, y, pt);
    return newEllipse(this.center.scale(x, y), mul(this.hradius, x), mul(this.vradius, y));
  }

  /** The tangent lines through p (SymPy tangent_lines). */
  tangentLines(pIn: PointInput): Line2DNode[] {
    const p = toPoint(pIn, { dim: 2 });
    if (this.enclosesPoint(p) === true) return [];
    if (this.contains(p)) {
      const delta = this.center.sub(p);
      const rise = mul(pow(this.vradius, 2), delta.coordinate(0));
      const run = mul(-1, pow(this.hradius, 2), delta.coordinate(1));
      const p2 = toPoint([simplify(add(p.coordinate(0), run)), simplify(add(p.coordinate(1), rise))]);
      return [as2DLine(Line(p, p2))];
    }
    // (SymPy's test 2*hradius - |f1 - p| - |f2 - p| > 0 repeats encloses_point, checked above)
    const eq = this.equation(ex, ey);
    const dydx = idiff(eq, ey, ex);
    const slope = as2DLine(Line(p, toPoint([ex, ey]))).slope;
    const tangentPoints = solveEquations([add(slope, mul(-1, dydx)), eq], [ex, ey]);
    if (tangentPoints.length === 1) {
      const t0 = at(tangentPoints, 0);
      if (same(at(t0, 0), p.coordinate(0)) || same(at(t0, 1), p.coordinate(1))) {
        return [as2DLine(Line(p, p.add([1, 0]))), as2DLine(Line(p, p.add([0, 1])))];
      }
      return [as2DLine(Line(p, p.add([0, 1]))), as2DLine(Line(p, t0))];
    }
    return [as2DLine(Line(p, at(tangentPoints, 0))), as2DLine(Line(p, at(tangentPoints, 1)))];
  }

  /** The second moments of area (Ixx, Iyy, Ixy) about the centroid or a point (SymPy second_moment_of_area). */
  secondMomentOfArea(point?: PointInput): [Expr, Expr, Expr] {
    let Ixx = mul(S.Pi, this.hradius, pow(this.vradius, 3), S.Half, S.Half);
    let Iyy = mul(S.Pi, pow(this.hradius, 3), this.vradius, S.Half, S.Half);
    let Ixy: Expr = S.Zero;
    if (point === undefined) return [Ixx, Iyy, Ixy];
    const q = toPoint(point);
    Ixx = add(Ixx, mul(this.area, pow(add(q.coordinate(1), mul(-1, this.center.y)), 2)));
    Iyy = add(Iyy, mul(this.area, pow(add(q.coordinate(0), mul(-1, this.center.x)), 2)));
    Ixy = add(Ixy, mul(this.area, add(q.coordinate(0), mul(-1, this.center.x)), add(q.coordinate(1), mul(-1, this.center.y))));
    return [Ixx, Iyy, Ixy];
  }

  /** The polar second moment of area (SymPy polar_second_moment_of_area). */
  polarSecondMomentOfArea(): Expr {
    const [a, b] = this.secondMomentOfArea();
    return add(a, b);
  }

  /** The section moduli (Sx, Sy) about the centroid or a point (SymPy section_modulus). */
  sectionModulus(point?: PointInput): [Expr, Expr] {
    const { x: xc, y: yc } = this.center;
    let x: Expr, y: Expr;
    if (point === undefined) {
      const [, , xmax, ymax] = this.bounds;
      // SymPy max(y_c - y_min, y_max - y_c): the two are equal for an ellipse
      y = add(ymax, mul(-1, yc));
      x = add(xmax, mul(-1, xc));
    } else {
      const q = as2D(toPoint(point, { dim: 2 }));
      y = add(q.y, mul(-1, yc));
      x = add(q.x, mul(-1, xc));
    }
    const [sx, sy] = this.secondMomentOfArea();
    return [mul(sx, pow(y, -1)), mul(sy, pow(x, -1))];
  }

  /** SymPy GeometryEntity.encloses for an ellipse. */
  override enclosedBy(container: GeometryEntity): boolean {
    return (
      container.enclosesPoint(this.center) === true &&
      container.enclosesPoint(toPoint([add(this.center.x, this.hradius), this.center.y])) === true &&
      container.intersection(this).length === 0
    );
  }
}

/** A polygon: an entity with sides. */
const hasSides = (o: GeometryEntity): o is GeometryEntity & { readonly sides: readonly GeometryEntity[] } =>
  ['Polygon', 'Triangle', 'RegularPolygon'].includes(o.name) && 'sides' in o;

const defd = <T>(e: T | undefined): T => defined(e, 'value');

const as2DLine = (e: Expr): Line2DNode => cast(e, Line2DNode, 'Line2DNode');

const sortedPoints = (ps: readonly PointNode[]): PointNode[] => ordered(ps).filter((p): p is PointNode => p instanceof PointNode);

const sharedRandom = new Random();

/** SymPy Circle: a circle with a center and a radius. */
export class CircleNode extends EllipseNode {
  constructor(center: Point2DNode, radius: Expr) {
    super([center, radius], 'Circle');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newCircle(at(args, 0), at(args, 1));
  }

  /** The radius (SymPy radius). */
  get radius(): Expr {
    return at(this.args, 1);
  }

  override get hradius(): Expr {
    return this.radius;
  }

  /** The vertical radius: the absolute value of the radius (SymPy vradius). */
  override get vradius(): Expr {
    return abs(this.radius);
  }

  override get major(): Expr {
    return this.radius;
  }

  override get minor(): Expr {
    return this.radius;
  }

  /** The center and radius evaluated numerically (SymPy _eval_evalf). */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    return newCircle(evalfArg(this.center), evalfArg(this.radius), { evaluate: false });
  }

  /** The perimeter 2*pi*r (SymPy circumference). */
  override get circumference(): Expr {
    return mul(2, S.Pi, this.radius);
  }

  /** The equation of the circle in real symbols x and y (SymPy equation). */
  override equation(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const t1 = pow(add(X, mul(-1, this.center.x)), 2);
    const t2 = pow(add(Y, mul(-1, this.center.y)), 2);
    return add(t1, t2, mul(-1, pow(this.major, 2)));
  }

  /** The point lies inside the circle (SymPy encloses_point). */
  override enclosesPoint(pIn: PointInput): boolean | 'unknown' {
    const p = toPoint(pIn, { dim: 2 });
    if (this.contains(p)) return false;
    return isPositive(add(this.radius, mul(-1, this.center.distance(p)))) ?? 'unknown';
  }

  /** The reflection in a line: the reflected center with the radius negated (SymPy Circle.reflect). */
  override reflect(line: Line2DNode): GeometryEntity {
    const c = this.center.reflect(line);
    return newCircle(c, mul(-1, this.radius));
  }

  /** The circle scaled by x and y about pt: a circle or an ellipse (SymPy Circle.scale). */
  override scale(xIn: ExprLike = 1, yIn: ExprLike = 1, pt?: PointInput | null): GeometryEntity {
    if (pt !== undefined && pt !== null) return GeometryEntity.prototype.scale.call(this, xIn, yIn, pt);
    const c = this.center.scale(xIn, yIn);
    const [x, y] = [abs(sympify(xIn)), abs(sympify(yIn))];
    if (same(x, y)) return newCircle(c, mul(x, this.radius));
    const h = this.radius;
    return newEllipse(c, mul(h, x), mul(h, y));
  }

}

/** SymPy Ellipse.__new__(center, hradius, vradius, eccentricity). */
export function newEllipse(centerIn?: PointInput, hIn?: ExprLike, vIn?: ExprLike, eIn?: ExprLike): GeometryEntity {
  let hradius = hIn === undefined ? undefined : sympify(hIn);
  let vradius = vIn === undefined ? undefined : sympify(vIn);
  let center: Point2DNode;
  if (centerIn === undefined) center = as2D(toPoint([0, 0]));
  else {
    const c = centerIn instanceof Expr ? centerIn.args : centerIn;
    if (c.length !== 2) throw new RangeError('The center of "Ellipse" must be a two dimensional point');
    center = as2D(toPoint(centerIn, { dim: 2 }));
  }
  if ([hradius, vradius, eIn].filter((v) => v !== undefined).length !== 2) {
    throw new RangeError('Exactly two arguments of "hradius", "vradius", and "eccentricity" must not be None.');
  }
  if (eIn !== undefined) {
    const e = sympify(eIn);
    if (isNegative(e) === true) throw new GeometryError('Eccentricity of ellipse/circle should lie between [0, 1)');
    if (hradius === undefined) hradius = mul(defd(vradius), pow(sqrt(add(1, mul(-1, pow(e, 2)))), -1));
    else vradius ??= mul(hradius, sqrt(add(1, mul(-1, pow(e, 2)))));
  }
  const h = defd(hradius);
  const v = defd(vradius);
  if (same(h, v)) return newCircle(center, h);
  if (same(h, 0) || same(v, 0)) return Segment([add(center.x, mul(-1, h)), add(center.y, mul(-1, v))], [add(center.x, h), add(center.y, v)]);
  if ([h, v].some((r) => isReal(r) === false || r instanceof Special || (r.freeSymbols().size === 0 && isNonRealNumber(r)))) {
    throw new GeometryError('Invalid value encountered when computing hradius / vradius.');
  }
  return new EllipseNode([center, h, v]);
}

/** SymPy linear_coeffs(eq, x**2, y**2, x, y) for the equation of a circle. */
function circleCoeffs(eq: Expr, x: Sym, y: Sym): [Expr, Expr, Expr, Expr, Expr] {
  const P = (() => {
    try {
      return Poly.from(eq, [x, y]);
    } catch {
      throw new GeometryError('The given equation is not that of a circle.');
    }
  })();
  const c = (i: number, j: number): Expr => P.coeffMonomial([i, j]);
  const terms = P.terms();
  if (terms.some(([m]) => at(m, 0) + at(m, 1) > 2 || (at(m, 0) === 1 && at(m, 1) === 1))) throw new GeometryError('The given equation is not that of a circle.');
  return [c(2, 0), c(0, 2), c(1, 0), c(0, 1), c(0, 0)];
}

/** SymPy Circle.__new__: a circle from an equation, three points, or a center and a radius. */
export function newCircle(...argsIn: unknown[]): GeometryEntity {
  const last = argsIn[argsIn.length - 1];
  const opts = isOptions(last) ? last : {};
  const args = isOptions(last) ? argsIn.slice(0, -1) : argsIn;
  const evaluate = opts['evaluate'] !== false;
  const first = args[0];
  if (args.length === 1 && first instanceof Expr && !(first instanceof GeometryEntity)) {
    const symName = (v: unknown, dflt: string): string | Sym => (v instanceof Sym || typeof v === 'string' ? v : dflt);
    const xName = symName(opts['x'], 'x');
    const yName = symName(opts['y'], 'y');
    let equation = expand(first);
    if (equation instanceof Rel && equation.op === 'Eq') equation = add(equation.lhs, mul(-1, equation.rhs));
    const x = find(xName, equation);
    const y = find(yName, equation);
    const [a, b, c, d, e] = circleCoeffs(equation, x, y);
    if (same(a, 0) || same(b, 0) || !same(a, b)) throw new GeometryError('The given equation is not that of a circle.');
    const cx = mul(-1, c, pow(a, -1), S.Half);
    const cy = mul(-1, d, pow(b, -1), S.Half);
    const r2 = add(pow(cx, 2), pow(cy, 2), mul(-1, e, pow(a, -1)));
    return newCircle([cx, cy], sqrt(r2), { evaluate });
  }
  if (args.length === 3) {
    const pts = args.map((a) => toPoint(toInput(a), { dim: 2, evaluate }));
    const t = defd(ellipseHooks.circumcircle)(at(pts, 0), at(pts, 1), at(pts, 2));
    if (!Array.isArray(t)) return t;
    return makeCircle(t[0], t[1]);
  }
  if (args.length === 2) {
    const c = toPoint(toInput(args[0]), { dim: 2, evaluate });
    let r: Expr;
    try {
      r = toPoint([exprArg(args[1]), 0], { evaluate }).coordinate(0);
    } catch (err) {
      if (err instanceof RangeError) throw new GeometryError('Circle with imaginary radius is not permitted');
      throw err;
    }
    return makeCircle(c, r);
  }
  throw new GeometryError('Circle.__new__ received unknown arguments');
}

function exprArg(v: unknown): Expr {
  if (v instanceof Expr || typeof v === 'number' || typeof v === 'bigint') return sympify(v);
  throw new TypeError(`Expecting an expression, not ${typeof v}`);
}

function makeCircle(c: PointNode, r: Expr): GeometryEntity {
  if (same(r, 0)) return c;
  return new CircleNode(as2D(c), r);
}

type EllipseArg = PointInput | ExprLike | EllipseOptions | undefined;

/**
 * SymPy Ellipse(center, hradius, vradius, eccentricity): an Ellipse, a
 * Circle (equal radii) or a Segment (a zero radius). The radii and the
 * eccentricity can also be given as options.
 */
export const Ellipse = /* @__PURE__ */ callableClass(EllipseNode, (...args: EllipseArg[]): GeometryEntity => {
  const last = args[args.length - 1];
  const o = isOptions(last) ? last : {};
  const pos = isOptions(last) ? args.slice(0, -1) : args;
  const opt = (k: string): ExprLike | undefined => {
    const v = o[k];
    return v instanceof Expr || typeof v === 'number' || typeof v === 'bigint' ? v : undefined;
  };
  const c = pos[0];
  const asExprLike = (v: unknown): ExprLike | undefined => (v instanceof Expr || typeof v === 'number' || typeof v === 'bigint' ? v : undefined);
  return newEllipse(c === undefined ? undefined : toInput(c), asExprLike(pos[1]) ?? opt('hradius'), asExprLike(pos[2]) ?? opt('vradius'), asExprLike(pos[3]) ?? opt('eccentricity'));
});
export type Ellipse = EllipseNode;

/**
 * SymPy Circle(center, radius), Circle(p1, p2, p3) or Circle(equation,
 * {x, y}): a Circle (or the point for a zero radius).
 */
export const Circle = /* @__PURE__ */ callableClass(CircleNode, (...args: unknown[]): GeometryEntity => newCircle(...args));
export type Circle = CircleNode;

