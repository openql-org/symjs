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

/** Options of Ellipse. */
export interface EllipseOptions {
  /** The horizontal radius. */
  hradius?: ExprLike;
  /** The vertical radius. */
  vradius?: ExprLike;
  /** The eccentricity, with one of the radii. */
  eccentricity?: ExprLike;
}

/**
 * An ellipse with axes parallel to the coordinate axes.
 *
 * @see SymPy `sympy.geometry.ellipse.Ellipse`
 * @example
 * ```ts
 * import { Ellipse } from '@symjs/symjs';
 *
 * Ellipse([0, 0], 5, 1); // => Ellipse(Point2D(0, 0), 5, 1)
 * ```
 */
export class EllipseNode extends GeometrySet {
  /**
   * Constructs an instance of `EllipseNode`.
   *
   * @param args - Operands in their defining order.
   * @param name - Symbolic name.
   */
  constructor(args: readonly Expr[], name = 'Ellipse') {
    super(name, args);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return newEllipse(at(args, 0), at(args, 1), at(args, 2));
  }

  /**
   * Counts the coordinates needed to describe a point in the ambient space.
   *
   * @returns The ambient dimension.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.ambient_dimension`
   */
  get ambientDimension(): number {
    return 2;
  }

  /**
   * Locates the center of symmetry.
   *
   * @returns The center point.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.center`
   */
  get center(): Point2DNode {
    return as2D(at(this.args, 0));
  }
  /**
   * Measures the radius along the horizontal axis.
   *
   * @returns The horizontal semiaxis.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.hradius`
   */
  get hradius(): Expr {
    return at(this.args, 1);
  }
  /**
   * Measures the radius along the vertical axis.
   *
   * @returns The vertical semiaxis.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.vradius`
   */
  get vradius(): Expr {
    return at(this.args, 2);
  }

  /**
   * Tests whether the operand is a point on this ellipse or the ellipse itself.
   *
   * @param o - Point or entity tested for containment.
   * @returns Whether the operand belongs to the entity.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.contains`
   */
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

  /**
   * Finds the greatest distance from a focus to a point on the ellipse.
   *
   * @returns The apoapsis distance.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.apoapsis`
   */
  get apoapsis(): Expr {
    return mul(this.major, add(1, this.eccentricity));
  }

  /**
   * Parametrizes the ellipse by the cosine and sine of a real parameter.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns A point on the ellipse.
   * @throws RangeError when the requested parameter name already occurs in the entity.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.arbitrary_point`
   */
  override arbitraryPoint(parameter: string | Sym | null = 't'): Point2DNode {
    const t = realSymbol(parameter ?? 't');
    if ([...this.freeSymbols()].filter((s) => s instanceof Sym).some((f) => f.name === t.name)) {
      throw new RangeError(`Symbol ${t.name} already appears in object and cannot be used as a parameter.`);
    }
    return as2D(newPoint([add(this.center.x, mul(this.hradius, cos(t))), add(this.center.y, mul(this.vradius, sin(t)))]));
  }

  /**
   * Computes the area enclosed by the ellipse from its two radii.
   *
   * @returns The ellipse area.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.area`
   */
  get area(): Expr {
    return simplify(mul(S.Pi, this.hradius, this.vradius));
  }

  /**
   * Finds the axis-aligned bounding rectangle.
   *
   * @returns The bounds `[xmin, ymin, xmax, ymax]`.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.bounds`
   */
  override get bounds(): [Expr, Expr, Expr, Expr] {
    const [h, v] = [this.hradius, this.vradius];
    const { x, y } = this.center;
    return [add(x, mul(-1, h)), add(y, mul(-1, v)), add(x, h), add(y, v)];
  }

  /**
   * Computes the length of the boundary.
   *
   * @returns The perimeter.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.circumference`
   */
  get circumference(): Expr {
    // (SymPy's cases e == 1 and e == 0 are a Segment and a Circle, never an Ellipse)
    return mul(4, this.major, ellipticE(pow(this.eccentricity, 2)));
  }

  /**
   * Measures the displacement of the foci relative to the semimajor axis.
   *
   * @returns The eccentricity.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.eccentricity`
   */
  get eccentricity(): Expr {
    return mul(this.focusDistance, pow(this.major, -1));
  }

  /**
   * Tests whether the point lies strictly inside the ellipse.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @returns A truth value, possibly `'unknown'`.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.encloses_point`
   */
  override enclosesPoint(pIn: PointInput): boolean | 'unknown' {
    const p = toPoint(pIn, { dim: 2 });
    if (this.contains(p)) return false;
    const [f1, f2] = this.foci;
    const test = add(mul(2, this.major), mul(-1, add(f1.distance(p), f2.distance(p))));
    return isPositive(test) ?? 'unknown';
  }

  /**
   * Forms the Cartesian equation for the ellipse using real coordinates.
   *
   * @param x - Symbol for the x coordinate.
   * @param y - Symbol for the y coordinate.
   * @param slope - Slope of the reflection axis.
   * @returns An expression that vanishes on the ellipse.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.equation`
   */
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

  /**
   * Computes the locus of centers of curvature of the ellipse.
   *
   * @param x - Symbol for the x coordinate.
   * @param y - Symbol for the y coordinate.
   * @returns The evolute expression.
   * @throws NotImplementedError when the evolute cannot be represented for the supplied ellipse.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.evolute`
   */
  evolute(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    if (this.args.length !== 3) throw new NotImplementedError('Evolute of arbitrary Ellipse is not supported.');
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const twoThirds = Rational.of(2n, 3n);
    const t1 = pow(mul(this.hradius, add(X, mul(-1, this.center.x))), twoThirds);
    const t2 = pow(mul(this.vradius, add(Y, mul(-1, this.center.y))), twoThirds);
    return add(t1, t2, mul(-1, pow(add(pow(this.hradius, 2), mul(-1, pow(this.vradius, 2))), twoThirds)));
  }

  /**
   * Locates both foci of the ellipse.
   *
   * @returns The pair of focal points.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.foci`
   */
  get foci(): [PointNode, PointNode] {
    const c = this.center;
    const [hr, vr] = [this.hradius, this.vradius];
    if (same(hr, vr)) return [c, c];
    const fd = sqrt(add(pow(this.major, 2), mul(-1, pow(this.minor, 2))));
    if (same(hr, this.minor)) return [c.add([0, mul(-1, fd)]), c.add([0, fd])];
    // hradius is the major radius (major gives the hradius when the order cannot be decided)
    return [c.add([mul(-1, fd), 0]), c.add([fd, 0])];
  }

  /**
   * Measures the separation of a focus from the center.
   *
   * @returns The focal distance.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.focus_distance`
   */
  get focusDistance(): Expr {
    return this.center.distance(this.foci[0]);
  }

  /**
   * Finds the geometric entities shared by the ellipse and the operand.
   *
   * @param o - Entity to intersect with this one.
   * @returns The intersection entities.
   * @throws TypeError when a three-dimensional entity is supplied to a planar operation or the operand type has no supported intersection rule.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.intersection`
   */
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

  /**
   * Tests whether the given entity is tangent to the ellipse.
   *
   * @param o - Entity tested for tangency.
   * @returns True if the entity is tangent.
   * @throws TypeError when a three-dimensional entity is supplied to a planar operation or tangency is undefined for the supplied entity.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.is_tangent`
   */
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

  /**
   * Identifies the larger semiaxis of the ellipse.
   *
   * @returns The major semiaxis length.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.major`
   */
  get major(): Expr {
    const [a, b] = [this.hradius, at(this.args, 2)];
    const o = decided(Lt(add(b, mul(-1, a)), 0));
    if (o === true) return a;
    if (o === false) return b;
    return this.hradius;
  }

  /**
   * Identifies the smaller semiaxis of the ellipse.
   *
   * @returns The minor semiaxis length.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.minor`
   */
  get minor(): Expr {
    const [a, b] = [this.hradius, at(this.args, 2)];
    const o = decided(Lt(add(a, mul(-1, b)), 0));
    if (o === true) return a;
    if (o === false) return b;
    return this.vradius;
  }

  /**
   * Finds the normals to the ellipse through the point, using the requested precision for their points
   * and slopes.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @param prec - Numerical precision.
   * @returns The normal lines.
   * @throws NotImplementedError when the general ellipse intersection is unsupported.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.normal_lines`
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

  /**
   * Finds the shortest distance from a focus to the ellipse.
   *
   * @returns The periapsis distance.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.periapsis`
   */
  get periapsis(): Expr {
    return mul(this.major, add(1, mul(-1, this.eccentricity)));
  }

  /**
   * Computes half the length of the focal chord perpendicular to the major axis.
   *
   * @returns The semi-latus rectum.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.semilatus_rectum`
   */
  get semilatusRectum(): Expr {
    return mul(this.major, add(1, mul(-1, pow(this.eccentricity, 2))));
  }

  /**
   * Constructs a concentric circle with the ellipse's larger radius.
   *
   * @returns The auxiliary circle.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.auxiliary_circle`
   */
  auxiliaryCircle(): GeometryEntity {
    return newCircle(this.center, Max(this.hradius, this.vradius));
  }

  /**
   * Finds the locus of intersections of perpendicular tangents to the ellipse.
   *
   * @returns The director circle.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.director_circle`
   */
  directorCircle(): GeometryEntity {
    return newCircle(this.center, sqrt(add(pow(this.hradius, 2), pow(this.vradius, 2))));
  }

  /**
   * Specifies the parameter range used to plot a parametrized point.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The plotting variable and endpoints.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.plot_interval`
   */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [realSymbol(parameter), mul(-1, S.Pi), S.Pi];
  }

  /**
   * Samples a point on the ellipse, reproducibly for a given integer seed.
   *
   * @param seed - Seed for reproducible sampling.
   * @returns The sampled point.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.random_point`
   */
  randomPoint(seed?: number | bigint): PointNode {
    const t = realSymbol('t');
    const [x, y] = this.arbitraryPoint(t).args;
    const rng = seed === undefined ? sharedRandom : new Random(seed);
    const r = rationalOf(rng.random());
    const c = add(mul(2, r), -1);
    const s = sqrt(add(1, mul(-1, pow(c, 2))));
    return toPoint([subs(defd(x), [[cos(t), c]]), subs(defd(y), [[sin(t), s]])]);
  }

  /**
   * Reflects the ellipse across a horizontal or vertical line.
   *
   * @param line - Line defining the direction or reflection axis.
   * @returns The reflected ellipse.
   * @throws NotImplementedError when the reflection produces a general rotated ellipse.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.reflect`
   */
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

  /**
   * Rotates the ellipse through a multiple of a quarter turn.
   *
   * @param angle - Rotation angle in radians.
   * @param pt - Center of rotation, defaulting to the origin.
   * @returns The rotated ellipse.
   * @throws NotImplementedError when the rotation of a noncircular ellipse is not a multiple of a quarter turn.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.rotate`
   */
  override rotate(angle: ExprLike = 0, pt?: PointInput | null): GeometryEntity {
    if (same(this.hradius, this.vradius)) return newEllipse(this.center.rotate(angle, pt), this.hradius, this.vradius);
    const a = sympify(angle);
    if (isIntegerQ(mul(a, pow(S.Pi, -1))) === true) return super.rotate(a, pt);
    if (isIntegerQ(mul(2, a, pow(S.Pi, -1))) === true) return newEllipse(this.center.rotate(a, pt), this.vradius, this.hradius);
    throw new NotImplementedError('Only rotations of pi/2 are currently supported for Ellipse.');
  }

  /**
   * Scales the ellipse about the given point along both axes.
   *
   * @param x - Scale factor along the x axis.
   * @param y - Scale factor along the y axis.
   * @param pt - Fixed point of the scaling, defaulting to the origin.
   * @returns The scaled entity.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.scale`
   */
  override scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): GeometryEntity {
    if (pt !== undefined && pt !== null) return super.scale(x, y, pt);
    return newEllipse(this.center.scale(x, y), mul(this.hradius, x), mul(this.vradius, y));
  }

  /**
   * Finds the tangents to the ellipse that pass through the point.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @returns The tangent lines.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.tangent_lines`
   */
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

  /**
   * Computes the second moments of area about the centroid or the supplied point.
   *
   * @param point - Point at which to evaluate the operation.
   * @returns The triple `[Ixx, Iyy, Ixy]`.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.second_moment_of_area`
   */
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

  /**
   * Computes the polar second moment of the enclosed area.
   *
   * @returns The polar moment.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.polar_second_moment_of_area`
   */
  polarSecondMomentOfArea(): Expr {
    const [a, b] = this.secondMomentOfArea();
    return add(a, b);
  }

  /**
   * Computes the section moduli about the centroid or the specified point.
   *
   * @param point - Point at which to evaluate the operation.
   * @returns The pair `[Sx, Sy]`.
   * @see SymPy `sympy.geometry.ellipse.Ellipse.section_modulus`
   */
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

  /**
   * Tests whether the given entity encloses this entity.
   *
   * @param container - Geometric entity tested for enclosure.
   * @returns Whether the supplied entity encloses this one.
   */
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

/**
 * A circle with a center and a radius.
 *
 * @see SymPy `sympy.geometry.ellipse.Circle`
 * @example
 * ```ts
 * import { Circle, ex } from '@symjs/symjs';
 *
 * Circle([0, 0], 5); // => Circle(Point2D(0, 0), 5)
 * Circle(ex`x**2 + y**2 - 25`); // => Circle(Point2D(0, 0), 5)
 * ```
 */
export class CircleNode extends EllipseNode {
  /**
   * Constructs an instance of `CircleNode`.
   *
   * @param center - Center of the figure.
   * @param radius - Distance from the center to the circumference.
   */
  constructor(center: Point2DNode, radius: Expr) {
    super([center, radius], 'Circle');
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return newCircle(at(args, 0), at(args, 1));
  }

  /**
   * Gives the defining radius of the figure.
   *
   * @returns The radius expression.
   * @see SymPy `sympy.geometry.ellipse.Circle.radius`
   */
  get radius(): Expr {
    return at(this.args, 1);
  }

  /**
   * Gives the circle's horizontal extent as a radius.
   *
   * @returns The horizontal radius.
   * @see SymPy `sympy.geometry.ellipse.Circle.hradius`
   */
  override get hradius(): Expr {
    return this.radius;
  }

  /**
   * Takes the absolute value of the circle's radius for its vertical semiaxis.
   *
   * @returns The vertical radius.
   * @see SymPy `sympy.geometry.ellipse.Circle.vradius`
   */
  override get vradius(): Expr {
    return abs(this.radius);
  }

  /**
   * Selects the longer semiaxis, defaulting to the horizontal radius if their order is undecidable.
   *
   * @returns The major semiaxis length.
   * @see SymPy `sympy.geometry.ellipse.Circle.major`
   */
  override get major(): Expr {
    return this.radius;
  }

  /**
   * Selects the shorter semiaxis, defaulting to the vertical radius if their order is undecidable.
   *
   * @returns The minor semiaxis length.
   * @see SymPy `sympy.geometry.ellipse.Circle.minor`
   */
  override get minor(): Expr {
    return this.radius;
  }

  /**
   * Evaluates the center and radius numerically.
   *
   * @param evalfArg - Function that evaluates an operand numerically.
   * @param _dps - Decimal digits of numerical precision.
   * @returns The numerically evaluated expression.
   * @see SymPy `sympy.geometry.ellipse.Circle._eval_evalf`
   */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    return newCircle(evalfArg(this.center), evalfArg(this.radius), { evaluate: false });
  }

  /**
   * Computes the circumference from the circle's radius.
   *
   * @returns The perimeter expression.
   * @see SymPy `sympy.geometry.ellipse.Circle.circumference`
   */
  override get circumference(): Expr {
    return mul(2, S.Pi, this.radius);
  }

  /**
   * Forms the Cartesian equation for the circle using real coordinates.
   *
   * @param x - Symbol for the x coordinate.
   * @param y - Symbol for the y coordinate.
   * @returns An expression that vanishes on the circle.
   * @see SymPy `sympy.geometry.ellipse.Circle.equation`
   */
  override equation(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const t1 = pow(add(X, mul(-1, this.center.x)), 2);
    const t2 = pow(add(Y, mul(-1, this.center.y)), 2);
    return add(t1, t2, mul(-1, pow(this.major, 2)));
  }

  /**
   * Tests whether the point lies strictly inside the circle.
   *
   * @param pIn - Point used in the geometric construction or comparison.
   * @returns A truth value, possibly `'unknown'`.
   * @see SymPy `sympy.geometry.ellipse.Circle.encloses_point`
   */
  override enclosesPoint(pIn: PointInput): boolean | 'unknown' {
    const p = toPoint(pIn, { dim: 2 });
    if (this.contains(p)) return false;
    return isPositive(add(this.radius, mul(-1, this.center.distance(p)))) ?? 'unknown';
  }

  /**
   * Reflects the center across the line and reverses the radius sign.
   *
   * @param line - Line defining the direction or reflection axis.
   * @returns The reflected circle.
   * @see SymPy `sympy.geometry.ellipse.Circle.reflect`
   */
  override reflect(line: Line2DNode): GeometryEntity {
    const c = this.center.reflect(line);
    return newCircle(c, mul(-1, this.radius));
  }

  /**
   * Scales the circle independently along each axis about the given point.
   *
   * @param xIn - Scale factor along the x axis.
   * @param yIn - Scale factor along the y axis.
   * @param pt - Fixed point of the scaling, defaulting to the origin.
   * @returns The resulting circle or ellipse.
   * @see SymPy `sympy.geometry.ellipse.Circle.scale`
   */
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
 * Constructs an axis-aligned ellipse specified by its center and radii or eccentricity.
 *
 * @param args - Center and two of horizontal radius, vertical radius and eccentricity, supplied positionally or by options.
 * @returns The resulting geometric entity, including a lower-dimensional entity for degenerate input.
 * @throws RangeError when the center is not two-dimensional or the radii and eccentricity do not supply exactly two parameters.
 * @throws GeometryError when the supplied eccentricity or derived radii are invalid.
 * @see SymPy `sympy.geometry.ellipse.Ellipse`
 * @example
 * ```ts
 * import { Ellipse } from '@symjs/symjs';
 *
 * Ellipse([0, 0], 5, 1); // => Ellipse(Point2D(0, 0), 5, 1)
 * ```
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
 * Constructs a circle specified by a center and radius, three points, or a circle equation.
 *
 * @param args - Center and radius, three points, or a circle equation and coordinate options.
 * @returns The resulting geometric entity, including a lower-dimensional entity for degenerate input.
 * @throws GeometryError when the inputs do not define a circle or its radius would be imaginary.
 * @see SymPy `sympy.geometry.ellipse.Circle`
 * @example
 * ```ts
 * import { Circle, ex } from '@symjs/symjs';
 *
 * Circle([0, 0], 5); // => Circle(Point2D(0, 0), 5)
 * Circle(ex`x**2 + y**2 - 25`); // => Circle(Point2D(0, 0), 5)
 * ```
 */
export const Circle = /* @__PURE__ */ callableClass(CircleNode, (...args: unknown[]): GeometryEntity => newCircle(...args));
export type Circle = CircleNode;

