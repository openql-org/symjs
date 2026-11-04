// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/polygon.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.polygon: polygons in the plane (Polygon,
 * RegularPolygon and Triangle) and the angle conversions rad and deg.
 *
 * Polygon(...) drops repeated and collinear vertices and gives a Triangle,
 * Segment or Point when fewer than four vertices remain. Polygons with the
 * same vertices in the same cyclic order (in either direction) are equal.
 */

import { Dummy, Expr, Rational, S, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { Le, Lt } from '../core/logic';
import { piecewise } from '../core/logic';
import { BoolOp, and } from '../core/boolalg';
import { subs } from '../core/traverse';
import { coeff } from '../core/methods';
import { ordered } from '../core/match';
import { callableClass } from '../core/callable';
import { isNegative, isNonNegative, isPositive, isZero as isZeroQ } from '../core/assumptions';
import { ExprMap } from '../core/exprmap';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, expectType, getOrThrow } from '../core/guard';
import { EmptySet } from '../sets/sets';
import { Piecewise as PiecewiseNode } from '../core/nodes';
import { BoolAtom } from '../core/nodes';
import { abs as absExpr, cos, sin, tan } from '../functions/elementary/elementary';
import { sign } from '../functions/special/special';
import { Mod } from '../functions/mod';
import { compareKeys, sortKey } from '../printing/sortkey';
import { simplify } from '../simplify/simplify';
import { GeometryEntity, GeometrySet, decide, realSymbol, tryDecide } from './entity';
import type { PointInput } from './entity';
import { GeometryError } from './exceptions';
import { Point2DNode, PointNode, isOptions, normalizeDimension, toInput, toPoint, uniqPoints } from './point';
import type { LinearEntity} from './line';
import { Line, Line2DNode, Ray, Ray2DNode, RayNode, Segment, SegmentNode, pyGt, pyLt } from './line';
import { newCircle, ellipseHooks } from './ellipse';
import { utilClasses } from './util';
import { solveEquations } from './solvehelp';

const [px, py, PT] = [new Dummy('polygon_dummy', { real: true }), new Dummy('polygon_dummy', { real: true }), new Dummy('polygon_dummy', { real: true })];

const same = (a: Expr, b: ExprLike): boolean => a.key === sympify(b).key;

/** SymPy is_nonpositive of a real expression. */
function isNonPositive(e: Expr): boolean | undefined {
  if (isNegative(e) === true || isZeroQ(e) === true) return true;
  if (isPositive(e) === true) return false;
  return undefined;
}

const as2D = (e: Expr): Point2DNode => cast(e, Point2DNode, 'Point2DNode');
const asPoint = (e: Expr): PointNode => cast(e, PointNode, 'PointNode');

/** Python list index with negative indices. */
const idx = (n: number, i: number): number => (i < 0 ? n + i : i);

/** The keys of the vertices in SymPy's canonical cyclic order (Polygon._hashable_content). */
function canonicalKeys(args: readonly Expr[]): string[] {
  const refList = (pts: readonly Expr[]): [number[], Map<number, Expr>] => {
    const sorted = ordered(uniqPoints(pts));
    const kee = new Map(sorted.map((p, i) => [p.key, i]));
    return [pts.map((p) => getOrThrow(kee, p.key)), new Map(sorted.map((p, i) => [i, p]))];
  };
  const leastRotation = (s: readonly number[]): number[] => {
    let best = [...s];
    for (let k = 1; k < s.length; k++) {
      const r = [...s.slice(k), ...s.slice(0, k)];
      if (lexLess(r, best)) best = r;
    }
    return best;
  };
  const [s1, d] = refList(args);
  const rNor = leastRotation(s1);
  const [s2] = refList([...args].reverse());
  const rRev = leastRotation(s2);
  const r = lexLess(rNor, rRev) ? rNor : rRev;
  return r.map((i) => getOrThrow(d, i).key);
}

/** a < b for two different rotations of the same length (the vertices are distinct, so they differ). */
const lexLess = (a: readonly number[], b: readonly number[]): boolean => {
  const i = a.findIndex((v, k) => v !== at(b, k));
  return at(a, i) < at(b, i);
};

/** SymPy Polygon: a simple polygon given by its vertices. */
export class PolygonNode extends GeometrySet {
  constructor(vertices: readonly Expr[], name = 'Polygon') {
    super(name, vertices);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newPolygon(args.map(asPoint));
  }

  protected override computeKey(): string {
    return `${this.name}(${canonicalKeys(this.args).join(',')})`;
  }

  get ambientDimension(): number {
    return at(this.vertices, 0).ambientDimension;
  }

  /** The vertices in order (SymPy vertices). */
  get vertices(): PointNode[] {
    return this.args.map(asPoint);
  }

  /** The signed area: positive for counterclockwise vertices (SymPy area). */
  get area(): Expr {
    const args = this.vertices;
    let area: Expr = S.Zero;
    for (let i = 0; i < args.length; i++) {
      const [x1, y1] = at(args, idx(args.length, i - 1)).args;
      const [x2, y2] = at(args, i).args;
      area = add(area, mul(d(x1), d(y2)), mul(-1, d(x2), d(y1)));
    }
    return mul(simplify(area), S.Half);
  }

  /** SymPy Polygon._is_clockwise(a, b, c): the turn a -> b -> c is clockwise (or straight). */
  static isClockwise(a: PointNode, b: PointNode, c: PointNode): boolean {
    const ba = b.sub(a);
    const ca = c.sub(a);
    const tArea = simplify(add(mul(ba.coordinate(0), ca.coordinate(1)), mul(-1, ca.coordinate(0), ba.coordinate(1))));
    const res = isNonPositive(tArea);
    if (res === undefined) throw new RangeError("Can't determine orientation");
    return res;
  }

  /** The interior angle at each vertex (SymPy angles). */
  get angles(): ExprMap<Expr> {
    const args = this.vertices;
    const n = args.length;
    const ret = new ExprMap<Expr>();
    for (let i = 0; i < n; i++) {
      const [a, b, c] = [at(args, idx(n, i - 2)), at(args, idx(n, i - 1)), at(args, i)];
      const reflexAng = Ray(b, a).angleBetween(Ray(b, c));
      ret.set(b, PolygonNode.isClockwise(a, b, c) ? add(mul(2, S.Pi), mul(-1, reflexAng)) : reflexAng);
    }
    const total = add(...ret.values());
    const wrong = isPositive(add(mul(add(mul(total, pow(S.Pi, -1)), -1), pow(Rational.of(BigInt(n - 2)), -1)), -1));
    if (wrong === true) {
      for (const [b, v] of ret) ret.set(b, add(mul(2, S.Pi), mul(-1, v)));
    } else if (wrong === undefined) throw new RangeError('could not determine Polygon orientation.');
    return ret;
  }

  /** The perimeter (SymPy perimeter). */
  get perimeter(): Expr {
    const args = this.vertices;
    let p: Expr = S.Zero;
    for (let i = 0; i < args.length; i++) p = add(p, at(args, idx(args.length, i - 1)).distance(at(args, i)));
    return simplify(p);
  }

  /** The centroid (SymPy centroid). */
  get centroid(): PointNode {
    const A = pow(mul(6, this.area), -1);
    let cx: Expr = S.Zero;
    let cy: Expr = S.Zero;
    const args = this.vertices;
    for (let i = 0; i < args.length; i++) {
      const [x1, y1] = at(args, idx(args.length, i - 1)).args;
      const [x2, y2] = at(args, i).args;
      const v = add(mul(d(x1), d(y2)), mul(-1, d(x2), d(y1)));
      cx = add(cx, mul(v, add(d(x1), d(x2))));
      cy = add(cy, mul(v, add(d(y1), d(y2))));
    }
    return toPoint([simplify(mul(A, cx)), simplify(mul(A, cy))]);
  }

  /** The second moments of area (Ixx, Iyy, Ixy) about the centroid or a point (SymPy second_moment_of_area). */
  secondMomentOfArea(point?: PointInput): [Expr, Expr, Expr] {
    let Ixx: Expr = S.Zero;
    let Iyy: Expr = S.Zero;
    let Ixy: Expr = S.Zero;
    const args = this.vertices;
    for (let i = 0; i < args.length; i++) {
      const [X1, Y1] = [at(args, idx(args.length, i - 1)).coordinate(0), at(args, idx(args.length, i - 1)).coordinate(1)];
      const [X2, Y2] = [at(args, i).coordinate(0), at(args, i).coordinate(1)];
      const v = add(mul(X1, Y2), mul(-1, X2, Y1));
      Ixx = add(Ixx, mul(add(pow(Y1, 2), mul(Y1, Y2), pow(Y2, 2)), v));
      Iyy = add(Iyy, mul(add(pow(X1, 2), mul(X1, X2), pow(X2, 2)), v));
      Ixy = add(Ixy, mul(add(mul(X1, Y2), mul(2, X1, Y1), mul(2, X2, Y2), mul(X2, Y1)), v));
    }
    const A = this.area;
    const c = this.centroid;
    const [cX, cY] = [c.coordinate(0), c.coordinate(1)];
    const IxxC = add(mul(Ixx, Rational.of(1n, 12n)), mul(-1, A, pow(cY, 2)));
    const IyyC = add(mul(Iyy, Rational.of(1n, 12n)), mul(-1, A, pow(cX, 2)));
    const IxyC = add(mul(Ixy, Rational.of(1n, 24n)), mul(-1, A, cX, cY));
    if (point === undefined) return [IxxC, IyyC, IxyC];
    const p = toPoint(point);
    return [
      add(IxxC, mul(A, pow(add(p.coordinate(1), mul(-1, cY)), 2))),
      add(IyyC, mul(A, pow(add(p.coordinate(0), mul(-1, cX)), 2))),
      add(IxyC, mul(A, add(p.coordinate(0), mul(-1, cX)), add(p.coordinate(1), mul(-1, cY)))),
    ];
  }

  /** The first moments of area (Qx, Qy) about the centroid or a point (SymPy first_moment_of_area). */
  firstMomentOfArea(point?: PointInput): [Expr, Expr] {
    const c = this.centroid;
    const [xc, yc] = [c.coordinate(0), c.coordinate(1)];
    const p = point === undefined ? c : toPoint(point);
    const hLine = Line(p, { slope: 0 });
    const vLine = Line(p, { slope: S.Infinity });
    const hPoly = this.cutSection(as2DLine(hLine));
    const vPoly = this.cutSection(as2DLine(vLine));
    const smaller = ([a, b]: [PolygonNode | typeof EmptySet, PolygonNode | typeof EmptySet]): PolygonNode => {
      const [pa, pb] = [cast(a, PolygonNode, 'Polygon'), cast(b, PolygonNode, 'Polygon')];
      return decide(Le(pa.area, pb.area)) ? pa : pb;
    };
    const poly1 = smaller(hPoly);
    const poly2 = smaller(vPoly);
    const Qx = mul(add(poly1.centroid.coordinate(1), mul(-1, yc)), poly1.area);
    const Qy = mul(add(poly2.centroid.coordinate(0), mul(-1, xc)), poly2.area);
    return [Qx, Qy];
  }

  /** The polar second moment of area (SymPy polar_second_moment_of_area). */
  polarSecondMomentOfArea(): Expr {
    const [a, b] = this.secondMomentOfArea();
    return add(a, b);
  }

  /** The section moduli (Sx, Sy) about the centroid or a point (SymPy section_modulus). */
  sectionModulus(point?: PointInput): [Expr, Expr] {
    const c = this.centroid;
    const [xc, yc] = [c.coordinate(0), c.coordinate(1)];
    let x: Expr, y: Expr;
    if (point === undefined) {
      const [xmin, ymin, xmax, ymax] = this.bounds;
      y = pyMax2(add(yc, mul(-1, ymin)), add(ymax, mul(-1, yc)));
      x = pyMax2(add(xc, mul(-1, xmin)), add(xmax, mul(-1, xc)));
    } else {
      const p = toPoint(point);
      y = add(p.coordinate(1), mul(-1, yc));
      x = add(p.coordinate(0), mul(-1, xc));
    }
    const [sx, sy] = this.secondMomentOfArea();
    return [mul(sx, pow(y, -1)), mul(sy, pow(x, -1))];
  }

  /** The sides as segments, starting from the last vertex (SymPy sides). */
  get sides(): SegmentNode[] {
    const args = this.vertices;
    const n = args.length;
    const res: SegmentNode[] = [];
    for (let i = -n; i < 0; i++) {
      // consecutive vertices are distinct, so each side is a segment
      res.push(cast(Segment(at(args, idx(n, i)), at(args, idx(n, i + 1))), SegmentNode, 'Segment'));
    }
    return res;
  }

  override get bounds(): [Expr, Expr, Expr, Expr] {
    const xs = this.vertices.map((p) => p.coordinate(0));
    const ys = this.vertices.map((p) => p.coordinate(1));
    return [pyMin(xs), pyMin(ys), pyMax(xs), pyMax(ys)];
  }

  /** The polygon is convex (SymPy is_convex). */
  isConvex(): boolean {
    const args = this.vertices;
    const n = args.length;
    const cw = PolygonNode.isClockwise(at(args, n - 2), at(args, n - 1), at(args, 0));
    for (let i = 1; i < n; i++) {
      if (cw !== PolygonNode.isClockwise(at(args, idx(n, i - 2)), at(args, idx(n, i - 1)), at(args, i))) return false;
    }
    const sides = this.sides;
    for (let i = 0; i < sides.length; i++) {
      const si = at(sides, i);
      const pts = si.args;
      for (let j = i === sides.length - 1 ? 1 : 0; j < i - 1; j++) {
        const sj = at(sides, j);
        const inPts = (q: PointNode): boolean => pts.some((p) => p.key === q.key);
        if (!inPts(sj.p1) && !inPts(sj.p2) && !boxesApart(si, sj) && si.intersection(sj).length) return false;
      }
    }
    return true;
  }

  /** The point lies inside the polygon (SymPy encloses_point; 'unknown' with symbolic coordinates). */
  override enclosesPoint(pIn: PointInput): boolean | 'unknown' {
    const p = toPoint(pIn, { dim: 2 });
    if (this.vertices.some((v) => v.key === p.key) || this.sides.some((s) => s.contains(p))) return false;
    const lit: PointNode[] = [];
    for (const v of this.vertices) {
      const w = v.sub(p);
      lit.push(w);
      if (w.freeSymbols().size) return 'unknown';
    }
    // the translated vertices form the same kind of polygon
    const poly = cast(newPolygon(lit), PolygonNode, 'Polygon');
    const args = poly.vertices;
    const n = args.length;
    if (poly.isConvex()) {
      let orientation: boolean | undefined | 'unset' = 'unset';
      for (let i = -n; i <= 0; i++) {
        const a = at(args, idx(n, i));
        const b = at(args, idx(n, i + 1));
        const [ax, ay, bx, by] = [a.coordinate(0), a.coordinate(1), b.coordinate(0), b.coordinate(1)];
        const test = isNegative(add(mul(-1, ay, add(bx, mul(-1, ax))), mul(ax, add(by, mul(-1, ay)))));
        if (orientation === 'unset') orientation = test;
        else if (test !== orientation) return false;
      }
      return true;
    }
    let hitOdd = false;
    let [p1x, p1y] = [at(args, 0).coordinate(0), at(args, 0).coordinate(1)];
    for (let i = -n + 1; i <= 0; i++) {
      const q = at(args, idx(n, i));
      const [p2x, p2y] = [q.coordinate(0), q.coordinate(1)];
      if (pyLt(pyMin([p1y, p2y]), 0) && !pyLt(pyMax([p1y, p2y]), 0) && !pyLt(pyMax([p1x, p2x]), 0) && !same(p1y, p2y)) {
        const xinters = add(mul(-1, p1y, add(p2x, mul(-1, p1x)), pow(add(p2y, mul(-1, p1y)), -1)), p1x);
        if (same(p1x, p2x) || !pyLt(xinters, 0)) hitOdd = !hitOdd;
      }
      [p1x, p1y] = [p2x, p2y];
    }
    return hitOdd;
  }

  /**
   * The point of the boundary at the fraction t of the perimeter, as a
   * Piecewise over the sides (SymPy arbitrary_point).
   */
  override arbitraryPoint(parameter: string | Sym | null = 't'): Expr {
    const t = realSymbol(parameter ?? 't');
    if ([...this.freeSymbols()].some((f) => f.name === t.name)) {
      throw new RangeError(`Symbol ${t.name} already appears in object and cannot be used as a parameter.`);
    }
    const sides: [Expr, Expr][] = [];
    const perimeter = this.perimeter;
    let start: Expr = S.Zero;
    for (const s of this.sides) {
      const frac = mul(s.length, pow(perimeter, -1));
      const end = add(start, frac);
      const pt = subs(s.arbitraryPoint(t), [[t, mul(add(t, mul(-1, start)), pow(frac, -1))]]);
      sides.push([pt, and(Le(start, t), Lt(t, end))]);
      start = end;
    }
    return piecewise(...sides);
  }

  /** The fraction of the perimeter at which the arbitrary point is other (SymPy parameter_value). */
  override parameterValue(otherIn: PointInput, t: Expr): ExprMap<Expr> {
    const other = otherIn instanceof GeometryEntity ? otherIn : toPoint(otherIn, { dim: this.ambientDimension });
    if (!(other instanceof PointNode)) throw new RangeError('other must be a point');
    if (other.freeSymbols().size) throw new NotImplementedError('non-numeric coordinates');
    let unknown = false;
    const p = cast(this.arbitraryPoint(PT), PiecewiseNode, 'Piecewise');
    for (const [pt, cond] of p.pairs) {
      const sol = solveEquations(asPoint(pt).sub(other).args, [PT]);
      const s0 = sol[0];
      if (s0 === undefined) continue;
      const value = at(s0, 0);
      if (conditionHolds(subs(cond, [[PT, value]]))) return new ExprMap([[t, value]]);
      unknown = true;
    }
    if (unknown) throw new RangeError(`Given point may not be on ${this.name}`);
    throw new RangeError(`Given point is not on ${this.name}`);
  }

  /** The parameter interval of the arbitrary point used for plotting (SymPy plot_interval). */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    return [typeof parameter === 'string' ? new Sym(parameter, { real: true }) : parameter, S.Zero, S.One];
  }

  /** The points and segments common to the polygon and o (SymPy intersection). */
  override intersection(o: unknown): GeometryEntity[] {
    const k: unknown[] = o instanceof PolygonNode ? o.sides : [o];
    let res: GeometryEntity[] = [];
    for (const side of this.sides) for (const side1 of k) res.push(...side.intersection(side1));
    res = uniqPoints(res);
    const points = res.filter((e): e is PointNode => e instanceof PointNode);
    const segments = res.filter((e): e is SegmentNode => e instanceof SegmentNode);
    if (points.length && segments.length) {
      const inSegments = uniqPoints(points.filter((pt) => segments.some((s) => s.contains(pt))));
      const rest = points.filter((pt) => !inSegments.some((q) => q.key === pt.key));
      return ordered([...segments, ...rest]).filter((e): e is GeometryEntity => e instanceof GeometryEntity);
    }
    return ordered(res).filter((e): e is GeometryEntity => e instanceof GeometryEntity);
  }

  /**
   * The polygons above and below a line that cuts the polygon (SymPy
   * cut_section); EmptySet for a side without a polygon (SymPy None).
   */
  cutSection(line: Line2DNode): [PolygonNode | typeof EmptySet, PolygonNode | typeof EmptySet] {
    if (this.intersection(line).length === 0) throw new RangeError('This line does not intersect the polygon');
    const points = [...this.vertices, at(this.vertices, 0)];
    const eq = line.equation(px, py);
    const a = coeff(eq, px);
    const b = coeff(eq, py);
    const upper: PointNode[] = [];
    const lower: PointNode[] = [];
    let prev = true;
    let prevPoint: PointNode | undefined;
    for (const point of points) {
      const compare = !same(b, 0)
        ? mul(subs(eq, [[px, point.coordinate(0)], [py, point.coordinate(1)]]), pow(b, -1))
        : mul(subs(eq, [[px, point.coordinate(0)]]), pow(a, -1));
      if (pyGt(compare, 0)) {
        if (!prev && prevPoint !== undefined) {
          const np = at(Line(point, prevPoint).intersection(line), 0);
          upper.push(asPoint(np));
          lower.push(asPoint(np));
        }
        upper.push(point);
        prev = true;
      } else {
        if (prev && prevPoint !== undefined) {
          const np = at(Line(point, prevPoint).intersection(line), 0);
          upper.push(asPoint(np));
          lower.push(asPoint(np));
        }
        lower.push(point);
        prev = false;
      }
      prevPoint = point;
    }
    const part = (vs: PointNode[]): PolygonNode | typeof EmptySet => {
      const q = vs.length ? newPolygon(vs) : EmptySet;
      return q instanceof PolygonNode ? q : EmptySet;
    };
    return [part(upper), part(lower)];
  }

  /** The shortest distance to a point, or between two convex polygons (SymPy distance). */
  override distance(o: unknown): Expr {
    if (o instanceof PointNode) {
      let dist: Expr = S.Infinity;
      for (const side of this.sides) {
        const current = side.distance(o);
        if (same(current, 0)) return S.Zero;
        if (pyLt(current, dist)) dist = current;
      }
      return dist;
    }
    if (o instanceof PolygonNode && this.isConvex() && o.isConvex()) return this.polyDistance(o);
    throw new NotImplementedError(`distance between a Polygon and ${String(o)}`);
  }

  /** SymPy _do_poly_distance: the distance of two convex polygons by rotating calipers. */
  private polyDistance(e2: PolygonNode): Expr {
    const e1: PolygonNode = this;
    let e1Ymax = toPoint([0, S.NegativeInfinity]);
    let e2Ymin = toPoint([0, S.Infinity]);
    for (const v of e1.vertices) {
      if (pyGt(v.coordinate(1), e1Ymax.coordinate(1)) || (same(v.coordinate(1), e1Ymax.coordinate(1)) && pyGt(v.coordinate(0), e1Ymax.coordinate(0)))) e1Ymax = v;
    }
    for (const v of e2.vertices) {
      if (pyLt(v.coordinate(1), e2Ymin.coordinate(1)) || (same(v.coordinate(1), e2Ymin.coordinate(1)) && pyLt(v.coordinate(0), e2Ymin.coordinate(0)))) e2Ymin = v;
    }
    let minDist = e1Ymax.distance(e2Ymin);
    const connections = (e: PolygonNode): Map<string, PointNode[]> => {
      const m = new Map<string, PointNode[]>();
      const push = (k: PointNode, v: PointNode): void => {
        const l = m.get(k.key);
        if (l) l.push(v);
        else m.set(k.key, [v]);
      };
      for (const side of e.sides) {
        push(side.p1, side.p2);
        push(side.p2, side.p1);
      }
      return m;
    };
    const c1 = connections(e1);
    const c2 = connections(e2);
    const conn = (m: Map<string, PointNode[]>, p: PointNode, i: number): PointNode => at(getOrThrow(m, p.key), i);
    let e1Current = e1Ymax;
    let e2Current = e2Ymin;
    const supportLine: LinearEntity = Line([0, 0], [1, 0]);
    const pick = (m: Map<string, PointNode[]>, p: PointNode, larger: boolean): PointNode => {
      const [q1, q2] = [conn(m, p, 0), conn(m, p, 1)];
      const a1 = supportLine.angleBetween(Line(p, q1));
      const a2 = supportLine.angleBetween(Line(p, q2));
      // the neighbours of the top (bottom) vertex of a convex polygon make different angles with the
      // horizontal, so SymPy's tie break by distance does not apply
      return (larger ? pyGt(a1, a2) : pyLt(a1, a2)) ? q1 : q2;
    };
    let e1Next = pick(c1, e1Ymax, false);
    let e2Next = pick(c2, e2Ymin, true);
    const advance = (m: Map<string, PointNode[]>, cur: PointNode, next: PointNode): [PointNode, PointNode] =>
      conn(m, next, 0).key !== cur.key ? [next, conn(m, next, 0)] : [next, conn(m, next, 1)];
    const evalLt = (a: Expr, b: Expr): boolean => decide(Lt(a.evalf(), b.evalf()));
    for (;;) {
      // SymPy compares the angles with the support line by (e1_angle < e2_angle) is True, which is
      // never the case for a SymPy boolean (S.true is not True): it always advances both polygons
      const m1 = asSeg(Segment(e1Current, e1Next)).distance(e2Next);
      const m2 = asSeg(Segment(e2Current, e2Next)).distance(e1Next);
      const cur = pyLt(m2, m1) ? m2 : m1;
      if (evalLt(cur, minDist)) minDist = cur;
      [e1Current, e1Next] = advance(c1, e1Current, e1Next);
      [e2Current, e2Next] = advance(c2, e2Current, e2Next);
      if (e1Current.key === e1Ymax.key && e2Current.key === e2Ymin.key) break;
    }
    return minDist;
  }

  /** SymPy `o in polygon`: o is the polygon, lies on a side, or is a vertex. */
  override contains(o: unknown): boolean {
    if (o instanceof PolygonNode) return polygonEquals(this, o);
    if (o instanceof SegmentNode) return this.sides.some((s) => s.contains(o));
    if (o instanceof PointNode) return this.vertices.some((v) => v.key === o.key) || this.sides.some((s) => s.contains(o));
    return false;
  }

  /**
   * The rays from the vertices that bisect the interior angles, with the
   * direction point evaluated to prec digits when given (SymPy bisectors).
   */
  bisectors(prec?: number): ExprMap<LinearEntity> {
    const b = new ExprMap<LinearEntity>();
    let pts = [...this.vertices, at(this.vertices, 0)];
    const cw = PolygonNode.isClockwise(at(pts, 0), at(pts, 1), at(pts, 2));
    if (cw) pts = pts.reverse();
    for (const [v, a] of this.angles) {
      const i = pts.findIndex((q) => q.key === v.key);
      const [p1, p2] = normalizeDimension([at(pts, i), at(pts, i + 1)]);
      let ray = asRay(Ray(d(p1), d(p2)).rotate(mul(a, S.Half), asPoint(v)));
      const dir = ray.direction;
      ray = Ray(ray.p1, ray.p1.add(dir.div(dir.distance([0, 0]))));
      if (prec !== undefined) ray = Ray(ray.p1, toPoint(ray.p2.evalf(prec)));
      b.set(v, ray);
    }
    return b;
  }

  /** SymPy GeometryEntity.encloses for a polygon: every vertex (and the center of a regular polygon) is enclosed. */
  override enclosedBy(container: GeometryEntity): boolean {
    if (this instanceof RegularPolygonNode && container.enclosesPoint(this.center) !== true) return false;
    return this.vertices.every((v) => container.enclosesPoint(v) === true);
  }

  /** The polygons are the same: equal vertices in the same cyclic order (SymPy ==). */
  override equals(o: ExprLike): boolean {
    return o instanceof PolygonNode && polygonEquals(this, o);
  }
}

/**
 * SymPy simplify(cond) == True for a condition of the arbitrary point: a
 * conjunction of comparisons of numbers, decided with the differences
 * simplified (a parameter at the end of a side compares equal).
 */
export function conditionHolds(c: Expr): boolean {
  if (c instanceof BoolAtom) return c.value;
  // the conditions are conjunctions of comparisons (And)
  if (c instanceof BoolOp) return c.args.every(conditionHolds);
  return tryDecide(c) === true;
}

/**
 * The bounding boxes of two segments with numeric end points are apart, so
 * the segments cannot meet (a shortcut before the exact intersection).
 */
function boxesApart(a: SegmentNode, b: SegmentNode): boolean {
  const box = (sg: SegmentNode): number[] | undefined => {
    if (sg.freeSymbols().size) return undefined;
    const [x1, y1, x2, y2] = [...sg.p1.args, ...sg.p2.args].map((c) => c.toNumber());
    return [Math.min(d(x1), d(x2)), Math.min(d(y1), d(y2)), Math.max(d(x1), d(x2)), Math.max(d(y1), d(y2))];
  };
  const [ba, bb] = [box(a), box(b)];
  if (ba === undefined || bb === undefined) return false;
  const [ax0, ay0, ax1, ay1] = ba.map(d);
  const [bx0, by0, bx1, by1] = bb.map(d);
  const eps = 1e-9 * (1 + Math.max(...ba.map(Math.abs), ...bb.map(Math.abs)));
  return d(ax1) < d(bx0) - eps || d(bx1) < d(ax0) - eps || d(ay1) < d(by0) - eps || d(by1) < d(ay0) - eps;
}

/** SymPy Polygon == Polygon (a RegularPolygon compares by its vertices with a polygon). */
function polygonEquals(a: PolygonNode, b: PolygonNode): boolean {
  if (a instanceof RegularPolygonNode && b instanceof RegularPolygonNode) return a.key === b.key;
  const ka = canonicalKeys(a.vertices);
  const kb = canonicalKeys(b.vertices);
  return ka.length === kb.length && ka.every((k, i) => k === kb[i]);
}

const d = <T>(e: T | undefined): T => defined(e, 'value');
const as2DLine = (e: Expr): Line2DNode => cast(e, Line2DNode, 'Line2DNode');
const asSeg = (e: Expr): SegmentNode => cast(e, SegmentNode, 'SegmentNode');
const asRay = (e: Expr): RayNode => cast(e, RayNode, 'RayNode');

const pyMin = (xs: readonly Expr[]): Expr => xs.reduce((m, x) => (pyLt(x, m) ? x : m));
const pyMax = (xs: readonly Expr[]): Expr => xs.reduce((m, x) => (pyGt(x, m) ? x : m));
const pyMax2 = (a: Expr, b: Expr): Expr => (pyGt(b, a) ? b : a);

/** SymPy RegularPolygon: a regular n-gon with a center, a radius and a rotation. */
export class RegularPolygonNode extends PolygonNode {
  readonly #args: Expr[];

  constructor(c: Point2DNode, r: Expr, n: Expr, rot: Expr) {
    const args = [c, r, n, rot];
    super(args, 'RegularPolygon');
    this.#args = args;
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newRegularPolygon(at(args, 0), at(args, 1), at(args, 2), at(args, 3));
  }

  /** The structural key follows the rotation, which spin changes. */
  override get key(): string {
    return `RegularPolygon(${this.#args.map((a) => a.key).join(',')})`;
  }

  /** The center, radius, number of sides and rotation evaluated numerically (SymPy _eval_evalf). */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    const [c, r, n, a] = this.#args;
    return newRegularPolygon(evalfArg(d(c)), evalfArg(d(r)), d(n), evalfArg(d(a)));
  }

  /** The signed area (SymPy area). */
  override get area(): Expr {
    // SymPy's order of the binary products: sign(r)*n*length**2/(4*tan(pi/n))
    const num = mul(mul(sign(this.radius), sideCount(this)), pow(this.length, 2));
    return mul(num, pow(mul(4, tan(mul(S.Pi, pow(sideCount(this), -1)))), -1));
  }


  /** The length of a side (SymPy length). */
  get length(): Expr {
    return mul(this.radius, 2, sin(mul(S.Pi, pow(sideCount(this), -1))));
  }

  /** The center (SymPy center). */
  get center(): Point2DNode {
    return as2D(at(this.#args, 0));
  }
  /** The centroid: the center (SymPy centroid). */
  override get centroid(): PointNode {
    return this.center;
  }
  /** The circumcenter: the center (SymPy circumcenter). */
  get circumcenter(): Point2DNode {
    return this.center;
  }
  /** The radius of the circumcircle (SymPy radius). */
  get radius(): Expr {
    return at(this.#args, 1);
  }
  /** The circumradius: the radius (SymPy circumradius). */
  get circumradius(): Expr {
    return this.radius;
  }
  /** The rotation angle (SymPy rotation). */
  get rotation(): Expr {
    return at(this.#args, 3);
  }
  /** The radius of the incircle (SymPy apothem). */
  get apothem(): Expr {
    return mul(this.radius, cos(mul(S.Pi, pow(sideCount(this), -1))));
  }
  /** The inradius: the apothem (SymPy inradius). */
  get inradius(): Expr {
    return this.apothem;
  }
  /** The interior angle (SymPy interior_angle). */
  get interiorAngle(): Expr {
    return mul(add(sideCount(this), -2), S.Pi, pow(sideCount(this), -1));
  }
  /** The exterior angle (SymPy exterior_angle). */
  get exteriorAngle(): Expr {
    return mul(2, S.Pi, pow(sideCount(this), -1));
  }
  /** The circumscribed circle (SymPy circumcircle). */
  get circumcircle(): GeometryEntity {
    return newCircle(this.center, this.radius);
  }
  /** The inscribed circle (SymPy incircle). */
  get incircle(): GeometryEntity {
    return newCircle(this.center, this.apothem);
  }
  /** The interior angle at every vertex (SymPy angles). */
  override get angles(): ExprMap<Expr> {
    const ang = this.interiorAngle;
    return new ExprMap(this.vertices.map((v): [Expr, Expr] => [v, ang]));
  }

  /** The point lies inside the polygon (SymPy encloses_point). */
  override enclosesPoint(p: PointInput): boolean | 'unknown' {
    const c = this.center;
    const dist = asSegLength(Segment(c, p));
    if (decide(Le(this.radius, dist))) return false;
    if (pyLt(dist, this.inradius)) return true;
    return super.enclosesPoint(p);
  }

  /** Rotate the polygon in place about its center (SymPy spin). */
  spin(angle: ExprLike): void {
    this.#args[3] = add(d(this.#args[3]), angle);
  }

  /** The polygon rotated about pt (SymPy rotate). */
  override rotate(angle: ExprLike, pt?: PointInput | null): GeometryEntity {
    const [c, r, n, rot] = this.#args;
    const rp = new RegularPolygonNode(as2D(d(c)), d(r), d(n), d(rot));
    rp.spin(angle);
    return GeometryEntity.prototype.rotate.call(rp, angle, pt);
  }

  /** The polygon scaled by x and y about pt: a regular polygon when x == y (SymPy scale). */
  override scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): GeometryEntity {
    if (pt !== undefined && pt !== null) return GeometryEntity.prototype.scale.call(this, x, y, pt);
    if (!same(sympify(x), y)) return newPolygon(this.vertices).scale(x, y);
    const [c, r, n, rot] = this.#args;
    return newRegularPolygon(d(c), mul(d(r), x), d(n), d(rot));
  }

  /** The reflection in a line (SymPy reflect). */
  override reflect(line: Parameters<GeometryEntity['reflect']>[0]): GeometryEntity {
    const [c, r, n, rot0] = this.#args;
    const v = at(this.vertices, 0);
    const dv = v.sub(d(c));
    const cc = asPoint(asPoint(d(c)).reflect(line));
    const vv = asPoint(v.reflect(line));
    const dd = vv.sub(cc);
    const l1 = cast(Ray([0, 0], dd), Ray2DNode, 'Ray2D');
    const ang = l1.closingAngle(cast(Ray([0, 0], dv), Ray2DNode, 'Ray2D'));
    return newRegularPolygon(cc, mul(-1, d(r)), d(n), add(d(rot0), ang));
  }

  /** The vertices (SymPy vertices). */
  override get vertices(): PointNode[] {
    const c = this.center;
    const r = absExpr(this.radius);
    const rot = this.rotation;
    const v = mul(2, S.Pi, pow(sideCount(this), -1));
    const n = Number(asRational(sideCount(this)).p);
    return Array.from({ length: n }, (_, k) => toPoint([add(c.x, mul(r, cos(add(mul(k, v), rot)))), add(c.y, mul(r, sin(add(mul(k, v), rot))))]));
  }

}

/** The number of sides of a regular polygon (SymPy _n). */
const sideCount = (p: RegularPolygonNode): Expr => at(p.args, 2);

const asRational = (e: Expr): Rational => expectType(e, (v): v is Rational => v instanceof Rational, 'the number of sides');
const asSegLength = (e: Expr): Expr => (e instanceof SegmentNode ? e.length : S.Zero);

/** SymPy Triangle: a polygon with three vertices. */
export class TriangleNode extends PolygonNode {
  constructor(vertices: readonly PointNode[]) {
    super(vertices, 'Triangle');
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newTriangle(args.map(asPoint));
  }

  /** The triangles are similar (SymPy is_similar). */
  override isSimilar(t2: GeometryEntity): boolean {
    if (!(t2 instanceof PolygonNode)) return false;
    const [a1, a2, a3] = this.sides.map((s) => s.length);
    const s2 = t2.sides.map((s) => s.length);
    const sim = (u1: Expr, u2: Expr, u3: Expr): boolean => {
      const e1 = simplify(mul(u1, pow(at(s2, 0), -1)));
      const e2 = simplify(mul(u2, pow(at(s2, 1), -1)));
      const e3 = simplify(mul(u3, pow(at(s2, 2), -1)));
      return same(e1, e2) && same(e2, e3);
    };
    const [A, B, C] = [d(a1), d(a2), d(a3)];
    return sim(A, B, C) || sim(A, C, B) || sim(B, A, C) || sim(B, C, A) || sim(C, A, B) || sim(C, B, A);
  }

  /** All sides have the same length (SymPy is_equilateral). */
  isEquilateral(): boolean {
    return new Set(this.sides.map((s) => s.length.key)).size <= 1;
  }

  /** Two sides have the same length (SymPy is_isosceles). */
  isIsosceles(): boolean {
    return new Set(this.sides.map((s) => s.length.key)).size < 3;
  }

  /** All sides have different lengths (SymPy is_scalene). */
  isScalene(): boolean {
    return new Set(this.sides.map((s) => s.length.key)).size === 3;
  }

  /** The triangle has a right angle (SymPy is_right). */
  isRight(): boolean {
    const [s0, s1, s2] = this.sides.map(d);
    const [a, b, c] = [d(s0), d(s1), d(s2)];
    return a.isPerpendicular(b) || b.isPerpendicular(c) || a.isPerpendicular(c);
  }

  /** The altitude from each vertex (SymPy altitudes). */
  get altitudes(): ExprMap<Expr> {
    const s = this.sides;
    const v = this.vertices;
    return new ExprMap<Expr>([
      [at(v, 0), at(s, 1).perpendicularSegment(at(v, 0))],
      [at(v, 1), at(s, 2).perpendicularSegment(at(v, 1))],
      [at(v, 2), at(s, 0).perpendicularSegment(at(v, 2))],
    ]);
  }

  /** The intersection of the altitudes (SymPy orthocenter). */
  get orthocenter(): PointNode {
    const a = this.altitudes;
    const v = this.vertices;
    const l0 = Line(d(a.get(at(v, 0))));
    const l1 = Line(d(a.get(at(v, 1))));
    return asPoint(at(l0.intersection(l1), 0));
  }

  /** The center of the circumcircle (SymPy circumcenter). */
  get circumcenter(): PointNode {
    const [a, b] = this.sides.map((x) => x.perpendicularBisector());
    return asPoint(at(d(a).intersection(d(b)), 0));
  }

  /** The radius of the circumcircle (SymPy circumradius). */
  get circumradius(): Expr {
    return this.circumcenter.distance(at(this.vertices, 0));
  }

  /** The circle through the vertices (SymPy circumcircle). */
  get circumcircle(): GeometryEntity {
    return newCircle(this.circumcenter, this.circumradius);
  }

  /** The angle bisectors from each vertex to the opposite side (SymPy Triangle.bisectors). */
  override bisectors(): ExprMap<LinearEntity> {
    const s = this.sides.map((l) => Line(l));
    const v = this.vertices;
    const c = this.incenter;
    const seg = (i: number, j: number): LinearEntity => asSeg(Segment(at(v, i), asPoint(at(Line(at(v, i), c).intersection(at(s, j)), 0))));
    return new ExprMap<LinearEntity>([
      [at(v, 0), seg(0, 1)],
      [at(v, 1), seg(1, 2)],
      [at(v, 2), seg(2, 0)],
    ]);
  }

  /** The center of the incircle (SymPy incenter). */
  get incenter(): PointNode {
    const s = this.sides;
    const l = [1, 2, 0].map((i) => at(s, i).length);
    const p = add(...l);
    const v = this.vertices;
    const x = simplify(mul(add(...l.map((li, i) => mul(li, at(v, i).coordinate(0)))), pow(p, -1)));
    const y = simplify(mul(add(...l.map((li, i) => mul(li, at(v, i).coordinate(1)))), pow(p, -1)));
    return toPoint([x, y]);
  }

  /** The radius of the incircle (SymPy inradius). */
  get inradius(): Expr {
    return simplify(mul(2, this.area, pow(this.perimeter, -1)));
  }

  /** The inscribed circle (SymPy incircle). */
  get incircle(): GeometryEntity {
    return newCircle(this.incenter, this.inradius);
  }

  /** The radius of the excircle opposite each side (SymPy exradii). */
  get exradii(): ExprMap<Expr> {
    const side = this.sides;
    const [a, b, c] = side.map((x) => x.length);
    const s = mul(add(d(a), d(b), d(c)), S.Half);
    const area = this.area;
    return new ExprMap<Expr>([
      [at(side, 0), simplify(mul(area, pow(add(s, mul(-1, d(a))), -1)))],
      [at(side, 1), simplify(mul(area, pow(add(s, mul(-1, d(b))), -1)))],
      [at(side, 2), simplify(mul(area, pow(add(s, mul(-1, d(c))), -1)))],
    ]);
  }

  /** The center of the excircle opposite each side, by SymPy's formula (SymPy excenters). */
  get excenters(): ExprMap<Expr> {
    const s = this.sides;
    const v = this.vertices;
    const [a, b, c] = s.map((x) => x.length).map(d);
    const [A, B, C] = [d(a), d(b), d(c)];
    const xs = v.map((p) => p.coordinate(0));
    const ys = v.map((p) => p.coordinate(1));
    const coord = (w: readonly Expr[], sa: number, sb: number, sc: number): Expr =>
      simplify(add(mul(sa, A, at(w, 0)), mul(sb, B, at(w, 1)), mul(sc, C, at(w, 2), pow(add(mul(sa, A), mul(sb, B), mul(sc, C)), -1))));
    return new ExprMap<Expr>([
      [at(s, 0), toPoint([coord(xs, -1, 1, 1), coord(ys, -1, 1, 1)])],
      [at(s, 1), toPoint([coord(xs, 1, -1, 1), coord(ys, 1, -1, 1)])],
      [at(s, 2), toPoint([coord(xs, 1, 1, -1), coord(ys, 1, 1, -1)])],
    ]);
  }

  /** The median from each vertex (SymPy medians). */
  get medians(): ExprMap<Expr> {
    const s = this.sides;
    const v = this.vertices;
    return new ExprMap<Expr>([
      [at(v, 0), Segment(at(v, 0), at(s, 1).midpoint)],
      [at(v, 1), Segment(at(v, 1), at(s, 2).midpoint)],
      [at(v, 2), Segment(at(v, 2), at(s, 0).midpoint)],
    ]);
  }

  /** The triangle of the midpoints of the sides (SymPy medial). */
  get medial(): GeometryEntity {
    const s = this.sides;
    return newTriangle([at(s, 0).midpoint, at(s, 1).midpoint, at(s, 2).midpoint]);
  }

  /** The nine-point circle (SymPy nine_point_circle). */
  get ninePointCircle(): GeometryEntity {
    const m = cast(this.medial, PolygonNode, 'Triangle');
    const [a, b, c] = m.vertices;
    return newCircle(d(a), d(b), d(c));
  }

  /** The Euler line, or the orthocenter of an equilateral triangle (SymPy eulerline). */
  get eulerline(): GeometryEntity {
    if (this.isEquilateral()) return this.orthocenter;
    return Line(this.orthocenter, this.circumcenter);
  }
}

// ---------------------------------------------------------------------------
// construction
// ---------------------------------------------------------------------------

/** The vertices without consecutive duplicates and a repeated first vertex. */
function dedupe(vertices: readonly PointNode[]): PointNode[] {
  const nodup: PointNode[] = [];
  for (const p of vertices) {
    const lastP = nodup[nodup.length - 1];
    if (lastP !== undefined && p.key === lastP.key) continue;
    nodup.push(p);
  }
  if (nodup.length > 1 && at(nodup, -1).key === at(nodup, 0).key) nodup.pop();
  return nodup;
}

/** SymPy Polygon.__new__ for vertices: collinear vertices removed, then a Polygon, Triangle, Segment or Point. */
export function newPolygon(points: readonly PointInput[], opts: { evaluate?: boolean } = {}): GeometryEntity {
  const vertices = points.map((a) => toPoint(a, { dim: 2, ...opts }));
  const nodup = dedupe(vertices);
  let i = -3;
  while (i < nodup.length - 3 && nodup.length > 2) {
    const n = nodup.length;
    const [a, b, c] = [at(nodup, idx(n, i)), at(nodup, idx(n, i + 1)), at(nodup, idx(n, i + 2))];
    if (a.isCollinear(b, c)) {
      nodup.splice(idx(n, i + 1), 1);
      if (a.key === c.key) nodup.splice(idx(nodup.length, i), 1);
    } else i++;
  }
  if (nodup.length > 3) return new PolygonNode(nodup);
  if (nodup.length === 3) return newTriangle(nodup);
  if (nodup.length === 2) return Segment(at(nodup, 0), at(nodup, 1));
  return toPoint(at(nodup, 0));
}

/** SymPy Triangle.__new__ for three vertices: a Triangle, or the Segment or Point it degenerates to. */
export function newTriangle(points: readonly PointInput[], opts: { evaluate?: boolean } = {}): GeometryEntity {
  const vertices = points.map((a) => toPoint(a, { dim: 2, ...opts }));
  const nodup: (PointNode | undefined)[] = dedupe(vertices);
  let i = -3;
  while (i < nodup.length - 3 && nodup.length > 2) {
    const n = nodup.length;
    const sorted = [at(nodup, idx(n, i)), at(nodup, idx(n, i + 1)), at(nodup, idx(n, i + 2))]
      .map(d)
      .sort((p, q) => compareKeys(sortKey(p), sortKey(q)));
    const [a, b, c] = sorted.map(d);
    if (d(a).isCollinear(d(b), d(c))) {
      nodup[idx(n, i)] = a;
      nodup.splice(idx(n, i + 1), 1);
    }
    i++;
  }
  const vs = nodup.filter((x): x is PointNode => x !== undefined);
  if (vs.length === 3) return new TriangleNode(vs);
  if (vs.length === 2) return Segment(at(vs, 0), at(vs, 1));
  return toPoint(at(vs, 0));
}

/** SymPy RegularPolygon.__new__(c, r, n, rot=0). */
export function newRegularPolygon(cIn: PointInput, rIn: ExprLike, nIn: ExprLike, rotIn: ExprLike = 0): RegularPolygonNode {
  const [r, n, rot] = [rIn, nIn, rotIn].map(sympify);
  const c = as2D(toPoint(cIn, { dim: 2 }));
  if (d(r) instanceof GeometryEntity) throw new GeometryError(`r must be an Expr object, not ${String(r)}`);
  if (d(n) instanceof Rational || d(n).isNumber) {
    if (!(d(n) instanceof Rational) || !asRational(d(n)).isInteger) throw new RangeError(`${String(n)} is not an integer`);
    if (asRational(d(n)).p < 3n) throw new GeometryError(`n must be a >= 3, not ${String(n)}`);
  }
  const R = d(rot);
  const rv = R.freeSymbols().size === 0 ? Mod(R, mul(2, S.Pi, pow(d(n), -1))) : R;
  return new RegularPolygonNode(c, d(r), d(n), rv);
}

/** Degrees to radians (SymPy rad). */
export function rad(deg_: ExprLike): Expr {
  return mul(deg_, S.Pi, Rational.of(1n, 180n));
}

/** Radians to degrees (SymPy deg). */
export function deg(r: ExprLike): Expr {
  return mul(r, pow(S.Pi, -1), 180);
}

const slopeOf = (dg: Expr): Expr => tan(rad(dg));

/** SymPy _asa: the triangle with angle d1, side l and angle d2. */
function asa(d1: Expr, l: Expr, d2: Expr): GeometryEntity {
  const xy = at(Line([0, 0], { slope: slopeOf(d1) }).intersection(Line([l, 0], { slope: slopeOf(add(180, mul(-1, d2))) })), 0);
  return newTriangle([[0, 0], [l, 0], asPoint(xy)]);
}

/** SymPy _sss: the triangle with sides l1, l2, l3 (GeometryError when there is none; SymPy returns None). */
function sss(l1: Expr, l2: Expr, l3: Expr): GeometryEntity {
  const c1 = newCircle([0, 0], l3);
  const c2 = newCircle([l1, 0], l2);
  const inter = c1.intersection(c2).filter((a) => a instanceof PointNode && isNonNegative(a.coordinate(1)) === true);
  const pt = inter[0];
  if (pt === undefined) throw new GeometryError('There is no triangle with these sides.');
  return newTriangle([[0, 0], [l1, 0], asPoint(pt)]);
}

/** SymPy _sas: the triangle with sides l1, l2 and the angle d between them. */
function sas(l1: Expr, dg: Expr, l2: Expr): GeometryEntity {
  return newTriangle([[0, 0], [l2, 0], [mul(cos(rad(dg)), l1), mul(sin(rad(dg)), l1)]]);
}

/** Options of Polygon (SymPy n: a regular polygon). */
export interface PolygonOptions {
  /** The number of sides of a regular polygon (Polygon(center, radius, {n})). */
  n?: number;
  /** Convert Floats to Rationals (default true). */
  evaluate?: boolean;
}

/** Options of Triangle (SymPy sss, asa, sas). */
export interface TriangleOptions {
  /** Three side lengths. */
  sss?: readonly ExprLike[];
  /** Angle, side, angle (degrees). */
  asa?: readonly ExprLike[];
  /** Side, angle (degrees), side. */
  sas?: readonly ExprLike[];
  /** Convert Floats to Rationals (default true). */
  evaluate?: boolean;
}

const evaluateOpt = (o: Record<string, unknown>): { evaluate?: boolean } => (typeof o['evaluate'] === 'boolean' ? { evaluate: o['evaluate'] } : {});
const triple = (v: unknown): Expr[] | undefined => (Array.isArray(v) ? v.map((x) => simplify(sympify(x))) : undefined);

/**
 * SymPy Polygon(*vertices): a Polygon, Triangle, Segment or Point;
 * Polygon(center, radius, {n}) or Polygon(center, radius, rot, {n}) is a
 * RegularPolygon.
 */
export const Polygon = /* @__PURE__ */ callableClass(PolygonNode, (...args: (PointInput | ExprLike | PolygonOptions)[]): GeometryEntity => {
  const last = args[args.length - 1];
  const o = isOptions(last) ? last : {};
  const pos = isOptions(last) ? args.slice(0, -1) : args;
  const n = o['n'];
  if (typeof n === 'number' && n !== 0) {
    const [c, r, rot] = pos;
    return newRegularPolygon(toInput(c), exprLike(r), n, rot === undefined ? 0 : exprLike(rot));
  }
  return newPolygon(pos.map(toInput), evaluateOpt(o));
});
export type Polygon = PolygonNode;

const exprLike = (v: unknown): ExprLike => {
  if (v instanceof Expr || typeof v === 'number' || typeof v === 'bigint') return v;
  throw new TypeError(`Expecting an expression, not ${typeof v}`);
};

/** SymPy RegularPolygon(c, r, n, rot=0). */
export const RegularPolygon = /* @__PURE__ */ callableClass(
  RegularPolygonNode,
  (c: PointInput, r: ExprLike, n: ExprLike, rot: ExprLike = 0): RegularPolygonNode => newRegularPolygon(c, r, n, rot),
);
export type RegularPolygon = RegularPolygonNode;

/**
 * SymPy Triangle(p1, p2, p3), or Triangle({sss}), Triangle({asa}),
 * Triangle({sas}) from sides and angles in degrees.
 */
export const Triangle = /* @__PURE__ */ callableClass(TriangleNode, (...args: (PointInput | TriangleOptions)[]): GeometryEntity => {
  const last = args[args.length - 1];
  const o = isOptions(last) ? last : {};
  const pos = isOptions(last) ? args.slice(0, -1) : args;
  if (pos.length !== 3) {
    const s = triple(o['sss']);
    if (s) return sss(d(s[0]), d(s[1]), d(s[2]));
    const a = triple(o['asa']);
    if (a) return asa(d(a[0]), d(a[1]), d(a[2]));
    const b = triple(o['sas']);
    if (b) return sas(d(b[0]), d(b[1]), d(b[2]));
    throw new GeometryError('Triangle instantiates with three points or a valid keyword.');
  }
  return newTriangle(pos.map(toInput), evaluateOpt(o));
});
export type Triangle = TriangleNode;

utilClasses.polygon = (...vertices) => newPolygon(vertices);
utilClasses.segment = (p1, p2) => Segment(p1, p2);
ellipseHooks.circumcircle = (a, b, c) => {
  const t = newTriangle([a, b, c]);
  return t instanceof TriangleNode ? [t.circumcenter, t.circumradius] : t;
};

