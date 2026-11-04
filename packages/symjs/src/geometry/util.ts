// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/util.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.util: functions of several geometric entities
 * (intersection, convex_hull, centroid, closest_points, farthest_points,
 * are_similar, are_coplanar) and implicit differentiation (idiff).
 *
 * The functions that build segments, polygons or planes use the
 * constructors registered by those modules (which import this one).
 */

import { Expr, Float, Rational, S, Sym, UndefFn } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { subs, xreplace } from '../core/traverse';
import { atoms } from '../core/methods';
import { ordered } from '../core/match';
import { ExprMap } from '../core/exprmap';
import { SymFunction } from '../core/undef';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, expectType, pair } from '../core/guard';
import { diff } from '../calculus/diff';
import { nsimplify } from '../numeric/nfloat';
import { precToDps } from '../numeric/mpf';
import { cancel } from '../simplify/rational';
import { expand } from '../simplify/expand';
import { factorTerms } from '../simplify/exprtools';
import { simplify } from '../simplify/simplify';
import { GeometryEntity, decide } from './entity';
import type { PointInput } from './entity';
import { Point3DNode, PointNode, toInput, toPoint, uniqPoints } from './point';
import { Gt, Lt } from '../core/logic';
import { SetExpr, intersection as setIntersection } from '../sets/sets';

/** A segment as util uses it (SymPy Segment). */
interface SegmentLike extends GeometryEntity {
  readonly length: Expr;
  readonly midpoint: PointNode;
  readonly points: readonly [PointNode, PointNode];
}

/** A polygon as util uses it (SymPy Polygon). */
interface PolygonLike extends GeometryEntity {
  readonly area: Expr;
  readonly centroid: PointNode;
  readonly vertices: readonly PointNode[];
}

/** A plane as util uses it (SymPy Plane). */
interface PlaneLike extends GeometryEntity {
  isCoplanar(o: GeometryEntity): boolean;
}

/** The constructors of the entity modules that import this one, registered when they load. */
export const utilClasses: {
  segment?: (p1: PointNode, p2: PointNode) => GeometryEntity;
  polygon?: (...vertices: PointNode[]) => GeometryEntity;
  plane?: (p1: PointNode, p2: PointNode, p3: PointNode) => GeometryEntity;
} = {};

const isSegment = (e: unknown): e is SegmentLike => e instanceof GeometryEntity && e.name.startsWith('Segment');
const isPolygon = (e: unknown): e is PolygonLike => e instanceof GeometryEntity && ['Polygon', 'Triangle', 'RegularPolygon'].includes(e.name);
const isPlane = (e: unknown): e is PlaneLike => e instanceof GeometryEntity && e.name === 'Plane';
const isLinear3D = (e: GeometryEntity): boolean => ['Line3D', 'Ray3D', 'Segment3D'].includes(e.name);

/** SymPy expand_mul(e, deep=False). */
const EXPAND_MUL_SHALLOW = { deep: false, mul: true, multinomial: false, power_exp: false, power_base: false, log: false } as const;

/** Rational(v) of a JS float: its exact binary value (SymPy Rational(float)). */
export const rationalOf = (v: number): Expr => nsimplify(new Float(v), { rational: true, rationalConversion: 'exact' });

/**
 * The free symbol of the equation that is x or is named x (SymPy find);
 * RangeError when there is none or several.
 */
export function find(x: string | Sym, equation: Expr): Sym {
  const xs = [...equation.freeSymbols()].filter((i) => (typeof x === 'string' ? i.name === x : i.key === x.key));
  if (xs.length === 0) throw new RangeError(`could not find ${String(x)}`);
  if (xs.length !== 1) throw new RangeError(`ambiguous ${String(x)}`);
  return at(xs, 0);
}

/**
 * The entities common to all the given entities (SymPy intersection); with
 * `pairwise: true`, those common to any two of them. Floats are converted
 * to Rationals for the computation and back at their least precision.
 */
export function intersection(...args: SetExpr[]): SetExpr;
export function intersection(...args: (GeometryEntity | PointInput | { pairwise?: boolean })[]): GeometryEntity[];
export function intersection(...args: (GeometryEntity | PointInput | SetExpr | { pairwise?: boolean })[]): GeometryEntity[] | SetExpr {
  // sets that are not geometric entities: their set intersection (SymPy Intersection)
  if (args.length && args.every((a): a is SetExpr => a instanceof SetExpr)) return setIntersection(...args);
  return geometryIntersection(args.filter((a): a is GeometryEntity | PointInput | { pairwise?: boolean } => !(a instanceof SetExpr)));
}

/** SymPy geometry.util.intersection. */
function geometryIntersection(args: readonly (GeometryEntity | PointInput | { pairwise?: boolean })[]): GeometryEntity[] {
  const last = args[args.length - 1];
  const optsObj = typeof last === 'object' && !(last instanceof Expr) && !Array.isArray(last) ? last : undefined;
  const pairwise = optsObj !== undefined && 'pairwise' in optsObj && optsObj.pairwise === true;
  const items = optsObj === undefined ? args : args.slice(0, -1);
  if (items.length <= 1) return [];
  let prec: number | undefined;
  const entities = items.map((a) => {
    const e = a instanceof GeometryEntity ? a : toPoint(toInput(a));
    const reps = atoms(e, (f) => f instanceof Float).map((f): [Expr, Expr] => {
      const p = cast(f, Float, 'Float').prec;
      prec = prec === undefined ? p : Math.min(p, prec);
      return [f, nsimplify(f, { rational: true })];
    });
    return reps.length ? cast(xreplace(e, reps), GeometryEntity, 'geometry entity') : e;
  });
  let res: GeometryEntity[];
  if (!pairwise) {
    res = at(entities, 0).intersection(at(entities, 1));
    for (const entity of entities.slice(2)) res = res.flatMap((x) => x.intersection(entity));
  } else {
    const ans: GeometryEntity[] = [];
    for (let j = 0; j < entities.length; j++) {
      for (let k = j + 1; k < entities.length; k++) ans.push(...geometryIntersection([at(entities, j), at(entities, k)]));
    }
    res = ordered(uniqPoints(ans)).filter((e): e is GeometryEntity => e instanceof GeometryEntity);
  }
  if (prec !== undefined) {
    const p = precToDps(prec);
    res = res.map((i) => cast(i.evalf(p), GeometryEntity, 'geometry entity'));
  }
  return res;
}

/**
 * The two entities are similar (SymPy are_similar). Every entity has
 * is_similar, so SymPy's GeometryError for entities without it does not
 * occur; entities that cannot decide raise NotImplementedError.
 */
export function areSimilar(e1: GeometryEntity, e2: GeometryEntity): boolean {
  if (e1.key === e2.key) return true;
  return e1.isSimilar(e2);
}

/**
 * The centroid of points, segments (weighted by length) or polygons
 * (weighted by area) (SymPy centroid).
 */
export function centroid(...args: GeometryEntity[]): PointNode {
  if (args.length === 0) throw new RangeError('centroid of no entities');
  let c: PointNode = toPoint([0, 0]);
  let den: Expr;
  if (args.every((g) => g instanceof PointNode)) {
    for (const g of args) c = c.add(g);
    den = Rational.of(BigInt(args.length));
  } else if (args.every(isSegment)) {
    let L: Expr = S.Zero;
    for (const g of args) {
      const l = g.length;
      c = c.add(g.midpoint.mul(l));
      L = add(L, l);
    }
    den = L;
  } else if (args.every(isPolygon)) {
    let A: Expr = S.Zero;
    for (const g of args) {
      const a = g.area;
      c = c.add(g.centroid.mul(a));
      A = add(A, a);
    }
    den = A;
  } else throw new TypeError('centroid of points, segments or polygons only');
  c = c.div(den);
  return toPoint(c.args.map((i) => simplify(i)), { evaluate: false });
}

/** The coordinates of points as numbers or expressions sorted like Python tuples (SymPy sort by args). */
function sortPoints(ps: PointNode[]): PointNode[] {
  const cmp = (a: Expr, b: Expr): number => (decide(Lt(a, b)) ? -1 : decide(Gt(a, b)) ? 1 : 0);
  try {
    return [...ps].sort((p, q) => cmp(p.coordinate(0), q.coordinate(0)) || cmp(p.coordinate(1), q.coordinate(1)));
  } catch {
    // an undecidable comparison (SymPy TypeError)
    throw new RangeError('The points could not be sorted.');
  }
}

/** The distance function of closest_points: exact for symbolic or irrational points, else floats. */
function hypotFor(p: readonly PointNode[]): (x: Expr, y: Expr) => Expr | number {
  if (!p.every((q) => q.args.every((i) => i instanceof Rational))) {
    return (x, y) => {
      const arg = add(mul(x, x), mul(y, y));
      return arg instanceof Rational ? Math.sqrt(Number(arg.p) / Number(arg.q)) : sqrt(arg);
    };
  }
  return (x, y) => Math.hypot(Number(x.toNumber()), Number(y.toNumber()));
}

const lessThan = (a: Expr | number, b: Expr | number): boolean =>
  typeof a === 'number' && typeof b === 'number' ? a < b : decide(Lt(typeof a === 'number' ? new Float(a) : a, typeof b === 'number' ? new Float(b) : b));
const sameValue = (a: Expr | number, b: Expr | number): boolean => (typeof a === 'number' && typeof b === 'number' ? a === b : sympify(a).key === sympify(b).key);

/** The distinct 2D points of the arguments (SymPy [Point2D(i) for i in set(args)]). */
const distinct2D = (args: readonly PointInput[]): PointNode[] => uniqPoints(args.map((a) => toPoint(a, { dim: 2 })));

/** The pairs of points at the smallest distance, as a set of [p, q] pairs (SymPy closest_points). */
export function closestPoints(...args: PointInput[]): Set<[PointNode, PointNode]> {
  let p = distinct2D(args);
  if (p.length < 2) throw new RangeError('At least 2 distinct points must be given.');
  p = sortPoints(p);
  const hypot = hypotFor(p);
  const P = (i: number): PointNode => at(p, i);
  let rv: [number, number][] = [[0, 1]];
  let best = hypot(add(P(1).coordinate(0), mul(-1, P(0).coordinate(0))), add(P(1).coordinate(1), mul(-1, P(0).coordinate(1))));
  let left = 0;
  const box: number[] = [0, 1];
  for (let i = 2; i < p.length; i++) {
    while (left < i && lessThan(best, add(P(i).coordinate(0), mul(-1, P(left).coordinate(0))))) {
      box.shift();
      left++;
    }
    for (const j of box) {
      const d = hypot(add(P(i).coordinate(0), mul(-1, P(j).coordinate(0))), add(P(i).coordinate(1), mul(-1, P(j).coordinate(1))));
      if (lessThan(d, best)) rv = [[j, i]];
      else if (sameValue(d, best)) rv.push([j, i]);
      else continue;
      best = d;
    }
    box.push(i);
  }
  return new Set(rv.map(([i, j]): [PointNode, PointNode] => [P(i), P(j)]));
}

/**
 * The convex hull of points, segments and polygons: a Polygon, a Segment
 * or a Point (SymPy convex_hull). With `polygon: false`, the upper and
 * lower hulls [U, L] (or [entity, undefined] for fewer than three points).
 */
export function convexHull(...args: (GeometryEntity | PointInput | { polygon?: boolean })[]): GeometryEntity | [GeometryEntity | PointNode[], PointNode[] | undefined] {
  const last = args[args.length - 1];
  const optsObj = typeof last === 'object' && !(last instanceof Expr) && !Array.isArray(last) ? last : undefined;
  const polygon = !(optsObj !== undefined && 'polygon' in optsObj && optsObj.polygon === false);
  const items = optsObj === undefined ? args : args.slice(0, -1);
  const pts: PointNode[] = [];
  for (const a of items) {
    let e: GeometryEntity;
    if (a instanceof GeometryEntity) e = a;
    else e = toPoint(toInput(a));
    if (e instanceof PointNode) pts.push(e);
    else if (isSegment(e)) pts.push(...e.points);
    else if (isPolygon(e)) pts.push(...e.vertices);
    else throw new NotImplementedError(`Convex hull for ${e.name} not implemented.`);
  }
  let p = uniqPoints(pts);
  if (p.some((x) => x.args.length !== 2)) throw new RangeError('Can only compute the convex hull in two dimensions');
  const seg = (a: PointNode, b: PointNode): GeometryEntity => defined(utilClasses.segment, 'Segment')(a, b);
  if (p.length === 1) return polygon ? at(p, 0) : [at(p, 0), undefined];
  if (p.length === 2) {
    const s = seg(at(p, 0), at(p, 1));
    return polygon ? s : [s, undefined];
  }
  const orientation = (a: PointNode, b: PointNode, c: PointNode): Expr =>
    add(mul(add(b.coordinate(1), mul(-1, a.coordinate(1))), add(c.coordinate(0), mul(-1, a.coordinate(0)))), mul(-1, add(b.coordinate(0), mul(-1, a.coordinate(0))), add(c.coordinate(1), mul(-1, a.coordinate(1)))));
  const U: PointNode[] = [];
  const L: PointNode[] = [];
  p = sortPoints(p);
  for (const pi of p) {
    while (U.length > 1 && !decide(Gt(orientation(at(U, -2), at(U, -1), pi), 0))) U.pop();
    while (L.length > 1 && !decide(Lt(orientation(at(L, -2), at(L, -1), pi), 0))) L.pop();
    U.push(pi);
    L.push(pi);
  }
  U.reverse();
  const hull = [...L, ...U.slice(1, -1)];
  if (hull.length === 2) {
    const s = seg(at(hull, 0), at(hull, 1));
    return polygon ? s : [s, undefined];
  }
  if (polygon) return defined(utilClasses.polygon, 'Polygon')(...hull);
  U.reverse();
  return [U, L];
}

/** The pairs of points at the largest distance, as a set of [p, q] pairs (SymPy farthest_points). */
export function farthestPoints(...args: PointInput[]): Set<[PointNode, PointNode]> {
  const p = distinct2D(args);
  const hypot = hypotFor(p);
  const pairs: [PointNode, PointNode][] = [];
  const [U, L] = expectType(convexHull(...p, { polygon: false }), (v): v is [GeometryEntity | PointNode[], PointNode[] | undefined] => Array.isArray(v), 'hull');
  if (L === undefined) {
    if (U instanceof PointNode) throw new RangeError('At least two distinct points must be given.');
    const seg = cast(U, GeometryEntity, 'Segment');
    pairs.push([toPoint(at(seg.args, 0)), toPoint(at(seg.args, 1))]);
  } else {
    const up = expectType(U, (v): v is PointNode[] => Array.isArray(v), 'upper hull');
    let i = 0;
    let j = L.length - 1;
    while (i < up.length - 1 || j > 0) {
      pairs.push([at(up, i), at(L, j)]);
      if (i === up.length - 1) j--;
      else if (j === 0) i++;
      else {
        const [ui, ui1, lj, lj1] = [at(up, i), at(up, i + 1), at(L, j), at(L, j - 1)];
        const lhs = mul(add(ui1.coordinate(1), mul(-1, ui.coordinate(1))), add(lj.coordinate(0), mul(-1, lj1.coordinate(0))));
        const rhs = mul(add(lj.coordinate(1), mul(-1, lj1.coordinate(1))), add(ui1.coordinate(0), mul(-1, ui.coordinate(0))));
        if (decide(Gt(lhs, rhs))) i++;
        else j--;
      }
    }
  }
  let rv: [PointNode, PointNode][] = [];
  let diam: Expr | number = 0;
  for (const pr of pairs) {
    const [h, q] = pair(sortPoints([...pr]));
    const d = hypot(add(h.coordinate(0), mul(-1, q.coordinate(0))), add(h.coordinate(1), mul(-1, q.coordinate(1))));
    if (lessThan(diam, d)) rv = [[h, q]];
    else if (sameValue(d, diam)) rv.push([h, q]);
    else continue;
    diam = d;
  }
  const seen = new Set<string>();
  return new Set(rv.filter(([h, q]) => !seen.has(h.key + q.key) && Boolean(seen.add(h.key + q.key))));
}

/** The entities lie in one plane (SymPy are_coplanar). */
export function areCoplanar(...eIn: GeometryEntity[]): boolean {
  const e = uniqPoints(eIn);
  const plane = e.find(isPlane);
  if (plane !== undefined) return e.filter((i) => i !== plane).every((p) => plane.isCoplanar(p));
  if (e.every((i) => i instanceof Point3DNode)) {
    if (e.length < 3) return false;
    const pts = e.filter((i): i is Point3DNode => i instanceof Point3DNode);
    const a = defined(pts.pop());
    const b = defined(pts.pop());
    const rest = pts.filter((i) => !Point3DNode.areCollinear(a, b, i));
    const c = rest.pop();
    if (c === undefined) return false;
    const p = defined(utilClasses.plane, 'Plane')(a, b, c);
    return rest.every((i) => p.contains(i));
  }
  const pt3d: PointNode[] = [];
  for (const i of e) {
    if (i instanceof Point3DNode) pt3d.push(i);
    else if (isLinear3D(i)) pt3d.push(...i.args.filter((a): a is PointNode => a instanceof PointNode));
    else for (const p of i.args) if (p instanceof PointNode) pt3d.push(toPoint([...p.args, 0]));
  }
  return areCoplanar(...pt3d);
}

/**
 * dy/dx (the n-th derivative) of y given implicitly by eq = 0 (SymPy
 * idiff). y is a symbol, a list of symbols that depend on x (the first one
 * is differentiated), or a function of x.
 */
export function idiff(eq: ExprLike, yIn: Sym | readonly Sym[] | UndefFn, x: Sym, n = 1): Expr {
  const e0 = sympify(eq);
  let dep: Sym[];
  let y: Sym | UndefFn;
  if (Array.isArray(yIn)) {
    dep = [...yIn];
    y = at(dep, 0);
  } else if (yIn instanceof Sym) {
    dep = [yIn];
    y = yIn;
  } else if (yIn instanceof UndefFn) {
    dep = [];
    y = yIn;
  } else throw new RangeError(`expecting x-dependent symbol(s) or function(s) but got: ${String(yIn)}`);
  const f = new ExprMap<Expr>();
  for (const s of e0.freeSymbols()) if (s.key !== x.key && dep.some((d) => d.key === s.key)) f.set(s, SymFunction(s.name)(x));
  let dydx: Expr = y instanceof Sym ? diff(SymFunction(y.name)(x), x) : diff(y, x);
  let e = subs(e0, [...f]);
  const derivs: [Expr, Expr][] = [];
  for (let i = 0; i < n; i++) {
    const deq = diff(e, x);
    const b = xreplace(deq, [[dydx, S.Zero]]);
    const a = xreplace(add(deq, mul(-1, b)), [[dydx, S.One]]);
    const yp = factorTerms(expand(cancel(subs(mul(-1, b, pow(a, -1)), derivs)), EXPAND_MUL_SHALLOW));
    if (i === n - 1) return subs(yp, [...f].map(([k, v]): [Expr, Expr] => [v, k]));
    derivs.push([dydx, yp]);
    e = add(dydx, mul(-1, yp));
    dydx = diff(dydx, x);
  }
  throw new RangeError('idiff: n must be a positive integer');
}

