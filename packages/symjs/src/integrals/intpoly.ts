// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/intpoly.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Integration of polynomials over 2- and 3-polytopes (SymPy
 * polytope_integrate and its helpers), by the evaluation technique of Chin,
 * Lasserre and Sukumar, "Numerical integration of homogeneous functions on
 * convex and nonconvex polygons and polyhedra", Computational Mechanics 56.6
 * (2015): the integral of a homogeneous polynomial over the polytope is
 * reduced to integrals over its facets (generalized Stokes and Euler
 * theorems).
 *
 * The integrals layer does not depend on the geometry layer at run time: a
 * Polygon, Segment or Point of `@symjs/symjs/geometry` is accepted by its
 * structure (a polygon's `vertices` and `sides`, a segment's `points`, a
 * point's coordinates), and the segments built from a hyperplane
 * representation or a clockwise sort are plain `{ points }` records.
 *
 * Differences from SymPy (mathematical correctness first):
 * - `norm` of a three-dimensional point is its Euclidean norm (SymPy 1.14
 *   adds z instead of z**2).
 * - `maxDegree: 0` gives the table of the monomials of degree 0 (SymPy tests
 *   `if max_degree:` and integrates the polynomial 0 instead).
 * - `bestOrigin` divides exactly (SymPy divides Python integers to a float:
 *   `(0, 3.0)` there is `[0, 3]` here).
 * - The integral over a 3-polytope integrates each homogeneous component
 *   with its own degree (SymPy 1.14 passes the whole polynomial and returns
 *   nan for one that is not homogeneous).
 * - A missing result (`intersection` of parallel lines, SymPy None) is an
 *   empty array.
 */

import type { ExprLike } from '../core/nodes';
import { Add, Expr, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { isNegative, isPositive, isZero } from '../core/assumptions';
import { add, div, mul, pow, sub, sympify } from '../core/ops';
import { at, defined, expectType, first } from '../core/guard';
import { ExprMap } from '../core/exprmap';
import { NotImplementedError, PolynomialError } from '../core/errors';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { Poly, gcdList } from '../polys/sympoly';
import { nsimplify } from '../numeric/nfloat';

const X = new Sym('x');
const Y = new Sym('y');
const Z = new Sym('z');

/** A point: a geometric Point (its coordinates are its arguments) or a sequence of coordinates. */
export type PointLike = Expr | readonly ExprLike[];
/** A line segment: a geometric Segment or a `{ points }` record of its two end points. */
export interface SegmentLike {
  readonly points: readonly PointLike[];
}
/** A polygon given by its vertices and sides (a geometric Polygon). */
export interface PolygonLike {
  readonly vertices: readonly PointLike[];
  readonly sides: readonly SegmentLike[];
}
/** A hyperplane a·x = b: its normal direction a and its distance parameter b. */
export type Hyperplane = readonly [readonly ExprLike[], ExprLike];
/** A face of a 3-polytope: the indices of its vertices. */
export type Face = readonly number[];
/** A 3-polytope in vertex representation: the vertices, then each face. */
export type Polytope3D = readonly [readonly PointLike[], ...Face[]];
/** A 2D record of gradient_terms: [term, x degree, y degree, value over the boundary]. */
export type MonomialRecord2D = [Expr, number, number, ExprLike];
/** A 3D record of gradient_terms: [term, x, y, z degrees, total degree, x index, z index, value over the face]. */
export type MonomialRecord3D = [Expr, number, number, number, number, number, number, ExprLike];
/** The 3D records of gradient_terms grouped by total degree, then by x degree. */
export type MonomialTable3D = MonomialRecord3D[][][];

const isSeq = (p: unknown): p is readonly ExprLike[] => Array.isArray(p);
/** The coordinates of a point. */
const coords = (p: PointLike): readonly Expr[] => (isSeq(p) ? p.map((c) => sympify(c)) : p.args);
/** Coordinate i of a point. */
const coord = (p: PointLike, i: number): Expr => at(coords(p), i);

const isPolygonLike = (p: unknown): p is PolygonLike => typeof p === 'object' && p !== null && 'vertices' in p && 'sides' in p;
const isHyperplaneList = (p: readonly Hyperplane[] | Polytope3D): p is readonly Hyperplane[] => p[0].length === 2;
const isSegmentList = (f: unknown): f is readonly SegmentLike[] => Array.isArray(f) && f.every((s) => typeof s === 'object' && s !== null && 'points' in s);
const isFaceList = (f: unknown): f is readonly Face[] => Array.isArray(f) && f.every((s) => Array.isArray(s) && s.every((i) => typeof i === 'number'));
const isTable2D = (v: unknown): v is readonly MonomialRecord2D[] => Array.isArray(v) && v.every((r) => Array.isArray(r) && r.length === 4);
const isTable3D = (v: unknown): v is readonly MonomialTable3D[number][] => Array.isArray(v) && v.every((r) => Array.isArray(r) && r.every((s) => Array.isArray(s)));

/** The sign of a comparison that must be decidable (SymPy raises TypeError for an undecidable relational). */
function signOf(e: Expr): -1 | 0 | 1 {
  if (isZero(e) === true) return 0;
  if (isPositive(e) === true) return 1;
  if (isNegative(e) === true) return -1;
  throw new TypeError(`cannot determine truth value of Relational: ${e.toString()} < 0`);
}

/** A degree of a polynomial term (a Python integer). */
function toInt(e: Expr): number {
  if (e instanceof Rational && e.q === 1n) return Number(e.p);
  throw new PolynomialError(`a polynomial expected: the exponent ${e.toString()} is not an integer`);
}

/**
 * Integrates polynomials over 2- and 3-polytopes (SymPy polytope_integrate).
 * The polytope is a Polygon, a list of hyperplanes [a, b] of a 2-polytope,
 * or a 3-polytope [vertices, ...faces]. With `maxDegree` and a list of
 * polynomials the result maps each polynomial of total degree at most
 * maxDegree to its integral; with `maxDegree` alone it maps every monomial
 * up to that degree to its integral; a list of polynomials without
 * `maxDegree` maps each of them (2D) to its integral.
 */
export function polytopeIntegrate(
  polyIn: PolygonLike | readonly Hyperplane[] | Polytope3D,
  expr?: ExprLike | readonly ExprLike[],
  opts: { clockwise?: boolean; maxDegree?: number } = {},
): Expr | ExprMap<Expr> {
  const { maxDegree } = opts;
  let poly = polyIn;
  if (opts.clockwise === true) {
    if (!isPolygonLike(poly)) throw new TypeError('clockwise=True works for only 2-Polytope V-representation input');
    const vs = pointSort(poly.vertices);
    poly = { vertices: vs, sides: vs.map((v, i): SegmentLike => ({ points: [v, at(vs, (i + 1) % vs.length)] })) };
  }
  let hpParams: readonly Hyperplane[];
  let facets: readonly SegmentLike[];
  if (isPolygonLike(poly)) {
    // vertex representation (2D)
    hpParams = hyperplaneParameters(poly);
    facets = poly.sides;
  } else if (isHyperplaneList(poly)) {
    // hyperplane representation (2D)
    if (first(poly)[0].length !== 2) throw new NotImplementedError('Integration for H-representation 3Dcase not implemented yet.');
    const plen = poly.length;
    const inters = poly.map((h, i) => intersection(at(poly, (i - 1 + plen) % plen), h, 'plane2D'));
    hpParams = poly;
    facets = inters.map((p, i): SegmentLike => ({ points: [p, at(inters, (i + 1) % plen)] }));
  } else {
    // vertex representation (3D)
    const [vertices, ...faces] = poly;
    const hp3 = hyperplaneParameters(faces, vertices);
    if (maxDegree === undefined) {
      if (expr === undefined || isSeq(expr)) throw new TypeError('Input expression must be a valid SymPy expression');
      return mainIntegrate3d(expr, faces, vertices, hp3);
    }
    return integrateList(expr, maxDegree, mainIntegrate3d(0, faces, vertices, hp3, maxDegree));
  }
  if (maxDegree !== undefined) return integrateList(expr, maxDegree, mainIntegrate(0, facets, hpParams, maxDegree));
  if (expr === undefined) throw new TypeError('Input expression must be a valid SymPy expression');
  return mainIntegrate(expr, facets, hpParams);
}

/** The integrals of the polynomials of exprs (up to maxDegree) from the table of the monomials' integrals. */
function integrateList(exprs: ExprLike | readonly ExprLike[] | undefined, maxDegree: number, table: Expr | ExprMap<Expr>): ExprMap<Expr> {
  const dict = expectType(table, (t): t is ExprMap<Expr> => t instanceof ExprMap, 'table');
  if (exprs === undefined) return dict;
  if (!isSeq(exprs)) throw new TypeError('Input polynomials must be list of expressions');
  const kept = exprs.filter((e) => {
    const d = decompose(e);
    return (d.size === 1 && d.has(0)) || Poly.from(e).totalDegree() <= maxDegree;
  });
  const result = new ExprMap<Expr>();
  for (const pIn of kept) {
    const p = sympify(pIn);
    if (result.has(p)) continue;
    if (isZero(p) === true) {
      result.set(S.Zero, S.Zero);
      continue;
    }
    let value: Expr = S.Zero;
    for (const monom of decompose(p, true)) {
      const [coeff, m] = strip(nsimplify(monom));
      const v = dict.get(m);
      if (v === undefined) throw new RangeError(`no integral of the monomial ${m.toString()} was computed`);
      value = add(value, mul(v, coeff));
    }
    result.set(p, value);
  }
  return result;
}

/** SymPy strip(monom): the coefficient of a monomial and the monomial divided by it. */
function strip(monom: Expr): [Expr, Expr] {
  if (monom.isNumber) return [monom, S.One];
  const coeff = Poly.from(monom).LC();
  return [coeff, div(monom, coeff)];
}

/** SymPy _polynomial_integrate: the integral of the homogeneous components over a 2-polytope. */
function polynomialIntegrate(polynomials: ReadonlyMap<number, Expr>, facets: readonly SegmentLike[], hpParams: readonly Hyperplane[]): Expr {
  const dims = [X, Y];
  let value: Expr = S.Zero;
  for (const [deg, p] of polynomials) {
    let contribution: Expr = S.Zero;
    hpParams.forEach((hp, i) => {
      const boundary = integrationReduction(facets, i, hp[0], hp[1], p, dims, deg);
      contribution = add(contribution, mul(boundary, div(hp[1], norm(hp[0]))));
    });
    value = add(value, div(contribution, dims.length + deg));
  }
  return value;
}

/**
 * The integral of a uni/bi/trivariate polynomial over a 3-polytope, reduced
 * to integrals over its faces (SymPy main_integrate3d). With maxDegree the
 * result maps every monomial up to that degree to its integral.
 */
export function mainIntegrate3d(exprIn: ExprLike, facets: readonly Face[], vertices: readonly PointLike[], hpParams: readonly Hyperplane[], maxDegree?: number): Expr | ExprMap<Expr> {
  const dims = [X, Y, Z];
  if (maxDegree !== undefined) {
    const gradTerms = gradientTerms(maxDegree, 3);
    const flat = gradTerms.flatMap((zTerms) => zTerms.flat());
    const result = new ExprMap<Expr>();
    for (const term of flat) result.set(term[0], S.Zero);
    hpParams.forEach((hp, facetCount) => {
      const [a, b] = [hp[0], sympify(hp[1])];
      const x0 = at(vertices, first(at(facets, facetCount)));
      flat.forEach((monom, i) => {
        const [e, xd, yd, zd, zIndex, yIndex, xIndex] = monom;
        const degree = xd + yd + zd;
        const value =
          isZero(b) === true ? S.Zero : integrationReductionDynamic(facets, facetCount, a, b, e, degree, dims, xIndex, yIndex, zIndex, x0, gradTerms, i, vertices, hp);
        monom[7] = value;
        result.set(e, add(defined(result.get(e)), div(mul(value, div(b, norm(a))), dims.length + degree)));
      });
    });
    return result;
  }
  const expr = sympify(exprIn);
  let value: Expr = S.Zero;
  for (const [deg, component] of decompose(expr)) {
    let contribution: Expr = S.Zero;
    facets.forEach((facet, i) => {
      const hp = at(hpParams, i);
      const b = sympify(hp[1]);
      if (isZero(b) === true) return;
      // the homogeneous component of this degree (SymPy passes the whole polynomial, which gives nan
      // for a polynomial that is not homogeneous: x**2 + y over the cube [0, 5]**3)
      const pi = polygonIntegrate(facet, hp, i, facets, vertices, component, deg);
      contribution = add(contribution, mul(pi, div(b, norm(hp[0]))));
    });
    value = add(value, div(contribution, dims.length + deg));
  }
  return value;
}

/**
 * The integral of a uni/bivariate polynomial (or of each of a list of them)
 * over a 2-polytope, reduced to its boundary facets (SymPy main_integrate).
 * With maxDegree the result maps every monomial up to that degree (and 0)
 * to its integral.
 */
export function mainIntegrate(exprIn: ExprLike | readonly ExprLike[], facets: readonly SegmentLike[], hpParams: readonly Hyperplane[], maxDegree?: number): Expr | ExprMap<Expr> {
  const dims = [X, Y];
  if (maxDegree !== undefined) {
    const gradTerms: MonomialRecord2D[] = [[S.Zero, 0, 0, 0], ...gradientTerms(maxDegree)];
    const result = new ExprMap<Expr>();
    hpParams.forEach((hp, facetCount) => {
      const [a, b] = [hp[0], sympify(hp[1])];
      const x0 = first(at(facets, facetCount).points);
      gradTerms.forEach((monom, i) => {
        const [m, xd, yd] = monom;
        const old = result.get(m);
        let degree = 0;
        let boundary: Expr = S.Zero;
        if (isZero(b) !== true) {
          degree = xd + yd;
          boundary = integrationReductionDynamic(facets, facetCount, a, b, m, degree, dims, xd, yd, maxDegree, x0, gradTerms, i);
        }
        monom[3] = boundary;
        const term = div(mul(boundary, div(b, norm(a))), dims.length + degree);
        result.set(m, old === undefined ? term : add(old, term));
      });
    });
    return result;
  }
  if (!isSeq(exprIn)) return polynomialIntegrate(decompose(exprIn), facets, hpParams);
  const out = new ExprMap<Expr>();
  for (const e of exprIn) out.set(sympify(e), polynomialIntegrate(decompose(e), facets, hpParams));
  return out;
}

/**
 * The integral of a uni/bi/trivariate homogeneous polynomial of the given
 * degree over one face of a 3-polytope (SymPy polygon_integrate).
 */
export function polygonIntegrate(
  facet: Face,
  hpParam: Hyperplane,
  index: number,
  facets: readonly Face[],
  vertices: readonly PointLike[],
  exprIn: ExprLike,
  degree: number,
): Expr {
  const expr = sympify(exprIn);
  if (isZero(expr) === true) return S.Zero;
  let result: Expr = S.Zero;
  const x0 = coords(at(vertices, first(facet)));
  const n = facet.length;
  facet.forEach((fac, i) => {
    const side = [at(vertices, fac), at(vertices, at(facet, (i + 1) % n))];
    result = add(result, mul(distanceToSide(x0, side, hpParam[0]), linesegIntegrate(facet, i, side, expr, degree)));
  });
  if (!expr.isNumber) {
    const inner = add(mul(diff(expr, X), at(x0, 0)), mul(diff(expr, Y), at(x0, 1)), mul(diff(expr, Z), at(x0, 2)));
    result = add(result, polygonIntegrate(facet, hpParam, index, facets, vertices, inner, degree - 1));
  }
  return div(result, degree + 2);
}

/** The signed distance between a 3D point and a line segment of the plane with normal a (SymPy distance_to_side). */
export function distanceToSide(point: PointLike, lineSeg: readonly PointLike[], a: readonly ExprLike[]): Expr {
  const [x1, x2] = [coords(at(lineSeg, 0)), coords(at(lineSeg, 1))];
  const nA = norm(a);
  const revNormal = a.map((i) => div(mul(-1, i), nA));
  const v0 = [0, 1, 2].map((i) => sub(at(x2, i), at(x1, i)));
  const nv = norm(v0);
  const vector = v0.map((c) => div(c, nv));
  const nSide = crossProduct([0, 0, 0], revNormal, vector);
  const p = coords(point);
  return add(...[0, 1, 2].map((i) => mul(sub(at(x1, i), at(p, i)), at(nSide, i))));
}

/** The line integral of a homogeneous polynomial of the given degree over a 3D line segment (SymPy lineseg_integrate). */
export function linesegIntegrate(polygon: readonly unknown[], index: number, lineSeg: readonly PointLike[], exprIn: ExprLike, degree: number): Expr {
  const expr = sympify(exprIn);
  if (isZero(expr) === true) return S.Zero;
  const x0 = coords(at(lineSeg, 0));
  const x1 = coords(at(lineSeg, 1));
  const distance = norm([0, 1, 2].map((i) => sub(at(x1, i), at(x0, i))));
  const values: [Expr, Expr][] = [
    [X, at(x1, 0)],
    [Y, at(x1, 1)],
    [Z, at(x1, 2)],
  ];
  let result = mul(distance, subs(expr, values));
  const inner = add(mul(diff(expr, X), at(x0, 0)), mul(diff(expr, Y), at(x0, 1)), mul(diff(expr, Z), at(x0, 2)));
  result = add(result, linesegIntegrate(polygon, index, lineSeg, inner, degree - 1));
  return div(result, degree + 1);
}

/**
 * The integral of a homogeneous polynomial of the given degree over the
 * facet facets[index] of a 2-polytope (SymPy integration_reduction).
 */
export function integrationReduction(
  facets: readonly SegmentLike[],
  index: number,
  a: readonly ExprLike[],
  b: ExprLike,
  exprIn: ExprLike,
  dims: readonly Expr[],
  degree: number,
): Expr {
  const expr = sympify(exprIn);
  if (isZero(expr) === true) return expr;
  let value: Expr = S.Zero;
  const x0 = first(at(facets, index).points);
  const inner = add(mul(diff(expr, X), coord(x0, 0)), mul(diff(expr, Y), coord(x0, 1)));
  if (isZero(inner) !== true) value = add(value, integrationReduction(facets, index, a, b, inner, dims, degree - 1));
  value = add(value, leftIntegral2D(facets.length, index, facets, x0, expr, [X, Y]));
  return div(value, dims.length + degree - 1);
}

/**
 * The left integral of Eq. 10 of Chin et al. in 2D (SymPy left_integral2D):
 * the polynomial at the intersections of facets[index] with its neighbours,
 * times their distances from x0.
 */
export function leftIntegral2D(m: number, index: number, facets: readonly SegmentLike[], x0: PointLike, exprIn: ExprLike, gens: readonly Expr[]): Expr {
  const expr = sympify(exprIn);
  let value: Expr = S.Zero;
  const p0 = coords(x0);
  for (let j = 0; j < m; j++) {
    if (j !== (((index - 1) % m) + m) % m && j !== (index + 1) % m) continue;
    const inter = intersection(at(facets, index), at(facets, j), 'segment2D');
    if (!isVertex(inter)) continue;
    const distance = norm(inter.map((c, i) => sub(c, at(p0, i))));
    value = add(value, mul(distance, subs(expr, inter.map((c, i): [Expr, Expr] => [at(gens, i), c]))));
  }
  return value;
}

/**
 * integration_reduction by dynamic programming (SymPy
 * integration_reduction_dynamic): the value of a monomial over a facet from
 * the values of the monomials of lower degree in monomialValues (the records
 * of gradientTerms). In 3D maxIndex is the z index of the monomial and
 * vertices and hpParam give the face.
 */
export function integrationReductionDynamic(
  facets: readonly SegmentLike[] | readonly Face[],
  index: number,
  _a: readonly ExprLike[],
  _b: ExprLike,
  exprIn: ExprLike,
  degree: number,
  dims: readonly Expr[],
  xIndexIn: number,
  yIndex: number,
  maxIndex: number,
  x0: PointLike,
  monomialValues: readonly MonomialRecord2D[] | readonly MonomialTable3D[number][],
  monomIndex: number,
  vertices?: readonly PointLike[],
  hpParam?: Hyperplane,
): Expr {
  const expr = sympify(exprIn);
  if (isZero(expr) === true) return expr;
  let value: Expr = S.Zero;
  const p0 = coords(x0);
  if (dims.length === 2) {
    const records = expectType(monomialValues, isTable2D, 'monomialValues');
    if (!expr.isNumber) {
      const [, xDegree, yDegree] = at(records, monomIndex);
      // a degree 0 contributes nothing (SymPy multiplies the value at index 0 by 0)
      const xValue = xDegree > 0 ? at(at(records, monomIndex - maxIndex + xIndexIn - 2), 3) : 0;
      const yValue = yDegree > 0 ? at(at(records, monomIndex - 1), 3) : 0;
      value = add(value, mul(xDegree, xValue, at(p0, 0)), mul(yDegree, yValue, at(p0, 1)));
    }
    const segs = expectType(facets, isSegmentList, 'facets');
    return div(add(value, leftIntegral2D(segs.length, index, segs, x0, expr, dims)), dims.length + degree - 1);
  }
  const terms = expectType(monomialValues, isTable3D, 'monomialValues');
  const zIndex = maxIndex;
  const xIndex = xIndexIn;
  if (!expr.isNumber) {
    const [xDegree, yDegree, zDegree] = [yIndex, zIndex - xIndex - yIndex, xIndex];
    const val = (i: number, j: number, k: number): ExprLike => at(at(at(at(terms, i), j), k), 7);
    const xValue = xDegree > 0 ? val(zIndex - 1, yIndex - 1, xIndex) : 0;
    const yValue = yDegree > 0 ? val(zIndex - 1, yIndex, xIndex) : 0;
    const zValue = zDegree > 0 ? val(zIndex - 1, yIndex, xIndex - 1) : 0;
    value = add(value, mul(xDegree, xValue, at(p0, 0)), mul(yDegree, yValue, at(p0, 1)), mul(zDegree, zValue, at(p0, 2)));
  }
  const faces = expectType(facets, isFaceList, 'facets');
  value = add(value, leftIntegral3D(faces, index, expr, defined(vertices, 'vertices'), defined(hpParam, 'hpParam'), degree));
  return div(value, dims.length + degree - 1);
}

/**
 * The left integral of Eq. 10 of Chin et al. in 3D (SymPy left_integral3D):
 * the integrals over the sides of the face facets[index] times their
 * distances from its first vertex.
 */
export function leftIntegral3D(facets: readonly Face[], index: number, expr: ExprLike, vertices: readonly PointLike[], hpParam: Hyperplane, degree: number): Expr {
  let value: Expr = S.Zero;
  const facet = at(facets, index);
  const x0 = at(vertices, first(facet));
  const n = facet.length;
  facet.forEach((fac, i) => {
    const side = [at(vertices, fac), at(vertices, at(facet, (i + 1) % n))];
    value = add(value, mul(distanceToSide(x0, side, hpParam[0]), linesegIntegrate(facet, i, side, expr, degree)));
  });
  return value;
}

/**
 * The monomials up to y**binomialPower (2D) or z**binomialPower (3D) as the
 * records that the dynamic programming fills in (SymPy gradient_terms).
 */
export function gradientTerms(binomialPower?: number, noOfGens?: 2): MonomialRecord2D[];
export function gradientTerms(binomialPower: number, noOfGens: 3): MonomialTable3D;
export function gradientTerms(binomialPower = 0, noOfGens: 2 | 3 = 2): MonomialRecord2D[] | MonomialTable3D {
  if (noOfGens === 2) {
    const terms: MonomialRecord2D[] = [];
    for (let xc = 0; xc <= binomialPower; xc++) for (let yc = 0; yc <= binomialPower - xc; yc++) terms.push([mul(pow(X, xc), pow(Y, yc)), xc, yc, 0]);
    return terms;
  }
  const terms: MonomialTable3D = [];
  for (let zc = 0; zc <= binomialPower; zc++) {
    const zTerms: MonomialRecord3D[][] = [];
    for (let xc = 0; xc <= zc; xc++) {
      const xTerms: MonomialRecord3D[] = [];
      for (let yc = zc - xc; yc >= 0; yc--) {
        const zd = zc - yc - xc;
        xTerms.push([mul(pow(X, xc), pow(Y, yc), pow(Z, zd)), xc, yc, zd, zc, xc, zd, 0]);
      }
      zTerms.push(xTerms);
    }
    terms.push(zTerms);
  }
  return terms;
}

/**
 * The hyperplane parameters [a, b] of the sides of a polygon, or of the
 * faces of a 3-polytope with the given vertices (SymPy hyperplane_parameters).
 */
export function hyperplaneParameters(poly: PolygonLike | readonly Face[], vertices?: readonly PointLike[]): [Expr[], Expr][] {
  if (isPolygonLike(poly)) {
    const vs = poly.vertices;
    return vs.map((v, i) => {
      const w = at(vs, (i + 1) % vs.length);
      const a1 = sub(coord(v, 1), coord(w, 1));
      const a2 = sub(coord(w, 0), coord(v, 0));
      const b = sub(mul(coord(w, 0), coord(v, 1)), mul(coord(w, 1), coord(v, 0)));
      const factor = gcdList([a1, a2, b]);
      return [[div(a1, factor), div(a2, factor)], div(b, factor)];
    });
  }
  const vs = defined(vertices, 'vertices');
  return poly.map((polygon) => {
    const v = (k: number): readonly Expr[] => coords(at(vs, at(polygon, k)));
    const normal = crossProduct(v(0), v(1), v(2));
    const b = add(...[0, 1, 2].map((j) => mul(at(normal, j), at(v(0), j))));
    const g = gcdList(normal);
    const fac = isZero(g) === true ? S.One : g;
    return [normal.map((j) => div(j, fac)), div(b, fac)];
  });
}

/** The cross product (v2 - v1) x (v3 - v1) (SymPy cross_product). */
export function crossProduct(v1: readonly ExprLike[], v2In: readonly ExprLike[], v3In: readonly ExprLike[]): Expr[] {
  const d = (v: readonly ExprLike[], j: number): Expr => sub(at(v, j), at(v1, j));
  const [A0, A1, A2, B0, B1, B2] = [d(v2In, 0), d(v2In, 1), d(v2In, 2), d(v3In, 0), d(v3In, 1), d(v3In, 2)];
  return [sub(mul(B2, A1), mul(B1, A2)), sub(mul(B0, A2), mul(B2, A0)), sub(mul(B1, A0), mul(B0, A1))];
}

/**
 * A point of the line segment whose inner product with the gradient of expr
 * gives the least maximum total power (SymPy best_origin; not used by the
 * main algorithm). a and b are the hyperplane parameters of the segment.
 */
export function bestOrigin(a: readonly ExprLike[], b: ExprLike, lineseg: SegmentLike, exprIn: ExprLike): [Expr, Expr] {
  const [p, q] = [coords(at(lineseg.points, 0)), coords(at(lineseg.points, 1))];
  const [px, py, qx, qy] = [at(p, 0), at(p, 1), at(q, 0), at(q, 1)];
  const xAxisCut = (): boolean => isZero(py) === true || isZero(qy) === true || isNegative(div(py, qy)) === true;
  const yAxisCut = (): boolean => isZero(px) === true || isZero(qx) === true || isNegative(div(px, qx)) === true;
  const onY: [Expr, Expr] = [S.Zero, div(b, at(a, 1))];
  const onX = (): [Expr, Expr] => [div(b, at(a, 0)), S.Zero];
  // vertical and horizontal lines
  if (isZero(sympify(at(a, 0))) === true) return yAxisCut() ? onY : [px, py];
  if (isZero(sympify(at(a, 1))) === true) return xAxisCut() ? onX() : [px, py];
  const expr = sympify(exprIn);
  const powers = new ExprMap<Expr>([
    [X, S.Zero],
    [Y, S.Zero],
  ]);
  const bump = (g: Expr, e: Expr): void => {
    const old = powers.get(g);
    if (old !== undefined) powers.set(g, add(old, e));
  };
  // a factor of a monomial: a generator counts once, a two-argument factor (a power) by its exponent
  const factor = (t: Expr): void => {
    if (t.args.length === 0) bump(t, S.One);
    else if (t.args.length === 2) bump(at(t.args, 0), at(t.args, 1));
  };
  if (expr instanceof Add) {
    // (a monomial that is a bare symbol has no arguments and is not counted, as in SymPy)
    for (const monomial of expr.args) {
      if (monomial instanceof Pow) bump(monomial.base, monomial.exp);
      else monomial.args.forEach(factor);
    }
  } else if (expr instanceof Mul) expr.args.forEach(factor);
  else if (expr instanceof Pow) powers.set(expr.base, expr.exp);
  else if (expr instanceof Sym) bump(expr, S.One);
  else return [px, py];
  if (signOf(sub(defined(powers.get(X)), defined(powers.get(Y)))) >= 0) return yAxisCut() ? onY : xAxisCut() ? onX() : [px, py];
  return xAxisCut() ? onX() : yAxisCut() ? onY : [px, py];
}

/**
 * The homogeneous components of a polynomial by degree, or with separate
 * the set of its terms (SymPy decompose).
 */
export function decompose(exprIn: ExprLike, separate?: false): Map<number, Expr>;
export function decompose(exprIn: ExprLike, separate: true): Set<Expr>;
export function decompose(exprIn: ExprLike, separate = false): Map<number, Expr> | Set<Expr> {
  const expr = sympify(exprIn);
  const dict = new Map<number, Expr>();
  if (expr.isNumber) dict.set(0, expr);
  else if (expr instanceof Sym) dict.set(1, expr);
  else if (expr instanceof Add) {
    if (separate) return uniqueSet(expr.args);
    const symbols = [...new ExprMap(collectSymbols(expr).map((s) => [s, true])).keys()];
    for (const term of expr.args) {
      const d = Poly.from(term, symbols)
        .degreeList()
        .reduce((s, k) => s + k, 0);
      const old = dict.get(d);
      dict.set(d, old === undefined ? term : add(old, term));
    }
  } else if (expr instanceof Pow) dict.set(toInt(expr.exp), expr);
  else {
    // a product
    let degree = 0;
    for (const term of expr.args) {
      if (term instanceof Sym) degree += 1;
      else if (term.args.length === 2) degree += toInt(at(term.args, 1));
    }
    dict.set(degree, expr);
  }
  return separate ? uniqueSet([...dict.values()]) : dict;
}

/** The symbols of an expression. */
const collectSymbols = (e: Expr): Expr[] => (e instanceof Sym ? [e] : e.args.flatMap(collectSymbols));
/** A set of expressions without structural duplicates. */
const uniqueSet = (es: readonly Expr[]): Set<Expr> => new Set(new ExprMap(es.map((e) => [e, true])).keys());

/**
 * The vertices of a polygon (or a list of points) sorted clockwise, or
 * anticlockwise, around their centre (SymPy point_sort); 3D points are
 * sorted around the given normal of their plane.
 */
export function pointSort(poly: PolygonLike | readonly PointLike[], normal?: readonly ExprLike[], clockwise = true): PointLike[] {
  const pts = isPolygonLike(poly) ? poly.vertices : poly;
  const n = pts.length;
  if (n < 2) return [...pts];
  const order = clockwise ? 1 : -1;
  const dim = coords(first(pts)).length;
  const center = (dim === 2 ? [0, 1] : [0, 1, 2]).map((i) => div(add(...pts.map((v) => coord(v, i))), n));
  const [cx, cy] = [at(center, 0), at(center, 1)];
  const compare = (pa: PointLike, pb: PointLike): number => {
    const [ax, ay] = [sub(coord(pa, 0), cx), sub(coord(pa, 1), cy)];
    const [bx, by] = [sub(coord(pb, 0), cx), sub(coord(pb, 1), cy)];
    const [sax, sbx] = [signOf(ax), signOf(bx)];
    if (sax >= 0 && sbx < 0) return -order;
    if (sax < 0 && sbx >= 0) return order;
    if (sax === 0 && sbx === 0) {
      if (signOf(ay) >= 0 || signOf(by) >= 0) return signOf(sub(ay, by)) > 0 ? -order : order;
      return signOf(sub(by, ay)) > 0 ? -order : order;
    }
    const det = signOf(sub(mul(ax, by), mul(bx, ay)));
    if (det !== 0) return det < 0 ? -order : order;
    return signOf(sub(add(mul(ax, ax), mul(ay, ay)), add(mul(bx, bx), mul(by, by)))) > 0 ? -order : order;
  };
  const compare3d = (pa: PointLike, pb: PointLike): number => {
    const det = crossProduct(center, coords(pa), coords(pb));
    const nrm = defined(normal, 'normal');
    // (points on one ray from the centre compare equal; SymPy's comparator returns None there)
    return order * signOf(add(...[0, 1, 2].map((i) => mul(at(det, i), at(nrm, i)))));
  };
  return [...pts].sort(dim === 2 ? compare : compare3d);
}

/** The Euclidean norm of a point, of a sequence of coordinates or of the values of a map (SymPy norm). */
export function norm(point: PointLike | ReadonlyMap<unknown, ExprLike>): Expr {
  const cs = point instanceof Expr || isSeq(point) ? coords(point) : [...point.values()];
  return pow(add(...cs.map((c) => pow(c, 2))), S.Half);
}

/**
 * The intersection of two line segments ('segment2D' and 'segment3D': of
 * their lines in the xy plane) or of two hyperplanes [a, b] of the plane
 * ('plane2D') (SymPy intersection of intpoly). Lines that do not meet in
 * one point give an empty array (SymPy None).
 */
export function intersection(geom1: SegmentLike | Hyperplane, geom2: SegmentLike | Hyperplane, intersectionType: string): Expr[] {
  if (intersectionType.slice(0, -2) === 'segment' && 'points' in geom1 && 'points' in geom2) {
    const xy = (s: SegmentLike, k: number, i: number): Expr => coord(at(s.points, k), i);
    const [X1, Y1, X2, Y2] = [xy(geom1, 0, 0), xy(geom1, 0, 1), xy(geom1, 1, 0), xy(geom1, 1, 1)];
    const [X3, Y3, X4, Y4] = [xy(geom2, 0, 0), xy(geom2, 0, 1), xy(geom2, 1, 0), xy(geom2, 1, 1)];
    const denom = sub(mul(sub(X1, X2), sub(Y3, Y4)), mul(sub(Y1, Y2), sub(X3, X4)));
    if (isZero(denom) === true) return [];
    const t1 = sub(mul(X1, Y2), mul(Y1, X2));
    const t2 = sub(mul(X3, Y4), mul(X4, Y3));
    return [div(sub(mul(t1, sub(X3, X4)), mul(t2, sub(X1, X2))), denom), div(sub(mul(t1, sub(Y3, Y4)), mul(t2, sub(Y1, Y2))), denom)];
  }
  if (intersectionType === 'plane2D' && !('points' in geom1) && !('points' in geom2)) {
    const [A1x, A1y, A2x, A2y] = [coord(geom1[0], 0), coord(geom1[0], 1), coord(geom2[0], 0), coord(geom2[0], 1)];
    const [b1, b2] = [geom1[1], geom2[1]];
    const denom = sub(mul(A1x, A2y), mul(A2x, A1y));
    if (isZero(denom) === true) return [];
    return [div(sub(mul(b1, A2y), mul(b2, A1y)), denom), div(sub(mul(b2, A1x), mul(b1, A2x)), denom)];
  }
  return [];
}

/** True for a vertex: a geometric Point or a tuple of two or three coordinates (SymPy is_vertex). */
export function isVertex(ent: unknown): boolean {
  if (Array.isArray(ent)) return ent.length === 2 || ent.length === 3;
  return ent instanceof Expr && 'isPoint' in ent && ent.isPoint === true;
}
