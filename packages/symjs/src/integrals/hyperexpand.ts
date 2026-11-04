// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/simplify/hyperexpand.py and the HyperRep
// functions of sympy/functions/special/hyper.py), BSD 3-Clause License,
// Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Expansion of hypergeometric and Meijer G-functions in closed form
 * (SymPy hyperexpand).
 *
 * A hypergeometric function is reduced in order, then reached from a known
 * formula of the same invariants (parameters congruent mod 1) by shift
 * operators acting on the formula's basis of functions. A Meijer G-function
 * is matched against a few G-function formulas, or expanded by Slater's
 * theorem into hypergeometric functions at zero or at infinity.
 */

import type { Expr, ExprLike, Substitution } from '../core/nodes';
import { Add, Dummy, ExtensionExpr, Fn, Mul, Order, Pow, Rational, S, Special, asRational } from '../core/nodes';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { at, cast, defined, expectType, first, pair } from '../core/guard';
import { Lt, Gt, piecewise } from '../core/logic';
import { mapBottomUp, some, xreplace } from '../core/traverse';
import { coeff, asNumerDenom } from '../core/methods';
import { countOps } from '../core/match';
import { isPositive } from '../core/assumptions';
import { compareKeys, sortKey } from '../printing/sortkey';
import { ExprMap } from '../core/exprmap';
import { diff } from '../calculus/diff';
import { PolynomialError } from '../core/errors';
import { polyCoefficients } from '../polys/poly';
import { abs, asin, atan, cos, cosh, fn, log, re, sin, sinh } from '../functions/elementary';
import { Ci, Chi, Ei, Shi, Si, erf, expandFuncRules, expint, factorial, fresnelc, fresnels, gamma, lowergamma, rf, uppergamma } from '../functions/special';
import { besseli, besselj } from '../functions/bessel';
import { Hyper, MeijerG, gaussAtOne, hyper, meijerg } from '../functions/hyper';
import { expPolar, extractBranchFactor, isPolar, polarify, polarLift, unpolarify } from '../functions/polar';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { powdenest } from '../simplify/powsimp';
import { simplify } from '../simplify/simplify';
import { series } from '../series/series';

// ---- small helpers ------------------------------------------------------------------

const I = S.I;
const pi = S.Pi;
const half = S.Half;
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));
const neg = (e: ExprLike): Expr => mul(-1, e);
const sub = (a: ExprLike, b: ExprLike): Expr => add(a, neg(b));
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));
const prod = (xs: readonly Expr[]): Expr => mul(...xs);
const sum = (xs: readonly Expr[]): Expr => add(...xs);
const isRat = (e: unknown): e is Rational => e instanceof Rational;
const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
/** The sort of SymPy's default_sort_key. */
const sorted = (xs: readonly Expr[], reverse = false): Expr[] => [...xs].sort((u, v) => (reverse ? -1 : 1) * compareKeys(sortKey(u), sortKey(v)));
/** Remove the first occurrence of e (Python list.remove). */
function removeOne(xs: Expr[], e: Expr): void {
  xs.splice(
    xs.findIndex((x) => x.key === e.key),
    1,
  );
}
const isBad = (e: Expr): boolean => some(e, (n) => n instanceof Special && ['nan', 'oo', '-oo', 'zoo'].includes(n.name));
const countHyper = (e: Expr): number => (e instanceof Hyper ? 1 : 0) + e.args.reduce((s, a) => s + countHyper(a), 0);

/** x mod 1, keeping the symbolic part (SymPy _mod1). */
export function mod1(x: Expr): Expr {
  const m = (c: Rational): Rational => Rational.of(((c.p % c.q) + c.q) % c.q, c.q);
  if (isRat(x)) return m(x);
  const terms = x instanceof Add ? x.args : [x];
  const c = terms.find(isRat);
  return c === undefined ? x : add(m(c), ...terms.filter((t) => t !== c));
}

/** Group parameters by a key (SymPy sift), keeping the order of first appearance. */
function sift(xs: readonly Expr[], key: (e: Expr) => Expr): Map<string, { mod: Expr; items: Expr[] }> {
  const out = new Map<string, { mod: Expr; items: Expr[] }>();
  for (const x of xs) {
    const k = key(x);
    const b = out.get(k.key);
    if (b) b.items.push(x);
    else out.set(k.key, { mod: k, items: [x] });
  }
  return out;
}
const buckets = (xs: readonly Expr[]) => sift(xs, mod1);
const bucket = (b: Map<string, { mod: Expr; items: Expr[] }>, mod: Expr): Expr[] => b.get(mod.key)?.items ?? [];

// ---- polynomials in the operator D = z*d/dz -----------------------------------------

/** A polynomial with expression coefficients, lowest degree first. */
type XPoly = Expr[];

function ptrim(p: XPoly): XPoly {
  const q = p.map((c) => expand(c));
  while (q.length > 1 && at(q, -1).key === S.Zero.key) q.pop();
  return q;
}
function padd(p: XPoly, q: XPoly): XPoly {
  const [u, v] = pair([p, q].sort((x, y) => y.length - x.length));
  return ptrim(u.map((c, i) => add(c, v[i] ?? 0)));
}
const pscale = (p: XPoly, c: Expr): XPoly => ptrim(p.map((a) => mul(a, c)));
function pmul(p: XPoly, q: XPoly): XPoly {
  const r: Expr[] = Array.from({ length: p.length + q.length - 1 }, () => S.Zero);
  for (const [i, a] of p.entries()) for (const [j, b] of q.entries()) r[i + j] = add(at(r, i + j), mul(a, b));
  return ptrim(r);
}
const pprod = (ps: readonly XPoly[]): XPoly => ps.reduce(pmul, [S.One]);
/** c0 + c1*X. */
const lin = (c0: ExprLike, c1: ExprLike): XPoly => ptrim([sympify(c0), sympify(c1)]);
/** p(q) for polynomials p and q. */
function pcompose(p: XPoly, q: XPoly): XPoly {
  let r: XPoly = [S.Zero];
  for (const c of [...p].reverse()) r = padd(pmul(r, q), [c]);
  return r;
}

// ---- operators -----------------------------------------------------------------------

/** A differential operator: a polynomial in D = z*d/dz acting to the right of its coefficients. */
interface OpPoly {
  poly: XPoly;
}
type Vec = Expr[];

/** Apply an operator to obj, where op applies D. */
function applyOp(o: OpPoly, obj: Vec, op: (v: Vec) => Vec): Vec {
  let d = obj;
  let r = obj.map((e) => mul(first(o.poly), e));
  for (const c of o.poly.slice(1)) {
    d = op(d);
    r = r.map((e, i) => add(e, mul(c, at(d, i))));
  }
  return r;
}
/** Apply the operators, the last one first (SymPy apply_operators). */
function applyOperators(obj: Vec, ops: readonly OpPoly[], op: (v: Vec) => Vec): Vec {
  let res = obj;
  for (const o of [...ops].reverse()) res = applyOp(o, res, op);
  return res;
}
const zDeriv =
  (z: Expr) =>
  (v: Vec): Vec =>
    v.map((e) => mul(z, diff(e, z)));

/** Simplify a rational function of z (SymPy make_simp). */
function simp(e: Expr): Expr {
  const [n, d] = asNumerDenom(e);
  return cancel(div(expand(n), d));
}
/** z*d/dz acting on the coefficient vector C of a basis with z*d/dz B = M B. */
const derivativeOperator =
  (M: readonly (readonly Expr[])[], z: Expr) =>
  (C: Vec): Vec =>
    C.map((c, j) => simp(add(mul(z, diff(c, z)), ...C.map((ci, i) => mul(ci, at(at(M, i), j))))));

const shiftA = (ai: Expr): OpPoly => ({ poly: lin(1, pow(ai, -1)) });
const shiftB = (bi: Expr): OpPoly => ({ poly: lin(1, pow(sub(bi, 1), -1)) });
const multOperator = (p: Expr): OpPoly => ({ poly: [p] });

/** Decrement an upper index (SymPy UnShiftA). */
function unShiftA(ap0: readonly Expr[], bq: readonly Expr[], i: number, z: Expr): OpPoly {
  const ap = [...ap0];
  const ai = sub(at(ap.splice(i, 1), 0), 1);
  const m = pprod([[mul(z, ai)], ...ap.map((a) => lin(a, 1))]);
  const D = lin(neg(ai), ai);
  const n = pprod([D, ...bq.map((b) => padd(D, [sub(b, 1)]))]);
  const b0 = neg(first(n));
  return { poly: pscale(padd(pcompose(n.slice(1), lin(1, pow(ai, -1))), pscale(m, S.NegOne)), pow(b0, -1)) };
}
/** Increment a lower index (SymPy UnShiftB). */
function unShiftB(ap: readonly Expr[], bq0: readonly Expr[], i: number, z: Expr): OpPoly {
  const bq = [...bq0];
  const bi = add(at(bq.splice(i, 1), 0), 1);
  const m = pprod([lin(0, sub(bi, 1)), ...bq.map((b) => lin(sub(b, 1), 1))]);
  const D = lin(sub(1, bi), sub(bi, 1));
  const n = pprod([[z], ...ap.map((a) => padd(D, [a]))]);
  const b0 = first(n);
  return { poly: pscale(padd(m, pscale(pcompose(n.slice(1), lin(1, pow(sub(bi, 1), -1))), S.NegOne)), pow(b0, -1)) };
}
/** (m - n(sub))/n(0), the common form of the Meijer G un-shift operators. */
const meijerUnshift = (m: XPoly, n: XPoly, s: XPoly): OpPoly => ({ poly: pscale(padd(m, pscale(pcompose(n.slice(1), s), S.NegOne)), pow(first(n), -1)) });
type GParams = [Expr[], Expr[], Expr[], Expr[]];
/** Decrement an upper b index (SymPy MeijerUnShiftA; the G-functions of the Meijer formulas have no ap and bq). */
function meijerUnShiftA([an, , bm0]: GParams, i: number, z: Expr): OpPoly {
  const bm = [...bm0];
  const bi = sub(at(bm.splice(i, 1), 0), 1);
  const m = pprod(bm.map((b) => lin(b, -1)));
  const D = lin(bi, -1);
  const n = pprod([[z], ...an.map((a) => padd(D, [sub(1, a)]))]);
  return meijerUnshift(m, n, lin(bi, -1));
}

/** Cancel an upper index ai with a lower index bj (SymPy ReduceOrder), or undefined. */
function reduceOrderOp(ai: Expr, bj: Expr): OpPoly | undefined {
  const n = expand(sub(ai, bj));
  if (!isInt(n) || n.isNegative) return undefined;
  if (isInt(bj) && !bj.isPositive) return undefined;
  const ps = Array.from({ length: Number(n.p) }, (_, k) => lin(1, pow(add(bj, k), -1)));
  return { poly: pprod(ps) };
}
/** Cancel b + sign*s and a + sign*s of a G-function (SymPy ReduceOrder._meijer). */
function reduceOrderMeijer(b: Expr, a: Expr, sign: 1 | -1): OpPoly | undefined {
  const n = expand(sub(b, a));
  if (!isInt(n) || n.isNegative) return undefined;
  return { poly: pprod(Array.from({ length: Number(n.p) }, (_, k) => lin(add(a, k), sign))) };
}

function reduceOrderLists(ap0: readonly Expr[], bq0: readonly Expr[], gen: (a: Expr, b: Expr) => OpPoly | undefined, reverse: boolean): [Expr[], Expr[], OpPoly[]] {
  const ap = sorted(ap0, reverse);
  const bq = sorted(bq0, reverse);
  const nap: Expr[] = [];
  const ops: OpPoly[] = [];
  for (const a of ap) {
    const i = bq.findIndex((b) => gen(a, b) !== undefined);
    if (i < 0) nap.push(a);
    else ops.push(defined(gen(a, at(bq.splice(i, 1), 0)), 'operator'));
  }
  return [nap, bq, ops];
}

// ---- hypergeometric and G-function parameter sets ------------------------------------

/** A hypergeometric function's parameters (SymPy Hyper_Function). */
export interface HyperFunc {
  ap: Expr[];
  bq: Expr[];
}
const hyperFunc = (ap: readonly ExprLike[], bq: readonly ExprLike[]): HyperFunc => ({ ap: ap.map((a) => expand(sympify(a))), bq: bq.map((b) => expand(sympify(b))) });
const hfGamma = (f: HyperFunc): number => f.ap.filter((a) => isInt(a) && a.isNegative).length;
function invariants(f: HyperFunc): string {
  const tr = (b: Map<string, { mod: Expr; items: Expr[] }>) =>
    [...b.values()]
      .map((v) => `${v.mod.key}:${v.items.length}`)
      .sort()
      .join(',');
  return `${hfGamma(f)}|${tr(buckets(f.ap))}|${tr(buckets(f.bq))}`;
}
/** The number of steps from f to func, -1 when impossible (SymPy Hyper_Function.difficulty). */
function difficulty(f: HyperFunc, func: HyperFunc): number {
  let d = 0;
  for (const [b, ob] of [
    [buckets(func.ap), buckets(f.ap)],
    [buckets(func.bq), buckets(f.bq)],
  ] as const) {
    for (const key of new Set([...b.keys(), ...ob.keys()])) {
      const l1 = b.get(key)?.items;
      const l2 = ob.get(key)?.items;
      if (l1 === undefined || l2 === undefined || l1.length !== l2.length) return -1;
      const s1 = sorted(l1);
      const s2 = sorted(l2);
      for (const [i, x] of s1.entries()) d += Math.abs(asRational(expand(sub(x, at(s2, i)))).value);
    }
  }
  return d;
}
/** SymPy Hyper_Function._is_suitable_origin. */
function isSuitableOrigin(f: HyperFunc): boolean {
  for (const a of f.ap) {
    for (const b of f.bq) {
      const d = expand(sub(a, b));
      if (isInt(d) && !d.isNegative) return false;
    }
  }
  if (f.ap.some((a) => isRat(a) && a.isZero)) return false;
  return !f.bq.some((b) => isInt(b) && !b.isPositive);
}

/** A Meijer G-function's parameters (SymPy G_Function). */
export interface GFunc {
  an: Expr[];
  ap: Expr[];
  bm: Expr[];
  bq: Expr[];
}
const ex = (l: readonly Expr[]): Expr[] => l.map((e) => expand(e));
const gFunc = (an: readonly Expr[], ap: readonly Expr[], bm: readonly Expr[], bq: readonly Expr[]): GFunc => ({ an: ex(an), ap: ex(ap), bm: ex(bm), bq: ex(bq) });
const signature = (g: GFunc): string => [g.an, g.ap, g.bm, g.bq].map((l) => l.length).join(',');
/** Buckets of the parameters, sorted by real part (an and bq descending). */
type Buckets = Map<string, { mod: Expr; items: Expr[] }>;
function computeBuckets(g: GFunc): [Buckets, Buckets, Buckets, Buckets] {
  const [an, ap, bm, bq] = [g.an, g.ap, g.bm, g.bq].map((l, i) => {
    const b = buckets(l);
    const flip = i === 0 || i === 3;
    for (const v of b.values()) {
      const x0 = first(v.items);
      v.items.sort((u, w) => (flip ? -1 : 1) * (asRational(expand(sub(u, x0))).value - asRational(expand(sub(w, x0))).value));
    }
    return b;
  });
  return [defined(an), defined(ap), defined(bm), defined(bq)];
}

// ---- HyperRep: closed forms on the branches of pFq at z = 1 --------------------------

export type HyperRepName = 'power1' | 'power2' | 'log1' | 'atanh' | 'asin1' | 'asin2' | 'sqrts1' | 'sqrts2' | 'log2' | 'cosasin' | 'sinasin';
/** The forms of a HyperRep function: for |x| < 1 at x and at -x, and for |x| > 1 on sheet n. */
interface RepForms {
  small(a: Expr, x: Expr): Expr;
  smallMinus(a: Expr, x: Expr): Expr;
  big(a: Expr, x: Expr, n: Expr): Expr;
  bigMinus(a: Expr, x: Expr, n: Expr): Expr;
}
const isEven = (n: Expr): boolean => isInt(n) && n.p % 2n === 0n;
const ipi = (c: ExprLike): Expr => mul(c, pi, I);
const REPS: Record<HyperRepName, RepForms> = {
  power1: {
    small: (a, x) => pow(sub(1, x), a),
    smallMinus: (a, x) => pow(add(1, x), a),
    big: (a, x, n) => {
      return isInt(a) ? pow(sub(1, x), a) : mul(pow(sub(x, 1), a), exp(mul(sub(mul(2, n), 1), pi, I, a)));
    },
    bigMinus: (a, x, n) => {
      return isInt(a) ? pow(add(1, x), a) : mul(pow(add(1, x), a), exp(mul(2, n, pi, I, a)));
    },
  },
  power2: {
    small: (a, x) => mul(pow(2, sub(mul(2, a), 1)), pow(add(1, sqrt(sub(1, x))), sub(1, mul(2, a)))),
    smallMinus: (a, x) => mul(pow(2, sub(mul(2, a), 1)), pow(add(1, sqrt(add(1, x))), sub(1, mul(2, a)))),
    big: (a, x, n0) => {
      const odd = !isEven(n0);
      const n = odd ? sub(n0, 1) : n0;
      return mul(pow(2, sub(mul(2, a), 1)), pow(add(1, mul(odd ? 1 : -1, I, sqrt(sub(x, 1)))), sub(1, mul(2, a))), exp(mul(-2, n, pi, I, a)));
    },
    bigMinus: (a, x, n) => {
      const sgn = isEven(n) ? 1 : -1;
      return mul(sgn, pow(2, sub(mul(2, a), 1)), pow(add(sqrt(add(1, x)), sgn), sub(1, mul(2, a))), exp(mul(-2, pi, I, a, n)));
    },
  },
  log1: {
    small: (_a, x) => log(sub(1, x)),
    smallMinus: (_a, x) => log(add(1, x)),
    big: (_a, x, n) => add(log(sub(x, 1)), ipi(sub(mul(2, n), 1))),
    bigMinus: (_a, x, n) => add(log(add(1, x)), ipi(mul(2, n))),
  },
  atanh: {
    small: (_a, x) => div(fn('atanh', [sqrt(x)]), sqrt(x)),
    smallMinus: (_a, x) => div(atan(sqrt(x)), sqrt(x)),
    big: (_a, x, n) => div(add(fn('acoth', [sqrt(x)]), mul(isEven(n) ? 1 : -1, I, pi, half)), sqrt(x)),
    bigMinus: (_a, x, n) => div(isEven(n) ? atan(sqrt(x)) : sub(atan(sqrt(x)), pi), sqrt(x)),
  },
  asin1: {
    small: (_a, z) => div(asin(sqrt(z)), sqrt(z)),
    smallMinus: (_a, z) => div(fn('asinh', [sqrt(z)]), sqrt(z)),
    big: (_a, z, n) => mul(pow(-1, n), add(div(mul(sub(half, n), pi), sqrt(z)), div(mul(I, fn('acosh', [sqrt(z)])), sqrt(z)))),
    bigMinus: (_a, z, n) => mul(pow(-1, n), add(div(fn('asinh', [sqrt(z)]), sqrt(z)), div(mul(n, pi, I), sqrt(z)))),
  },
  asin2: {
    small: (_a, z) => div(REPS.asin1.small(S.Zero, z), REPS.power1.small(half, z)),
    smallMinus: (_a, z) => div(REPS.asin1.smallMinus(S.Zero, z), REPS.power1.smallMinus(half, z)),
    big: (_a, z, n) => div(REPS.asin1.big(S.Zero, z, n), REPS.power1.big(half, z, n)),
    bigMinus: (_a, z, n) => div(REPS.asin1.bigMinus(S.Zero, z, n), REPS.power1.bigMinus(half, z, n)),
  },
  sqrts1: {
    small: (a, z) => div(add(pow(sub(1, sqrt(z)), mul(2, a)), pow(add(1, sqrt(z)), mul(2, a))), 2),
    smallMinus: (a, z) => mul(pow(add(1, z), a), cos(mul(2, a, atan(sqrt(z))))),
    big: (a, z, n0) => {
      if (isEven(n0)) return div(add(mul(pow(add(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, n0, a))), mul(pow(sub(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, sub(n0, 1), a)))), 2);
      const n = sub(n0, 1);
      return div(add(mul(pow(sub(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, a, add(n, 1)))), mul(pow(add(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, a, n)))), 2);
    },
    bigMinus: (a, z, n) => {
      const c = mul(2, a, atan(sqrt(z)));
      return mul(pow(add(1, z), a), exp(mul(2, pi, I, n, a)), cos(isEven(n) ? c : sub(c, mul(2, pi, a))));
    },
  },
  sqrts2: {
    small: (a, z) => mul(sqrt(z), div(sub(pow(sub(1, sqrt(z)), mul(2, a)), pow(add(1, sqrt(z)), mul(2, a))), 2)),
    smallMinus: (a, z) => mul(sqrt(z), pow(add(1, z), a), sin(mul(2, a, atan(sqrt(z))))),
    big: (a, z, n0) => {
      if (isEven(n0)) return mul(div(sqrt(z), 2), sub(mul(pow(sub(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, a, sub(n0, 1)))), mul(pow(add(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, a, n0)))));
      const n = sub(n0, 1);
      return mul(div(sqrt(z), 2), sub(mul(pow(sub(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, a, add(n, 1)))), mul(pow(add(sqrt(z), 1), mul(2, a)), exp(mul(2, pi, I, a, n)))));
    },
    bigMinus: (a, z, n) => {
      const c = mul(2, a, atan(sqrt(z)));
      return mul(pow(add(1, z), a), exp(mul(2, pi, I, n, a)), sqrt(z), sin(isEven(n) ? c : sub(c, mul(2, pi, a))));
    },
  },
  log2: {
    small: (_a, z) => log(add(half, div(sqrt(sub(1, z)), 2))),
    smallMinus: (_a, z) => log(add(half, div(sqrt(add(1, z)), 2))),
    big: (_a, z, n) => add(ipi(sub(n, half)), log(div(sqrt(z), 2)), mul(isEven(n) ? 1 : -1, I, asin(pow(sqrt(z), -1)))),
    bigMinus: (_a, z, n) => add(ipi(n), log(isEven(n) ? add(half, div(sqrt(add(1, z)), 2)) : sub(div(sqrt(add(1, z)), 2), half))),
  },
  cosasin: {
    small: (a, z) => cos(mul(2, a, asin(sqrt(z)))),
    smallMinus: (a, z) => cosh(mul(2, a, fn('asinh', [sqrt(z)]))),
    big: (a, z, n) => cosh(add(mul(2, a, fn('acosh', [sqrt(z)])), mul(a, pi, I, sub(mul(2, n), 1)))),
    bigMinus: (a, z, n) => cosh(add(mul(2, a, fn('asinh', [sqrt(z)])), mul(2, a, pi, I, n))),
  },
  sinasin: {
    small: (a, z) => mul(div(sqrt(z), sqrt(sub(1, z))), sin(mul(2, a, asin(sqrt(z))))),
    smallMinus: (a, z) => mul(-1, div(sqrt(z), sqrt(add(1, z))), sinh(mul(2, a, fn('asinh', [sqrt(z)])))),
    big: (a, z, n) => mul(-1, pow(sqrt(sub(1, pow(z, -1))), -1), sinh(add(mul(2, a, fn('acosh', [sqrt(z)])), mul(a, pi, I, sub(mul(2, n), 1))))),
    bigMinus: (a, z, n) => mul(-1, pow(sqrt(add(1, pow(z, -1))), -1), sinh(add(mul(2, a, fn('asinh', [sqrt(z)])), mul(2, a, pi, I, n)))),
  },
};

/** A representative of a hypergeometric function branched at 1 (SymPy HyperRep_*). */
export class HyperRep extends ExtensionExpr {
  constructor(
    readonly rep: HyperRepName,
    args: readonly Expr[],
  ) {
    // the parameters are not polar (SymPy HyperRep.eval)
    super(`HyperRep_${rep}`, [...args.slice(0, -1).map((a) => unpolarify(a)), at(args, -1)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new HyperRep(this.rep, args);
  }
  /** The closed form: 'nonrepsmall' for |x| < 1, 'nonrep' with the branch for |x| > 1 as well. */
  closedForm(target: 'nonrep' | 'nonrepsmall'): Expr {
    const [x, n0] = extractBranchFactor(at(this.args, -1), true);
    const params = this.args.length > 1 ? first(this.args) : S.Zero;
    const minus = !isInt(n0);
    const forms = REPS[this.rep];
    const small = minus ? forms.smallMinus(params, x) : forms.small(params, x);
    if (target === 'nonrepsmall') return small;
    const big = minus ? forms.bigMinus(params, x, sub(n0, half)) : forms.big(params, x, n0);
    return big.key === small.key ? small : piecewise([big, Gt(abs(x), 1)], [small, true]);
  }
}
const hrep = (rep: HyperRepName, ...args: ExprLike[]): Expr => new HyperRep(rep, args.map(sympify));
/** Replace the HyperRep functions by closed forms (SymPy rewrite('nonrep') and rewrite('nonrepsmall')). */
const rewriteReps = (e: Expr, target: 'nonrep' | 'nonrepsmall'): Expr => mapBottomUp(e, (t) => (t instanceof HyperRep ? t.closedForm(target) : t));

// ---- formulas ---------------------------------------------------------------------------

/** A formula: closed form C*B with z*d/dz B = M B (SymPy Formula). */
interface Formula {
  func: HyperFunc;
  z: Expr;
  symbols: Expr[];
  B: Expr[];
  C: Expr[];
  M: Expr[][];
}
const mapMat = (M: readonly (readonly Expr[])[], f: (e: Expr) => Expr): Expr[][] => M.map((r) => r.map(f));

/** The characteristic polynomial x*prod(x + b - 1) - z*prod(x + a) of the hypergeometric equation. */
const charPoly = (func: HyperFunc, z: Expr): XPoly => padd(pprod([lin(0, 1), ...func.bq.map((b) => lin(sub(b, 1), 1))]), pscale(pprod(func.ap.map((a) => lin(a, 1))), neg(z)));

/** A formula from a closed form, with the basis of its z*d/dz derivatives (SymPy Formula._compute_basis). */
function formulaFromClosedForm(func: HyperFunc, z: Expr, res: Expr, symbols: readonly Expr[]): Formula {
  const poly = charPoly(func, z);
  const n = poly.length - 2;
  const B = [res];
  for (let k = 0; k < n; k++) B.push(mul(z, diff(at(B, -1), z)));
  const C = [S.One, ...Array.from({ length: n }, () => S.Zero)];
  const lc = at(poly, -1);
  const M = Array.from({ length: n + 1 }, (_, i) =>
    Array.from({ length: n + 1 }, (__, j) => {
      if (i < n) return j === i + 1 ? S.One : S.Zero;
      return neg(div(at(poly, j), lc));
    }),
  );
  return { func, z, symbols: symbols.filter((s) => [...func.ap, ...func.bq].some((p) => p.has(s))), B, C, M };
}

/** The table of hypergeometric formulas (SymPy add_formulae). */
function addFormulae(): Formula[] {
  const a = new Dummy('a');
  const b = new Dummy('b');
  const c = new Dummy('c');
  const z = new Dummy('z');
  const syms = [a, b, c];
  const out: Formula[] = [];
  const add0 = (ap: ExprLike[], bq: ExprLike[], res: Expr) => out.push(formulaFromClosedForm(hyperFunc(ap, bq), z, res, syms));
  const addb = (ap: ExprLike[], bq: ExprLike[], B: Expr[], C: ExprLike[], M: ExprLike[][]) => {
    const func = hyperFunc(ap, bq);
    out.push({ func, z, symbols: syms.filter((s) => [...func.ap, ...func.bq].some((p) => p.has(s))), B, C: C.map(sympify), M: M.map((r) => r.map(sympify)) });
  };
  const omz = sub(1, z);
  // 0F0, 1F0
  add0([], [], exp(z));
  add0([a], [], hrep('power1', neg(a), z));
  // 2F1
  addb([a, sub(a, half)], [mul(2, a)], [hrep('power2', a, z), div(hrep('power2', add(a, half), z), 2)], [1, 0], [
    [div(mul(sub(a, half), z), omz), div(mul(sub(half, a), z), omz)],
    [div(a, omz), div(mul(a, sub(z, 2)), omz)],
  ]);
  addb([1, 1], [2], [hrep('log1', z), S.One], [neg(pow(z, -1)), 0], [
    [0, div(z, sub(z, 1))],
    [0, 0],
  ]);
  addb([half, 1], [R(3, 2)], [hrep('atanh', z), S.One], [1, 0], [
    [R(-1, 2), div(pow(omz, -1), 2)],
    [0, 0],
  ]);
  addb([half, half], [R(3, 2)], [hrep('asin1', z), hrep('power1', R(-1, 2), z)], [1, 0], [
    [R(-1, 2), half],
    [0, div(div(z, omz), 2)],
  ]);
  addb([a, add(half, a)], [half], [hrep('sqrts1', neg(a), z), neg(hrep('sqrts2', sub(neg(a), half), z))], [1, 0], [
    [0, neg(a)],
    [div(mul(z, sub(mul(-2, a), 1)), mul(2, omz)), sub(half, div(mul(z, sub(mul(-2, a), 1)), omz))],
  ]);
  addb([a, neg(a)], [half], [hrep('cosasin', a, z), hrep('sinasin', a, z)], [1, 0], [
    [0, neg(a)],
    [div(mul(a, z), omz), div(pow(omz, -1), 2)],
  ]);
  addb([1, 1], [R(3, 2)], [hrep('asin2', z), S.One], [1, 0], [
    [div(sub(z, half), omz), div(pow(omz, -1), 2)],
    [0, 0],
  ]);
  // 3F2
  addb([R(-1, 2), 1, 1], [half, 2], [mul(z, hrep('atanh', z)), hrep('log1', z), S.One], [R(-2, 3), neg(div(1, mul(3, z))), R(2, 3)], [
    [half, 0, div(div(z, omz), 2)],
    [0, 0, div(z, sub(z, 1))],
    [0, 0, 0],
  ]);
  addb([R(-1, 2), 1, 1], [2, 2], [hrep('power1', half, z), hrep('log2', z), S.One], [sub(R(4, 9), div(16, mul(9, z))), div(4, mul(3, z)), div(16, mul(9, z))], [
    [div(div(z, 2), sub(z, 1)), 0, 0],
    [div(1, mul(2, sub(z, 1))), 0, half],
    [0, 0, 0],
  ]);
  // 1F1
  addb([1], [b], [mul(pow(z, sub(1, b)), exp(z), lowergamma(sub(b, 1), z)), S.One], [sub(b, 1), 0], [
    [add(sub(1, b), z), 1],
    [0, 0],
  ]);
  const ib = (nu: Expr) => mul(pow(z, sub(half, a)), exp(div(z, 2)), besseli(nu, div(z, 2)), gamma(add(a, half)), pow(pow(4, sub(half, a)), -1));
  addb([a], [mul(2, a)], [ib(sub(a, half)), ib(add(a, half))], [1, 0], [
    [div(z, 2), div(z, 2)],
    [div(z, 2), sub(div(z, 2), mul(2, a))],
  ]);
  const mz = mul(polarLift(-1), z);
  addb([a], [add(a, 1)], [mul(pow(mz, neg(a)), a, lowergamma(a, mz)), mul(a, exp(z))], [1, 0], [
    [neg(a), 1],
    [0, z],
  ]);
  add0([R(-1, 2)], [half], sub(exp(z), mul(sqrt(mul(pi, z)), neg(I), erf(mul(I, sqrt(z))))));
  const r4 = pow(z, R(1, 4));
  const eI4 = exp(div(mul(I, pi), 4));
  const fr = (f: (e: Expr) => Expr) => f(div(mul(2, r4, eI4), sqrt(pi)));
  addb([1], [R(3, 4), R(5, 4)], [
    div(mul(sqrt(pi), add(mul(I, sinh(mul(2, sqrt(z))), fr(fresnels)), mul(cosh(mul(2, sqrt(z))), fr(fresnelc))), exp(div(mul(-1, I, pi), 4))), mul(2, r4)),
    div(mul(sqrt(pi), r4, add(mul(sinh(mul(2, sqrt(z))), fr(fresnelc)), mul(I, cosh(mul(2, sqrt(z))), fr(fresnels))), exp(div(mul(-1, I, pi), 4))), 2),
    S.One,
  ], [1, 0, 0], [
    [R(-1, 4), 1, R(1, 4)],
    [z, R(1, 4), 0],
    [0, 0, 0],
  ]);
  // 2F2
  const c2 = div(a, sub(mul(2, a), 1));
  addb([half, a], [R(3, 2), add(a, 1)], [mul(c2, neg(I), sqrt(div(pi, z)), erf(mul(I, sqrt(z)))), mul(c2, pow(mz, neg(a)), lowergamma(a, mz)), mul(c2, exp(z))], [1, -1, 0], [
    [R(-1, 2), 0, 1],
    [0, neg(a), 1],
    [0, 0, z],
  ]);
  addb([1, 1], [2, 2], [sub(Ei(z), log(z)), exp(z), S.One, S.EulerGamma], [pow(z, -1), 0, 0, neg(pow(z, -1))], [
    [0, 1, -1, 0],
    [0, z, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
  ]);
  // 0F1
  add0([], [half], cosh(mul(2, sqrt(z))));
  addb([], [b], [mul(gamma(b), pow(z, div(sub(1, b), 2)), besseli(sub(b, 1), mul(2, sqrt(z)))), mul(gamma(b), pow(z, sub(1, div(b, 2))), besseli(b, mul(2, sqrt(z))))], [1, 0], [
    [0, 1],
    [z, sub(1, b)],
  ]);
  // 0F3
  const x4 = mul(4, r4);
  const fp = (nu: Expr) => add(besseli(nu, x4), besselj(nu, x4));
  const fm = (nu: Expr) => sub(besseli(nu, x4), besselj(nu, x4));
  const k03 = mul(pow(2, mul(-2, a)), gamma(mul(2, a)), pow(z, div(sub(1, mul(2, a)), 4)));
  addb([], [half, a, add(a, half)], [fp(sub(mul(2, a), 1)), mul(fm(mul(2, a)), r4), mul(fm(sub(mul(2, a), 1)), sqrt(z)), mul(fp(mul(2, a)), pow(z, R(3, 4)))].map((e) => mul(e, k03)), [1, 0, 0, 0], [
    [0, 1, 0, 0],
    [0, sub(half, a), 1, 0],
    [0, 0, half, 1],
    [z, 0, 0, sub(1, a)],
  ]);
  const xx = mul(2, pow(mul(4, z), R(1, 4)), expPolar(div(mul(I, pi), 4)));
  const k3 = mul(pow(mul(2, sqrt(mul(polarLift(-1), z))), sub(1, mul(2, a))), pow(gamma(mul(2, a)), 2));
  const J = (nu: Expr) => besselj(nu, xx);
  const Iv = (nu: Expr) => besseli(nu, xx);
  const a2 = mul(2, a);
  const a21 = sub(a2, 1);
  addb([], [a, add(a, half), mul(2, a)], [
    mul(J(a21), Iv(a21)),
    mul(xx, sub(mul(Iv(a2), J(a21)), mul(Iv(a21), J(a2)))),
    mul(pow(xx, 2), Iv(a2), J(a2)),
    mul(pow(xx, 3), add(mul(Iv(a2), J(a21)), mul(Iv(a21), J(a2)))),
  ].map((e) => mul(k3, e)), [1, 0, 0, 0], [
    [0, R(1, 4), 0, 0],
    [0, div(sub(1, a2), 2), R(-1, 2), 0],
    [0, 0, sub(1, a2), R(1, 4)],
    [mul(-32, z), 0, 0, sub(1, a)],
  ]);
  // 1F2
  const sz = sqrt(z);
  addb([a], [sub(a, half), mul(2, a)], [
    mul(pow(z, sub(half, a)), pow(besseli(sub(a, half), sz), 2)),
    mul(pow(z, sub(1, a)), besseli(sub(a, half), sz), besseli(sub(a, R(3, 2)), sz)),
    mul(pow(z, sub(R(3, 2), a)), pow(besseli(sub(a, R(3, 2)), sz), 2)),
  ], [div(neg(pow(gamma(add(a, half)), 2)), pow(4, sub(half, a))), div(mul(2, gamma(sub(a, half)), gamma(add(a, half))), pow(4, sub(1, a))), 0], [
    [sub(1, a2), 1, 0],
    [div(z, 2), sub(half, a), half],
    [0, z, 0],
  ]);
  const kb = div(mul(pi, sub(1, b)), sin(mul(pi, b)));
  addb([half], [b, sub(2, b)], [
    mul(besseli(sub(1, b), sz), besseli(sub(b, 1), sz)),
    mul(sz, add(mul(besseli(neg(b), sz), besseli(sub(b, 1), sz)), mul(besseli(sub(1, b), sz), besseli(b, sz)))),
    mul(besseli(neg(b), sz), besseli(b, sz)),
  ].map((e) => mul(kb, e)), [1, 0, 0], [
    [sub(b, 1), half, 0],
    [z, 0, z],
    [0, half, neg(b)],
  ]);
  const s2z = mul(2, sz);
  addb([half], [R(3, 2), R(3, 2)], [div(div(Shi(s2z), 2), sz), div(div(sinh(s2z), 2), sz), cosh(s2z)], [1, 0, 0], [
    [R(-1, 2), half, 0],
    [0, R(-1, 2), half],
    [0, mul(2, z), 0],
  ]);
  const fa = mul(eI4, r4, 2, pow(sqrt(pi), -1));
  addb([R(3, 4)], [R(3, 2), R(7, 4)], [div(fresnels(fa), mul(pi, pow(fa, 3))), div(sinh(s2z), sz), cosh(s2z)], [6, 0, 0], [
    [R(-3, 4), R(1, 16), 0],
    [0, R(-1, 2), 1],
    [0, z, 0],
  ]);
  addb([R(1, 4)], [half, R(5, 4)], [div(mul(sqrt(pi), exp(div(mul(-1, I, pi), 4)), fresnelc(div(mul(2, r4, eI4), sqrt(pi)))), mul(2, r4)), cosh(s2z), mul(sinh(s2z), sz)], [1, 0, 0], [
    [R(-1, 4), R(1, 4), 0],
    [0, 0, 1],
    [0, z, half],
  ]);
  // 2F3
  const k23 = mul(gamma(b), gamma(add(sub(a2, b), 1)), pow(div(sz, 2), sub(1, a2)));
  addb([a, add(a, half)], [a2, b, add(sub(a2, b), 1)], [
    mul(besseli(sub(b, 1), sz), besseli(sub(a2, b), sz)),
    mul(sz, besseli(b, sz), besseli(sub(a2, b), sz)),
    mul(sz, besseli(sub(b, 1), sz), besseli(add(sub(a2, b), 1), sz)),
    mul(besseli(b, sz), besseli(add(sub(a2, b), 1), sz)),
  ].map((e) => mul(k23, e)), [1, 0, 0, 0], [
    [0, half, half, 0],
    [div(z, 2), sub(1, b), 0, div(z, 2)],
    [div(z, 2), 0, sub(b, a2), div(z, 2)],
    [0, half, half, neg(a2)],
  ]);
  addb([1, 1], [2, 2, R(3, 2)], [sub(Chi(s2z), log(s2z)), cosh(s2z), mul(sz, sinh(s2z)), S.One, S.EulerGamma], [pow(z, -1), 0, 0, 0, neg(pow(z, -1))], [
    [0, half, 0, R(-1, 2), 0],
    [0, 0, 1, 0, 0],
    [0, z, half, 0, 0],
    [0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0],
  ]);
  // 3F3
  const d33 = add(pow(a, 2), mul(-2, a), 1);
  addb([1, 1, a], [2, 2, add(a, 1)], [
    div(mul(a, add(log(neg(z)), expint(1, neg(z)), S.EulerGamma)), mul(z, d33)),
    div(mul(a, pow(neg(z), neg(a)), sub(gamma(a), uppergamma(a, neg(z)))), pow(sub(a, 1), 2)),
    div(mul(a, exp(z)), d33),
    div(a, mul(z, d33)),
  ], [sub(1, a), 1, neg(pow(z, -1)), 1], [
    [-1, 0, neg(pow(z, -1)), 1],
    [0, neg(a), 1, 0],
    [0, 0, z, 0],
    [0, 0, 0, -1],
  ]);
  return out;
}

let collection: { concrete: Map<string, Formula>; symbolic: Map<string, Formula[]> } | undefined;
function formulaCollection(): { concrete: Map<string, Formula>; symbolic: Map<string, Formula[]> } {
  if (collection) return collection;
  const concrete = new Map<string, Formula>();
  const symbolic = new Map<string, Formula[]>();
  for (const f of addFormulae()) {
    const sizes = `${f.func.ap.length},${f.func.bq.length}`;
    if (f.symbols.length) symbolic.set(sizes, [...(symbolic.get(sizes) ?? []), f]);
    else concrete.set(`${sizes}|${invariants(f.func)}`, f);
  }
  collection = { concrete, symbolic };
  return collection;
}

const floorQ = (q: Rational): number => Math.floor(q.value);
const ceilQ = (q: Rational): number => Math.ceil(q.value);
function cartesian<T>(lists: readonly (readonly T[])[]): T[][] {
  return lists.reduce<T[][]>((acc, l) => acc.flatMap((xs) => l.map((y) => [...xs, y])), [[]]);
}

/** Substitutions of the formula's symbols that may match func (SymPy Formula.find_instantiations). */
function findInstantiations(f: Formula, func: HyperFunc): Map<Expr, Expr>[] {
  const symbolValues = f.symbols.map((s) => (f.func.ap.some((p) => p.key === s.key) ? func.ap : func.bq));
  const baseRepl = cartesian(symbolValues).map((vals) => new Map(f.symbols.map((s, i) => [s, at(vals, i)] as const)));
  const [abuckets, bbuckets] = [buckets(func.ap), buckets(func.bq)];
  const critical: Rational[][] = f.symbols.map(() => [S.Zero]);
  const nDummy = new Dummy('n');
  const result: Map<Expr, Expr>[] = [];
  for (const repl of baseRepl) {
    const rep = (e: Expr, r: ReadonlyMap<Expr, Expr>) => expand(xreplace(e, [...r]));
    const symbA = sift(f.func.ap, (p) => mod1(rep(p, repl)));
    const symbB = sift(f.func.bq, (p) => mod1(rep(p, repl)));
    for (const [bk, obk] of [
      [abuckets, symbA],
      [bbuckets, symbB],
    ] as const) {
      for (const key of new Set([...bk.keys(), ...obk.keys()])) {
        const targets = bk.get(key)?.items;
        const exprs0 = obk.get(key)?.items;
        if (targets === undefined || exprs0 === undefined || targets.length !== exprs0.length) break;
        for (const [i, s] of f.symbols.entries()) {
          const v = at([...repl.values()], i);
          if (v.freeSymbols().size) continue;
          const repl0 = new Map(repl);
          repl0.set(s, add(v, nDummy));
          for (const e of exprs0.filter((x) => x.has(s))) {
            for (const t of targets) {
              // the solution of the linear equation e(repl0) = t for n
              const lhs = sub(rep(e, repl0), t);
              const c1 = diff(lhs, nDummy);
              at(critical, i).push(asRational(expand(neg(div(xreplace(lhs, [[nDummy, S.Zero]]), c1)))));
            }
          }
        }
      }
    }
    const values = f.symbols.map((_s, i) => {
      const vals = at(critical, i);
      const lo = Math.min(...vals.map(floorQ));
      const hi = Math.max(...vals.map(ceilQ));
      const a0 = at([...repl.values()], i);
      return Array.from({ length: hi - lo + 1 }, (_, k) => add(a0, lo + k));
    });
    for (const l of cartesian(values)) result.push(new Map(f.symbols.map((s, i) => [s, at(l, i)] as const)));
  }
  return result;
}

/** A formula reaching func, or undefined (SymPy FormulaCollection.lookup_origin). */
function lookupOrigin(func: HyperFunc): Formula | undefined {
  const { concrete, symbolic } = formulaCollection();
  const sizes = `${func.ap.length},${func.bq.length}`;
  const c = concrete.get(`${sizes}|${invariants(func)}`);
  if (c) return c;
  const possible: [number, Map<Expr, Expr>, Formula, HyperFunc][] = [];
  for (const f of symbolic.get(sizes) ?? []) {
    for (const repl of findInstantiations(f, func)) {
      const r = [...repl];
      const func2 = hyperFunc(
        f.func.ap.map((p) => xreplace(p, r)),
        f.func.bq.map((p) => xreplace(p, r)),
      );
      if (!isSuitableOrigin(func2)) continue;
      const d = difficulty(func2, func);
      if (d === -1) continue;
      possible.push([d, repl, f, func2]);
    }
  }
  possible.sort((u, v) => u[0] - v[0]);
  for (const [, repl, f, func2] of possible) {
    const r = [...repl];
    const s = (e: Expr) => xreplace(e, r);
    const f2: Formula = { func: func2, z: f.z, symbols: [], B: f.B.map(s), C: f.C.map(s), M: mapMat(f.M, s) };
    if (![...f2.B, ...f2.C, ...f2.M.flat()].some(isBad)) return f2;
  }
  return undefined;
}

// ---- Meijer G formulas ------------------------------------------------------------------

interface MeijerFormula {
  func: GFunc;
  z: Expr;
  B: Expr[];
  C: Expr[];
  M: Expr[][];
}
const isZeroMod1 = (e: Expr): boolean => {
  const m = mod1(simplify(e));
  return isRat(m) && m.isZero;
};
/** The formulas for G-functions that Slater's theorem cannot do (SymPy add_meijerg_formulae). */
function meijerFormulae(): { func: GFunc; match: (g: GFunc) => MeijerFormula | undefined }[] {
  const a = new Dummy('a');
  const rho = new Dummy('rho');
  const z = new Dummy('z');
  const make = (B: Expr[], C: ExprLike[], M: ExprLike[][]) => (subst: [Expr, Expr][], g: GFunc): MeijerFormula => {
    const s = (e: Expr) => xreplace(e, subst);
    return { func: g, z, B: B.map(s), C: C.map((c) => s(sympify(c))), M: M.map((r) => r.map((c) => s(sympify(c)))) };
  };
  const upper = make([mul(gamma(sub(1, a)), pow(z, rho), exp(z), uppergamma(a, z)), mul(gamma(sub(1, a)), pow(z, add(a, rho)))], [1, 0], [
    [add(rho, z), -1],
    [0, add(a, rho)],
  ]);
  // G(z) with an = [x], bm = [y, x]: z**y*exp(z)*Gamma(x - y, z)
  const detectUppergamma = (g: GFunc): MeijerFormula | undefined => {
    const x = first(g.an);
    let [y, w] = [first(g.bm), at(g.bm, 1)];
    const swapped = isZeroMod1(sub(x, y));
    if (swapped) [y, w] = [w, y];
    if (!isZeroMod1(sub(x, w)) || isPositive(sub(x, w)) === true) return undefined;
    return upper(
      [
        [rho, y],
        [a, sub(x, y)],
      ],
      gFunc([x], [], swapped ? [x, y] : [y, x], []),
    );
  };
  const s2 = sin(mul(2, sqrt(z)));
  const c2 = cos(mul(2, sqrt(z)));
  const S2 = sub(Si(mul(2, sqrt(z))), div(pi, 2));
  const C2 = Ci(mul(2, sqrt(z)));
  const f3113 = make([mul(sqrt(pi), pow(z, sub(a, half)), sub(mul(c2, S2), mul(s2, C2))), mul(sqrt(pi), pow(z, a), add(mul(s2, S2), mul(c2, C2))), mul(sqrt(pi), pow(z, a))], [-2, 0, 0], [
    [sub(a, half), -1, 0],
    [z, a, half],
    [0, 0, a],
  ]);
  // https://functions.wolfram.com/07.34.03.0984.01
  const detect3113 = (g: GFunc): MeijerFormula | undefined => {
    const x = first(g.an);
    const [u, v, w] = [at(g.bm, 0), at(g.bm, 1), at(g.bm, 2)];
    let sig: [Expr, Expr, Expr];
    let x1: Expr;
    let x2: Expr;
    let y: Expr;
    if (isZeroMod1(sub(u, v))) {
      if (isZeroMod1(sub(v, w))) return undefined;
      sig = [half, half, S.Zero];
      [x1, x2, y] = [u, v, w];
    } else if (isZeroMod1(sub(x, u))) {
      sig = [half, S.Zero, half];
      [x1, y, x2] = [u, v, w];
    } else {
      sig = [S.Zero, half, half];
      [y, x1, x2] = [u, v, w];
    }
    const m = mod1(simplify(sub(x, y)));
    if (!isZeroMod1(sub(x, x1)) || !isZeroMod1(sub(x, x2)) || m.key !== half.key || isPositive(sub(x, x1)) === true || isPositive(sub(x, x2)) === true) return undefined;
    return f3113([[a, x]], gFunc([x], [], sig.map((t) => add(sub(x, half), t)), []));
  };
  return [
    { func: gFunc([add(a, rho)], [], [rho, add(a, rho)], []), match: detectUppergamma },
    { func: gFunc([a], [], [a, a, sub(a, half)], []), match: detect3113 },
  ];
}
let meijerCollection: ReturnType<typeof meijerFormulae> | undefined;
function lookupMeijer(func: GFunc): MeijerFormula | undefined {
  meijerCollection ??= meijerFormulae();
  for (const f of meijerCollection) {
    if (signature(f.func) !== signature(func)) continue;
    const r = f.match(func);
    if (r) return r;
  }
  return undefined;
}

// ---- plans -------------------------------------------------------------------------------

/** Shift and un-shift operators taking origin to target (SymPy devise_plan). */
function devisePlan(target: HyperFunc, origin: HyperFunc, z: Expr): OpPoly[] {
  const ab = buckets(target.ap);
  const bb = buckets(target.bq);
  const A = defined2(ab);
  const B = defined2(bb);
  const NA = defined2(buckets(origin.ap));
  const NB = defined2(buckets(origin.bq));
  const ops: OpPoly[] = [];
  const doShifts = (fro: Expr[], to: readonly Expr[], inc: (p: Expr[], i: number) => OpPoly, dec: (p: Expr[], i: number) => OpPoly): OpPoly[] => {
    const out: OpPoly[] = [];
    for (const [i, t] of to.entries()) {
      const up = asRational(expand(sub(t, at(fro, i)))).isPositive;
      while (expand(sub(t, at(fro, i))).key !== S.Zero.key) {
        out.push((up ? inc : dec)(fro, i));
        fro[i] = add(at(fro, i), up ? 1 : -1);
      }
    }
    return out;
  };
  const others = (dic: Map<string, Expr[]>, key: string): Expr[] => [...dic].filter(([k]) => k !== key).flatMap(([, v]) => v);
  const keys = sorted([...new Map([...ab.values(), ...bb.values()].map((v) => [v.mod.key, v.mod])).values()]);
  for (const r of keys) {
    const al = sorted(A.get(r.key) ?? []);
    const nal = sorted(NA.get(r.key) ?? []);
    const bk = sorted(B.get(r.key) ?? []);
    const nbk = sorted(NB.get(r.key) ?? []);
    const aother = others(NA, r.key);
    const bother = others(NB, r.key);
    const shiftsA = (from: Expr[], nb: Expr[]) =>
      doShifts(
        from,
        al,
        (p, i) => shiftA(at(p, i)),
        (p, i) => unShiftA([...p, ...aother], [...nb, ...bother], i, z),
      );
    const shiftsB = (na: Expr[], from: Expr[]) =>
      doShifts(
        from,
        bk,
        (p, i) => unShiftB([...na, ...aother], [...p, ...bother], i, z),
        (p, i) => shiftB(at(p, i)),
      );
    if (al.length === 0) ops.push(...shiftsB([], nbk));
    else if (bk.length === 0) ops.push(...shiftsA(nal, []));
    else if (isPositive(sub(at(nal, -1), at(al, -1))) === true) {
      ops.push(...shiftsA(nal, nbk));
      ops.push(...shiftsB(al, nbk));
    } else {
      ops.push(...shiftsB(nal, nbk));
      ops.push(...shiftsA(nal, bk));
    }
    NA.set(r.key, al);
    NB.set(r.key, bk);
  }
  return ops.reverse();
}
const defined2 = (b: Map<string, { mod: Expr; items: Expr[] }>): Map<string, Expr[]> => new Map([...b].map(([k, v]) => [k, v.items]));

/**
 * Operators taking the G-function fro to to (SymPy devise_plan_meijer). The
 * Meijer G formulas of the table differ from the functions they match only in
 * the parameters bm, so only those are shifted.
 */
function devisePlanMeijer(fro: GFunc, to: GFunc, z: Expr): OpPoly[] {
  const f: GParams = [[...fro.an], [...fro.ap], [...fro.bm], [...fro.bq]];
  const fbm = f[2];
  const ops: OpPoly[] = [];
  const step = (): OpPoly | undefined => {
    // a decrease first (MeijerUnShiftA, unless the parameter meets an upper one), then an increase (MeijerShiftA)
    for (const [idx, b] of fbm.entries()) {
      if (asRational(expand(sub(at(to.bm, idx), b))).isNegative && [...f[0], ...f[1]].every((x) => x.key !== b.key)) {
        const op = meijerUnShiftA(f, idx, z);
        fbm[idx] = sub(b, 1);
        return op;
      }
    }
    for (const [idx, b] of fbm.entries()) {
      if (asRational(expand(sub(at(to.bm, idx), b))).isPositive) {
        fbm[idx] = add(b, 1);
        return { poly: lin(b, -1) };
      }
    }
    return undefined;
  };
  for (let op = step(); op; op = step()) ops.push(op);
  return ops.reverse();
}

// ---- special cases ------------------------------------------------------------------------

/** A hypergeometric sum starting at k > 0 (SymPy try_shifted_sum). */
function tryShiftedSum(func: HyperFunc, z: Expr): [HyperFunc, OpPoly[], Expr] | undefined {
  const ab = buckets(func.ap);
  const bb = buckets(func.bq);
  const a0 = bucket(ab, S.Zero);
  if (a0.length !== 1) return undefined;
  // (r > 0 and k > 0: a nonpositive integer parameter makes the series a polynomial, tried before)
  const r = asRational(first(a0));
  const b0 = sorted(bucket(bb, S.Zero));
  if (b0.length === 0) return undefined;
  const k0 = asRational(first(b0));
  const nap0 = [...func.ap];
  removeOne(nap0, r);
  const nbq0 = [...func.bq];
  removeOne(nbq0, k0);
  const k = Number(k0.p) - 1;
  const nap = nap0.map((x) => sub(x, k));
  const nbq = nbq0.map((x) => sub(x, k));
  const ops: OpPoly[] = Array.from({ length: Number(r.p) - 1 }, (_, n) => shiftA(R(n + 1))).reverse();
  ops.push(multOperator(div(mul(factorial(k), pow(z, -k), prod(nbq.map((b) => rf(b, k)))), prod(nap.map((a) => rf(a, k))))));
  const p = sum(Array.from({ length: k }, (_, n) => div(mul(pow(z, n), prod(nap.map((a) => rf(a, n)))), mul(factorial(n), prod(nbq.map((b) => rf(b, n)))))));
  return [hyperFunc(nap, nbq), ops, neg(p)];
}

/** A terminating series, oo for an undefined one, undefined otherwise (SymPy try_polynomial). */
function tryPolynomial(func: HyperFunc, z: Expr): Expr | undefined {
  const al0 = sorted(bucket(buckets(func.ap), S.Zero)).filter((x) => !asRational(x).isPositive);
  const bl0 = sorted(bucket(buckets(func.bq), S.Zero)).filter((x) => !asRational(x).isPositive);
  if (bl0.length && al0.every((a) => asRational(a).value < asRational(at(bl0, -1)).value)) return S.Infinity;
  if (!al0.length) return undefined;
  const a = asRational(at(al0, -1));
  let fac: Expr = S.One;
  let res: Expr = S.One;
  for (let n = 0; n < -Number(a.p); n++) {
    fac = div(mul(fac, z, prod(func.ap.map((x) => add(x, n)))), mul(n + 1, prod(func.bq.map((b) => add(b, n)))));
    res = add(res, fac);
  }
  return res;
}

/** A formula in terms of hypergeometric functions with shifted parameters (SymPy build_hypergeometric_formula). */
function buildHypergeometricFormula(func: HyperFunc): Formula {
  const z = new Dummy('z');
  if (func.ap.length) {
    const poly = charPoly(func, z);
    const n = poly.length - 1;
    const M: Expr[][] = Array.from({ length: n }, () => Array.from({ length: n }, () => S.Zero));
    const B: Expr[] = [];
    for (let k = 0; k < n; k++) {
      const a = add(first(func.ap), k);
      B.push(hyper([a, ...func.ap.slice(1)], func.bq, z));
      if (k < n - 1) {
        at(M, k)[k] = neg(a);
        at(M, k)[k + 1] = a;
      }
    }
    const C = [S.One, ...Array.from({ length: n - 1 }, () => S.Zero)];
    const matmul = (X: Expr[][], Y: Expr[][]) => X.map((r) => first(Y).map((_, j) => sum(r.map((x, i) => mul(x, at(at(Y, i), j))))));
    const derivs: Expr[][][] = [Array.from({ length: n }, (_, i) => Array.from({ length: n }, (__, j) => (i === j ? S.One : S.Zero)))];
    for (let k = 0; k < n; k++) derivs.push(matmul(M, at(derivs, k)));
    const res: Expr[] = Array.from({ length: n }, () => S.Zero);
    for (const [k, c] of poly.entries()) {
      const row = at(at(derivs, k), 0);
      for (const [r, d] of row.entries()) res[r] = add(at(res, r), mul(c, d));
    }
    for (const [k, c] of res.entries()) at(M, n - 1)[k] = neg(div(div(c, at(at(at(derivs, n - 1), 0), n - 1)), at(poly, -1)));
    return { func, z, symbols: [], B, C, M: mapMat(M, expand) };
  }
  const bq = [...func.bq];
  const B: Expr[] = [];
  for (const [i] of bq.entries()) {
    B.push(hyper([], bq, z));
    bq[i] = add(at(bq, i), 1);
  }
  B.push(hyper([], bq, z));
  const n = B.length;
  const C = [S.One, ...Array.from({ length: n - 1 }, () => S.Zero)];
  const M: Expr[][] = Array.from({ length: n }, () => Array.from({ length: n }, () => S.Zero));
  at(M, 0)[n - 1] = div(z, prod(func.bq));
  for (let k = 1; k < n; k++) {
    at(M, k)[k - 1] = at(func.bq, k - 1);
    at(M, k)[k] = neg(at(func.bq, k - 1));
  }
  return { func, z, symbols: [], B, C, M };
}

/** Classical summation formulas (Gauss, Kummer) at special points (SymPy hyperexpand_special). */
function hyperexpandSpecial(ap: readonly Expr[], bq: readonly Expr[], z0: Expr): Expr {
  const z = unpolarify(z0);
  if (ap.length === 2 && bq.length === 1) {
    let [a, b] = [first(ap), at(ap, 1)];
    const c = first(bq);
    if (z.key === S.One.key) return div(mul(gamma(sub(sub(c, a), b)), gamma(c)), mul(gamma(sub(c, a)), gamma(sub(c, b))));
    if (z.key === S.NegOne.key && simplify(add(sub(b, a), c)).key === S.One.key) [a, b] = [b, a];
    if (z.key === S.NegOne.key && simplify(add(sub(a, b), c)).key === S.One.key) {
      // (a negative integer b makes the series a polynomial, summed before)
      return div(mul(gamma(add(div(b, 2), 1)), gamma(add(sub(b, a), 1))), mul(gamma(add(b, 1)), gamma(add(sub(div(b, 2), a), 1))));
    }
  }
  return hyper(ap, bq, z0);
}
const replaceHyperSpecial = (e: Expr): Expr => mapBottomUp(e, (t) => (t instanceof Hyper ? hyperexpandSpecial(t.ap, t.bq, t.argument) : t));

/**
 * The incomplete gamma functions on other sheets: lowergamma(a, z*exp_polar(2*pi*I*n))
 * = exp(2*pi*I*n*a)*lowergamma(a, z) (as SymPy's lowergamma evaluates them).
 */
export function liftBranches(e: Expr): Expr {
  const polar = (z: Expr | undefined): boolean => z !== undefined && some(z, (n) => n instanceof Fn && n.name === 'exp_polar');
  return mapBottomUp(e, (t) => {
    if (!(t instanceof Fn)) return t;
    if (t.name === 'lowergamma' && polar(t.args[1])) {
      const [a, z] = [first(t.args), at(t.args, 1)];
      const [w, n] = extractBranchFactor(z);
      return isRat(n) && !n.isZero && !polar(w) ? mul(exp(mul(2, pi, I, n, a)), fn('lowergamma', [a, w])) : t;
    }
    // Ei(w*exp_polar(I*pi*m)) = Ei((-1)**m*w) + I*pi*m, Ei being real on the negative axis
    if (t.name === 'Ei' && polar(t.args[0])) {
      const [w, n] = extractBranchFactor(first(t.args), true);
      const m = mul(2, n);
      return isInt(m) && !m.isZero && !polar(w) ? add(Ei(mul(pow(-1, m), w)), mul(I, pi, m)) : t;
    }
    return t;
  });
}

/**
 * SymPy unpolarify: it rebuilds every node, so hyper.eval drops the polar factors of an argument
 * at which the function is not branched (Hyper nodes are rebuilt here for that).
 */
export function unpolarifyEval(e: Expr, opts: { subs?: Substitution } = {}): Expr {
  return mapBottomUp(unpolarify(e, opts), (t) => (t instanceof Hyper ? hyper(t.ap, t.bq, t.argument) : t));
}

/**
 * The polar factors of a power's base are split off as in SymPy's _denest_pow:
 * (p*q*x)**e = p**e*q**e*x**e for polar p, q (a polar number has no branch cut).
 */
function denestPolarPow(t: Expr): Expr {
  if (!(t instanceof Pow)) return t;
  const factors = t.base instanceof Mul ? t.base.args : [t.base];
  const polars = factors.filter(isPolar);
  if (polars.length === 0) return t;
  const rest = mul(...factors.filter((f) => !isPolar(f)));
  return mul(...polars.map((f) => (f instanceof Pow ? pow(f.base, mul(f.exp, t.exp)) : pow(f, t.exp))), pow(rest, t.exp));
}

/**
 * SymPy powdenest(e, polar=True): polarify (the symbols replaced by polar dummies), unpolarify the
 * exponents, denest, then substitute the symbols back and unpolarify.
 */
export function powdenestPolar(e: Expr): Expr {
  const [eq, rep] = expectType(polarify(e), (r): r is [Expr, [Expr, Expr][]] => Array.isArray(r), 'polarify');
  return unpolarifyEval(mapBottomUp(powdenest(unpolarify(eq, { exponentsOnly: true })), denestPolarPow), { subs: rep });
}

const z0Default = new Dummy('z0');
/** polarify(e, subs=False), which is an expression. */
const polarifyNoSubs = (e: Expr): Expr => expectType(polarify(e, { subs: false }), (r): r is Expr => !Array.isArray(r), 'polarify');

/**
 * The closed form of the hypergeometric function func at z, multiplied by
 * premult = a*z0**prem and with ops0 applied (SymPy _hyperexpand).
 */
function hyperexpandFunc(func0: HyperFunc, zIn: Expr, ops0: readonly OpPoly[] = [], z0: Expr = z0Default, premult: Expr = S.One, prem: Expr = S.Zero, rewrite: 'nonrepsmall' | 'none' = 'nonrepsmall'): Expr {
  if (zIn instanceof Rational && zIn.isZero) return S.One;
  const z = polarifyNoSubs(zIn);
  const carryout = (f: Formula, ops: readonly OpPoly[]): Expr => {
    const s0 = (e: Expr) => xreplace(e, [[f.z, z0]]);
    const M = mapMat(f.M, s0);
    let C = applyOperators(f.C.map(s0), ops, derivativeOperator(M, z0));
    C = applyOperators(C, ops0, derivativeOperator(M.map((r, i) => r.map((c, j) => (i === j ? add(c, prem) : c))), z0));
    if (premult.key === S.One.key) C = C.map(simp);
    const r = mul(sum(C.map((c, i) => mul(c, s0(at(f.B, i))))), premult);
    const res = xreplace(r, [[z0, z]]);
    return rewrite === 'none' ? res : rewriteReps(res, rewrite);
  };
  const [rfunc, rops] = reduceOrderHyper(func0);
  let func = rfunc;
  const ops = [...rops];
  const poly = tryPolynomial(func, z0);
  if (poly !== undefined) {
    let p = first(applyOperators([poly], ops, zDeriv(z0)));
    p = first(applyOperators([mul(p, premult)], ops0, zDeriv(z0)));
    return unpolarifyEval(xreplace(simplify(p), [[z0, z]]));
  }
  let p: Expr = S.Zero;
  const shifted = tryShiftedSum(func, z0);
  if (shifted) {
    const [f2, nops, p2] = shifted;
    func = f2;
    ops.push(...nops);
    p = p2;
  }
  p = first(applyOperators([p], ops, zDeriv(z0)));
  p = first(applyOperators([mul(p, premult)], ops0, zDeriv(z0)));
  p = xreplace(simplify(p), [[z0, z]]);
  const uz = unpolarify(z);
  if ((uz.key === S.One.key || uz.key === S.NegOne.key) && func.ap.length === 2 && func.bq.length === 1) {
    const r = replaceHyperSpecial(carryout(buildHypergeometricFormula(func), ops));
    if (!some(r, (n) => n instanceof Hyper)) return add(r, p);
  }
  const formula = lookupOrigin(func) ?? buildHypergeometricFormula(func);
  ops.push(...devisePlan(func, formula.func, z0));
  const r = add(carryout(formula, ops), p);
  return replaceHyperSpecial(powdenestPolar(r));
}

function reduceOrderHyper(func: HyperFunc): [HyperFunc, OpPoly[]] {
  const [nap, nbq, ops] = reduceOrderLists(func.ap, func.bq, reduceOrderOp, false);
  return [hyperFunc(nap, nbq), ops];
}
function reduceOrderG(func: GFunc): [GFunc, OpPoly[]] {
  const [nan, nbq, ops1] = reduceOrderLists(func.an, func.bq, (a, b) => reduceOrderMeijer(sub(1, a), sub(1, b), 1), true);
  const [nbm, nap, ops2] = reduceOrderLists(func.bm, func.ap, (b, a) => reduceOrderMeijer(b, a, -1), false);
  return [gFunc(nan, nap, nbm, nbq), [...ops1, ...ops2]];
}

/** The residue of f at s0 (SymPy residue), from the Laurent series. */
function residue(f: Expr, s: Dummy, s0: Expr): Expr {
  const t = new Dummy('t');
  const ser = series(xreplace(f, [[s, add(t, s0)]]), t, 0, 1);
  return coeff(expand(mapBottomUp(ser, (u) => (u instanceof Order ? S.Zero : u))), t, -1);
}

type Cond = Expr | boolean;
/**
 * The expansion of a G-function by Slater's theorem: a sum of
 * hypergeometric functions at zero, and the condition under which it holds.
 */
function doSlater(an: readonly Expr[], bm: readonly Expr[], ap: readonly Expr[], bq: readonly Expr[], z: Expr, zfinal: Expr, ops: readonly OpPoly[], t: Dummy): [Expr, Cond] {
  const [, pbm, pap] = computeBuckets(gFunc(an, bm, ap, bq));
  for (const v of pbm.values()) {
    if (v.items.length > 1 && (pap.get(v.mod.key)?.items.length ?? 0) + 1 < v.items.length) return [S.Zero, false];
  }
  let cond: Cond = an.length + ap.length < bm.length + bq.length;
  if (an.length + ap.length === bm.length + bq.length) cond = Lt(abs(z), 1);
  if (cond === false) return [S.Zero, false];
  let res: Expr = S.Zero;
  for (const { mod, items } of pbm.values()) {
    if (items.length === 1) {
      const bh = first(items);
      const bo = [...bm];
      removeOne(bo, bh);
      const fac = div(mul(...bo.map((bj) => gamma(sub(bj, bh))), ...an.map((aj) => gamma(sub(add(1, bh), aj)))), mul(...bq.map((bj) => gamma(sub(add(1, bh), bj))), ...ap.map((aj) => gamma(sub(aj, bh)))));
      const nap = [...an, ...ap].map((a) => sub(add(1, bh), a));
      const nbq = [...bo, ...bq].map((b) => sub(add(1, bh), b));
      const k = polarLift(pow(-1, ap.length - bm.length));
      const hyp = hyperexpandFunc(hyperFunc(nap, nbq), mul(k, zfinal), ops, t, pow(div(t, k), bh), bh, 'none');
      res = add(res, mul(fac, hyp));
    } else {
      const b0 = first(items);
      const ki = items.slice(1).map((bi) => sub(bi, b0));
      const u = ki.length;
      const li = bucket(pap, mod)
        .slice(0, u + 1)
        .map((ai) => sub(ai, b0));
      const bo = [...bm];
      for (const b of items) removeOne(bo, b);
      const ao = [...ap];
      for (const a of bucket(pap, mod).slice(0, u)) removeOne(ao, a);
      const lu = asRational(at(li, -1));
      const di = li.map((l, i) => sub(l, ki[i] ?? 0));
      const s = new Dummy('s');
      const integrand = expand(mul(pow(z, s), ...bm.map((b) => gamma(sub(b, s))), ...an.map((a) => gamma(add(sub(1, a), s))), ...bq.map((b) => pow(gamma(add(sub(1, b), s)), -1)), ...ap.map((a) => pow(gamma(sub(a, s)), -1))));
      for (let r = 0; r < Number(lu.p); r++) {
        const resid = first(applyOperators([residue(integrand, s, add(b0, r))], ops, zDeriv(z)));
        res = sub(res, resid);
      }
      const au = add(b0, lu);
      const k = polarLift(pow(-1, ao.length + bo.length + 1));
      const nap = [...[...an, ...ap].map((a) => sub(add(1, au), a)), S.One];
      const nbq = [...bm, ...bq].map((b) => sub(add(1, au), b));
      const hyp = hyperexpandFunc(hyperFunc(nap, nbq), mul(k, zfinal), ops, t, pow(div(t, k), au), au, 'none');
      let C: Expr = div(pow(-1, lu), factorial(lu));
      for (let i = 0; i < u; i++) C = mul(C, div(pow(-1, at(di, i)), rf(add(sub(lu, at(li, i)), 1), at(di, i))));
      C = div(mul(C, ...an.map((a) => gamma(add(sub(1, a), au))), ...bo.map((b) => gamma(sub(b, au)))), mul(...ao.map((a) => gamma(sub(a, au))), ...bq.map((b) => gamma(add(sub(1, b), au)))));
      res = add(res, mul(C, hyp));
    }
  }
  return [res, cond];
}

const condKey = (c: Cond): number => (c === true ? 0 : c === false ? 1 : 2);

/** The closed form of a G-function (SymPy _meijergexpand), or the G-function itself. */
function meijergExpand(func0: GFunc, z0: Expr, allowHyper: boolean, place: 'zero' | 'infinity' | undefined): Expr {
  const z = new Dummy('z');
  const [func, ops] = reduceOrderG(func0);
  const f = lookupMeijer(func);
  if (f) {
    const allOps = [...ops, ...devisePlanMeijer(f.func, func, z)];
    const s = (e: Expr) => xreplace(e, [[f.z, z]]);
    const C = applyOperators(f.C.map(s), allOps, derivativeOperator(mapMat(f.M, s), z)).map(simp);
    const r = sum(C.map((c, i) => mul(c, s(at(f.B, i)))));
    return powdenestPolar(xreplace(r, [[z, z0]]));
  }
  const t = new Dummy('t');
  const [s1, c1] = doSlater(func.an, func.bm, func.ap, func.bq, z, z0, ops, t);
  const tr = (l: readonly Expr[]) => l.map((x) => sub(1, x));
  const ops2 = ops.map((o) => ({ poly: o.poly.map((c, k) => mul(xreplace(c, [[z, pow(t, -1)]]), k % 2 ? -1 : 1)) }));
  const [s2, c2a] = doSlater(tr(func.bm), tr(func.an), tr(func.bq), tr(func.ap), t, pow(z0, -1), ops2, t);
  let slater1 = powdenestPolar(xreplace(s1, [[z, z0]]));
  let slater2 = powdenestPolar(xreplace(s2, [[t, pow(z0, -1)]]));
  let cond1: Cond = c1;
  let cond2: Cond = typeof c2a === 'boolean' ? c2a : xreplace(c2a, [[t, pow(z, -1)]]);
  const g = cast(meijerg(func.an, func.ap, func.bm, func.bq, z), MeijerG);
  const d = g.delta;
  if (
    isPositive(d) === true ||
    (isRat(d) && d.isZero && g.ap.length === g.bq.length && decideFalse(Lt(re(g.nu), -1)) !== true && polarLift(z0).key === polarLift(1).key)
  ) {
    if (cond1 !== false) cond1 = true;
    if (cond2 !== false) cond2 = true;
  }
  slater1 = rewriteReps(slater1, cond1 === true ? 'nonrep' : 'nonrepsmall');
  slater2 = rewriteReps(slater2, cond2 === true ? 'nonrep' : 'nonrepsmall');
  if (cond1 !== false && cond2 !== false) {
    if (place === 'zero') cond2 = false;
    if (place === 'infinity') cond1 = false;
  }
  if (typeof cond1 !== 'boolean') cond1 = xreplace(cond1, [[z, z0]]);
  if (typeof cond2 !== 'boolean') cond2 = xreplace(cond2, [[z, z0]]);
  const weight = (e: Expr, c: Cond): [number, number, number] => [isBad(e) ? 3 : condKey(c), countHyper(e), countOps(e)];
  const w1 = weight(slater1, cond1);
  const w2 = weight(slater2, cond2);
  const lt = (u: readonly number[], v: readonly number[]): boolean => {
    for (const [i, x] of u.entries()) if (x !== at(v, i)) return x < at(v, i);
    return false;
  };
  const wmin = lt(w2, w1) ? w2 : w1;
  if (wmin[0] === 0 && wmin[1] <= 1) return lt(w1, w2) ? slater1 : slater2;
  const orig = meijerg(func0.an, func0.ap, func0.bm, func0.bq, z0);
  const r = piecewise([slater1, cond1], [slater2, cond2], [orig, true]);
  if (Math.max(w1[0], w2[0]) <= 1 && Math.max(w1[1], w2[1]) <= 1) return r;
  return allowHyper || !some(r, (n) => n instanceof Hyper) ? r : orig;
}
/** True when the relation is decided false, false when decided true, undefined otherwise. */
const decideFalse = (c: Expr): boolean | undefined => (c.key === S.false.key ? true : c.key === S.true.key ? false : undefined);

/** Options of hyperexpand. */
export interface HyperexpandOptions {
  /** Allow a partial expansion, a result that still contains hypergeometric functions. */
  allowHyper?: boolean;
  /** For a G-function with expansions at zero and at infinity, the one to prefer. */
  place?: 'zero' | 'infinity';
}

/**
 * Expand the hypergeometric functions and Meijer G-functions of f in closed
 * form where possible (SymPy hyperexpand); the others are left unchanged.
 */
export function hyperexpand(fIn: ExprLike, opts: HyperexpandOptions = {}): Expr {
  const f = sympify(fIn);
  const r1 = mapBottomUp(f, (t) => (t instanceof Hyper ? hyperexpandFunc(hyperFunc(t.ap, t.bq), t.argument) : t));
  // Deliberate difference: Ei on another sheet is written with Ei on the principal one
  // (liftBranches), because the numeric evaluation of Ei(z*exp_polar(I*pi)) does not add the
  // I*pi of SymPy's Ei._eval_evalf yet
  return liftBranches(
    mapBottomUp(r1, (t) => {
      if (!(t instanceof MeijerG)) return t;
      const r = meijergExpand(gFunc(t.an, t.aother, t.bm, t.bother), t.argument, opts.allowHyper ?? false, opts.place);
      return isBad(r) ? t : r;
    }),
  );
}


// SymPy hyper._eval_expand_func and meijerg._eval_expand_func: Gauss's theorem at 1, else hyperexpand
expandFuncRules.hyper = (e) => {
  const h = cast(e, Hyper);
  return gaussAtOne(h) ?? hyperexpand(h);
};
expandFuncRules.meijerg = (e) => hyperexpand(e);

// ---- the parameter objects of SymPy's hyperexpand --------------------------------------

/**
 * SymPy Operator: a differential operator, a polynomial whose generator (by convention
 * D = z*d/dz) acts to the right of all coefficients. `new Operator(x**2 + z*x + y, x)` is SymPy's
 * `op._poly = Poly(x**2 + z*x + y, x)`; without a generator the polynomial is constant.
 * @experimental May change in a minor release.
 */
export class Operator {
  /** The coefficients of the polynomial, the constant one first. */
  readonly poly: readonly Expr[];
  constructor(poly: ExprLike = 0, gen?: Expr) {
    const p = sympify(poly);
    if (gen === undefined) this.poly = [p];
    else {
      const cs = polyCoefficients(p, gen);
      if (!cs) throw new PolynomialError(`${String(p)} is not a polynomial in ${String(gen)}`);
      this.poly = Array.from({ length: Math.max(0, ...cs.keys()) + 1 }, (_, k) => cs.get(k) ?? S.Zero);
    }
  }
  /** SymPy apply: the operator applied to obj, where op applies the generator. */
  apply(obj: ExprLike, op: (e: Expr) => Expr): Expr {
    let d = sympify(obj);
    let r = mul(first(this.poly), d);
    for (const c of this.poly.slice(1)) {
      d = op(d);
      r = add(r, mul(c, d));
    }
    return r;
  }
}

/**
 * SymPy Hyper_Function(ap, bq): the parameters of a generalized hypergeometric
 * function, as hyperexpand classifies them.
 * @experimental May change in a minor release.
 */
export class Hyper_Function {
  /** The numerator parameters. */
  readonly ap: readonly Expr[];
  /** The denominator parameters. */
  readonly bq: readonly Expr[];
  constructor(ap: readonly ExprLike[], bq: readonly ExprLike[]) {
    const f = hyperFunc(ap, bq);
    this.ap = f.ap;
    this.bq = f.bq;
  }
  /** The number of negative integer numerator parameters. */
  get gamma(): number {
    return hfGamma({ ap: [...this.ap], bq: [...this.bq] });
  }
  /**
   * SymPy build_invariants: [gamma, ((mod, count), ...) of ap, ((mod, count), ...) of bq], the
   * parameters grouped by their residue mod 1 (sorted), which shift operators leave unchanged.
   */
  buildInvariants(): [number, [Expr, number][], [Expr, number][]] {
    const tr = (xs: readonly Expr[]): [Expr, number][] =>
      [...buckets(xs).values()].sort((u, v) => compareKeys(sortKey(u.mod), sortKey(v.mod))).map((v): [Expr, number] => [v.mod, v.items.length]);
    return [this.gamma, tr(this.ap), tr(this.bq)];
  }
}

/**
 * SymPy G_Function(an, ap, bm, bq): the parameters of a Meijer G-function, as
 * hyperexpand classifies them.
 * @experimental May change in a minor release.
 */
export class G_Function {
  readonly an: readonly Expr[];
  readonly ap: readonly Expr[];
  readonly bm: readonly Expr[];
  readonly bq: readonly Expr[];
  constructor(an: readonly ExprLike[], ap: readonly ExprLike[], bm: readonly ExprLike[], bq: readonly ExprLike[]) {
    const g = gFunc(an.map(sympify), ap.map(sympify), bm.map(sympify), bq.map(sympify));
    this.an = g.an;
    this.ap = g.ap;
    this.bm = g.bm;
    this.bq = g.bq;
  }
  /**
   * SymPy compute_buckets: the parameters of an, ap, bm and bq grouped by their
   * residue mod 1, each group sorted by real part (an and bq descending, ap and bm ascending).
   */
  computeBuckets(): [ExprMap<Expr[]>, ExprMap<Expr[]>, ExprMap<Expr[]>, ExprMap<Expr[]>] {
    const toMap = (b: Buckets): ExprMap<Expr[]> => new ExprMap([...b.values()].map((v) => [v.mod, v.items] as const));
    const [an, ap, bm, bq] = computeBuckets({ an: [...this.an], ap: [...this.ap], bm: [...this.bm], bq: [...this.bq] });
    return [toMap(an), toMap(ap), toMap(bm), toMap(bq)];
  }
}
