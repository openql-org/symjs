// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/meijerint.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Integration by rewriting integrands as Meijer G-functions (SymPy
 * meijerint_definite and meijerint_inversion).
 *
 * The integrand is written as x**s times one or two G-functions of
 * arguments a*x**b, using a table of the G-function representations of the
 * elementary and special functions. The integral over (0, oo) of one
 * G-function is a quotient of gamma functions, that of two G-functions is a
 * G-function (the theorems of Luke and of Saxena), each under convergence
 * conditions that are returned with the result. The resulting G-functions
 * are expanded in closed form with hyperexpand.
 *
 * References: [L] Y. L. Luke, The Special Functions and Their
 * Approximations, Volume 1 (1969); [P] A. P. Prudnikov, Yu. A. Brychkov and
 * O. I. Marichev, Integrals and Series: More Special Functions, Vol. 3 (1990).
 *
 * Not ported: the recursive rewriting of factors through Mellin transforms,
 * the lookup entries of Prudnikov 8.4.2 (12, 13), log(Abs(t - a)), the
 * elliptic integrals and the rewriting of hyperbolic functions as
 * exponentials.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Fn, Mul, Pow, Rational, Rel, S, Special, asRational } from '../core/nodes';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { BoolOp, and, or } from '../core/boolalg';
import { Eq, Ge, Gt, Le, Lt, Ne, piecewise } from '../core/logic';
import { at, cast, expectType, first, pair } from '../core/guard';
import { lcm } from '../core/numbers';
import { mapBottomUp, some, xreplace } from '../core/traverse';
import { asCoeffMul } from '../core/methods';
import { isPositive, isNegative, isReal } from '../core/assumptions';
import { compareKeys, sortKey } from '../printing/sortkey';
import { abs, arg, cos, im, log, re, sin } from '../functions/elementary/elementary';
import { factorial, gamma, sign } from '../functions/special/special';
import { MeijerG, meijerg } from '../functions/special/hyper';
import { expPolar, polarify, polarLift, principalBranch, unbranchedArgument, unpolarify } from '../functions/elementary/complexes';
import { expand, expandMul } from '../simplify/expand';
import { gammasimp } from '../simplify/gammasimp';
import { rewrite } from '../simplify/rewrite';
import { powsimp } from '../simplify/powsimp';
import { factor } from '../polys/sympoly';
import { multisetPartitions } from '../utilities/iterables';
import { relCanonical } from '../logic/boolalg';
import { hyperexpand, liftBranches, powdenestPolar, unpolarifyEval } from '../simplify/hyperexpand';
import { Heaviside, isDiracDelta, isHeaviside } from './transforms/delta';

const pi = S.Pi;
const I = S.I;
const half = S.Half;
const neg = (e: ExprLike): Expr => mul(-1, e);
const sub = (a: ExprLike, b: ExprLike): Expr => add(a, neg(b));
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));
const isRat = (e: unknown): e is Rational => e instanceof Rational;
const isFalse = (c: Expr): boolean => c.key === S.false.key;
const isFnN = (e: Expr, name: string): e is Fn => e instanceof Fn && e.name === name;
const isOo = (e: Expr, name: 'oo' | '-oo'): boolean => e instanceof Special && e.name === name;
const hasInf = (e: Expr): boolean => some(e, (n) => n instanceof Special && ['oo', '-oo', 'zoo', 'nan'].includes(n.name));
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
const addArgs = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);

/** A G-function term C*x**s*G of a rewritten integrand. */
export type GTerm = [Expr, Expr, MeijerG];
const G = (an: readonly ExprLike[], ap: readonly ExprLike[], bm: readonly ExprLike[], bq: readonly ExprLike[], z: ExprLike): MeijerG => cast(meijerg(an, ap, bm, bq, z), MeijerG);
/** The G-function with its parameters unpolarified (the parameters of SymPy's meijerg are not polar). */
const Gu = (an: readonly ExprLike[], ap: readonly ExprLike[], bm: readonly ExprLike[], bq: readonly ExprLike[], z: Expr): MeijerG => {
  const u = (l: readonly ExprLike[]) => l.map((e) => unpolarify(sympify(e)));
  return G(u(an), u(ap), u(bm), u(bq), z);
};

// ---- polar helpers ----------------------------------------------------------------------

/** SymPy unpolarify(e, exponents_only=True). */
export const unpolarifyExponents = (e: Expr): Expr => unpolarify(e, { exponentsOnly: true });
/** The expression of a polarify result (without substitutions, it is an expression). */
const polarExpr = (r: Expr | [Expr, [Expr, Expr][]]): Expr => expectType(r, (v): v is Expr => !Array.isArray(v), 'polarify');
/** unpolarify(polarify(e, lift=True), exponents_only=True): the polar number lying over e. */
export function liftPolar(e: Expr): Expr {
  return unpolarifyExponents(polarExpr(polarify(e, { lift: true })));
}

// ---- coefficients and exponents ---------------------------------------------------------

/** The internal error of _get_coeff_exp: expr is not of the form c*x**b. */
export class CoeffExpError extends RangeError {}

const expandPowerBase = (e: Expr): Expr => expand(e, { power_base: true, mul: false, multinomial: false, power_exp: false, log: false });

/** [c, b] with expr = c*x**b, or undefined (SymPy _get_coeff_exp). */
function coeffExp(expr: Expr, x: Sym): [Expr, Expr] | undefined {
  const [c, m] = asCoeffMul(expandPowerBase(powsimp(expr)), [x]);
  if (m.length === 0) return [c, S.Zero];
  const t = first(m);
  if (m.length === 1 && t instanceof Pow && t.base.key === x.key) return [c, t.exp];
  if (m.length === 1 && t.key === x.key) return [c, S.One];
  return undefined;
}
/** [c, b] with expr = c*x**b (SymPy _get_coeff_exp); throws CoeffExpError otherwise. */
export function getCoeffExp(expr: Expr, x: Sym): [Expr, Expr] {
  const r = coeffExp(expr, x);
  if (!r) throw new CoeffExpError(`expr not of form a*x**b: ${String(expr)}`);
  return r;
}

/** The exponents of x in expr (SymPy _exponents). */
function exponents(expr: Expr, x: Sym): Set<string> {
  const res = new Set<string>();
  const go = (e: Expr): void => {
    if (e.key === x.key) res.add(S.One.key);
    else if (e instanceof Pow && e.base.key === x.key) res.add(e.exp.key);
    else e.args.forEach(go);
  };
  go(expr);
  return res;
}
/** The functions in expr that contain x (SymPy _functions). */
function functions(expr: Expr, x: Sym): Set<string> {
  const res = new Set<string>();
  const go = (e: Expr): void => {
    if (e instanceof Fn && e.has(x)) res.add(e.name);
    else if (isHeaviside(e) && e.has(x)) res.add('Heaviside');
    e.args.forEach(go);
  };
  go(expr);
  return res;
}
/** Numbers c such that x -> x + c may simplify expr (SymPy _find_splitting_points). */
export function findSplittingPoints(expr: Expr, x: Sym): Expr[] {
  const res = new Map<string, Expr>();
  const go = (e: Expr): void => {
    const lin = linearIn(e, x);
    if (lin) {
      const c = div(neg(lin[1]), lin[0]);
      res.set(c.key, c);
      return;
    }
    e.args.forEach(go);
  };
  go(expr);
  return [...res.values()];
}
/** [p, q] with e = p*x + q, p nonzero, or undefined. */
function linearIn(e: Expr, x: Sym): [Expr, Expr] | undefined {
  if (!e.has(x)) return undefined;
  const ex = expandMul(e);
  let p: Expr = S.Zero;
  let q: Expr = S.Zero;
  for (const t of addArgs(ex)) {
    if (!t.has(x)) q = add(q, t);
    else {
      const c = div(t, x);
      if (c.has(x)) return undefined;
      p = add(p, c);
    }
  }
  return isRat(p) && p.isZero ? undefined : [p, q];
}

/** f = fac*po*g with fac free of x and po = x**s (SymPy _split_mul). */
export function splitMul(f: Expr, x: Sym): [Expr, Expr, Expr] {
  let fac: Expr = S.One;
  let po: Expr = S.One;
  let g: Expr = S.One;
  for (const a of mulArgs(expandPowerBase(f))) {
    if (a.key === x.key) po = mul(po, x);
    else if (!a.has(x)) fac = mul(fac, a);
    else {
      if (a instanceof Pow && !a.exp.has(x)) {
        let [c, t] = asCoeffMul(a.base, [x]);
        if (!(t.length === 1 && first(t).key === x.key)) [c, t] = asCoeffMul(expandMul(a.base), [x]);
        if (t.length === 1 && first(t).key === x.key) {
          po = mul(po, pow(x, a.exp));
          fac = mul(fac, unpolarify(polarExpr(polarify(pow(c, a.exp), { subs: false }))));
          continue;
        }
      }
      g = mul(g, a);
    }
  }
  return [fac, po, g];
}

/** The factors of f, with integer powers repeated (SymPy _mul_args). */
function mulArgsRepeated(f: Expr): Expr[] {
  const gs: Expr[] = [];
  for (const g of mulArgs(f)) {
    if (g instanceof Pow && g.exp instanceof Rational && g.exp.isInteger) {
      const n = Number(g.exp.p);
      const base = n < 0 ? pow(g.base, -1) : g.base;
      for (let i = 0; i < Math.abs(n); i++) gs.push(base);
    } else gs.push(g);
  }
  return gs;
}
/** The ways to write f as a product of two factors (SymPy _mul_as_two_parts). */
function mulAsTwoParts(f: Expr): [Expr, Expr][] | undefined {
  const gs = mulArgsRepeated(f);
  if (gs.length < 2) return undefined;
  if (gs.length === 2) return [[at(gs, 0), at(gs, 1)]];
  const out: [Expr, Expr][] = [];
  for (const parts of multisetPartitions(gs, 2)) {
    const [u, v] = pair(parts);
    out.push([mul(...u), mul(...v)]);
  }
  return out;
}

// ---- G-function manipulations ------------------------------------------------------------

/** [C, h] with h a G-function of argument z**n and g = C*h (SymPy _inflate_g). */
function inflateG(g: MeijerG, n: number): [Expr, MeijerG] {
  const inflate = (params: readonly Expr[]) => params.flatMap((a) => Array.from({ length: n }, (_, i) => div(add(a, i), n)));
  const v = R(g.ap.length - g.bq.length);
  const C = div(pow(n, add(1, g.nu, div(v, 2))), pow(mul(2, pi), mul(n - 1, g.delta)));
  return [C, G(inflate(g.an), inflate(g.aother), inflate(g.bm), inflate(g.bother), mul(pow(g.argument, n), pow(n, mul(n, v))))];
}
/** The G-function of inverse argument (SymPy _flip_g). */
function flipG(g: MeijerG): MeijerG {
  const tr = (l: readonly Expr[]) => l.map((a) => sub(1, a));
  return G(tr(g.bm), tr(g.bother), tr(g.an), tr(g.aother), pow(g.argument, -1));
}
/** C and the G-function equal to the Fox H-function with gamma(a*s) in the denominator (SymPy _inflate_fox_h). */
function inflateFoxH(g0: MeijerG, a0: Rational): [Expr, MeijerG] {
  const [g1, a] = a0.isNegative ? [flipG(g0), Rational.of(-a0.p, a0.q)] : [g0, a0];
  const p = Number(a.p);
  const [D0, g] = inflateG(g1, Number(a.q));
  const D = div(D0, mul(pow(mul(2, pi), div(sub(1, p), 2)), pow(p, R(-1, 2))));
  const z = div(g.argument, pow(p, p));
  const bs = Array.from({ length: p }, (_, n) => R(n + 1, p));
  return [D, G(g.an, g.aother, g.bm, [...g.bother, ...bs], z)];
}

/** principal_branch(expr, period) without unevaluated principal_branch() factors unless fullPb (SymPy _my_principal_branch). */
function myPrincipalBranch(expr: Expr, period: Expr, fullPb = false): Expr {
  // (exp_polar(0) is the polar number 1, which is positive)
  const res = xreplace(principalBranch(expr, period), [[expPolar(0), S.One]]);
  if (fullPb) return res;
  return mapBottomUp(res, (t) => (isFnN(t, 'principal_branch') ? first(t.args) : t));
}

// ---- conditions ------------------------------------------------------------------------

/** Re-evaluate a condition (SymPy _eval_cond with the canonical forms of _condsimp). */
export function condsimp(cond: Expr): Expr {
  return mapBottomUp(cond, (t) => {
    if (t instanceof Rel && t.freeSymbols().size === 0) {
      const d = sub(t.lhs, t.rhs);
      const v = numericValue(d);
      if (v !== undefined) return rel0(t.op, v);
    }
    if (t instanceof Rel) return condRel(relCanonical(t));
    // p > 0 and p < 0 together are False
    if (t instanceof BoolOp && t.op === 'And') {
      const rels = t.args.filter((r): r is Rel => r instanceof Rel && isRat(r.rhs) && r.rhs.isZero);
      if (rels.some((r) => r.op === 'Gt' && rels.some((q) => q.op === 'Lt' && q.lhs.key === r.lhs.key))) return S.false;
    }
    return t;
  });
}
/** Eq(unbranched_argument(p), 0) for a non-polar p is p > 0 (SymPy rel_touchup). */
function condRel(t0: Rel): Expr {
  // a constant term moves to the right (SymPy _canonical_coeff)
  const c = t0.lhs instanceof Add && isRat(t0.rhs) ? t0.lhs.args.find(isRat) : undefined;
  const t1 = c ? new Rel(t0.op, sub(t0.lhs, c), sub(t0.rhs, c)) : t0;
  // a positive numeric factor of the left side divides out
  const f = t1.lhs instanceof Mul && t1.rhs.freeSymbols().size === 0 ? t1.lhs.args.find(isRat) : undefined;
  const t = f?.isPositive === true ? new Rel(t1.op, div(t1.lhs, f), div(t1.rhs, f)) : t1;
  const [lhs, rhs] = [t.lhs, t.rhs];
  // an absolute value is not negative
  if (t.op === 'Lt' && isFnN(lhs, 'abs') && isRat(rhs) && rhs.isZero) return S.false;
  if (t.op === 'Eq' && isRat(rhs) && rhs.isZero && isFnN(lhs, 'arg') && !isPolarish(first(lhs.args))) return Gt(first(lhs.args), 0);
  return t;
}
/** The value of a real number without symbols, or undefined. */
function numericValue(d: Expr): number | undefined {
  try {
    const c = unpolarify(d).toComplex();
    return Math.abs(c.im) > 1e-12 * Math.max(1, Math.abs(c.re)) || !Number.isFinite(c.re) ? undefined : c.re;
  } catch {
    return undefined;
  }
}
const rel0 = (op: string, v: number): Expr => {
  const z = Math.abs(v) < 1e-14;
  const r = { Eq: z, Ne: !z, Lt: !z && v < 0, Le: z || v < 0, Gt: !z && v > 0, Ge: z || v > 0 }[op];
  return r === true ? S.true : S.false;
};
const isPolarish = (e: Expr): boolean => some(e, (n) => isFnN(n, 'exp_polar') || isFnN(n, 'polar_lift'));
/** SymPy _my_unpolarify: _eval_cond(unpolarify(f)), with Ei on other sheets lifted as in powdenestPolar. */
const myUnpolarify = (e: Expr): Expr => condsimp(unpolarifyEval(liftBranches(e)));
/** unbranched_argument(e), additively over the factors and powers of polar numbers. */
function uarg(e: Expr): Expr {
  if (e instanceof Mul) return add(...e.args.map(uarg));
  if (e instanceof Pow && isRat(e.exp) && isPolarish(e.base)) return mul(e.exp, uarg(e.base));
  if (isFnN(e, 'polar_lift')) return arg(first(e.args));
  return unbranchedArgument(e);
}
const absArg = (e: Expr): Expr => abs(uarg(e));

/** The condition under which the Mellin transform of g at s = 1 exists (SymPy _check_antecedents_1). */
function checkAntecedents1(g: MeijerG, x: Sym, helper = false): Expr {
  const delta = g.delta;
  const [eta] = getCoeffExp(g.argument, x);
  const [m, n, p, q] = [g.bm.length, g.an.length, g.ap.length, g.bq.length];
  if (p > q) {
    const tr = (l: readonly Expr[]) => l.map((a) => sub(1, a));
    return checkAntecedents1(G(tr(g.bm), tr(g.bother), tr(g.an), tr(g.aother), div(x, eta)), x, helper);
  }
  const tmp: Expr[] = [...g.bm.map((b) => Lt(neg(re(b)), 1)), ...g.an.map((a) => Lt(1, sub(1, re(a))))];
  const cond3 = and(...tmp);
  const cond4 = Gt(add(neg(re(g.nu)), R(q + 1 - p, 2)), q - p);
  const delta2 = asRat(delta);
  const conds: Expr[] = [];
  const tmp1 = [1 <= n, p < q, 1 <= m];
  const tmp2 = [1 <= p, 1 <= m, q === p + 1, !(n === 0 && m === p + 1)];
  const tmp3: (Expr | boolean)[] = [1 <= p, q === p];
  for (let k = 0; k <= Math.ceil(delta2.value / 2); k++) tmp3.push(Ne(absArg(eta), mul(sub(delta, 2 * k), pi)));
  const tmpd = [Gt(delta, 0), Lt(absArg(eta), mul(delta, pi))];
  const extra = helper ? [] : [Ne(eta, 0), cond3];
  for (const t of [tmp1, tmp2, tmp3]) conds.push(and(...t, ...tmpd, ...extra));
  conds.push(and(n === 0, p + 1 <= m, m <= q, Lt(absArg(eta), mul(delta, pi)), ...(helper ? [] : [cond3])));
  const extra3 = helper ? [] : [cond3, cond4];
  conds.push(and(p < q, 1 <= m, Gt(delta, 0), Eq(absArg(eta), mul(delta, pi)), ...extra3));
  conds.push(and(p <= q - 2, Eq(delta, 0), Eq(absArg(eta), 0), ...extra3));
  const ss = g.ap.map((a, i) => sub(at(g.bq, i), a));
  conds.push(and(p === q, Eq(delta, 0), Eq(uarg(eta), 0), Ne(eta, 0), ...(helper ? [] : [cond3]), Lt(re(add(...ss)), 0)));
  conds.push(and(Gt(delta, 0), Lt(absArg(eta), mul(delta, pi)), ...(helper ? [] : [cond3])));
  return or(...conds);
}
const asRat = (e: Expr): Rational => asRational(e);

/** The integral of g over (0, oo), assuming the conditions hold (SymPy _int0oo_1). */
function int0oo1(g: MeijerG, x: Sym): Expr {
  const [eta] = getCoeffExp(g.argument, x);
  let res = pow(eta, -1);
  for (const b of g.bm) res = mul(res, gamma(add(b, 1)));
  for (const a of g.an) res = mul(res, gamma(sub(sub(1, a), 1)));
  for (const b of g.bother) res = div(res, gamma(sub(sub(1, b), 1)));
  for (const a of g.aother) res = div(res, gamma(add(a, 1)));
  return gammasimp(unpolarify(res));
}

/** fac*po*g with po = x**s as C*G(a*x) for the integral over (0, oo) (SymPy _rewrite_saxena_1). */
function rewriteSaxena1(fac: Expr, po: Expr, g: MeijerG, x: Sym): [Expr, MeijerG] {
  const [, s] = getCoeffExp(po, x);
  const [a0, b] = getCoeffExp(g.argument, x);
  const a = myPrincipalBranch(a0, g.getPeriod());
  const e = sub(div(add(s, 1), b), 1);
  const C = div(fac, mul(abs(b), pow(a, e)));
  const tr = (l: readonly Expr[]) => l.map((p) => add(p, e));
  return [C, G(tr(g.an), tr(g.aother), tr(g.bm), tr(g.bother), mul(a, x))];
}

/** fac*po*g1*g2 as C*f1*f2 with f1, f2 of arguments c*x (SymPy _rewrite_saxena). */
function rewriteSaxena(fac0: Expr, po: Expr, g10: MeijerG, g20: MeijerG, x: Sym, fullPb: boolean): [Expr, MeijerG, MeijerG] | undefined {
  const pb = (g: MeijerG): MeijerG => {
    const [a, b] = getCoeffExp(g.argument, x);
    return G(g.an, g.aother, g.bm, g.bother, mul(myPrincipalBranch(a, g.getPeriod(), fullPb), pow(x, b)));
  };
  const [, s] = getCoeffExp(po, x);
  let [, b1] = getCoeffExp(g10.argument, x);
  let [, b2] = getCoeffExp(g20.argument, x);
  let g1 = g10;
  let g2 = g20;
  if (isNegative(b1) === true) {
    b1 = neg(b1);
    g1 = flipG(g1);
  }
  if (isNegative(b2) === true) {
    b2 = neg(b2);
    g2 = flipG(g2);
  }
  if (!isRat(b1) || !isRat(b2)) return undefined;
  const [m1, n1, m2, n2] = [b1.p, b1.q, b2.p, b2.q];
  const tau = lcm(m1 * n2, m2 * n1);
  const [C1, h1] = inflateG(g1, Number(tau / (m1 * n2)));
  const [C2, h2] = inflateG(g2, Number(tau / (m2 * n1)));
  const p1 = pb(h1);
  const p2 = pb(h2);
  const [a1, b] = getCoeffExp(p1.argument, x);
  const [a2] = getCoeffExp(p2.argument, x);
  const e = sub(div(add(s, 1), b), 1);
  const fac = div(mul(fac0, C1, C2), mul(abs(b), pow(a1, e)));
  const tr = (l: readonly Expr[]) => l.map((a) => add(a, e));
  return [powdenestPolar(fac), G(tr(p1.an), tr(p1.aother), tr(p1.bm), tr(p1.bother), mul(a1, x)), G(p2.an, p2.aother, p2.bm, p2.bother, mul(a2, x))];
}

/** The condition under which the integral theorem for a product of two G-functions applies (SymPy _check_antecedents). */
function checkAntecedents(g1: MeijerG, g2: MeijerG, x: Sym): Expr {
  const [sigma] = getCoeffExp(g1.argument, x);
  const [omega] = getCoeffExp(g2.argument, x);
  const [s, t, u, v] = [g1.bm.length, g1.an.length, g1.ap.length, g1.bq.length];
  const [m, n, p, q] = [g2.bm.length, g2.an.length, g2.ap.length, g2.bq.length];
  const bstar = R(2 * (s + t) - (u + v), 2);
  const cstar = R(2 * (m + n) - (p + q), 2);
  const rho = add(g1.nu, R(u - v, 2), 1);
  const mu = add(g2.nu, R(p - q, 2), 1);
  const phi = q - p - (v - u);
  const eta = sub(sub(sub(1, v - u), mu), rho);
  const psi = div(add(mul(pi, q - m - n), absArg(omega)), q - p);
  const theta = div(add(mul(pi, v - s - t), absArg(sigma)), v - u);
  const c1 = ![g1, g2].some((g) => g.an.some((i) => g.bm.some((j) => {
    const d = sub(i, j);
    return isRat(d) && d.isInteger && d.isPositive;
  })));
  const c2 = and(...g1.bm.flatMap((i) => g2.bm.map((j) => Gt(re(add(1, i, j)), 0))));
  const c3 = and(...g1.an.flatMap((i) => g2.an.map((j) => Lt(re(add(1, i, j)), 2))));
  const c4 = and(...g1.an.map((i) => Gt(sub(mul(p - q, re(i)), re(mu)), R(-3, 2))));
  const c5 = and(...g1.bm.map((i) => Gt(sub(mul(p - q, re(add(1, i))), re(mu)), R(-3, 2))));
  const c6 = and(...g2.an.map((i) => Gt(sub(mul(u - v, re(i)), re(rho)), R(-3, 2))));
  const c7 = and(...g2.bm.map((i) => Gt(sub(mul(u - v, re(add(1, i))), re(rho)), R(-3, 2))));
  const inner = re(add(mul(sub(rho, 1), q - p), (v - u) * (q - p), mul(sub(mu, 1), v - u)));
  const c8 = Gt(add(Math.abs(phi), mul(2, inner)), 0);
  const c9 = Gt(sub(Math.abs(phi), mul(2, inner)), 0);
  const c10 = Lt(absArg(sigma), mul(bstar, pi));
  const c11 = Eq(absArg(sigma), mul(bstar, pi));
  const c12 = Lt(absArg(omega), mul(cstar, pi));
  const c13 = Eq(absArg(omega), mul(cstar, pi));
  const z0 = exp(mul(neg(add(bstar, cstar)), pi, I));
  const zos = unpolarify(div(mul(z0, omega), sigma));
  const zso = unpolarify(div(mul(z0, sigma), omega));
  let c14: Expr;
  if (zos.key === pow(zso, -1).key) {
    c14 = and(phi === 0, Le(add(bstar, cstar), 1), or(Ne(zos, 1), Lt(re(add(mu, rho, v - u)), 1), Lt(re(add(mu, rho, q - p)), 1)));
  } else {
    const cnd = (zz: Expr): Expr | boolean => zz.key !== S.One.key && Lt(abs(arg(sub(1, zz))), pi);
    c14 = or(
      and(phi === 0, Le(sub(add(bstar, cstar), 1), 0), or(and(Ne(zos, 1), cnd(zos)), and(Lt(re(add(mu, rho, v - u)), 1), Eq(zos, 1)))),
      and(phi === 0, Le(sub(add(cstar, bstar), 1), 0), or(and(Ne(zso, 1), cnd(zso)), and(Lt(re(add(mu, rho, q - p)), 1), Eq(zso, 1)))),
    );
  }
  let c15: Expr;
  try {
    const lambdaC = add(mul(q - p, pow(abs(omega), pow(R(q - p), -1)), cos(psi)), mul(v - u, pow(abs(sigma), pow(R(v - u), -1)), cos(theta)));
    if (!isFalse(condsimp(Gt(lambdaC, 0)))) c15 = Gt(lambdaC, 0);
    else {
      const ls0 = (a: ExprLike, b: ExprLike) => add(mul(a, q - p, pow(abs(omega), pow(R(q - p), -1)), sin(psi)), mul(b, v - u, pow(abs(sigma), pow(R(v - u), -1)), sin(theta)));
      const ao = uarg(omega);
      const as = uarg(sigma);
      const lambdaS = piecewise(
        [mul(ls0(1, 1), ls0(-1, -1)), and(Eq(as, 0), Eq(ao, 0))],
        [mul(ls0(sign(ao), 1), ls0(sign(ao), -1)), and(Eq(as, 0), Ne(ao, 0))],
        [mul(ls0(1, sign(as)), ls0(-1, sign(as))), and(Ne(as, 0), Eq(ao, 0))],
        [ls0(sign(ao), sign(as)), true],
      );
      c15 = or(Gt(lambdaC, 0), and(Eq(lambdaC, 0), Ne(lambdaS, 0), Gt(re(eta), -1)), and(Eq(lambdaC, 0), Eq(lambdaS, 0), Gt(re(eta), 0)));
    }
  } catch {
    // (a NaN comparison: the condition is False, as in SymPy)
    c15 = S.false;
  }
  const pos = (e: Expr) => isPositive(e) === true;
  const negq = (e: Expr) => isNegative(e) === true;
  const bs = pos(bstar);
  const cs = pos(cstar);
  const conds: Expr[] = [
    and(m * n * s * t !== 0, bs, cs, c1, c2, c3, c10, c12),
    and(u === v, bstar.isZero, cs, pos(sigma), Lt(re(rho), 1), c1, c2, c3, c12),
    and(p === q, cstar.isZero, bs, pos(omega), Lt(re(mu), 1), c1, c2, c3, c10),
    and(p === q, u === v, bstar.isZero, cstar.isZero, pos(sigma), pos(omega), Lt(re(mu), 1), Lt(re(rho), 1), Ne(sigma, omega), c1, c2, c3),
    and(p === q, u === v, bstar.isZero, cstar.isZero, pos(sigma), pos(omega), Lt(re(add(mu, rho)), 1), Ne(omega, sigma), c1, c2, c3),
    and(p > q, s > 0, bs, !cstar.isNegative, c1, c2, c3, c5, c10, c13),
    and(p < q, t > 0, bs, !cstar.isNegative, c1, c2, c3, c4, c10, c13),
    and(u > v, m > 0, cs, !bstar.isNegative, c1, c2, c3, c7, c11, c12),
    and(u < v, n > 0, cs, !bstar.isNegative, c1, c2, c3, c6, c11, c12),
    and(p > q, u === v, bstar.isZero, !cstar.isNegative, pos(sigma), Lt(re(rho), 1), c1, c2, c3, c5, c13),
    and(p < q, u === v, bstar.isZero, !cstar.isNegative, pos(sigma), Lt(re(rho), 1), c1, c2, c3, c4, c13),
    and(p === q, u > v, !bstar.isNegative, cstar.isZero, pos(omega), Lt(re(mu), 1), c1, c2, c3, c7, c11),
    and(p === q, u < v, !bstar.isNegative, cstar.isZero, pos(omega), Lt(re(mu), 1), c1, c2, c3, c6, c11),
    and(p < q, u > v, !bstar.isNegative, !cstar.isNegative, c1, c2, c3, c4, c7, c11, c13),
    and(p > q, u < v, !bstar.isNegative, !cstar.isNegative, c1, c2, c3, c5, c6, c11, c13),
    and(p > q, u > v, !bstar.isNegative, !cstar.isNegative, c1, c2, c3, c5, c7, c8, c11, c13, c14),
    and(p < q, u < v, !bstar.isNegative, !cstar.isNegative, c1, c2, c3, c4, c6, c9, c11, c13, c14),
    and(t === 0, s > 0, bs, phi > 0, c1, c2, c10),
    and(s === 0, t > 0, bs, phi < 0, c1, c3, c10),
    and(n === 0, m > 0, cs, phi < 0, c1, c2, c12),
    and(m === 0, n > 0, cs, phi > 0, c1, c3, c12),
    and(s * t === 0, bs, cs, c1, c2, c3, c10, c12),
    and(m * n === 0, bs, cs, c1, c2, c3, c10, c12),
  ];
  const mt1 = checkAntecedents1(g1, x, true);
  const mt2 = checkAntecedents1(g2, x, true);
  conds.push(and(mt2, t === 0, u < s, bs, c10, c1, c2, c3));
  conds.push(and(mt2, s === 0, v < t, bs, c10, c1, c2, c3));
  conds.push(and(mt1, n === 0, p < m, cs, c12, c1, c2, c3));
  conds.push(and(mt1, m === 0, q < n, cs, c12, c1, c2, c3));
  const r = or(...conds);
  if (!isFalse(condsimp(r))) return r;
  const ao = absArg(omega);
  const asg = absArg(sigma);
  conds.push(
    and(m + n > p, t === 0, phi === 0, s > 0, bs, negq(cstar), Lt(ao, mul(m + n - p + 1, pi)), c1, c2, c10, c14, c15),
    and(m + n > q, s === 0, phi === 0, t > 0, bs, negq(cstar), Lt(ao, mul(m + n - q + 1, pi)), c1, c3, c10, c14, c15),
    and(p === q - 1, t === 0, phi === 0, s > 0, bs, !cstar.isNegative, Lt(mul(cstar, pi), ao), c1, c2, c10, c14, c15),
    and(p === q + 1, s === 0, phi === 0, t > 0, bs, !cstar.isNegative, Lt(mul(cstar, pi), ao), c1, c3, c10, c14, c15),
    and(p < q - 1, t === 0, phi === 0, s > 0, bs, !cstar.isNegative, Lt(mul(cstar, pi), ao), Lt(ao, mul(m + n - p + 1, pi)), c1, c2, c10, c14, c15),
    and(p > q + 1, s === 0, phi === 0, t > 0, bs, !cstar.isNegative, Lt(mul(cstar, pi), ao), Lt(ao, mul(m + n - q + 1, pi)), c1, c3, c10, c14, c15),
    and(n === 0, phi === 0, s + t > 0, m > 0, cs, negq(bstar), Lt(asg, mul(s + t - u + 1, pi)), c1, c2, c12, c14, c15),
    and(m === 0, phi === 0, s + t > v, n > 0, cs, negq(bstar), Lt(asg, mul(s + t - v + 1, pi)), c1, c3, c12, c14, c15),
    and(n === 0, phi === 0, u === v - 1, m > 0, cs, !bstar.isNegative, Lt(mul(bstar, pi), asg), Lt(asg, mul(add(bstar, 1), pi)), c1, c2, c12, c14, c15),
    and(m === 0, phi === 0, u === v + 1, n > 0, cs, !bstar.isNegative, Lt(mul(bstar, pi), asg), Lt(asg, mul(add(bstar, 1), pi)), c1, c3, c12, c14, c15),
    and(n === 0, phi === 0, u < v - 1, m > 0, cs, !bstar.isNegative, Lt(mul(bstar, pi), asg), Lt(asg, mul(s + t - u + 1, pi)), c1, c2, c12, c14, c15),
    and(m === 0, phi === 0, u > v + 1, n > 0, cs, !bstar.isNegative, Lt(mul(bstar, pi), asg), Lt(asg, mul(s + t - v + 1, pi)), c1, c3, c12, c14, c15),
  );
  return or(...conds);
}

/** The integral of g1*g2 over (0, oo) as a G-function, assuming the conditions hold (SymPy _int0oo). */
function int0oo(g1: MeijerG, g2: MeijerG, x: Sym): Expr {
  const [eta] = getCoeffExp(g1.argument, x);
  const [omega] = getCoeffExp(g2.argument, x);
  const negl = (l: readonly Expr[]) => l.map(neg);
  return div(meijerg([...negl(g1.bm), ...g2.an], [...g2.aother, ...negl(g1.bother)], [...negl(g1.an), ...g2.bm], [...g2.bother, ...negl(g1.aother)], div(omega, eta)), eta);
}

// ---- the lookup table ------------------------------------------------------------------

/** The G-function terms of a factor and the condition under which they hold. */
type Rewritten = [GTerm[], Expr];
/** A table entry: terms [fac, G] in the dummy z, and the condition. */
type Entry = [[Expr, MeijerG][], Expr | true];

const constant = (a: Expr, z: Expr): [Expr, MeijerG][] => [
  [a, G([1], [], [], [0], z)],
  [a, G([], [1], [0], [], z)],
];

/** t = p*z**q with p lifted to a polar number, or undefined. */
function argT(u: Expr, z: Sym): Expr | undefined {
  if (!u.has(z)) return undefined;
  const ce = coeffExp(u, z);
  if (!ce) return undefined;
  return mul(liftPolar(ce[0]), pow(z, ce[1]));
}
/** [t, b] with L = t - b, t = p*z**q and b free of z, or undefined. */
function splitLinear(L: Expr, z: Sym): [Expr, Expr] | undefined {
  const xs = addArgs(L).filter((a) => a.has(z));
  if (xs.length !== 1) return undefined;
  const t = argT(first(xs), z);
  if (!t) return undefined;
  return [t, liftPolar(neg(add(...addArgs(L).filter((a) => !a.has(z)))))];
}

const isNonPosInt = (e: Expr): boolean => {
  const u = unpolarify(e);
  return isRat(u) && u.isInteger && !u.isPositive;
};

/** The table entries for the factor f in z (SymPy _create_lookup_table). */
export function lookup(f: Expr, z: Sym): Entry[] {
  const out: Entry[] = [];
  const one = (fac: Expr, g: MeijerG, cond: Expr | true = true): Entry => [[[fac, g]], cond];
  // Heaviside(t - b)*(t - b)**(a - 1) and Heaviside(b - t)*(b - t)**(a - 1)
  const fs = mulArgs(f);
  const hv = fs.filter(isHeaviside);
  const logs = fs.filter((u) => isFnN(u, 'log') || (u instanceof Pow && isFnN(u.base, 'log') && isRat(u.exp) && u.exp.isInteger && u.exp.isPositive));
  if (hv.length === 1 && logs.length === 0 && fs.length <= 2) {
    const H = first(hv);
    const L = first(H.args);
    const rest = fs.filter((u) => u !== H);
    let e: Expr = S.Zero;
    let base: Expr = L;
    if (rest.length === 1) {
      const w = first(rest);
      if (w instanceof Pow && !w.exp.has(z)) {
        base = w.base;
        e = w.exp;
      } else base = S.NaN;
    }
    const a = add(e, 1);
    const tb = splitLinear(L, z);
    if (tb && base.key === L.key) {
      const [t, b] = tb;
      out.push(one(mul(gamma(a), pow(b, sub(a, 1))), Gu([a], [], [], [0], div(t, b)), Gt(b, 0)));
    }
    const bt = splitLinear(neg(L), z);
    if (bt && base.key === L.key) {
      const [t, b] = bt;
      out.push(one(mul(gamma(a), pow(b, sub(a, 1))), Gu([], [a], [0], [], div(t, b)), Gt(b, 0)));
    }
  }
  // (b + t)**(-a) and Abs(b - t)**(-a)
  if (f instanceof Pow && !f.exp.has(z)) {
    const a = neg(f.exp);
    if (f.base instanceof Add) {
      const tb = splitLinear(f.base, z);
      if (tb && !isNonPosInt(a)) {
        const [t, mb] = tb;
        const b = liftPolar(neg(unpolarify(mb)));
        out.push(one(div(pow(b, neg(a)), gamma(a)), Gu([sub(1, a)], [], [0], [], div(t, b))));
      }
    }
    if (isFnN(f.base, 'abs')) {
      // Abs(t - b) = Abs(b - t)
      const tb = splitLinear(first(f.base.args), z);
      if (tb) {
        const [t, b] = tb;
        out.push(one(mul(2, sin(div(mul(pi, a), 2)), gamma(sub(1, a)), pow(abs(b), neg(a))), Gu([sub(1, a)], [div(sub(1, a), 2)], [0], [div(sub(1, a), 2)], div(t, b)), Lt(re(a), 1)));
      }
    }
    // log(t)**n
    if (isFnN(f.base, 'log') && isRat(f.exp) && f.exp.isInteger && f.exp.isPositive) {
      const t = argT(first(f.base.args), z);
      if (t) out.push([logTerms(Number(f.exp.p), t, true, true), true]);
    }
  }
  // exp(polar_lift(-1)*t)
  if (f instanceof Pow && f.base.key === S.E.key) {
    const ce = coeffExp(f.exp, z);
    if (ce) out.push(one(S.One, Gu([], [], [0], [], mul(liftPolar(mul(ce[0], expPolar(mul(-1, I, pi)))), pow(z, ce[1])))));
  }
  // log(t)**n*Heaviside(1 - t) and log(t)**n*Heaviside(t - 1)
  if (hv.length === 1 && logs.length === 1 && fs.length === 2) {
    const lg = first(logs);
    const [lf, n] = lg instanceof Pow ? [lg.base, Number(asRat(lg.exp).p)] : [lg, 1];
    const t = argT(first(lf.args), z);
    const L = first(first(hv).args);
    if (t) {
      const u = first(lf.args);
      if (sub(1, u).key === L.key) out.push([logTerms(n, t, true, false), true]);
      else if (sub(u, 1).key === L.key) out.push([logTerms(n, t, false, true), true]);
    }
  }
  if (f instanceof Fn) {
    const args = f.args;
    const u = at(args, -1);
    const t = argT(u, z);
    const t2 = t ? div(pow(t, 2), 4) : S.Zero;
    if (t && args.length === 1) {
      switch (f.name) {
        case 'sinh':
          out.push(one(pow(pi, R(3, 2)), Gu([], [S.One], [half], [S.One, S.Zero], t2)));
          break;
        case 'cosh':
          out.push(one(pow(pi, R(3, 2)), Gu([], [half], [S.Zero], [half, half], t2)));
          break;
        case 'sin':
          out.push(one(sqrt(pi), Gu([], [], [half], [S.Zero], t2)));
          break;
        case 'cos':
          out.push(one(sqrt(pi), Gu([], [], [S.Zero], [half], t2)));
          break;
        case 'sinc':
          out.push(one(div(sqrt(pi), 2), Gu([], [], [S.Zero], [R(-1, 2)], t2)));
          break;
        case 'log':
          out.push([logTerms(1, t, true, true), true]);
          break;
        case 'Ei':
          out.push([[...constant(neg(mul(I, pi)), z), [S.NegOne, Gu([], [S.One], [S.Zero, S.Zero], [], mul(t, polarLift(-1)))]], true]);
          break;
        case 'Si':
          out.push(one(div(sqrt(pi), 2), Gu([S.One], [], [half], [S.Zero, S.Zero], t2)));
          break;
        case 'Ci':
          out.push(one(neg(div(sqrt(pi), 2)), Gu([], [S.One], [S.Zero, S.Zero], [half], t2)));
          break;
        case 'Shi':
          out.push(one(div(mul(t, sqrt(pi)), 4), Gu([half], [], [S.Zero], [R(-1, 2), R(-1, 2)], mul(polarLift(-1), t2))));
          break;
        case 'Chi':
          out.push(one(neg(div(pow(pi, R(3, 2)), 2)), Gu([], [half, S.One], [S.Zero, S.Zero], [half, half], t2)));
          break;
        case 'erf':
          out.push(one(pow(sqrt(pi), -1), Gu([S.One], [], [half], [S.Zero], pow(t, 2))));
          break;
        case 'erfc':
          out.push(one(pow(sqrt(pi), -1), Gu([], [S.One], [S.Zero, half], [], pow(t, 2))));
          break;
        case 'erfi':
          out.push(one(div(t, sqrt(pi)), Gu([half], [], [S.Zero], [R(-1, 2)], neg(pow(t, 2)))));
          break;
        case 'fresnels':
          out.push(one(half, Gu([S.One], [], [R(3, 4)], [S.Zero, R(1, 4)], div(mul(pow(pi, 2), pow(t, 4)), 16))));
          break;
        case 'fresnelc':
          out.push(one(half, Gu([S.One], [], [R(1, 4)], [S.Zero, R(3, 4)], div(mul(pow(pi, 2), pow(t, 4)), 16))));
          break;
        default:
          break;
      }
    } else if (args.length === 1 && f.name === 'log') {
      // log(t + a)
      const tb = splitLinear(u, z);
      if (tb) {
        const [tt, ma] = tb;
        const a = liftPolar(neg(unpolarify(ma)));
        out.push([[...constant(log(a), z), [S.One, Gu([S.One, S.One], [], [S.One], [S.Zero], div(tt, a))]], true]);
      }
    }
    if (t && args.length === 2 && !first(args).has(z)) {
      const a = first(args);
      switch (f.name) {
        case 'expint':
          out.push(one(S.One, Gu([], [a], [sub(a, 1), S.Zero], [], t)));
          break;
        case 'besselj':
          out.push(one(S.One, Gu([], [], [div(a, 2)], [div(neg(a), 2)], t2)));
          break;
        case 'bessely':
          out.push(one(S.One, Gu([], [div(neg(add(a, 1)), 2)], [div(a, 2), div(neg(a), 2)], [div(neg(add(a, 1)), 2)], t2)));
          break;
        case 'besseli':
          out.push(one(pi, Gu([], [div(add(1, a), 2)], [div(a, 2)], [div(neg(a), 2), div(add(1, a), 2)], t2)));
          break;
        case 'besselk':
          out.push(one(half, Gu([], [], [div(a, 2), div(neg(a), 2)], [], t2)));
          break;
        default:
          break;
      }
    }
  }
  return out;
}
/** log(t)**n with Heaviside(1 - t) (below), Heaviside(t - 1) (above) or both (SymPy make_log1, make_log2). */
function logTerms(n: number, t: Expr, below: boolean, above: boolean): [Expr, MeijerG][] {
  const ones = Array.from({ length: n + 1 }, () => S.One);
  const zeros = Array.from({ length: n + 1 }, () => S.Zero);
  const out: [Expr, MeijerG][] = [];
  if (below) out.push([mul(pow(-1, n), factorial(n)), G([], ones, zeros, [], t)]);
  if (above) out.push([factorial(n), G(ones, [], [], zeros, t)]);
  return out;
}

/**
 * f as a sum of terms C*x**s*G(a*x**b) with b rational (SymPy _rewrite_single,
 * without the recursive rewriting through Mellin transforms).
 */
export function rewriteSingle(f: Expr, x: Sym): Rewritten | undefined {
  if (f instanceof MeijerG) {
    const [c, m] = asCoeffMul(factor(f.argument), [x]);
    if (m.length !== 1) return undefined;
    const t = first(m);
    if (t instanceof Pow ? t.base.key !== x.key || !isRat(t.exp) : t.key !== x.key) return undefined;
    return [[[S.One, S.Zero, G(f.an, f.aother, f.bm, f.bother, mul(c, t))]], S.true];
  }
  if (!f.has(x)) return [constant(f, x).map(([fac, g]) => [fac, S.Zero, g]), S.true];
  for (const entry of lookup(f, x)) {
    const [terms, cond0] = entry;
    const cond = cond0 === true ? S.true : unpolarify(cond0);
    if (isFalse(condsimp(cond))) continue;
    const res: GTerm[] = [];
    for (const [fac, g] of terms) {
      const r1 = getCoeffExp(unpolarifyExponents(fac), x);
      if ([r1[0], r1[1], g].some(hasInf)) continue;
      res.push([r1[0], r1[1], G(g.an, g.aother, g.bm, g.bother, unpolarifyExponents(g.argument))]);
    }
    if (res.length) return [res, cond];
  }
  return undefined;
}

/** f = fac*po*g with g a sum of single G-functions (SymPy _rewrite1). */
export function rewrite1(f: Expr, x: Sym): [Expr, Expr, GTerm[], Expr] | undefined {
  const [fac, po, g] = splitMul(f, x);
  const r = rewriteSingle(g, x);
  return r ? [fac, po, r[0], r[1]] : undefined;
}

/** f = fac*po*g1*g2 with g1, g2 sums of single G-functions (SymPy _rewrite2). */
export function rewrite2(f: Expr, x: Sym): [Expr, Expr, GTerm[], GTerm[], Expr] | undefined {
  const [fac, po, g] = splitMul(f, x);
  if (mulArgsRepeated(g).some((e) => rewriteSingle(e, x) === undefined)) return undefined;
  const l = mulAsTwoParts(g);
  if (!l) return undefined;
  const key = (pr: [Expr, Expr]): number[] => [
    Math.max(exponents(pr[0], x).size, exponents(pr[1], x).size),
    Math.max(functions(pr[0], x).size, functions(pr[1], x).size),
    Math.max(findSplittingPoints(pr[0], x).length, findSplittingPoints(pr[1], x).length),
  ];
  const ordered = l
    .map((pr) => [key(pr), pr] as const)
    .sort((u, v) => {
      for (const [i, a] of u[0].entries()) if (a !== at(v[0], i)) return a - at(v[0], i);
      return compareKeys(sortKey(mul(...u[1])), sortKey(mul(...v[1])));
    })
    .map(([, pr]) => pr);
  for (const [f1, f2] of ordered) {
    const g1 = rewriteSingle(f1, x);
    const g2 = rewriteSingle(f2, x);
    // (the conditions of the table are not False)
    if (g1 && g2) return [fac, po, g1[0], g2[0], and(g1[1], g2[1])];
  }
  return undefined;
}

// ---- definite integrals --------------------------------------------------------------------

/** The integral of f over (0, oo) by one or two G-functions (SymPy _meijerint_definite_4). */
function meijerintDefinite4(f: Expr, x: Sym): [Expr, Expr] | undefined {
  const gs = rewrite1(f, x);
  if (gs) {
    const [fac, po, terms, cond0] = gs;
    let cond = cond0;
    let res: Expr = S.Zero;
    for (const [C0, s, g0] of terms) {
      if (isRat(C0) && C0.isZero) continue;
      const [C, g] = rewriteSaxena1(mul(fac, C0), mul(po, pow(x, s)), g0, x);
      res = add(res, mul(C, int0oo1(g, x)));
      cond = and(cond, checkAntecedents1(g, x));
      if (isFalse(cond)) break;
    }
    cond = myUnpolarify(cond);
    if (!isFalse(cond)) return [myUnpolarify(hyperexpand(res)), cond];
  }
  const gs2 = rewrite2(f, x);
  if (!gs2) return undefined;
  for (const fullPb of [false, true]) {
    const [fac, po, g1, g2, cond0] = gs2;
    let cond = cond0;
    let res: Expr = S.Zero;
    outer: for (const [C1, s1, f1] of g1) {
      for (const [C2, s2, f2] of g2) {
        const r = rewriteSaxena(mul(fac, C1, C2), mul(po, pow(x, add(s1, s2))), f1, f2, x, fullPb);
        if (!r) return undefined;
        const [C, f1n, f2n] = r;
        cond = and(cond, checkAntecedents(f1n, f2n, x));
        if (isFalse(cond)) break outer;
        res = add(res, mul(C, int0oo(f1n, f2n, x)));
      }
    }
    cond = myUnpolarify(cond);
    if (!isFalse(cond)) return [myUnpolarify(hyperexpand(res)), cond];
  }
  return undefined;
}

/** The integral over (0, oo), also term by term (SymPy _meijerint_definite_3). */
function meijerintDefinite3(f: Expr, x: Sym): [Expr, Expr] | undefined {
  const res = meijerintDefinite4(f, x);
  if (res) return res;
  if (!(f instanceof Add)) return undefined;
  const ress = f.args.map((g) => meijerintDefinite4(g, x));
  if (ress.some((r) => r === undefined)) return undefined;
  const parts = ress.filter((r): r is [Expr, Expr] => r !== undefined);
  return [add(...parts.map(([v]) => v)), and(...parts.map(([, cc]) => cc))];
}

/** The integral over (0, oo) of f and of its expansions (SymPy _meijerint_definite_2). */
function meijerintDefinite2(f0: Expr, x0: Sym): [Expr, Expr] | undefined {
  const x = new Dummy('x', { positive: true });
  const f = xreplace(f0, [[x0, x]]);
  if (isRat(f) && f.isZero) return [S.Zero, S.true];
  const seen = new Set<string>();
  for (const g of [f, expandMul(f), expand(f)]) {
    if (seen.has(g.key)) continue;
    seen.add(g.key);
    const res = meijerintDefinite3(g, x);
    if (res) return res;
  }
  return undefined;
}

/**
 * The integral of f over [a, b] by rewriting it as one or a product of two
 * Meijer G-functions, with the convergence condition, or undefined (SymPy
 * meijerint_definite).
 */
export function meijerintDefinite(fIn: ExprLike, x0: Sym, aIn: ExprLike, bIn: ExprLike): [Expr, Expr] | undefined {
  const f0 = sympify(fIn);
  const a = sympify(aIn);
  const b = sympify(bIn);
  if (some(f0, isDiracDelta)) return undefined;
  const x = new Dummy('x');
  let f = xreplace(f0, [[x0, x]]);
  if (a.key === b.key) return [S.Zero, S.true];
  // (SymPy goes on looking for a result without G-functions after one with them; symjs takes the first one)
  let result: [Expr, Expr] | undefined;
  if (isOo(a, '-oo') && !isOo(b, 'oo')) return meijerintDefinite(xreplace(f, [[x, neg(x)]]), x, neg(b), neg(a));
  if (isOo(a, '-oo')) {
    const points = findSplittingPoints(f, x).sort((u, v) => compareKeys(sortKey(v), sortKey(u)));
    for (const c of [...points, S.Zero]) {
      if (isReal(c) !== true) continue;
      const r1 = meijerintDefinite2(xreplace(f, [[x, add(x, c)]]), x);
      if (!r1) continue;
      const r2 = meijerintDefinite2(xreplace(f, [[x, sub(c, x)]]), x);
      if (!r2) continue;
      // (the conditions are not False)
      return [add(r1[0], r2[0]), condsimp(and(r1[1], r2[1]))];
    }
    return undefined;
  }
  if (isOo(a, 'oo')) {
    const r = meijerintDefinite(f, x, b, S.Infinity);
    return r ? [neg(r[0]), r[1]] : undefined;
  }
  if (a.key === S.Zero.key && isOo(b, 'oo')) result = meijerintDefinite2(f, x);
  else {
    if (isOo(b, 'oo')) {
      for (const split of findSplittingPoints(f, x)) {
        if (isPositive(sub(a, split)) === true || sub(a, split).key === S.Zero.key) {
          result ??= meijerintDefinite2(mul(xreplace(f, [[x, add(x, split)]]), Heaviside(sub(add(x, split), a))), x);
        }
      }
    }
    f = xreplace(f, [[x, add(x, a)]]);
    let bb = sub(b, a);
    if (!isOo(bb, 'oo')) {
      const phi = exp(mul(I, arg(bb)));
      bb = abs(bb);
      f = mul(xreplace(f, [[x, mul(phi, x)]]), Heaviside(sub(bb, x)), phi);
    }
    result ??= meijerintDefinite2(f, x);
  }
  // hyperbolic functions written with exponentials (SymPy _rewrite_hyperbolics_as_exp)
  if (!result && some(f0, (n) => isFnN(n, 'sinh') || isFnN(n, 'cosh'))) {
    const g = mapBottomUp(f0, (n) => (isFnN(n, 'sinh') || isFnN(n, 'cosh') ? rewrite(n, 'exp') : n));
    result = meijerintDefinite(g, x0, a, b);
  }
  return result;
}

// ---- inverse Laplace transforms -----------------------------------------------------------

/** The convergence condition of the Laplace inversion integral of g (SymPy _check_antecedents_inversion). */
function checkAntecedentsInversion(g0: MeijerG, x: Sym): Expr | boolean {
  const [, e0] = getCoeffExp(g0.argument, x);
  if (isNegative(e0) === true) return checkAntecedentsInversion(flipG(g0), x);
  const g = g0;
  const z = g.argument;
  const [, e] = getCoeffExp(z, x);
  const statementHalf = (a0: Expr, b0: Expr, c0: Expr, zz: Expr, plus: boolean): Expr => {
    const [coeff, exponent] = getCoeffExp(zz, x);
    const a = mul(a0, exponent);
    const b = mul(b0, pow(coeff, c0));
    const c = mul(c0, exponent);
    const w = mul(b, exp(mul(plus ? 1 : -1, I, re(c), pi, half)));
    return or(
      and(or(Eq(b, 0), Le(re(c), 0)), Le(re(a), -1)),
      and(Ne(b, 0), Eq(im(c), 0), Gt(re(c), 0), Lt(re(w), 0)),
      and(Ne(b, 0), Eq(im(c), 0), Gt(re(c), 0), Le(re(w), 0), Le(re(a), -1)),
    );
  };
  const statement = (a: Expr, b: Expr, c: Expr, zz: Expr): Expr => and(statementHalf(a, b, c, zz, true), statementHalf(a, b, c, zz, false));
  const [m, n, p, q] = [g.bm.length, g.an.length, g.ap.length, g.bq.length];
  const tau = m + n - p;
  const nu = q - m - n;
  const rho = R(tau - nu, 2);
  const sigma = q - p;
  const epsilon = sigma === 1 ? half : sigma > 1 ? S.One : S.NaN;
  const theta = div(add(R(1 - sigma, 2), ...g.bq, ...g.ap.map(neg)), sigma);
  const delta = g.delta;
  if (!(isPositive(sub(delta, div(e, 2))) === true || sub(delta, div(e, 2)).key === S.Zero.key || (p >= 1 && p >= q))) return false;
  for (const a of g.an) {
    for (const b of g.bm) {
      const d = sub(a, b);
      if (isRat(d) && d.isInteger && d.isPositive) return false;
    }
  }
  const E = (zz: Expr) => and(...g.an.map((a) => statement(sub(a, 1), S.Zero, S.Zero, zz)));
  if (p >= q) return E(z);
  const H = (zz: Expr) => statement(theta, R(-sigma), R(1, sigma), zz);
  const Hp = (zz: Expr) => statementHalf(theta, R(-sigma), R(1, sigma), zz, true);
  const Hm = (zz: Expr) => statementHalf(theta, R(-sigma), R(1, sigma), zz, false);
  const ei = (c: ExprLike) => exp(mul(I, pi, c));
  const halfPi = div(pi, 2);
  return or(
    and(1 <= n, 1 <= m, Ge(sub(mul(rho, pi), delta), halfPi), Gt(delta, 0), E(mul(z, ei(nu + 1)))),
    and(p + 1 <= m, m + 1 <= q, Gt(delta, 0), Lt(delta, halfPi), n === 0, Ge(sub(mul(m - p + 1, pi), delta), halfPi), Hp(mul(z, ei(q - m))), Hm(mul(z, ei(-(q - m))))),
    and(m === q, n === 0, Gt(delta, 0), Ge(sub(mul(add(sigma, epsilon), pi), delta), halfPi), H(z)),
    and(or(and(p <= q - 2, 1 <= tau, tau <= sigma / 2), and(p + 1 <= m + n, m + n <= (p + q) / 2)), Gt(delta, 0), Lt(delta, halfPi), Ge(sub(mul(tau + 1, pi), delta), halfPi), Hp(mul(z, ei(nu))), Hm(mul(z, ei(-nu)))),
    and(1 <= m, rho.isPositive, Gt(delta, 0), Lt(add(delta, mul(rho, pi)), halfPi), Ge(sub(mul(add(tau, epsilon), pi), delta), halfPi), Hp(mul(z, ei(nu))), Hm(mul(z, ei(-nu)))),
    m === 0,
  );
}

/** The Laplace inversion integral of g, assuming the formula applies (SymPy _int_inversion). */
function intInversion(g: MeijerG, x: Sym, t: Expr): Expr {
  const [b, a] = getCoeffExp(g.argument, x);
  const [C, h] = inflateFoxH(G(g.an, g.aother, g.bm, g.bother, div(b, pow(t, a))), asRat(neg(a)));
  return mul(div(C, t), h);
}

/**
 * The inverse Laplace transform of f, the integral of f(x)*exp(t*x) from
 * c - I*oo to c + I*oo divided by 2*pi*I, by rewriting f as a G-function;
 * [value, condition] or undefined (SymPy meijerint_inversion, for t > 0).
 */
export function meijerintInversion(f0: Expr, x: Sym, t0: Sym): [Expr, Expr] | undefined {
  const t = new Dummy('t', { positive: true });
  let f = xreplace(f0, [[t0, t]]);
  if (some(f, (e) => isHeaviside(e) || isFnN(e, 'abs'))) return undefined;
  let shift: Expr = S.Zero;
  if (f instanceof Mul || (f instanceof Pow && f.base.key === S.E.key)) {
    const args = [...mulArgs(f)];
    const newargs: Expr[] = [];
    const exponentials: Expr[] = [];
    for (let a = args.pop(); a !== undefined; a = args.pop()) {
      if (a instanceof Pow && a.base.key === S.E.key) {
        const a2 = expand(a);
        if (a2 instanceof Mul) {
          args.push(...a2.args);
          continue;
        }
        const ce = coeffExp(a.exp, x);
        if (ce && ce[1].key === S.One.key) exponentials.push(ce[0]);
        else newargs.push(a);
      } else newargs.push(a);
    }
    shift = add(...exponentials);
    f = mul(...newargs);
  }
  // exp(c*s) with c > 0 (or of unknown sign) is no Laplace transform (an advance, not a delay)
  if (isNegative(shift) !== true && !(isRat(shift) && shift.isZero)) return undefined;
  if (!f.has(x)) return undefined;
  const gs = rewrite1(f, x);
  if (!gs) return undefined;
  const [fac, po, terms, cond0] = gs;
  let cond: Expr = cond0;
  let res: Expr = S.Zero;
  for (const [C0, s, g0] of terms) {
    const [, sp] = getCoeffExp(mul(po, pow(x, s)), x);
    const [a, b] = getCoeffExp(g0.argument, x);
    // (the inversion integral needs a rational exponent b)
    if (!isRat(b)) return undefined;
    const tr = (l: readonly Expr[]) => l.map((p) => add(p, div(sp, b)));
    const C = powdenestPolar(div(mul(fac, C0), pow(a, div(sp, b))));
    const g = G(tr(g0.an), tr(g0.aother), tr(g0.bm), tr(g0.bother), g0.argument);
    res = add(res, mul(C, intInversion(g, x, t)));
    const ca = checkAntecedentsInversion(g, x);
    cond = and(cond, ca);
    if (isFalse(cond)) break;
  }
  cond = myUnpolarify(cond);
  if (isFalse(cond)) return undefined;
  const r = myUnpolarify(hyperexpand(res));
  // (t is positive here: the Heaviside step is put in with t0; hyperexpand gives no Heaviside function itself)
  const back = (e: Expr): Expr => xreplace(xreplace(e, [[t, add(t, shift)]]), [[t, t0]]);
  return [mul(back(r), Heaviside(add(t0, shift))), back(cond)];
}

