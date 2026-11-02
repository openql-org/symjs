// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy simplify.sqrtdenest (denesting of square roots:
 * numeric and symbolic denesting, Borodin's recursive algorithm,
 * biquadratic denesting, rational combinations of radicals) together with
 * the parts of simplify.radsimp it relies on (radsimp, rad_rationalize,
 * split_surds).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Mul, Pow, Rational, S, impl } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { countOps, ordered } from '../core/match';
import { keepCoeff } from '../core/methods';
import { rebuild } from '../core/traverse';
import { gcd as igcd } from '../core/numbers';
import { expand } from './expand';
import { fraction } from './rational';
import { gcdTerms, signsimp } from './exprtools';
import { powdenest, powsimp } from './powsimp';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at, defined, first, last } from '../core/guard';

// an internal control-flow signal that never leaves this module
// oxlint-disable-next-line no-restricted-globals
class StopDenest extends Error {}

const isHalfAbs = (e: Expr) => e instanceof Rational && e.q === 2n && (e.p === 1n || e.p === -1n);
const isSqrt = (e: Expr): e is Pow => e instanceof Pow && isHalfAbs(e.exp);
const isZero = (e: Expr) => e instanceof Rational && e.isZero;
const isOne = (e: Expr) => e instanceof Rational && e.isOne;
const sortedArgs = (e: Expr) => [...e.args].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
/** SymPy _mexpand: expand_mul and expand_multinomial. */
const mexpand = (e: Expr): Expr => expand(e, { power_exp: false, power_base: false, log: false });
const num = (e: Expr): number => e.toComplex().re;
const isRat = (e: Expr): e is Rational => e instanceof Rational;
const asCoeffMul = (e: Expr): [Expr, Expr] => {
  if (e instanceof Mul && e.args[0] instanceof Rational) return [e.args[0], e.args.length === 2 ? at(e.args, 1) : new Mul(e.args.slice(1))];
  if (e instanceof Rational) return [e, S.One];
  return [S.One, e];
};

/** Nesting depth of square roots (I counts as one). */
export function sqrtDepth(p: Expr): number {
  if (p instanceof Constant && p.name === 'I') return 1;
  if (p.args.length === 0) return 0;
  if (p instanceof Add || p instanceof Mul) return Math.max(...p.args.map(sqrtDepth));
  if (isSqrt(p)) return sqrtDepth(p.base) + 1;
  return 0;
}

function isAlgebraic(p: Expr): boolean {
  if (p instanceof Rational) return true;
  if (p.args.length === 0) return false;
  if (isSqrt(p) || (p instanceof Pow && p.exp instanceof Rational && p.exp.isInteger)) return isAlgebraic((p).base);
  if (p instanceof Add || p instanceof Mul) return p.args.every(isAlgebraic);
  return false;
}

function subsets(n: number): number[][] {
  if (n === 1) return [[1]];
  if (n === 2) return [[1, 0], [0, 1], [1, 1]];
  if (n === 3) return [[1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]];
  const b = subsets(n - 1);
  return [...b.map((x) => [...x, 0]), [...Array<number>(n - 1).fill(0), 1], ...b.map((x) => [...x, 1])];
}

// ---- radsimp helpers -------------------------------------------------------------

function splitGcd(...a: Expr[]): [Expr, Expr[], Expr[]] {
  let g = first(a);
  const b1 = [g];
  const b2: Expr[] = [];
  for (const x of a.slice(1)) {
    const g1 = isRat(g) && isRat(x) && g.isInteger && x.isInteger ? Rational.of(igcd(g.p, x.p)) : S.One;
    if (isOne(g1)) b2.push(x);
    else {
      g = g1;
      b1.push(x);
    }
  }
  return [g, b1, b2];
}

/** SymPy split_surds: [g, a, b] with expr = a*sqrt(g) + b. */
export function splitSurds(expr: Expr): [Expr, Expr, Expr] {
  const args = sortedArgs(expr);
  const coeffMuls = args.map(asCoeffMul);
  const surds = coeffMuls.filter(([, s]) => s instanceof Pow).map(([, s]) => pow(s, 2)).sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
  if (!surds.length) return [S.One, S.Zero, expr];
  let [g, b1, b2] = splitGcd(...surds);
  let g2 = g;
  if (!b2.length && b1.length >= 2) {
    const b1n = b1.map((x) => mul(x, pow(g, -1))).filter((x) => !isOne(x));
    if (b1n.length) {
      const [g1] = splitGcd(...b1n);
      g2 = mul(g, g1);
    }
  }
  const a1v: Expr[] = [];
  const a2v: Expr[] = [];
  const inB1 = new Set(b1.map((x) => x.key));
  for (const [c, s] of coeffMuls) {
    if (s instanceof Pow && s.exp.key === S.Half.key && inB1.has(s.base.key)) a1v.push(mul(c, sqrt(mul(s.base, pow(g2, -1)))));
    else a2v.push(mul(c, s));
  }
  return [g2, add(...a1v), add(...a2v)];
}

/** SymPy rad_rationalize(num, den): rationalize den = a*sqrt(g) + b step by step. */
export function radRationalize(numIn: Expr, den: Expr): [Expr, Expr] {
  if (!(den instanceof Add)) return [numIn, den];
  const [g, a0, b] = splitSurds(den);
  const a = mul(a0, sqrt(g));
  return radRationalize(mexpand(mul(add(a, mul(-1, b)), numIn)), mexpand(add(pow(a, 2), mul(-1, pow(b, 2)))));
}

/**
 * SymPy radsimp: rationalize the denominator, removing square roots (up to
 * four radical terms; symbolic radicands unless `symbolic` is false).
 */
export function radsimp(exIn: ExprLike, opts: { symbolic?: boolean; maxTerms?: number } = {}): Expr {
  const symbolic = opts.symbolic ?? true;
  const maxTerms = opts.maxTerms ?? 4;
  const expr0 = sympify(exIn);
  const sq = (x: Expr) => sqrt(x);
  const numFor = (rterms: [Expr, Expr][]): Expr => {
    const [A, a] = first(rterms);
    if (rterms.length === 1) return sq(A);
    const [B, b] = at(rterms, 1);
    if (rterms.length === 2) return add(mul(sq(A), a), mul(-1, sq(B), b));
    const [C, c] = at(rterms, 2);
    if (rterms.length === 3) {
      return mul(
        add(mul(sq(A), a), mul(sq(B), b), mul(-1, sq(C), c)),
        add(mul(2, sq(A), sq(B), a, b), mul(-1, A, pow(a, 2)), mul(-1, B, pow(b, 2)), mul(C, pow(c, 2))),
      );
    }
    const [D, d] = at(rterms, 3);
    return mul(
      add(mul(sq(A), a), mul(sq(B), b), mul(-1, sq(C), c), mul(-1, sq(D), d)),
      add(mul(2, sq(A), sq(B), a, b), mul(-1, A, pow(a, 2)), mul(-1, B, pow(b, 2)), mul(-2, sq(C), sq(D), c, d), mul(C, pow(c, 2)), mul(D, pow(d, 2))),
      add(
        mul(-8, sq(A), sq(B), sq(C), sq(D), a, b, c, d),
        mul(pow(A, 2), pow(a, 4)),
        mul(-2, A, B, pow(a, 2), pow(b, 2)),
        mul(-2, A, C, pow(a, 2), pow(c, 2)),
        mul(-2, A, D, pow(a, 2), pow(d, 2)),
        mul(pow(B, 2), pow(b, 4)),
        mul(-2, B, C, pow(b, 2), pow(c, 2)),
        mul(-2, B, D, pow(b, 2), pow(d, 2)),
        mul(pow(C, 2), pow(c, 4)),
        mul(-2, C, D, pow(c, 2), pow(d, 2)),
        mul(pow(D, 2), pow(d, 4)),
      ),
    );
  };
  const denomOf = (e: Expr) => fraction(e)[1];
  const ispow2 = (d: Expr, log2 = false): d is Pow => {
    if (!(d instanceof Pow)) return false;
    const e = d.exp;
    if ((e instanceof Rational && e.q === 2n) || (symbolic && denomOf(e).key === Rational.of(2n).key)) return true;
    if (log2) {
      let q = 1n;
      if (e instanceof Rational) q = e.q;
      else if (symbolic) {
        const dd = denomOf(e);
        if (dd instanceof Rational && dd.isInteger) q = dd.p;
      }
      if (q !== 1n && (q & (q - 1n)) === 0n) return true;
    }
    return false;
  };
  const handle = (expr: Expr): Expr => {
    if (expr.args.length === 0) return expr;
    let [n, d] = fraction(expr);
    if (d.args.length === 0 && n.args.length === 0) return expr;
    if (n.args.length > 0) {
      n = rebuild(n, n.args.map(handle));
      return mul(n, handle(pow(d, -1)));
    }
    if (!isOne(n)) return mul(n, handle(pow(d, -1)));
    if (d instanceof Mul) return mul(...d.args.map((x) => handle(pow(x, -1))));
    if (!symbolic && d.freeSymbols().size) return expr;
    if (ispow2(d)) {
      const d2 = pow(sqrtdenest(sqrt(d.base)), fraction(d.exp)[0]);
      if (d2.key !== d.key) return handle(pow(d2, -1));
    } else if (d instanceof Pow && (d.exp instanceof Rational && d.exp.isInteger)) {
      return pow(handle(pow(d.base, -1)), d.exp);
    }
    if (!(d instanceof Add || ispow2(d))) return pow(rebuild(d, d.args.map(handle)), -1);
    let keep = true;
    d = mexpand(d);
    if (d.args.length === 0) return pow(d, -1);
    for (;;) {
      const collected = new Map<string, [Expr[], Expr[]]>();
      for (const m of d instanceof Add ? d.args : [d]) {
        const p2: Expr[] = [];
        const other: Expr[] = [];
        for (const i of m instanceof Mul ? m.args : [m]) {
          if (ispow2(i, true)) p2.push(i.exp.key === S.Half.key ? i.base : pow(i.base, mul(2, i.exp)));
          else if (i instanceof Constant && i.name === 'I') p2.push(S.NegOne);
          else other.push(i);
        }
        const key = ordered(p2);
        const k = key.map((x) => x.key).join('|');
        const cur = collected.get(k);
        if (cur) cur[1].push(mul(...other));
        else collected.set(k, [key, [mul(...other)]]);
      }
      let rterms: [Expr, Expr][] = [...collected.values()].map(([k, v]) => [mul(...k), add(...v)] as [Expr, Expr]);
      rterms = rterms.sort((x, y) => compareKeys(sortKey(x[0]), sortKey(y[0])));
      const nrad = rterms.length - (isOne(first(rterms)[0]) ? 1 : 0);
      if (nrad < 1) break;
      if (nrad > maxTerms) {
        keep = false;
        break;
      }
      if (rterms.length > 4) {
        if (rterms.every(([x, y]) => x instanceof Rational && x.isInteger && pow(y, 2) instanceof Rational)) {
          const [nd, dd] = radRationalize(S.One, add(...rterms.map(([x, y]) => mul(sqrt(x), y))));
          n = mul(n, nd);
          d = dd;
        } else keep = false;
        break;
      }
      const nm = powsimp(numFor(rterms));
      n = mul(n, nm);
      d = mul(d, nm);
      d = powdenest(mexpand(d), { force: symbolic });
      if (d.args.length === 0) break;
    }
    if (!keep) return expr;
    return mul(n, pow(d, -1));
  };
  // coeff + rest
  let coeff: Expr = S.Zero;
  let expr = expr0;
  if (expr instanceof Add && expr.args[0] instanceof Rational) {
    coeff = expr.args[0];
    expr = add(...expr.args.slice(1));
  }
  const old = fraction(expr);
  let [n, d] = fraction(handle(expr));
  if (n.key !== old[0].key || d.key !== old[1].key) {
    if (d.args.length > 0) {
      const was: [Expr, Expr] = [n, d];
      n = signsimp(n);
      d = signsimp(d);
      [n, d] = fraction(mul(n, pow(d, -1)));
      if (n.key === old[0].key && d.key === old[1].key) [n, d] = was;
    }
    n = expand(n, { power_exp: false, power_base: false, log: false, multinomial: false });
    if (d instanceof Rational || d instanceof Add) {
      const [n2, d2] = fraction(gcdTerms(mul(n, pow(d, -1))));
      if (d2 instanceof Rational || countOps(d2) <= countOps(d)) [n, d] = [signsimp(n2), signsimp(d2)];
    }
  }
  // a rational denominator stays outside the sum, (2 - sqrt(2))/2 (SymPy _unevaluated_Mul)
  const q = d instanceof Rational && n instanceof Add ? keepCoeff(pow(d, -1), n) : mul(n, pow(d, -1));
  return add(coeff, q);
}

// ---- sqrtdenest -------------------------------------------------------------------

/** SymPy sqrtdenest: denest the square roots of an expression (at most maxIter passes). */
export function sqrtdenest(exIn: ExprLike, maxIter = 3): Expr {
  let expr = expand(sympify(exIn), { power_exp: false, power_base: false, log: false, multinomial: false });
  for (let i = 0; i < maxIter; i++) {
    const z = sqrtdenest0(expr);
    if (z.key === expr.key) return expr;
    expr = z;
  }
  return expr;
}

/** [a, b, r] with p = a + b*sqrt(r), or undefined. */
function sqrtMatch(p0: Expr): [Expr, Expr, Expr] | undefined {
  const p = mexpand(p0);
  if (p.isNumber && p.args.length === 0) return [p, S.Zero, S.Zero];
  if (p instanceof Add) {
    const pargs = sortedArgs(p);
    if (pargs.every((x) => {
      const s = pow(x, 2);
      return s instanceof Rational && s.isPositive;
    })) {
      const [r, b, a] = splitSurds(p);
      return [a, b, r];
    }
    const v = pargs.map((x, i) => [sqrtDepth(x), x, i] as [number, Expr, number]);
    const nmax = v.reduce((m, c) => (c[0] > m[0] || (c[0] === m[0] && compareKeys(sortKey(c[1]), sortKey(m[1])) > 0) ? c : m));
    if (nmax[0] === 0) return undefined;
    const [depth, , idx] = nmax;
    let r = first(pargs.splice(idx, 1));
    v.splice(idx, 1);
    let b: Expr = S.One;
    if (r instanceof Mul) {
      const bv: Expr[] = [];
      const rv: Expr[] = [];
      for (const x of r.args) (sqrtDepth(x) < depth ? bv : rv).push(x);
      b = mul(...bv);
      r = mul(...rv);
    }
    const a1: Expr[] = [];
    const b1: Expr[] = [b];
    for (const [dep, x1] of v) {
      if (dep < depth) a1.push(x1);
      else if (x1.key === r.key) b1.push(S.One);
      else if (x1 instanceof Mul && x1.args.some((y) => y.key === r.key)) {
        const rest = [...x1.args];
        rest.splice(rest.findIndex((y) => y.key === r.key), 1);
        b1.push(mul(...rest));
      } else a1.push(x1);
    }
    return [add(...a1), add(...b1), pow(r, 2)];
  }
  const [b, r] = asCoeffMul(p);
  if (isSqrt(r)) return [S.Zero, b, pow(r, 2)];
  return undefined;
}

function sqrtdenest0(expr: Expr): Expr {
  if (isSqrt(expr)) {
    const [n, d] = fraction(expr);
    if (isOne(d)) {
      let e: Expr = n;
      if (n instanceof Pow && n.base instanceof Add) {
        const args = sortedArgs(n.base);
        if (args.length > 2 && args.every((x) => {
            const x2 = pow(x, 2);
            return x2 instanceof Rational && x2.isInteger;
          })) {
          try {
            return sqrtdenestRec(n);
          } catch (err) {
            if (!(err instanceof StopDenest)) throw err;
          }
        }
        e = sqrt(mexpand(add(...args.map(sqrtdenest0))));
      }
      return sqrtdenest1(e);
    }
    return mul(sqrtdenest0(n), pow(sqrtdenest0(d), -1));
  }
  if (expr instanceof Add) {
    const parts = expr.args.map(asCoeffMul);
    const radicals = parts.map(([, a]) => a).filter(isSqrt);
    if (parts.every(([c]) => c instanceof Rational) && radicals.length === parts.length) {
      return sqrtRatcomb(
        parts.map(([c]) => c),
        radicals,
      );
    }
  }
  if (expr.args.length) return rebuild(expr, expr.args.map(sqrtdenest0));
  return expr;
}

function sqrtdenestRec(expr: Expr): Expr {
  if (!(expr instanceof Pow)) return sqrtdenest(expr);
  if (num(expr.base) < 0) return mul(S.I, sqrtdenestRec(sqrt(mul(-1, expr.base))));
  let [g, a, b] = splitSurds(expr.base);
  a = mul(a, sqrt(g));
  if (num(a) < num(b)) [a, b] = [b, a];
  const c2 = mexpand(add(pow(a, 2), mul(-1, pow(b, 2))));
  let c: Expr;
  if (c2.args.length > 2) {
    let [g1, a1, b1] = splitSurds(c2);
    a1 = mul(a1, sqrt(g1));
    if (num(a1) < num(b1)) [a1, b1] = [b1, a1];
    const c21 = mexpand(add(pow(a1, 2), mul(-1, pow(b1, 2))));
    const c1 = sqrtdenestRec(sqrt(c21));
    const d1 = sqrtdenestRec(sqrt(add(a1, c1)));
    const [nn, dd] = radRationalize(b1, d1);
    c = mexpand(add(mul(d1, pow(sqrt(2), -1)), mul(nn, pow(mul(dd, sqrt(2)), -1))));
  } else c = sqrtdenest1(sqrt(c2));
  if (sqrtDepth(c) > 1) throw new StopDenest();
  const ac = add(a, c);
  if (ac.args.length >= expr.args.length && countOps(ac) >= countOps(expr.base)) throw new StopDenest();
  const d = sqrtdenest(sqrt(ac));
  if (sqrtDepth(d) > 1) throw new StopDenest();
  const [nn, dd] = radRationalize(b, d);
  const r = radsimp(add(mul(d, pow(sqrt(2), -1)), mul(nn, pow(mul(dd, sqrt(2)), -1))));
  return mexpand(r);
}

function sqrtdenest1(expr: Expr, denester = true): Expr {
  if (!isSqrt(expr)) return expr;
  const a0 = expr.base;
  if (a0.args.length === 0) return expr;
  const val = sqrtMatch(a0);
  if (!val) return expr;
  const [a, b, r] = val;
  const d2 = mexpand(add(pow(a, 2), mul(-1, pow(b, 2), r)));
  if (d2 instanceof Rational) {
    if (d2.isPositive) {
      const z = sqrtNumericDenest(a, b, r, d2);
      if (z) return z;
    } else {
      const dr2 = mexpand(mul(-1, d2, r));
      if (sqrt(dr2) instanceof Rational) {
        const z = sqrtNumericDenest(mexpand(mul(b, r)), a, r, dr2);
        if (z) return mul(z, pow(r, Rational.of(-1n, 4n)));
      }
    }
  } else {
    const z = sqrtSymbolicDenest(a, b, r);
    if (z) return z;
  }
  if (!denester || !isAlgebraic(expr)) return expr;
  const res = sqrtBiquadraticDenest(expr, a, b, r, d2);
  if (res) return res;
  const av0: (Expr | undefined)[] = [a, b, r, d2];
  const z = denesterRec([radsimp(pow(expr, 2))], av0, 0, sqrtDepth(expr))[0];
  if (av0[1] === undefined) return expr;
  if (z) {
    if (sqrtDepth(z) === sqrtDepth(expr) && countOps(z) > countOps(expr)) return expr;
    return z;
  }
  return expr;
}

function sqrtSymbolicDenest(a: Expr, b: Expr, r: Expr): Expr | undefined {
  const rval = sqrtMatch(r);
  if (!rval) return undefined;
  const [ra, rb, rr] = rval;
  if (isZero(rb)) return undefined;
  // a in terms of y = sqrt(r): a(y) = ca*y**2 + cb*y + cc with b added to cb
  const y = new Sym_('y_sqd');
  const ay = expand(mexpand(a).subs([[sqrt(rr), mul(add(pow(y, 2), mul(-1, ra)), pow(rb, -1))]]));
  const coeff = (k: number) => {
    const terms = ay instanceof Add ? ay.args : [ay];
    return add(...terms.filter((t) => degreeIn(t, y) === k).map((t) => mul(t, pow(y, -k))));
  };
  if (degreeOf(ay, y) !== 2) return undefined;
  const ca = coeff(2);
  const cb = add(coeff(1), b);
  const cc = coeff(0);
  if ([ca, cb, cc].some((c) => c.has(y))) return undefined;
  if (!isZero(mexpand(add(pow(cb, 2), mul(-4, ca, cc))))) return undefined;
  let z = sqrt(mul(ca, pow(add(sqrt(r), mul(cb, pow(mul(2, ca), -1))), 2)));
  if (z.freeSymbols().size === 0) z = mexpand(z);
  return z;
}

// a positive symbol for the substitution in sqrtSymbolicDenest
import { Sym as Sym_ } from '../core/nodes';
const degreeIn = (t: Expr, y: Expr): number => {
  let k = 0;
  for (const f of t instanceof Mul ? t.args : [t]) {
    if (f.key === y.key) k += 1;
    else if (f instanceof Pow && f.base.key === y.key && f.exp instanceof Rational && f.exp.isInteger) k += Number(f.exp.p);
    else if (f.has(y)) return -1;
  }
  return k;
};
const degreeOf = (e: Expr, y: Expr): number => Math.max(...(e instanceof Add ? e.args : [e]).map((t) => degreeIn(t, y)));

function sqrtNumericDenest(a: Expr, b: Expr, r: Expr, d2: Expr): Expr | undefined {
  const d = sqrt(d2);
  const s = add(a, d);
  if (sqrtDepth(s) < sqrtDepth(r) + 1 || pow(s, 2) instanceof Rational) {
    let s1 = Math.sign(num(s));
    let s2 = Math.sign(num(b));
    if (s1 === -1 && s2 === -1) s1 = s2 = 1;
    return expand(mul(add(mul(s1, sqrt(add(a, d))), mul(s2, sqrt(add(a, mul(-1, d))))), sqrt(2), S.Half));
  }
  return undefined;
}

function sqrtBiquadraticDenest(expr: Pow, a: Expr, b: Expr, r: Expr, d2: Expr): Expr | undefined {
  if (num(r) <= 0 || num(d2) < 0 || isZero(b) || sqrtDepth(expr.base) < 2) return undefined;
  for (const x of [a, b, r]) {
    for (const y of x.args) {
      const y2 = pow(y, 2);
      if (!(y2 instanceof Rational && y2.isInteger && y2.isPositive)) return undefined;
    }
  }
  const sqd = mexpand(sqrtdenest(sqrt(radsimp(d2))));
  if (sqrtDepth(sqd) > 1) return undefined;
  for (const x of [add(mul(a, S.Half), mul(sqd, S.Half)), add(mul(a, S.Half), mul(-1, sqd, S.Half))]) {
    const A = sqrtdenest(sqrt(x));
    if (sqrtDepth(A) > 1) continue;
    const [Bn, Bd] = radRationalize(b, mexpand(mul(2, A)));
    let z = add(A, mul(Bn, pow(Bd, -1), sqrt(r)));
    if (num(z) < 0) z = mul(-1, z);
    return mexpand(z);
  }
  return undefined;
}

function denesterRec(nested: Expr[], av0: (Expr | undefined)[], h: number, maxDepth: number): [Expr | undefined, number[] | undefined] {
  if (h > maxDepth) return [undefined, undefined];
  if (av0[1] === undefined) return [undefined, undefined];
  if (av0[0] === undefined && nested.every((n) => n.isNumber && n.args.length === 0)) {
    for (const f of subsets(nested.length)) {
      let p = mexpand(mul(...nested.filter((_, i) => f[i])));
      if (f.filter((x) => x === 1).length > 1 && f[f.length - 1]) p = mul(-1, p);
      const sqp = sqrt(p);
      if (sqp instanceof Rational) return [sqp, f];
    }
    return [sqrt(last(nested)), Array<number>(nested.length).fill(0)];
  }
  let R: Expr | undefined;
  let values: [Expr, Expr, Expr][];
  let nested2: Expr[];
  if (av0[0] !== undefined) {
    values = [[av0[0], av0[1], S.Zero]];
    R = defined(av0[2]);
    nested2 = [defined(av0[3]), R];
    av0[0] = undefined;
  } else {
    values = nested.map(sqrtMatch).filter((v): v is [Expr, Expr, Expr] => v !== undefined);
    for (const v of values) {
      if (!isZero(v[2])) {
        if (R !== undefined) {
          if (R.key !== v[2].key) {
            av0[1] = undefined;
            return [undefined, undefined];
          }
        } else R = v[2];
      }
    }
    if (R === undefined) return [sqrt(last(nested)), Array<number>(nested.length).fill(0)];
    const r0 = R;
    nested2 = [...values.map((v) => add(mexpand(pow(v[0], 2)), mul(-1, mexpand(mul(r0, pow(v[1], 2)))))), r0];
  }
  const [d, f] = denesterRec(nested2, av0, h + 1, maxDepth);
  if (!f || d === undefined) return [undefined, undefined];
  if (!nested.some((_, i) => f[i])) {
    const v = last(values);
    return [sqrt(add(v[0], mexpand(mul(v[1], d)))), f];
  }
  const p = mul(...nested.filter((_, i) => f[i]));
  const v = sqrtMatch(p);
  if (!v) return [undefined, undefined];
  let [v0, v1] = v;
  const firstOne = f.indexOf(1);
  if (firstOne >= 0 && firstOne < nested.length - 1 && f[nested.length - 1]) {
    v0 = mul(-1, v0);
    v1 = mul(-1, v1);
  }
  if (!f[nested.length]) {
    const vad = mexpand(add(v0, d));
    if (num(vad) <= 0) return [sqrt(last(nested)), Array<number>(nested.length).fill(0)];
    if (!(sqrtDepth(vad) <= sqrtDepth(R) + 1 || pow(vad, 2).isNumber)) {
      av0[1] = undefined;
      return [undefined, undefined];
    }
    const sqvad = sqrtdenest1(sqrt(vad), false);
    if (!(sqrtDepth(sqvad) <= sqrtDepth(R) + 1)) {
      av0[1] = undefined;
      return [undefined, undefined];
    }
    const sqvad1 = radsimp(pow(sqvad, -1));
    return [mexpand(add(mul(sqvad, pow(sqrt(2), -1)), mul(v1, sqrt(R), sqvad1, pow(sqrt(2), -1)))), f];
  }
  const s2 = add(mexpand(mul(v1, R)), d);
  if (num(s2) <= 0) return [sqrt(last(nested)), Array<number>(nested.length).fill(0)];
  const FR = pow(mexpand(R), Rational.of(1n, 4n));
  const s = sqrt(s2);
  return [mexpand(add(mul(s, pow(mul(sqrt(2), FR), -1)), mul(v0, FR, pow(mul(sqrt(2), s), -1)))), f];
}

function sqrtRatcomb(cs0: Expr[], args0: Pow[]): Expr {
  const cs = [...cs0];
  const args = [...args0];
  const find = (): [Expr, number, number] | undefined => {
    for (let i = 0; i < args.length - 1; i++) {
      const ai = at(args, i);
      for (let j = i + 1; j < args.length; j++) {
        const p = mexpand(mul(ai.base, at(args, j).base));
        const s = sqrtdenest(sqrt(p));
        if (s.key !== sqrt(p).key) return [s, i, j];
      }
    }
    return undefined;
  };
  const found = find();
  if (!found) return add(...cs.map((c, i) => mul(c, at(args, i))));
  const [s, i1, i2] = found;
  const c2 = first(cs.splice(i2, 1));
  args.splice(i2, 1);
  const a1 = at(args, i1);
  cs[i1] = add(at(cs, i1), radsimp(mul(c2, s, pow(a1.base, -1))));
  return sqrtRatcomb(cs, args);
}

impl.radsimp = (e) => radsimp(e);
