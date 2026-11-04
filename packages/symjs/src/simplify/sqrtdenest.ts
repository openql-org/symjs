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
import { Add, Constant, Mul, Pow, Rational, S, Special, impl, isNum } from '../core/nodes';
import { isPositive } from '../core/assumptions';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { countOps, ordered } from '../core/match';
import { asContentPrimitive, asNumerDenom } from '../core/methods';
import { rebuild } from '../core/traverse';
import { mgcd } from '../polys/mpoly';
import { expand, expandMulOnly } from './expand';
import { fraction } from './rational';
import { gcdTerms, signsimp } from './exprtools';
import { powdenest, powsimp } from './powsimp';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at, defined, expectType, first, last } from '../core/guard';

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
const termsOf = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
const factorsOf = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
/** SymPy as_coeff_Mul: the numeric (Rational or Float) coefficient and the rest. */
const asCoeffMul = (e: Expr): [Expr, Expr] => {
  if (e instanceof Mul && e.args[0] !== undefined && isNum(e.args[0])) return [e.args[0], e.args.length === 2 ? at(e.args, 1) : new Mul(e.args.slice(1))];
  if (isNum(e)) return [e, S.One];
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
  // (n >= 2: denesterRec always nests at least two radicands)
  if (n === 2) return [[1, 0], [0, 1], [1, 1]];
  if (n === 3) return [[1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]];
  const b = subsets(n - 1);
  return [...b.map((x) => [...x, 0]), [...Array<number>(n - 1).fill(0), 1], ...b.map((x) => [...x, 1])];
}

// ---- radsimp helpers -------------------------------------------------------------

/**
 * The generators SymPy's gcd would build polynomials in: symbols, radicals (powers with a
 * non-integer exponent) and other non-polynomial atoms, in their order of appearance.
 */
function gcdGens(es: readonly Expr[]): Expr[] {
  const gens = new Map<string, Expr>();
  const walk = (e: Expr): void => {
    if (e instanceof Rational) return;
    if (e instanceof Add || e instanceof Mul) e.args.forEach(walk);
    else if (e instanceof Pow && e.exp instanceof Rational && e.exp.isInteger) walk(e.base);
    else gens.set(e.key, e);
  };
  es.forEach(walk);
  return [...gens.values()];
}

/** SymPy gcd(a, b) of expressions: the polynomial gcd in the radicals and symbols they contain. */
const exprGcd = (a: Expr, b: Expr): Expr => mgcd(a, b, gcdGens([a, b]));

/** SymPy _split_gcd. */
function splitGcd(...a: Expr[]): [Expr, Expr[], Expr[]] {
  let g = first(a);
  const b1 = [g];
  const b2: Expr[] = [];
  for (const x of a.slice(1)) {
    const g1 = exprGcd(g, x);
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
  // (every caller passes a sum with a radical term; SymPy raises IndexError otherwise)
  let [g, b1, b2] = splitGcd(...surds);
  let g2 = g;
  if (!b2.length && b1.length >= 2) {
    // (the squares of distinct radicals of a sum differ, so some quotient is not 1)
    const b1n = b1.map((x) => mul(x, pow(g, -1))).filter((x) => !isOne(x));
    g2 = mul(g, splitGcd(...b1n)[0]);
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

/** Does e contain 0, nan or zoo (SymPy d.has(S.Zero, nan, zoo))? */
const hasZeroOrNaN = (e: Expr): boolean =>
  (e instanceof Rational && e.isZero) || (e instanceof Special && (e.name === 'nan' || e.name === 'zoo')) || e.args.some(hasZeroOrNaN);

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
      return unevaluatedMul(n, handle(pow(d, -1)));
    }
    if (!isOne(n)) return unevaluatedMul(n, handle(pow(d, -1)));
    if (d instanceof Mul) return unevaluatedMul(...d.args.map((x) => handle(pow(x, -1))));
    if (!symbolic && d.freeSymbols().size) return expr;
    if (ispow2(d)) {
      const d2 = pow(sqrtdenest(sqrt(d.base)), fraction(d.exp)[0]);
      if (d2.key !== d.key) return handle(pow(d2, -1));
    } else if (d instanceof Pow && ((d.exp instanceof Rational && d.exp.isInteger) || isPositive(d.base))) {
      return pow(handle(pow(d.base, -1)), d.exp);
    }
    if (!(d instanceof Add || ispow2(d))) return pow(rebuild(d, d.args.map(handle)), -1);
    let keep = true;
    d = mexpand(d);
    if (d.args.length === 0) return pow(d, -1);
    for (;;) {
      const collected = new Map<string, [Expr[], Expr[]]>();
      for (const m of termsOf(d)) {
        const p2: Expr[] = [];
        const other: Expr[] = [];
        for (const i of factorsOf(m)) {
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
      // a vanishing denominator (1/(x + sqrt(x**2))): the squaring was invalid, keep the input
      if (hasZeroOrNaN(d)) return expr;
      if (d.args.length === 0) break;
    }
    if (!keep) return expr;
    return unevaluatedMul(n, pow(d, -1));
  };
  // coeff + rest
  let coeff: Expr = S.Zero;
  let expr = expr0;
  if (expr instanceof Add && expr.args[0] instanceof Rational) {
    coeff = expr.args[0];
    expr = add(...expr.args.slice(1));
  }
  // SymPy expr.normal(): the expression as one fraction
  const [en, ed] = asNumerDenom(expr);
  if (!isOne(ed)) expr = isNum(ed) ? unevaluatedMul(en, pow(ed, -1)) : mul(en, pow(ed, -1));
  const old = fraction(expr);
  let [n, d] = fraction(handle(expr));
  if (n.key !== old[0].key || d.key !== old[1].key) {
    if (d.args.length > 0) {
      const was: [Expr, Expr] = [n, d];
      n = signsimp(n, false);
      d = signsimp(d, false);
      [n, d] = fraction(unevaluatedMul(...powersOf(unevaluatedMul(n, pow(d, -1)))));
      if (n.key === old[0].key && d.key === old[1].key) [n, d] = was;
    }
    n = expandMulOnly(n);
    if (d instanceof Rational || d instanceof Add) {
      const [n2, d2] = fraction(gcdTerms(mul(n, pow(d, -1))));
      if (d2 instanceof Rational || countOps(d2) <= countOps(d)) [n, d] = [signsimp(n2), signsimp(d2)];
    }
  }
  return add(coeff, unevaluatedMul(n, pow(d, -1)));
}

/**
 * SymPy _unevaluated_Mul: the product with nested products flattened and the numbers combined
 * into one leading coefficient, without evaluating anything else (sqrt(x)/x stays).
 */
function unevaluatedMul(...xs: Expr[]): Expr {
  let c: Expr = S.One;
  const rest: Expr[] = [];
  const walk = (x: Expr): void => {
    if (x instanceof Mul) x.args.forEach(walk);
    else if (isNum(x)) c = mul(c, x);
    else rest.push(x);
  };
  xs.forEach(walk);
  const bases = new Set(rest.map((f) => (f instanceof Pow ? f.base : f).key));
  // the evaluated product is the same unless powers of a base combine or a number distributes over a sum
  if (bases.size === rest.length && !(rest.length === 1 && first(rest) instanceof Add && !(c instanceof Rational && c.p === -1n && c.q === 1n))) return mul(c, ...rest);
  const args = [...(isOne(c) ? [] : [c]), ...rest.sort((a, b) => compareKeys(sortKey(a), sortKey(b)))];
  return args.length === 1 ? first(args) : new Mul(args);
}

/** The factors k**v of SymPy Factors(e): numbers and equal bases combined. */
function powersOf(e: Expr): Expr[] {
  const m = new Map<string, [Expr, Expr]>();
  let c: Expr = S.One;
  for (const f of factorsOf(e)) {
    if (isNum(f)) {
      c = mul(c, f);
      continue;
    }
    const [b, x] = f instanceof Pow ? [f.base, f.exp] : [f, S.One];
    const cur = m.get(b.key);
    m.set(b.key, [b, cur ? add(cur[1], x) : x]);
  }
  return [c, ...[...m.values()].map(([b, x]) => pow(b, x))];
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
    const [n, d] = asNumerDenom(expr);
    if (isOne(d)) {
      let e: Expr = n;
      if (n instanceof Pow && n.base instanceof Add) {
        const args = sortedArgs(n.base);
        if (args.length > 2 && args.every((x) => {
            const x2 = pow(x, 2);
            return x2 instanceof Rational && x2.isInteger;
          })) {
          // a failure of the recursive method (its StopDenest signal) falls back to the general one
          try {
            return sqrtdenestRec(n);
          } catch {
            // fall through
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
  // a in terms of y = sqrt(r): a(y) = ca*y**2 + cc (the substitution gives even powers of y only);
  // as in SymPy (Poly(..., y)) a term that is not a power of y times a y-free factor fails
  const y = new Sym_('y_sqd');
  const ay = expand(mexpand(a).subs([[sqrt(rr), mul(add(pow(y, 2), mul(-1, ra)), pow(rb, -1))]]));
  const terms = termsOf(ay).map((t) => [t, degreeIn(t, y)] as const);
  if (terms.some(([, k]) => k < 0) || Math.max(...terms.map(([, k]) => k)) !== 2) return undefined;
  const coeff = (k: number) => add(...terms.filter(([, kt]) => kt === k).map(([t]) => mul(t, pow(y, -k))));
  const ca = coeff(2);
  const cb = add(coeff(1), b);
  const cc = coeff(0);
  if (!isZero(mexpand(add(pow(cb, 2), mul(-4, ca, cc))))) return undefined;
  const w = add(sqrt(r), mul(cb, pow(mul(2, ca), -1)));
  let z = sqrt(mul(ca, pow(w, 2)));
  if (z.freeSymbols().size === 0) z = mexpand(mul(...asContentPrimitive(sqrtNumericSquare(ca, w) ?? z)));
  return z;
}

/**
 * sqrt(ca*w**2) = sqrt(ca)*|w| for numbers ca > 0 and real w. SymPy's Pow gives this form because
 * it decides the sign of a number by evaluating it; the core assumptions do not evaluate, so the
 * number case is done here. undefined when ca or w is not such a number.
 */
function sqrtNumericSquare(ca: Expr, w: Expr): Expr | undefined {
  const cv = ca.toComplex();
  const wv = w.toComplex();
  if (!(cv.re > 0 && cv.im === 0 && wv.im === 0)) return undefined;
  const s = sqrtOfPositive(ca);
  const sw = mul(s, w);
  return num(sw) < 0 ? mul(-1, sw) : sw;
}

/** sqrt(c) for a number c > 0: the product of sqrt(|f|) over the factors f of c. */
const sqrtOfPositive = (c: Expr): Expr => mul(...factorsOf(c).map(sqrtAbs));

/** sqrt(|f|) for a real number f that is not a product; even powers come out of the root with their sign. */
function sqrtAbs(f: Expr): Expr {
  if (f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.p % 2n === 0n) {
    const h = pow(f.base, Rational.of(f.exp.p / 2n));
    return num(h) < 0 ? mul(-1, h) : h;
  }
  return sqrt(num(f) < 0 ? mul(-1, f) : f);
}

// a positive symbol for the substitution in sqrtSymbolicDenest
import { Sym as Sym_ } from '../core/nodes';
/** The degree of the term in y, or -1 when it is not y**k times a y-free factor. */
const degreeIn = (t: Expr, y: Expr): number => {
  let k = 0;
  for (const f of factorsOf(t)) {
    // (y occurs only as y**(2*j) after the substitution)
    if (f instanceof Pow && f.base.key === y.key) k += Number(expectType(f.exp, (v): v is Rational => v instanceof Rational, 'the exponent of y').p);
    else if (f.has(y)) return -1;
  }
  return k;
};

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
  // (av0[1] is cleared only right before returning, so it is set on entry)
  if (h > maxDepth) return [undefined, undefined];
  if (av0[0] === undefined && nested.every((n) => n.isNumber && n.args.length === 0)) {
    for (const f of subsets(nested.length)) {
      let p = mexpand(mul(...nested.filter((_, i) => f[i])));
      if (f.filter((x) => x === 1).length > 1 && f[f.length - 1]) p = mul(-1, p);
      const sqp = sqrt(p);
      if (sqp instanceof Rational) return [sqp, f];
    }
    return [sqrt(last(nested)), Array<number>(nested.length).fill(0)];
  }
  let R: Expr;
  let values: [Expr, Expr, Expr][];
  let nested2: Expr[];
  if (av0[0] !== undefined) {
    values = [[av0[0], defined(av0[1]), S.Zero]];
    R = defined(av0[2]);
    nested2 = [defined(av0[3]), R];
    av0[0] = undefined;
  } else {
    values = nested.map(sqrtMatch).filter((v): v is [Expr, Expr, Expr] => v !== undefined);
    let found: Expr | undefined;
    for (const v of values) {
      if (!isZero(v[2])) {
        if (found !== undefined) {
          if (found.key !== v[2].key) {
            av0[1] = undefined;
            return [undefined, undefined];
          }
        } else found = v[2];
      }
    }
    // (some value has b != 0: a nested term without a square root is a rational atom, and nested terms
    // that are all atoms take the branch above)
    const r0 = defined(found, 'the common radicand');
    R = r0;
    nested2 = [...values.map((v) => add(mexpand(pow(v[0], 2)), mul(-1, mexpand(mul(r0, pow(v[1], 2)))))), r0];
  }
  const [d, f] = denesterRec(nested2, av0, h + 1, maxDepth);
  if (!f || d === undefined) return [undefined, undefined];
  if (!nested.some((_, i) => f[i])) {
    const v = last(values);
    return [sqrt(add(v[0], mexpand(mul(v[1], d)))), f];
  }
  const p = mul(...nested.filter((_, i) => f[i]));
  // (p is a product of nested algebraic numbers; expanded it is a number, a sum or c*sqrt(n), as SymPy assumes)
  let [v0, v1] = defined(sqrtMatch(p), 'the square root form of the product');
  const firstOne = f.indexOf(1);
  if (firstOne >= 0 && firstOne < nested.length - 1 && f[nested.length - 1]) {
    v0 = mul(-1, v0);
    v1 = mul(-1, v1);
  }
  if (!f[nested.length]) {
    const vad = mexpand(add(v0, d));
    if (num(vad) <= 0) return [sqrt(last(nested)), Array<number>(nested.length).fill(0)];
    // (SymPy first gives up when vad itself is deeper than sqrt(R) and vad**2 is not a number;
    // the check of sqvad below then fails as well unless sqrt(vad) denests, which is a valid result)
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
