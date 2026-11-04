// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Generalized hypergeometric functions (SymPy hyper), Meijer G-functions
 * (meijerg), spherical Bessel functions (jn, yn) and the Kronecker delta.
 */

import { NotImplementedError } from '../core/errors';
import { at, defined, first, pair } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Fn, Mul, Pow, Rational, S, Special } from '../core/nodes';
import { rebuild } from '../core/traverse';
import { isIntegerQ, isNonZero, isPositive, isZero } from '../core/assumptions';
import { compareKeys, sortKey } from '../printing/sortkey';
import { Gt, piecewise } from '../core/logic';
import { add, mul, pow, sympify } from '../core/ops';
import { fnPartials } from '../calculus/diff';
import { cos, evaluators, fn, sin } from './elementary';
import { numericFns } from '../numeric/evalf';
import { c as cx, cmul } from '../numeric/complex';
import { besselj, bessely } from './bessel';
import { registerRewrite } from '../simplify/rewrite';
import { unpolarify } from './polar';
import { derivative } from '../core/undef';
import { mpFns } from '../numeric/mpeval';
import * as F from '../numeric/mpf';
import * as M from '../numeric/mpfun';
import type { Mpc } from '../numeric/mpfun';
import { chyp2f1 } from '../numeric/mporthopoly';

const gcdBig = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcdBig(b, a % b));

const tuple = (print: (e: Expr) => string, xs: readonly Expr[]) => (xs.length === 1 ? `(${print(first(xs))},)` : `(${xs.map(print).join(', ')})`);

/** SymPy hyper(ap, bq, z): args are [z, ...ap, ...bq]. */
export class Hyper extends ExtensionExpr {
  constructor(
    args: readonly Expr[],
    readonly p: number,
  ) {
    super('hyper', args);
  }
  get ap(): Expr[] {
    return this.args.slice(1, 1 + this.p);
  }
  get bq(): Expr[] {
    return this.args.slice(1 + this.p);
  }
  get argument(): Expr {
    return first(this.args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Hyper(args, this.p);
  }
  override printStr(print: (e: Expr) => string): string {
    return `hyper(${tuple(print, this.ap)}, ${tuple(print, this.bq)}, ${print(this.argument)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const col = (xs: Expr[]) => (xs.length ? xs.map(print).join(', ') : '');
    return `{{}_{${this.ap.length}}F_{${this.bq.length}}\\left(\\begin{matrix} ${col(this.ap)} \\\\ ${col(this.bq)} \\end{matrix}\\middle| {${print(this.argument)}} \\right)}`;
  }
  /** d/dz hyper(a, b, z) = prod(a)/prod(b) * hyper(a + 1, b + 1, z). */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if ([...this.ap, ...this.bq].some((e) => e.has(x))) return undefined;
    const dz = d(this.argument, x);
    const c = mul(mul(...this.ap), pow(mul(...this.bq), -1));
    return mul(c, hyper(this.ap.map((a) => add(a, 1)), this.bq.map((b) => add(b, 1)), this.argument), dz);
  }
  /** The value by the power series (|z| < 1 or terminating). */
  override numericValue(dps: number): Expr | undefined {
    const z = this.argument.toComplex();
    if (Math.hypot(z.re, z.im) >= 1) return undefined;
    const as = this.ap.map((a) => a.toNumber());
    const bs = this.bq.map((b) => b.toNumber());
    let term = 1;
    let zp = cx(1);
    let acc = cx(1);
    for (let k = 0; k < 2000; k++) {
      const num = as.reduce((s, a) => s * (a + k), 1);
      const den = bs.reduce((s, b) => s * (b + k), 1) * (k + 1);
      term *= num / den;
      zp = cmul(zp, z);
      acc = { re: acc.re + term * zp.re, im: acc.im + term * zp.im };
      if (Math.abs(term) * Math.hypot(zp.re, zp.im) < 1e-17 * Math.max(1, Math.hypot(acc.re, acc.im))) break;
    }
    void dps;
    return add(acc.re, mul(acc.im, S.I));
  }
}

/** The parameters in SymPy's canonical order (ordered). */
const orderedParams = (xs: readonly Expr[]): Expr[] => [...xs].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));

/**
 * SymPy hyper(ap, bq, z): the parameters are sorted, and those common to ap
 * and bq cancel unless `evaluate` is false. The argument of a function that
 * is not branched at it loses its polar factors (SymPy hyper.eval).
 */
export function hyper(ap: readonly ExprLike[], bq: readonly ExprLike[], zIn: ExprLike, opts: { evaluate?: boolean } = {}): Expr {
  let as = ap.map(sympify);
  let bs = bq.map(sympify);
  if (opts.evaluate !== false) {
    // remove the parameters common to ap and bq (with multiplicity)
    const rest = [...bs];
    as = as.filter((a) => {
      const k = rest.findIndex((b) => b.key === a.key);
      if (k < 0) return true;
      rest.splice(k, 1);
      return false;
    });
    bs = rest;
  }
  const z = sympify(zIn);
  const evaluated = opts.evaluate !== false && (as.length <= bs.length || (as.length === bs.length + 1 && absAtMostOne(z))) ? unpolarify(z) : z;
  // unevaluated like SymPy, also at z = 0 (hyperexpand gives 1 there)
  return new Hyper([evaluated, ...orderedParams(as), ...orderedParams(bs)], as.length);
}

/** (Abs(z) <= 1) == True, decided numerically for a number. */
function absAtMostOne(z: Expr): boolean {
  if (z.freeSymbols().size > 0) return false;
  try {
    const v = z.toComplex();
    return Math.hypot(v.re, v.im) <= 1;
  } catch {
    return false;
  }
}

/** Gauss's theorem 2F1(a, b; c; 1) = gamma(c)*gamma(c - a - b)/(gamma(c - a)*gamma(c - b)) (SymPy hyper._eval_expand_func), else undefined. */
export function gaussAtOne(h: Hyper): Expr | undefined {
  if (!(h.ap.length === 2 && h.bq.length === 1 && h.argument instanceof Rational && h.argument.isOne)) return undefined;
  const [a, b] = pair(h.ap);
  const c = first(h.bq);
  const g = (e: Expr) => fn('gamma', [e]);
  return mul(g(c), g(add(c, mul(-1, a), mul(-1, b))), pow(mul(g(add(c, mul(-1, a))), g(add(c, mul(-1, b)))), -1));
}

/** SymPy meijerg(((a_1..a_n), (a_n+1..a_p)), ((b_1..b_m), (b_m+1..b_q)), z): args are [z, ...an, ...ap, ...bm, ...bq]. */
export class MeijerG extends ExtensionExpr {
  constructor(
    args: readonly Expr[],
    readonly sizes: readonly [number, number, number, number],
  ) {
    super('meijerg', args);
  }
  private part(i: number): Expr[] {
    const start = 1 + this.sizes.slice(0, i).reduce((s, k) => s + k, 0);
    return this.args.slice(start, start + at(this.sizes, i));
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MeijerG(args, this.sizes);
  }
  /** The argument z. */
  get argument(): Expr {
    return first(this.args);
  }
  /** The first n upper parameters (SymPy meijerg.an). */
  get an(): Expr[] {
    return this.part(0);
  }
  /** The other upper parameters (SymPy meijerg.aother). */
  get aother(): Expr[] {
    return this.part(1);
  }
  /** All upper parameters (SymPy meijerg.ap). */
  get ap(): Expr[] {
    return [...this.part(0), ...this.part(1)];
  }
  /** The first m lower parameters (SymPy meijerg.bm). */
  get bm(): Expr[] {
    return this.part(2);
  }
  /** The other lower parameters (SymPy meijerg.bother). */
  get bother(): Expr[] {
    return this.part(3);
  }
  /** All lower parameters (SymPy meijerg.bq). */
  get bq(): Expr[] {
    return [...this.part(2), ...this.part(3)];
  }
  /** SymPy meijerg.nu: sum(bq) - sum(ap). */
  get nu(): Expr {
    return add(...this.bq, ...this.ap.map((a) => mul(-1, a)));
  }
  /** SymPy meijerg.delta: m + n - (p + q)/2. */
  get delta(): Expr {
    const [n, p, m, q] = this.sizes;
    return Rational.of(BigInt(2 * (m + n) - (n + p) - (m + q)), 2n);
  }
  /**
   * SymPy meijerg.get_period: a number P with G(z*exp_polar(I*P)) = G(z), oo
   * when there is none (for parameters that are not rational or differ by
   * integers).
   */
  getPeriod(): Expr {
    const compute = (l: readonly Expr[]): bigint | undefined => {
      let lcm = 1n;
      for (const [i, b] of l.entries()) {
        if (!(b instanceof Rational)) return undefined;
        for (const c of l.slice(i + 1)) {
          const d = add(b, mul(-1, c));
          if (d instanceof Rational && d.isInteger) return undefined;
        }
        const g = gcdBig(lcm, b.q);
        lcm = (lcm / g) * b.q;
      }
      return lcm;
    };
    const beta = compute(this.bm);
    const alpha = compute(this.an);
    const [n, p, m, q] = this.sizes;
    const twoPi = (k: bigint | undefined): Expr => (k === undefined ? S.Infinity : mul(2, S.Pi, Rational.of(k)));
    if (n + p === m + q) return alpha === undefined || beta === undefined ? S.Infinity : twoPi((alpha / gcdBig(alpha, beta)) * beta);
    return n + p < m + q ? twoPi(beta) : twoPi(alpha);
  }
  override printStr(print: (e: Expr) => string): string {
    const t = (xs: Expr[]) => tuple(print, xs);
    return `meijerg((${t(this.part(0))}, ${t(this.part(1))}), (${t(this.part(2))}, ${t(this.part(3))}), ${print(first(this.args))})`;
  }
  protected override computeKey(): string {
    return `meijerg[${this.sizes.join(',')}](${this.args.map((a) => a.key).join(',')})`;
  }
}

/** SymPy meijerg(((an), (ap)), ((bm), (bq)), z). */
export function meijerg(an: readonly ExprLike[], ap: readonly ExprLike[], bm: readonly ExprLike[], bq: readonly ExprLike[], z: ExprLike): Expr {
  const parts = [an, ap, bm, bq].map((xs) => xs.map(sympify));
  const sizes: [number, number, number, number] = [an.length, ap.length, bm.length, bq.length];
  return new MeijerG([sympify(z), ...parts.flat()], sizes);
}

// d/dnu expint(nu, z) (SymPy expint.fdiff(1))
const expintPartials = fnPartials['expint'];
fnPartials['expint'] = (args, i) => {
  if (i === 0) {
    const [nu, z] = pair(args);
    return mul(-1, pow(z, add(nu, -1)), meijerg([], [1, 1], [0, 0, add(1, mul(-1, nu))], [], z));
  }
  return defined(expintPartials, 'expint partial derivatives')(args, i);
};

// catalan(n) = hyper((-n, 1 - n), (2,), 1)
registerRewrite('catalan', 'hyper', (args) => {
  const n = first(args);
  return hyper([mul(-1, n), add(1, mul(-1, n))], [2], 1);
});

// ---- spherical Bessel functions --------------------------------------------------

/** SymPy jn(n, z): spherical Bessel function of the first kind. */
export const jn = (n: ExprLike, z: ExprLike): Expr => fn('jn', [n, z]);
/** SymPy yn(n, z): spherical Bessel function of the second kind. */
export const yn = (n: ExprLike, z: ExprLike): Expr => fn('yn', [n, z]);

/** SymPy jn.eval: the values at 0 and at +-oo. */
evaluators.jn = (n, z) => {
  if (z instanceof Rational && z.isZero) {
    if (n instanceof Rational && n.isZero) return S.One;
    if (isIntegerQ(n) === true) return isPositive(n) === true ? S.Zero : S.ComplexInfinity;
    return undefined;
  }
  if (z instanceof Special && (z.name === 'oo' || z.name === '-oo')) return S.Zero;
  return undefined;
};
evaluators.yn = () => undefined;
// d/dz jn(n, z) = jn(n - 1, z) - (n + 1)/z * jn(n, z) (SymPy fdiff)
for (const name of ['jn', 'yn'] as const) {
  fnPartials[name] = (args, i) => {
    if (i !== 1) throw new NotImplementedError(`diff: ${name} w.r.t. its order`);
    const [n, z] = pair(args);
    return add(fn(name, [add(n, -1), z]), mul(-1, add(n, 1), pow(z, -1), fn(name, [n, z])));
  };
  numericFns[name] = (args) => {
    const [n, zz] = pair(args);
    // sqrt(pi/(2 z)) * J_{n+1/2}(z)
    const v = (name === 'jn' ? besselj : bessely)(n.re + 0.5, add(zz.re, mul(zz.im, S.I))).toComplex();
    const r = Math.sqrt(Math.PI / 2) / Math.sqrt(Math.hypot(zz.re, zz.im));
    const ph = -Math.atan2(zz.im, zz.re) / 2;
    return cmul(v, { re: r * Math.cos(ph), im: r * Math.sin(ph) });
  };
}
registerRewrite('sinc', 'jn', (args) => jn(0, first(args)));

/** jn(n, z) for integer n >= 0 in terms of sin and cos (SymPy expand_func). */
export function expandJn(n: number, z: Expr, kind: 'jn' | 'yn' = 'jn'): Expr {
  // jn: j0 = sin(z)/z, j1 = sin(z)/z**2 - cos(z)/z, j_{k+1} = (2k + 1)/z j_k - j_{k-1}
  let a = kind === 'jn' ? mul(sin(z), pow(z, -1)) : mul(-1, cos(z), pow(z, -1));
  if (n === 0) return a;
  let b = kind === 'jn' ? add(mul(sin(z), pow(z, -2)), mul(-1, cos(z), pow(z, -1))) : add(mul(-1, cos(z), pow(z, -2)), mul(-1, sin(z), pow(z, -1)));
  for (let k = 1; k < n; k++) [a, b] = [b, add(mul(2 * k + 1, pow(z, -1), b), mul(-1, a))];
  return b;
}

// ---- Kronecker delta ---------------------------------------------------------------

/** SymPy KroneckerDelta(i, j): 1 when equal, 0 for distinct numbers, unevaluated otherwise. */
export const KroneckerDelta = (i: ExprLike, j: ExprLike): Expr => fn('KroneckerDelta', [i, j]);
/** Is d a number (no free symbols) whose value is clearly not 0? */
function numericallyNonZero(d: Expr): boolean {
  if (d.freeSymbols().size > 0) return false;
  try {
    const v = d.toComplex();
    return Math.hypot(v.re, v.im) > 1e-10;
  } catch {
    return false;
  }
}

/** SymPy KroneckerDelta.eval: 1 or 0 when i - j is known to be zero or not, else the arguments in canonical order. */
evaluators.KroneckerDelta = (i, j) => {
  if (i.key === j.key) return S.One;
  const d = add(i, mul(-1, j));
  if (isZero(d) === true) return S.One;
  if (isNonZero(d) === true || numericallyNonZero(d)) return S.Zero;
  if (compareKeys(sortKey(j), sortKey(i)) < 0) return new Fn('KroneckerDelta', [j, i]);
  return undefined;
};

/**
 * SymPy kroneckersimp: a product of deltas sharing an index with distinct
 * numbers on the other side vanishes, e.g. KroneckerDelta(0, i)*KroneckerDelta(1, i) = 0.
 */
export function kroneckersimp(eIn: ExprLike): Expr {
  const e = sympify(eIn);
  const go = (x: Expr): Expr => {
    const args = x.args.map(go);
    const y = args.some((a, i) => a !== x.args[i]) ? rebuild(x, args) : x;
    // KroneckerDelta(i, j)**n = KroneckerDelta(i, j) for a positive integer n
    if (y instanceof Pow && y.base instanceof Fn && y.base.name === 'KroneckerDelta' && y.exp instanceof Rational && y.exp.isInteger && y.exp.isPositive) return y.base;
    if (!(y instanceof Mul)) return y;
    const deltas = y.args.filter((f): f is Fn => f instanceof Fn && f.name === 'KroneckerDelta');
    for (const [a, da] of deltas.entries()) {
      for (const db of deltas.slice(a + 1)) {
        const [p, q] = pair(da.args);
        const [r, s] = pair(db.args);
        const orders: [Expr, Expr, Expr, Expr][] = [[p, q, r, s], [p, q, s, r], [q, p, r, s], [q, p, s, r]];
        for (const [u, v, w, t] of orders) {
          if (v.key === t.key && u.freeSymbols().size === 0 && w.freeSymbols().size === 0 && u.key !== w.key) return S.Zero;
        }
      }
    }
    return y;
  };
  return go(e);
}


// rf(x, n) = gamma(x + n)/gamma(x) for x > 0, (-1)**n*gamma(1 - x)/gamma(1 - x - n) otherwise (SymPy)
registerRewrite('RisingFactorial', 'gamma', (args) => {
  const [x, n] = pair(args);
  const pos = mul(fn('gamma', [add(n, x)]), pow(fn('gamma', [x]), -1));
  const neg = mul(pow(-1, n), fn('gamma', [add(1, mul(-1, x))]), pow(fn('gamma', [add(1, mul(-1, x), mul(-1, n))]), -1));
  // a number: decided by its value
  const p = x.freeSymbols().size === 0 ? x.toNumber() > 0 : isPositive(x);
  if (p === true) return pos;
  if (p === false) return neg;
  return piecewise([pos, Gt(x, 0)], [neg, true]);
});

// ---- incomplete beta functions in terms of hyper ------------------------------------

// betainc(a, b, x1, x2) = (x2**a*hyper((a, 1 - b), (a + 1,), x2) - x1**a*hyper((a, 1 - b), (a + 1,), x1))/a
const betaincHyper = (args: readonly Expr[]): Expr => {
  const [a, b, x1, x2] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3)];
  const h = (x: Expr) => mul(pow(x, a), hyper([a, add(1, mul(-1, b))], [add(a, 1)], x));
  return mul(add(h(x2), mul(-1, h(x1))), pow(a, -1));
};
registerRewrite('betainc', 'hyper', betaincHyper);
registerRewrite('betainc_regularized', 'hyper', (args) => mul(betaincHyper(args), pow(fn('beta', [at(args, 0), at(args, 1)]), -1)));

// ---- Appell F1 ---------------------------------------------------------------------------

/** SymPy appellf1(a, b1, b2, c, x, y): the Appell hypergeometric function of two variables F1. */
export const appellf1 = (a: ExprLike, b1: ExprLike, b2: ExprLike, c: ExprLike, x: ExprLike, y: ExprLike): Expr => fn('appellf1', [a, b1, b2, c, x, y]);

/** SymPy appellf1.eval: b1 <= b2 (and x <= y when b1 = b2) in sort-key order; 1 at x = y = 0. */
evaluators.appellf1 = (a, ...rest) => {
  const [b1, b2, c, x, y] = [at(rest, 0), at(rest, 1), at(rest, 2), at(rest, 3), at(rest, 4)];
  const cmp = compareKeys(sortKey(b1), sortKey(b2));
  if (cmp > 0) return fn('appellf1', [a, b2, b1, c, y, x]);
  if (b1.key === b2.key && compareKeys(sortKey(x), sortKey(y)) > 0) return fn('appellf1', [a, b1, b2, c, y, x]);
  if (isZero(x) === true && isZero(y) === true) return S.One;
  return undefined;
};
// d/dx F1 = a*b1/c*F1(a + 1, b1 + 1, b2, c + 1, x, y), d/dy likewise with b2
fnPartials.appellf1 = (args, i) => {
  const [a, b1, b2, c, x, y] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3), at(args, 4), at(args, 5)];
  if (i === 4) return mul(a, b1, pow(c, -1), appellf1(add(a, 1), add(b1, 1), b2, add(c, 1), x, y));
  if (i === 5) return mul(a, b2, pow(c, -1), appellf1(add(a, 1), b1, add(b2, 1), add(c, 1), x, y));
  return derivative(new Fn('appellf1', args), [[at(args, i), 1]]);
};

const mpAbs = (z: Mpc): number => F.toNumber(M.cabs(z, 53));
const mpNpInt = (z: Mpc): boolean => F.isZero(z[1]) && z[0].man <= 0n && F.toRational(z[0])[1] === 1n;
const mpInt = (k: number): Mpc => [F.fromInt(BigInt(k)), F.ZERO];

/**
 * F1(a, b1, b2, c; x, y) = sum_m (a)_m (b1)_m/((c)_m m!) x**m 2F1(a + m, b2; c + m; y)
 * (mpmath appellf1 and hyper2d), after the transformation of mpmath for |x| >= 0.99.
 */
export function mpAppellF1(args: readonly Mpc[], prec: number): Mpc {
  let [a, b1, b2, c, x, y] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3), at(args, 4), at(args, 5)];
  const wp = prec + 30;
  if (mpAbs(x) > mpAbs(y)) [x, y, b1, b2] = [y, x, b2, b1];
  const ok = (z: Mpc) => mpAbs(z) < 0.99;
  if (!mpNpInt(a) && !mpNpInt(b1)) {
    if (mpNpInt(b2)) [x, y, b1, b2] = [y, x, b2, b1];
    else if (!ok(x)) {
      const u1 = M.cdiv(M.csub(x, y, wp), M.csub(x, M.C1, wp), wp);
      if (!ok(u1)) throw new NotImplementedError('appellf1: analytic continuation');
      const f = M.cmul(M.cpow(M.csub(M.C1, x, wp), M.cneg(b1), wp), M.cpow(M.csub(M.C1, y, wp), M.csub(M.csub(c, a, wp), b2, wp), wp), wp);
      const v = mpAppellF1([M.csub(c, a, wp), b1, M.csub(M.csub(c, b1, wp), b2, wp), c, u1, y], wp);
      return M.cmul(f, v, prec);
    }
  }
  let coef: Mpc = M.C1;
  let sum: Mpc = M.C0;
  let small = 0;
  for (let m = 0; m < 100000; m++) {
    const term = M.cmul(coef, chyp2f1(M.cadd(a, mpInt(m), wp), b2, M.cadd(c, mpInt(m), wp), y, wp), wp);
    sum = M.cadd(sum, term, wp);
    const mk = mpInt(m);
    coef = M.cdiv(M.cmul(M.cmul(coef, M.cmul(M.cadd(a, mk, wp), M.cadd(b1, mk, wp), wp), wp), x, wp), M.cmul(M.cadd(c, mk, wp), mpInt(m + 1), wp), wp);
    if (F.isZero(coef[0]) && F.isZero(coef[1])) break;
    const mag = Math.max(F.mag(term[0]), F.mag(term[1]));
    small = mag < Math.max(F.mag(sum[0]), F.mag(sum[1])) - wp ? small + 1 : 0;
    if (small >= 3) break;
  }
  return [F.round(sum[0], prec), F.round(sum[1], prec)];
}
mpFns['appellf1'] = mpAppellF1;
numericFns.appellf1 = (args) => {
  const v = mpAppellF1(args.map((z) => [F.fromNumber(z.re), F.fromNumber(z.im)]), 53);
  return cx(F.toNumber(v[0]), F.toNumber(v[1]));
};
