// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Combinatorial and special functions with SymPy-compatible
 * evaluation rules, derivatives, conjugation and numeric evaluation.
 */

import { NotImplementedError } from '../../core/errors';
import { at, defined, first, pair } from '../../core/guard';
import '../../numeric/mpspecialfns';
import { isIntegerQ, isNegative, isNonNegative, isPositive, isReal, isZero } from '../../core/assumptions';
import type {
  ComplexValue as C,
  Expr,
  ExprLike,
  FnName } from '../../core/nodes';
import {
  Add,
  Constant,
  Dummy,
  ExtensionExpr,
  Float,
  Fn,
  Mul,
  Rational,
  S,
  Special,
  Sym,
  isNum,
} from '../../core/nodes';
import { numAdd, numMul } from '../../core/num';
import { derivative } from '../../core/undef';
import { SubsNode } from '../../core/subsnode';
import { evalMp, MpSpecialValue, mpFns } from '../../numeric/mpeval';
import * as F from '../../numeric/mpf';
import * as M from '../../numeric/mpfun';
import type { Mpc } from '../../numeric/mpfun';
import * as SP from '../../numeric/mpspecial';
import { chyp2f1 } from '../../numeric/mporthopoly';
import { add, couldExtractMinusSign, exp, mul, neg, pow, splitCoeff, sqrt, sympify } from '../../core/ops';
import { fnPartials } from '../../calculus/diff';
import { rebuild } from '../../core/traverse';
import { impl } from '../../core/nodes';
import { c as cx, cadd, cdiv, cexp, clog, cLambertW, cmul, cpow, csin } from '../../numeric/complex';
import { numericFns } from '../../numeric/evalf';
import { compareKeys, sortKey } from '../../printing/sortkey';
import { expandMul } from '../../simplify/expand';
import { conjugateCommutes, cos, cosh, evaluators, fn, forEachEntry, log, re, sin, sinh } from '../elementary/elementary';

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const R = (p: bigint | number, q: bigint | number = 1) => Rational.of(p, q);
/** Exact rational sum and product (numAdd/numMul restricted to Rational). */
const qAdd = (a: Rational, b: Rational): Rational => (a.q === b.q ? Rational.of(a.p + b.p, a.q) : Rational.of(a.p * b.q + b.p * a.q, a.q * b.q));
const qMul = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.p, a.q * b.q);
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
const isSpecial = (e: Expr, name: string) => e instanceof Special && e.name === name;

/**
 * The partial derivative of name(args) in an argument it has no formula for
 * (SymPy Function.fdiff after ArgumentIndexError): Derivative(f, a) for a
 * symbol a, Subs(Derivative(f(.., xi, ..), xi), xi, a) otherwise.
 */
export function noPartial(name: FnName, args: readonly Expr[], i: number): Expr {
  const a = at(args, i);
  if (a instanceof Sym) return derivative(new Fn(name, args), [[a, 1]]);
  const xi = new Dummy(`xi_${i + 1}`);
  return new SubsNode([derivative(new Fn(name, args.map((b, j) => (j === i ? xi : b))), [[xi, 1]]), xi, a]);
}

/** A double-precision value through the arbitrary-precision evaluator of name (53 bits). */
export function mpNumeric(name: string, args: readonly C[]): C {
  const v = defined(mpFns[name], name)(args.map((z) => [F.fromNumber(z.re), F.fromNumber(z.im)]), 53);
  return cx(F.toNumber(v[0]), F.toNumber(v[1]));
}
const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const iOo = () => mul(S.I, S.Infinity);
const isIOo = (e: Expr) => e.key === iOo().key;
const isNegIOo = (e: Expr) => e.key === mul(-1, S.I, S.Infinity).key;

function factorialBig(n: bigint): bigint {
  let r = 1n;
  for (let i = 2n; i <= n; i++) r *= i;
  return r;
}

/** Bernoulli numbers B_n (B_1 = -1/2 convention... SymPy uses +1/2; only even n used here). */
const bernoulliCache: Rational[] = [];
export function bernoulliNumber(n: number): Rational {
  // Akiyama–Tanigawa algorithm (gives B_1 = +1/2)
  if (bernoulliCache[n]) return bernoulliCache[n];
  const a: Rational[] = [];
  for (let m = 0; m <= n; m++) {
    a[m] = R(1, m + 1);
    for (let j = m; j >= 1; j--) {
      a[j - 1] = qMul(R(j), qAdd(at(a, j - 1), qMul(R(-1), at(a, j))));
    }
  }
  const b = first(a);
  bernoulliCache[n] = b;
  return b;
}

const fnN = (name: FnName, ...args: ExprLike[]) => fn(name, args);

// ---------------------------------------------------------------------------
// evaluation rules
// ---------------------------------------------------------------------------

function evalFactorial(n: Expr): Expr | undefined {
  if (isInt(n)) return n.isNegative ? S.ComplexInfinity : R(factorialBig(n.p));
  if (isOo(n)) return S.Infinity;
  return undefined;
}

const FACTORIAL2_DOMAIN = 'argument must be nonnegative integer or negative odd integer';

function evalFactorial2(n: Expr): Expr | undefined {
  // SymPy factorial2.eval: a number that is not a nonnegative or negative odd integer is a ValueError
  if ((isNum(n) && !isInt(n)) || (n instanceof Special && n.name !== 'zoo')) throw new RangeError(FACTORIAL2_DOMAIN);
  if (!isInt(n)) return undefined;
  if (n.p >= 0n) {
    let r = 1n;
    for (let i = n.p; i > 1n; i -= 2n) r *= i;
    return R(r);
  }
  if (n.p % 2n === 0n) throw new RangeError(FACTORIAL2_DOMAIN);
  // negative odd: n!! = (n + 2)!! / (n + 2)
  let v: Rational = S.One;
  for (let k = -1n; k > n.p; k -= 2n) v = qMul(v, R(1n, k));
  return v;
}

function evalBinomial(n: Expr, k: Expr): Expr | undefined {
  // SymPy binomial.eval: binomial(n, n) = 1 and binomial(n, n - 1) = n unless n may be a negative integer
  const d = add(n, neg(k));
  const generic = isNonNegative(n) === true || isIntegerQ(n) === false;
  if (generic && d instanceof Rational && d.isZero) return S.One;
  if (generic && d instanceof Rational && d.isOne) return n;
  if (isInt(k)) {
    if (k.isNegative) return S.Zero;
    if (k.isZero) return S.One;
    if (isInt(n) && !n.isNegative && k.p > n.p) return S.Zero;
    if (n instanceof Rational) {
      // very large k: keep binomial(n, k) unevaluated instead of looping k times, unless
      // n - k is small (n >= k here for an integer n >= 0) or the reflection
      // binomial(n, k) = (-1)**k*binomial(k - n - 1, -n - 1) of a negative integer n is cheap
      if (k.p > 100000n) {
        if (isInt(n) && n.isNegative) {
          const v = evalBinomial(R(k.p - n.p - 1n), R(-n.p - 1n));
          return v === undefined ? undefined : k.p % 2n === 0n ? v : neg(v);
        }
        if (!(isInt(n) && n.p - k.p <= 100000n)) return undefined;
      }
      if (isInt(n) && n.p >= 0n && n.p - k.p < k.p) {
        // binomial(n, k) = binomial(n, n - k)
        return evalBinomial(n, R(n.p - k.p));
      }
      let num: Rational = S.One;
      for (let i = 0n; i < k.p; i++) num = qMul(num, qAdd(n, R(-i)));
      return numMul(num, R(1n, factorialBig(k.p)));
    }
    if (k.isOne) return n;
    return undefined;
  }
  if (isNonNegative(n) === false && isIntegerQ(n) === true) return S.ComplexInfinity;
  if (k.freeSymbols().size === 0 && !(k instanceof Special)) return mul(fnN('gamma', add(n, 1)), pow(mul(fnN('gamma', add(k, 1)), fnN('gamma', add(d, 1))), -1));
  return undefined;
}

function evalFF(x: Expr, k: Expr): Expr | undefined {
  if (isInt(k)) {
    if (k.isZero) return S.One;
    if (k.isPositive) return mul(...Array.from({ length: Number(k.p) }, (_, i) => add(x, -i)));
    return mul(...Array.from({ length: Number(-k.p) }, (_, i) => pow(add(x, i + 1), -1)));
  }
  // SymPy: ff(k, k) = k! for an integer k (both are zoo for a negative integer)
  if (k.key === x.key && isIntegerQ(k) === true) return fnN('factorial', x);
  return undefined;
}

function evalRF(x: Expr, k: Expr): Expr | undefined {
  if (x instanceof Rational && x.isOne) return fn('factorial', [k]);
  if (isInt(k)) {
    if (k.isZero) return S.One;
    if (k.isPositive) return mul(...Array.from({ length: Number(k.p) }, (_, i) => add(x, i)));
    return mul(...Array.from({ length: Number(-k.p) }, (_, i) => pow(add(x, -(i + 1)), -1)));
  }
  return undefined;
}

function evalSubfactorial(n: Expr): Expr | undefined {
  if (!isInt(n) || n.isNegative) return undefined;
  // !n = n * !(n-1) + (-1)^n
  let d = 1n;
  for (let i = 1n; i <= n.p; i++) d = i * d + (i % 2n === 0n ? 1n : -1n);
  return R(n.p === 0n ? 1n : d);
}

function evalZeta(s: Expr): Expr | undefined {
  if (!isInt(s)) return undefined;
  if (s.isOne) return S.ComplexInfinity;
  if (s.isZero) return S.NegHalf;
  const n = Number(s.p);
  if (n > 0 && n % 2 === 0) {
    // zeta(2k) = (-1)^(k+1) B_2k (2 pi)^(2k) / (2 (2k)!)
    const b = bernoulliNumber(n);
    const k = n / 2;
    const c = numMul(numMul(b, R(k % 2 === 1 ? 1 : -1)), R(2n ** BigInt(n), 2n * factorialBig(BigInt(n))));
    return mul(c, pow(S.Pi, n));
  }
  if (n < 0) {
    // zeta(-m) = -B_{m+1}/(m+1)
    const m = -n;
    return numMul(R(-1), numMul(bernoulliNumber(m + 1), R(1, m + 1)));
  }
  return undefined;
}

/** SymPy zeta.eval: zeta(s) and the Hurwitz zeta function zeta(s, a). */
function evalZetaHurwitz(s: Expr, a?: Expr): Expr | undefined {
  if (isSpecial(s, 'nan') || (a !== undefined && isSpecial(a, 'nan'))) return S.NaN;
  if (isOo(s)) return S.One;
  if (a === undefined) return evalZeta(s);
  if (a instanceof Rational && a.isOne) return fnN('zeta', s);
  if (s instanceof Rational && s.isOne) return S.ComplexInfinity;
  if (isOo(a)) return S.Zero;
  if (isInt(s) && !s.isPositive) return mul(fnN('bernoulli', add(1, neg(s)), a), pow(add(s, -1), -1));
  if (isInt(s) && isInt(a) && a.isPositive) return add(fnN('zeta', s), neg(fnN('harmonic', add(a, -1), s)));
  if (isInt(a) && !a.isPositive && (isIntegerQ(s) === false || isPositive(s) === true)) return S.NaN;
  return undefined;
}

/** SymPy harmonic.eval: harmonic(n, m) = sum(k**-m, (k, 1, n)). */
function evalHarmonic(n: Expr, m: Expr = S.One): Expr | undefined {
  if (isZero(n) === true) return S.Zero;
  if (isZero(m) === true) return n;
  if (isOo(n)) {
    if (m instanceof Rational && m.isOne) return S.Infinity;
    if (isInt(m) && m.p > 1n) return fnN('zeta', m);
    if (isNegative(m) === true) return S.NaN;
    if (isPositive(add(m, -1)) === true) return fnN('zeta', m);
    // SymPy: oo for m <= 1
    if (isPositive(add(m, -1)) === false) return S.Infinity;
    return undefined;
  }
  // a nonpositive integer m: the Faulhaber sum (bernoulli(1 - m, n + 1) - bernoulli(1 - m))/(1 - m)
  if (isInt(m) && m.isNegative) {
    const k = add(1, neg(m));
    return mul(add(fnN('bernoulli', k, add(n, 1)), neg(fnN('bernoulli', k))), pow(k, -1));
  }
  if (!isInt(n)) return undefined;
  if (n.isNegative) {
    // SymPy (m not an integer or not nonpositive): a pole of the analytic continuation (zoo for m = 1, nan otherwise)
    if (isIntegerQ(m) === false || isPositive(m) === true || isReal(m) === false) return m instanceof Rational && m.isOne ? S.ComplexInfinity : S.NaN;
    return undefined;
  }
  if (isInt(m)) {
    let s: Rational = S.Zero;
    for (let k = 1n; k <= n.p; k++) s = qAdd(s, R(1n, k ** m.p));
    return s;
  }
  // a symbolic exponent: 1 + 2**(-m) + ... + n**(-m)
  const terms: Expr[] = [];
  for (let k = 1n; k <= n.p; k++) terms.push(pow(R(k), neg(m)));
  return add(...terms);
}

function evalCatalan(n: Expr): Expr | undefined {
  if (isInt(n) && !n.isNegative) {
    const c = factorialBig(2n * n.p) / (factorialBig(n.p) * factorialBig(n.p + 1n));
    return R(c);
  }
  // SymPy catalan.eval: the gamma formula for a negative non-integer, 0 or -1/2 for a negative integer
  if (isIntegerQ(n) === false && isNegative(n) === true) {
    return mul(pow(4, n), fnN('gamma', add(n, S.Half)), pow(mul(sqrt(S.Pi), fnN('gamma', add(n, 2))), -1));
  }
  if (isIntegerQ(n) === true && isNegative(n) === true) {
    if (isNegative(add(n, 1)) === true) return S.Zero;
    if (n instanceof Rational) return S.NegHalf;
  }
  return undefined;
}

/** gamma(n + 1/2) for integer n: sqrt(pi) * (2n)! / (4^n n!) (also negative n). */
function gammaHalf(n: bigint): Expr {
  if (n >= 0n) {
    return mul(R(factorialBig(2n * n), 4n ** n * factorialBig(n)), sqrt(S.Pi));
  }
  const m = -n;
  const sign = m % 2n === 0n ? 1n : -1n;
  return mul(R(sign * 4n ** m * factorialBig(m), factorialBig(2n * m)), sqrt(S.Pi));
}

function evalGamma(x: Expr): Expr | undefined {
  if (isInt(x)) return x.isPositive ? R(factorialBig(x.p - 1n)) : S.ComplexInfinity;
  if (x instanceof Rational && x.q === 2n) return gammaHalf((x.p - 1n) / 2n);
  if (isOo(x)) return S.Infinity;
  return undefined;
}

function evalLoggamma(x: Expr): Expr | undefined {
  if (isInt(x)) {
    if (!x.isPositive) return S.Infinity;
    if (x.p <= 2n) return S.Zero;
    return log(R(factorialBig(x.p - 1n)));
  }
  // positive half-integers only (SymPy loggamma.eval): log(gamma(-5/2)) is not loggamma(-5/2)
  if (x instanceof Rational && x.q === 2n && x.p > 0n) return log(gammaHalf((x.p - 1n) / 2n));
  // half of a positive integer symbol: log(sqrt(pi)*2**(1 - p)*gamma(p)/gamma((p + 1)/2))
  if (x instanceof Mul && x.args.length === 2 && x.args[0] instanceof Rational && x.args[0].p === 1n && x.args[0].q === 2n) {
    const p = at(x.args, 1);
    if (isIntegerQ(p) === true && isPositive(p) === true) {
      return log(mul(sqrt(S.Pi), pow(2, add(1, neg(p))), fnN('gamma', p), pow(fnN('gamma', mul(add(p, 1), S.Half)), -1)));
    }
  }
  if (isOo(x)) return S.Infinity;
  if (isNegOo(x)) return S.ComplexInfinity;
  if (isIntegerQ(x) === true) {
    if (isPositive(x) === true) return log(fnN('gamma', x));
    if (isPositive(x) === false) return S.Infinity;
  }
  return undefined;
}

/** SymPy polygamma.eval. */
function evalPolygamma(n: Expr, x: Expr): Expr | undefined {
  const n0 = n instanceof Rational && n.isZero;
  // polygamma(n, oo) is 0 for n != 0 (SymPy also returns 0 for an n that may be 0; keep that unevaluated)
  if (isOo(x) && (n0 || isPositive(n) === true || isNegative(n) === true)) return n0 ? S.Infinity : S.Zero;
  if (isInt(x) && !x.isPositive) return S.ComplexInfinity;
  if (n instanceof Rational && n.p === -1n && n.q === 1n) return add(fnN('loggamma', x), mul(S.NegHalf, log(mul(2, S.Pi))));
  if (n0 && (isNegOo(x) || isIOo(x) || isNegIOo(x))) return S.Infinity;
  if (!isInt(n) || n.isNegative) return undefined;
  if (n.isZero) {
    if (isInt(x)) {
      const h = defined(evalHarmonic(R(x.p - 1n)), 'harmonic number');
      return add(h, mul(-1, S.EulerGamma));
    }
    if (x instanceof Rational && x.p === 1n && x.q === 2n) return add(mul(-2, log(2)), mul(-1, S.EulerGamma));
    if (x instanceof Rational && x.q <= 6n) return digammaRational(x);
    return undefined;
  }
  if (isInt(x) && x.isPositive) {
    // psi^(n)(m) = (-1)^(n+1) n! (zeta(n+1) - sum_{k<m} 1/k^(n+1))
    const z = evalZeta(R(n.p + 1n)) ?? fnN('zeta', R(n.p + 1n));
    let partial: Rational = S.Zero;
    for (let k = 1n; k < x.p; k++) partial = qAdd(partial, R(1n, k ** (n.p + 1n)));
    const sign = n.p % 2n === 0n ? -1n : 1n;
    return mul(R(sign * factorialBig(n.p)), add(z, mul(-1, partial)));
  }
  if (x instanceof Rational && x.p === 1n && x.q === 2n) {
    // (-1)**(n + 1) n! (2**(n + 1) - 1) zeta(n + 1)
    const sign = n.p % 2n === 0n ? -1n : 1n;
    return mul(R(sign * factorialBig(n.p) * (2n ** (n.p + 1n) - 1n)), evalZeta(R(n.p + 1n)) ?? fnN('zeta', R(n.p + 1n)));
  }
  return undefined;
}

/** digamma(p/q) (a non-integer p/q) by Gauss's theorem (SymPy polygamma._eval_expand_func, J. Choi 2007). */
function digammaRational(z: Rational): Expr {
  // the shift to z0 in (0, 1] by the recurrence digamma(x + 1) = digamma(x) + 1/x
  const terms: Expr[] = [];
  let z0: Rational;
  if (z.isPositive) {
    const n = (z.p - 1n) / z.q; // z0 = z - n in (0, 1]
    z0 = qAdd(z, R(-n));
    for (let k = 0n; k < n; k++) terms.push(pow(numAdd(z0, R(k)), -1));
  } else {
    const n = (z.q - z.p) / z.q; // floor(1 - z)
    z0 = qAdd(z, R(n));
    for (let k = 0n; k < n; k++) terms.push(mul(-1, pow(numAdd(z0, R(-1n - k)), -1)));
  }
  // Gauss's digamma theorem for 0 < p < q
  const p = z0.p;
  const q = Number(z0.q);
  terms.push(mul(-1, S.EulerGamma), mul(-1, S.Pi, fnN('cot', mul(R(p, z0.q), S.Pi)), S.Half), mul(-1, log(R(z0.q))));
  for (let k = 1; k < q; k++) {
    terms.push(mul(cos(mul(R(2n * BigInt(k) * p, z0.q), S.Pi)), log(mul(2, sin(mul(R(k, q), S.Pi))))));
  }
  return add(...terms);
}

/** SymPy LambertW.eval. */
function evalLambertW(x: Expr, k?: Expr): Expr | undefined {
  if (k !== undefined && k instanceof Rational && k.isZero) return fnN('LambertW', x);
  const main = k === undefined || (k instanceof Rational && k.isZero);
  const minusInvE = mul(-1, pow(S.E, -1));
  if (main) {
    if (x instanceof Rational && x.isZero) return S.Zero;
    if (x.key === S.E.key) return S.One;
    if (x.key === minusInvE.key) return S.NegOne;
    if (x.key === mul(-1, log(2), S.Half).key) return mul(-1, log(2));
    if (isOo(x)) return S.Infinity;
    return undefined;
  }
  if (k instanceof Rational && k.p === -1n && k.q === 1n) {
    if (x.key === minusInvE.key) return S.NegOne;
    if (x instanceof Rational && x.isZero) return S.NegativeInfinity;
  }
  return undefined;
}

function sumSeries(x: Expr, s: number): Expr {
  // sum_{k=0}^{s-1} x^k/k!
  const terms: Expr[] = [];
  for (let k = 0; k < s; k++) terms.push(mul(pow(x, k), R(1n, factorialBig(BigInt(k)))));
  return add(...terms);
}

/** SymPy Add(*[f(k) for k in range(lo, hi)]) for small integer bounds. */
function sumRange(lo: number, hi: number, f: (k: number) => Expr): Expr {
  const terms: Expr[] = [];
  for (let k = lo; k < hi; k++) terms.push(f(k));
  return add(...terms);
}

const isHalfInt = (a: Expr): a is Rational => a instanceof Rational && a.q === 2n;

/** SymPy uppergamma.eval (without the branch-factor extraction). */
function evalUppergamma(a: Expr, z: Expr): Expr | undefined {
  if (isOo(z)) return S.Zero;
  if (z instanceof Rational && z.isZero && isPositive(re(a)) === true) return fnN('gamma', a);
  if (a instanceof Rational) {
    if (a.isZero && isPositive(z) === true) return neg(fnN('Ei', neg(z)));
    if (a.isOne) return exp(neg(z));
    if (a.p === 1n && a.q === 2n) return mul(sqrt(S.Pi), fnN('erfc', sqrt(z)));
    if (a.isInteger || isHalfInt(a)) {
      const b = qAdd(a, R(-1));
      if (b.isPositive) {
        if (a.isInteger) return mul(exp(neg(z)), R(factorialBig(b.p)), sumSeries(z, Number(a.p)));
        // gamma(a) erfc(sqrt(z)) + (-1)**(a - 3/2) e^-z sqrt(z) sum_k gamma(-1/2 - k) (-z)**k / gamma(1 - a)
        const kmax = Number((a.p - 1n) / 2n);
        return add(
          mul(fnN('gamma', a), fnN('erfc', sqrt(z))),
          mul(
            pow(-1, qAdd(a, R(-3, 2))),
            exp(neg(z)),
            sqrt(z),
            sumRange(0, kmax, (k) => mul(fnN('gamma', R(-1 - 2 * k, 2)), pow(neg(z), k), pow(fnN('gamma', qAdd(S.One, qMul(R(-1), a))), -1))),
          ),
        );
      }
      if (b.isInteger) return mul(fnN('expint', neg(b), z), pow(z, qAdd(b, S.One)));
      // (-1)**(1/2 - a) pi erfc(sqrt(z)) / gamma(1 - a) - z**a e^-z sum_k z**k gamma(a) / gamma(a + k + 1)
      const kmax = Number((1n - a.p) / 2n);
      return add(
        mul(pow(-1, qAdd(S.Half, qMul(R(-1), a))), S.Pi, fnN('erfc', sqrt(z)), pow(fnN('gamma', qAdd(S.One, qMul(R(-1), a))), -1)),
        mul(-1, pow(z, a), exp(neg(z)), sumRange(0, kmax, (k) => mul(pow(z, k), fnN('gamma', a), pow(fnN('gamma', qAdd(a, R(k + 1))), -1)))),
      );
    }
  }
  return undefined;
}

/** SymPy lowergamma.eval (without the branch-factor extraction). */
function evalLowergamma(a: Expr, x: Expr): Expr | undefined {
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (a instanceof Rational) {
    if (a.isOne) return add(1, neg(exp(neg(x))));
    if (a.p === 1n && a.q === 2n) return mul(sqrt(S.Pi), fnN('erf', sqrt(x)));
    if (a.isInteger || isHalfInt(a)) {
      const b = qAdd(a, R(-1));
      if (b.isPositive) {
        if (a.isInteger) {
          const f = R(factorialBig(b.p));
          return add(f, mul(-1, exp(neg(x)), f, sumSeries(x, Number(a.p))));
        }
        // gamma(a) (lowergamma(1/2, x)/sqrt(pi) - e^-x sum_k x**(k - 1/2) / gamma(1/2 + k))
        const kmax = Number((a.p + 1n) / 2n);
        return mul(
          fnN('gamma', a),
          add(
            mul(fnN('lowergamma', S.Half, x), pow(sqrt(S.Pi), -1)),
            mul(-1, exp(neg(x)), sumRange(1, kmax, (k) => mul(pow(x, R(2 * k - 1, 2)), pow(fnN('gamma', R(2 * k + 1, 2)), -1)))),
          ),
        );
      }
      if (!a.isInteger) {
        // (-1)**(1/2 - a) pi erf(sqrt(x)) / gamma(1 - a) + e^-x sum_k x**(k + a - 1) gamma(a) / gamma(a + k)
        const kmax = Number((3n - a.p) / 2n);
        return add(
          mul(pow(-1, qAdd(S.Half, qMul(R(-1), a))), S.Pi, fnN('erf', sqrt(x)), pow(fnN('gamma', qAdd(S.One, qMul(R(-1), a))), -1)),
          mul(exp(neg(x)), sumRange(1, kmax, (k) => mul(pow(x, qAdd(a, R(k - 1))), fnN('gamma', a), pow(fnN('gamma', qAdd(a, R(k))), -1)))),
        );
      }
    }
  }
  return undefined;
}

/** Odd function helper: f(-z) = -f(z). */
const odd = (name: FnName, z: Expr): Expr | undefined =>
  couldExtractMinusSign(z) ? neg(fnN(name, neg(z))) : undefined;

/** Split z = I*w; returns w or undefined. */
function imagFactor(z: Expr): Expr | undefined {
  const [c, rest] = splitCoeff(z);
  if (rest instanceof Constant && rest.name === 'I') return c;
  if (rest instanceof Mul && rest.args.some((a) => a instanceof Constant && a.name === 'I')) {
    return mul(c, ...rest.args.filter((a) => !(a instanceof Constant && a.name === 'I')));
  }
  return undefined;
}

function evalErf(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.Zero;
  if (isOo(z)) return S.One;
  if (isNegOo(z)) return S.NegOne;
  if (isIOo(z)) return iOo();
  if (isNegIOo(z)) return neg(iOo());
  if (z instanceof Fn && z.name === 'erfinv') return z.args[0];
  return odd('erf', z);
}

function evalErfc(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.One;
  if (isOo(z)) return S.Zero;
  if (isNegOo(z)) return S.Two;
  if (isIOo(z)) return neg(iOo());
  if (isNegIOo(z)) return iOo();
  if (z instanceof Fn && z.name === 'erfcinv') return z.args[0];
  if (couldExtractMinusSign(z)) return add(2, neg(fnN('erfc', neg(z))));
  return undefined;
}

function evalErfi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.Zero;
  if (isOo(z)) return S.Infinity;
  if (isNegOo(z)) return S.NegativeInfinity;
  if (isIOo(z)) return S.I;
  if (isNegIOo(z)) return neg(S.I);
  return odd('erfi', z);
}

function evalErfinv(z: Expr): Expr | undefined {
  if (z instanceof Rational) {
    if (z.isZero) return S.Zero;
    if (z.isOne) return S.Infinity;
    if (z.p === -1n && z.q === 1n) return S.NegativeInfinity;
  }
  // erfinv(erf(x)) = x and erfinv(-erf(x)) = -x for real x (SymPy erfinv.eval)
  if (z instanceof Fn && z.name === 'erf' && isReal(first(z.args)) === true) return first(z.args);
  const nz = neg(z);
  if (nz instanceof Fn && nz.name === 'erf' && isReal(first(nz.args)) === true) return neg(first(nz.args));
  return undefined;
}

function evalErfcinv(z: Expr): Expr | undefined {
  if (z instanceof Rational) {
    if (z.isOne) return S.Zero;
    if (z.isZero) return S.Infinity;
    if (z.p === 2n && z.q === 1n) return S.NegativeInfinity;
  }
  return undefined;
}

function evalErf2(x: Expr, y: Expr): Expr | undefined {
  if (x.key === y.key) return S.Zero;
  if (x instanceof Rational && x.isZero) return fnN('erf', y);
  if (y instanceof Rational && y.isZero) return neg(fnN('erf', x));
  if (isOo(x)) return add(fnN('erf', y), -1);
  if (isNegOo(x)) return add(fnN('erf', y), 1);
  if (isOo(y)) return add(1, neg(fnN('erf', x)));
  if (isNegOo(y)) return add(neg(fnN('erf', x)), -1);
  if (couldExtractMinusSign(x) && couldExtractMinusSign(y)) return neg(fnN('erf2', neg(x), neg(y)));
  return undefined;
}

function evalErf2inv(x: Expr, y: Expr): Expr | undefined {
  // SymPy erf2inv.eval (is_zero holds for 0.0 too)
  if (isSpecial(x, 'nan') || isSpecial(y, 'nan')) return S.NaN;
  const x0 = isZero(x) === true;
  const y0 = isZero(y) === true;
  if (x0 && y0) return S.Zero;
  if (x0 && y instanceof Rational && y.isOne) return S.Infinity;
  if (x instanceof Rational && x.isOne && y0) return S.One;
  if (x0) return fnN('erfinv', y);
  if (isOo(x)) return fnN('erfcinv', neg(y));
  if (y0) return x;
  if (isOo(y)) return fnN('erfinv', x);
  return undefined;
}

function evalEi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.NegativeInfinity;
  if (isOo(z)) return S.Infinity;
  if (isNegOo(z)) return S.Zero;
  return undefined;
}

function evalLi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.Zero;
  if (z instanceof Rational && z.isOne) return S.NegativeInfinity;
  if (isOo(z)) return S.Infinity;
  return undefined;
}

function evalLiOffset(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.p === 2n && z.q === 1n) return S.Zero;
  return undefined;
}

function evalSi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.Zero;
  if (isOo(z)) return mul(S.Half, S.Pi);
  if (isNegOo(z)) return mul(S.NegHalf, S.Pi);
  const w = imagFactor(z);
  if (w !== undefined) return mul(S.I, fnN('Shi', w));
  return odd('Si', z);
}

function evalShi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.Zero;
  if (isOo(z)) return S.Infinity;
  if (isNegOo(z)) return S.NegativeInfinity;
  const w = imagFactor(z);
  if (w !== undefined) return mul(S.I, fnN('Si', w));
  return odd('Shi', z);
}

/** SymPy Ci.eval: the values at 0 (a logarithmic branch point) and at +-oo. */
function evalCi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.ComplexInfinity;
  if (isOo(z)) return S.Zero;
  if (isNegOo(z)) return mul(S.I, S.Pi);
  return undefined;
}

function evalChi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.ComplexInfinity;
  if (isOo(z) || isNegOo(z)) return S.Infinity;
  return undefined;
}

/** SymPy expint.eval: E_nu(z) = z**(nu - 1) uppergamma(1 - nu, z) for an integer nu <= 0 or a half-integer nu. */
function evalExpint(nu: Expr, z: Expr): Expr | undefined {
  if (nu instanceof Rational && ((nu.isInteger && !nu.isPositive) || nu.q === 2n)) {
    return expandMul(mul(pow(z, add(nu, -1)), fnN('uppergamma', add(1, neg(nu)), z)));
  }
  return undefined;
}

function evalFresnel(name: 'fresnels' | 'fresnelc', z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.Zero;
  if (isOo(z)) return S.Half;
  if (isNegOo(z)) return S.NegHalf;
  if (isIOo(z)) return name === 'fresnels' ? mul(S.NegHalf, S.I) : mul(S.Half, S.I);
  if (isNegIOo(z)) return name === 'fresnels' ? mul(S.Half, S.I) : mul(S.NegHalf, S.I);
  const w = imagFactor(z);
  if (w !== undefined) {
    // fresnels(I z) = -I fresnels(z), fresnelc(I z) = I fresnelc(z)
    if (!couldExtractMinusSign(w)) return mul(name === 'fresnels' ? neg(S.I) : S.I, fnN(name, w));
  }
  return odd(name, z);
}

function evalSign(x: Expr): Expr | undefined {
  if (isNum(x)) return x.isZero ? S.Zero : x.isPositive ? S.One : S.NegOne;
  if (isPositive(x) === true) return S.One;
  if (isNegative(x) === true) return S.NegOne;
  if (x instanceof Constant && x.name === 'I') return S.I;
  if (x instanceof Mul) {
    const [c, r] = splitCoeff(x);
    if (!(c instanceof Rational && c.isOne)) return mul(defined(evalSign(c), 'sign of the coefficient'), fnN('sign', r));
  }
  return undefined;
}

function numericComplex(x: Expr): C | undefined {
  if (x.freeSymbols().size > 0) return undefined;
  try {
    return x.toComplex();
  } catch {
    return undefined;
  }
}

function numericReal(x: Expr): number | undefined {
  const v = numericComplex(x);
  return v !== undefined && Math.abs(v.im) < 1e-300 ? v.re : undefined;
}

function evalFloorCeil(name: 'floor' | 'ceiling', x: Expr): Expr | undefined {
  // an imaginary argument I*w gives I*floor(w) when floor(w) evaluates
  const w = imagFactor(x);
  const wv = w === undefined || isReal(w) !== true ? undefined : evalFloorCeil(name, w);
  if (wv !== undefined) return mul(S.I, wv);
  if (x instanceof Add && x.args.length === 2 && x.args[0] instanceof Rational) {
    const iw = imagFactor(at(x.args, 1));
    const iv = iw === undefined ? undefined : evalFloorCeil(name, iw);
    if (iv !== undefined) return add(defined(evalFloorCeil(name, x.args[0])), mul(S.I, iv));
  }
  if (x instanceof Rational) {
    const f = x.p / x.q - (x.p % x.q !== 0n && x.p < 0n ? 1n : 0n);
    if (name === 'floor' || x.isInteger) return R(f);
    return R(f + 1n);
  }
  if (x instanceof Special) return x;
  // SymPy Float.floor / Float.ceiling: the exact integer of the binary value
  if (x instanceof Float) return R(name === 'floor' ? F.floor(x.mpf) : -F.floor(F.neg(x.mpf)));
  if (isIntegerQ(x) === true) return x;
  if (x instanceof Add) {
    // SymPy floor/ceiling.eval: integer terms and imaginary terms with an integer imaginary part
    // (an integer-valued Float counts as its integer) come out
    const ints = x.args.map(intTerm);
    if (ints.some((t) => t !== undefined) && ints.some((t) => t === undefined)) {
      return add(...ints.filter((t) => t !== undefined), fnN(name, add(...x.args.filter((_, k) => ints[k] === undefined))));
    }
  }
  return x.freeSymbols().size === 0 ? integerPart(x, name) : undefined;
}

/** An integer-valued Float as its Integer. */
const intValued = (a: Expr): Expr | undefined =>
  isIntegerQ(a) === true ? a : a instanceof Float && F.sub(a.mpf, F.fromInt(F.floor(a.mpf))).man === 0n ? R(F.floor(a.mpf)) : undefined;

/** A term with an integer value, or I times an integer (SymPy RoundFunction.eval intof), else undefined. */
function intTerm(a: Expr): Expr | undefined {
  const i = intValued(a);
  if (i !== undefined) return i;
  if (isReal(a) !== false) return undefined;
  const w = intValued(mul(-1, S.I, a));
  return w === undefined ? undefined : mul(S.I, w);
}

/** The largest magnitude (in bits) of a number whose integer part is computed. */
const INTEGER_PART_MAX_BITS = 100000;

/**
 * The floor or ceiling of the real and imaginary parts of a number without
 * free symbols, or undefined when it cannot be evaluated (SymPy
 * get_integer_part): evaluated with enough bits for the integer part plus a
 * margin, the margin doubling until two successive evaluations agree and the
 * distance of each part to its nearest integer is resolved. A part that stays
 * within the error of an integer n up to the largest margin is n when x - n
 * is zero (SymPy equals(0): floor(sin(1)**2 + cos(1)**2) = 1), else it is
 * left unevaluated.
 */
function integerPart(x: Expr, name: 'floor' | 'ceiling'): Expr | undefined {
  try {
    const v0 = evalMp(x, 30);
    const size = Math.max(F.mag(v0[0]), F.mag(v0[1]), 0);
    if (size > INTEGER_PART_MAX_BITS) return undefined;
    let prev = v0;
    for (let margin = 32; margin <= 1024; margin *= 2) {
      const wp = size + margin;
      const v = evalMp(x, wp);
      // an imaginary part that is exactly zero (real arithmetic) is 0; a real part that cancels to an
      // integer is decided after the loop
      const re = partOf(v[0], prev[0], wp, name);
      const im = F.isZero(v[1]) && F.isZero(prev[1]) ? 0n : partOf(v[1], prev[1], wp, name);
      if (re !== undefined && im !== undefined) return add(R(re), mul(S.I, R(im)));
      prev = v;
    }
    // SymPy: a real part within the error of an integer n is n when (x - n).equals(0)
    if (!F.isZero(prev[1])) return undefined;
    const n = R(F.floor(F.add(prev[0], { man: 1n, exp: -1n })));
    return impl.equalsZero?.(add(x, neg(n))) ? n : undefined;
  } catch (err) {
    // SymPy RoundFunction.eval: an infinite argument is its own floor and ceiling
    // (else a function without an arbitrary-precision evaluation)
    return err instanceof MpSpecialValue ? x : undefined;
  }
}

/**
 * floor/ceiling of one part p evaluated at wp bits, or undefined when it is within the error of an
 * integer: the error is estimated by the change from the value q at the previous precision (a sum
 * that cancels loses bits that the magnitude of p does not show).
 */
function partOf(p: F.Mpf, q: F.Mpf, wp: number, name: 'floor' | 'ceiling'): bigint | undefined {
  const n = F.floor(F.add(p, { man: 1n, exp: -1n }));
  const r = F.sub(p, F.fromInt(n));
  const err = Math.max(F.mag(F.sub(p, q)) + 4, F.mag(p) - wp + 8);
  if (F.isZero(r) || F.mag(r) < err) return undefined;
  return name === 'floor' ? (F.sign(r) < 0 ? n - 1n : n) : F.sign(r) > 0 ? n + 1n : n;
}

function evalAtan2(y: Expr, x: Expr): Expr | undefined {
  const yv = numericReal(y);
  const xv = numericReal(x);
  // a zero Float counts as zero (SymPy atan2(1, 0.0) = pi/2)
  const isZeroNum = (e: Expr): boolean => isNum(e) && e.isZero;
  if (isZeroNum(y)) {
    if (isPositive(x) === true) return S.Zero;
    if (isNegative(x) === true) return S.Pi;
  }
  if (isZeroNum(x)) {
    if (isPositive(y) === true) return mul(S.Half, S.Pi);
    if (isNegative(y) === true) return mul(S.NegHalf, S.Pi);
  }
  if (yv !== undefined && xv !== undefined) {
    const at = fnN('atan', mul(y, pow(x, -1)));
    if (xv > 0) return at;
    if (xv < 0) return yv >= 0 ? add(at, S.Pi) : add(at, neg(S.Pi));
  }
  if (isPositive(x) === true && isReal(y) === true) return fnN('atan', mul(y, pow(x, -1)));
  return undefined;
}

/** Is a > b known? (numerically or from assumptions) */
function greater(a: Expr, b: Expr): boolean | undefined {
  if (a instanceof Special && a.name === 'oo') return b instanceof Special && b.name === 'oo' ? false : true;
  if (b instanceof Special && b.name === '-oo') return true;
  if (b instanceof Special && b.name === 'oo') return false;
  const d = add(a, neg(b));
  if (isPositive(d) === true) return true;
  if (isNegative(d) === true || (d instanceof Rational && d.isZero)) return false;
  return undefined;
}

function evalMinMax(name: 'Min' | 'Max', ...args: Expr[]): Expr | undefined {
  const flat0: Expr[] = [];
  for (const a of args) {
    if (a instanceof Fn && a.name === name) flat0.push(...a.args);
    else flat0.push(a);
  }
  // drop arguments dominated by another argument
  const flat = flat0.filter(
    (a, i) =>
      !flat0.some((b, j) => j !== i && (name === 'Max' ? greater(b, a) === true : greater(a, b) === true) && b.key !== a.key),
  );
  if (flat.length === 1) return flat[0];
  const nums = flat.filter((a) => numericReal(a) !== undefined);
  const syms = flat.filter((a) => numericReal(a) === undefined);
  let best: Expr | undefined;
  let bv = 0;
  for (const n of nums) {
    const nv = defined(numericReal(n), 'numeric value');
    if (best === undefined || (name === 'Min' ? nv < bv : nv > bv)) {
      best = n;
      bv = nv;
    }
  }
  // SymPy keeps the arguments of Min/Max in sort_key order
  const rest = collapseMinMax(name, [...(best ? [best] : []), ...uniq(syms)]).sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
  if (rest.length === 1) return rest[0];
  if (rest.length === flat.length && flat.length === args.length && rest.every((r, i) => r === args[i])) return undefined;
  return new Fn(name, rest);
}

const uniq = (xs: Expr[]) => [...new Map(xs.map((x) => [x.key, x])).values()];

/**
 * SymPy MinMaxBase._collapse_arguments (the part that removes an argument
 * from nested Min/Max): in Min(a, Max(b, Min(a, c))) the inner a is dropped,
 * and in Min(a, Max(b, Min(c, Max(a, e)))) the inner Max(a, e) becomes a.
 */
function collapseMinMax(name: 'Min' | 'Max', argsIn: Expr[]): Expr[] {
  const isMM = (e: Expr): e is Fn => e instanceof Fn && (e.name === 'Min' || e.name === 'Max');
  if (!argsIn.some(isMM)) return argsIn;
  const args = [...argsIn];
  const build = (n: FnName, xs: Expr[]): Expr =>
    xs.length === 1 ? first(xs) : new Fn(n, [...xs].sort((u, v) => compareKeys(sortKey(u), sortKey(v))));
  const doIt = (ai: Expr, a: Expr): Expr => {
    if (!isMM(ai)) return ai;
    if (!ai.args.some((t) => t.key === a.key)) return build(ai.name, ai.args.map((t) => doIt(t, a)));
    if (ai.name === name) return build(ai.name, ai.args.filter((t) => t.key !== a.key).map((t) => doIt(t, a)));
    return a;
  };
  for (let i = 0; i < args.length; i++) {
    const ai = at(args, i);
    for (let j = i + 1; j < args.length; j++) args[j] = doIt(at(args, j), ai);
  }
  return args;
}

// ---------------------------------------------------------------------------
// numerics (double precision)
// ---------------------------------------------------------------------------

const LANCZOS = [
  0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
  12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7,
] as const;

export function cgamma(z: C): C {
  if (z.re < 0.5) {
    // reflection: gamma(z) gamma(1 - z) = pi / sin(pi z)
    const s = csin(cmul(cx(Math.PI), z));
    return cdiv(cx(Math.PI), cmul(s, cgamma(cadd(cx(1), cmul(cx(-1), z)))));
  }
  const zz = cadd(z, cx(-1));
  const [l0, ...ls] = LANCZOS;
  let a = cx(l0);
  const t = cadd(zz, cx(7.5));
  for (const [j, l] of ls.entries()) a = cadd(a, cdiv(cx(l), cadd(zz, cx(j + 1))));
  const r = cmul(cmul(cx(Math.sqrt(2 * Math.PI)), cpow(t, cadd(zz, cx(0.5)))), cmul(cexp(cmul(cx(-1), t)), a));
  return r;
}

/**
 * loggamma(z), the analytic continuation of log(gamma(z)) to the plane cut
 * along the negative real axis (mpmath loggamma): not the principal log of
 * gamma(z). The recurrence loggamma(z) = loggamma(z + 1) - log(z) with
 * principal logs shifts to Re(w) >= 8, where Stirling's series is used.
 */
export function cloggamma(z: C): C {
  if (z.im === 0 && z.re > 0) return cx(Math.log(Math.abs(cgamma(z).re)));
  let acc = cx(0);
  let w = z;
  while (w.re < 8) {
    acc = cadd(acc, clog(w));
    w = cadd(w, cx(1));
  }
  const inv = cdiv(cx(1), w);
  const inv2 = cmul(inv, inv);
  // (w - 1/2) log w - w + log(2 pi)/2 + sum B_2k / (2k (2k - 1) w**(2k - 1))
  let s = cadd(cadd(cmul(cadd(w, cx(-0.5)), clog(w)), cmul(cx(-1), w)), cx(0.5 * Math.log(2 * Math.PI)));
  let p = inv;
  for (const k of [1 / 12, -1 / 360, 1 / 1260, -1 / 1680, 1 / 1188, -691 / 360360, 1 / 156]) {
    s = cadd(s, cmul(cx(k), p));
    p = cmul(p, inv2);
  }
  return cadd(s, cmul(cx(-1), acc));
}

/** digamma via recurrence and asymptotic series. */
function cdigamma(z: C): C {
  let acc = cx(0);
  let w = z;
  while (w.re < 8) {
    acc = cadd(acc, cmul(cx(-1), cdiv(cx(1), w)));
    w = cadd(w, cx(1));
  }
  const inv = cdiv(cx(1), w);
  const inv2 = cmul(inv, inv);
  // log w - 1/(2w) - sum B_2k/(2k w^2k)
  let s = cadd(clog(w), cmul(cx(-0.5), inv));
  const coeffs = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760, 1 / 12];
  let p = inv2;
  for (const k of coeffs) {
    s = cadd(s, cmul(cx(-k), p));
    p = cmul(p, inv2);
  }
  return cadd(s, acc);
}

/** polygamma(n, z) for n >= 1 via recurrence and asymptotic series. */
function cpolygamma(n: number, z: C): C {
  if (n === 0) return cdigamma(z);
  const sign = n % 2 === 1 ? 1 : -1;
  let fact = 1;
  for (let i = 2; i <= n; i++) fact *= i;
  let acc = cx(0);
  let w = z;
  while (w.re < 15) {
    acc = cadd(acc, cdiv(cx(sign * fact), cpow(w, cx(n + 1))));
    w = cadd(w, cx(1));
  }
  // asymptotic: (-1)^(n+1) [ (n-1)!/w^n + n!/(2 w^(n+1)) + sum B_2k (2k+n-1)!/((2k)! w^(2k+n)) ]
  let fnm1 = 1;
  for (let i = 2; i <= n - 1; i++) fnm1 *= i;
  let s = cadd(cdiv(cx(fnm1), cpow(w, cx(n))), cdiv(cx(fact / 2), cpow(w, cx(n + 1))));
  const B = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6];
  for (const [k0, b] of B.entries()) {
    const k = k0 + 1;
    let num = 1;
    for (let i = 2; i <= 2 * k + n - 1; i++) num *= i;
    let den = 1;
    for (let i = 2; i <= 2 * k; i++) den *= i;
    s = cadd(s, cdiv(cx((b * num) / den), cpow(w, cx(2 * k + n))));
  }
  return cadd(cmul(cx(sign), s), acc);
}

function erfReal(x: number): number {
  const ax = Math.abs(x);
  if (ax < 2.5) {
    // Taylor series
    let sum = 0;
    let term = x;
    for (let n = 0; n < 200; n++) {
      const t = term / (2 * n + 1);
      sum += t;
      if (Math.abs(t) < 1e-17 * Math.abs(sum)) break;
      term *= (-x * x) / (n + 1);
    }
    return (2 / Math.sqrt(Math.PI)) * sum;
  }
  const r = 1 - erfcPos(ax);
  return x < 0 ? -r : r;
}

/** erfc(x) for x > 0 by continued fraction (Lentz). */
function erfcPos(x: number): number {
  if (x < 2.5) return 1 - erfReal(x);
  // every partial numerator a and x are positive, so D and Cc stay positive (no zero guard needed)
  let f = x;
  let Cc = x;
  let D = 0;
  for (let n = 1; n < 500; n++) {
    const a = n / 2;
    D = x + a * D;
    Cc = x + a / Cc;
    D = 1 / D;
    const delta = Cc * D;
    f *= delta;
    if (Math.abs(delta - 1) < 1e-16) break;
  }
  return Math.exp(-x * x) / (f * Math.sqrt(Math.PI));
}

function cerf(z: C): C {
  if (z.im === 0) return cx(erfReal(z.re));
  // Taylor series for moderate |z|
  let sum = cx(0);
  let term = z;
  const z2 = cmul(cx(-1), cmul(z, z));
  for (let n = 0; n < 400; n++) {
    const t = cdiv(term, cx(2 * n + 1));
    sum = cadd(sum, t);
    if (Math.hypot(t.re, t.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
    term = cdiv(cmul(term, z2), cx(n + 1));
  }
  return cmul(cx(2 / Math.sqrt(Math.PI)), sum);
}

function cerfc(z: C): C {
  if (z.im === 0) return cx(z.re >= 0 ? erfcPos(z.re) : 2 - erfcPos(-z.re));
  return cadd(cx(1), cmul(cx(-1), cerf(z)));
}

function cerfi(z: C): C {
  // erfi(z) = -i erf(i z)
  return cmul(cx(0, -1), cerf(cmul(cx(0, 1), z)));
}

function erfinvReal(y: number): number {
  if (y <= -1) return -Infinity;
  if (y >= 1) return Infinity;
  // initial guess then Newton
  const a = 0.147;
  const ln = Math.log(1 - y * y);
  const t = 2 / (Math.PI * a) + ln / 2;
  let x = Math.sign(y) * Math.sqrt(Math.sqrt(t * t - ln / a) - t);
  for (let i = 0; i < 8; i++) {
    const err = erfReal(x) - y;
    x -= err / ((2 / Math.sqrt(Math.PI)) * Math.exp(-x * x));
  }
  return x;
}

const EULER_GAMMA = 0.5772156649015329;

/** Ei(z) = gamma + log z + sum z^k/(k k!) */
function cEi(z: C): C {
  let sum = cx(0);
  let term = cx(1);
  for (let k = 1; k < 500; k++) {
    term = cdiv(cmul(term, z), cx(k));
    const t = cdiv(term, cx(k));
    sum = cadd(sum, t);
    if (Math.hypot(t.re, t.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
  }
  const l = z.im === 0 && z.re < 0 ? cx(Math.log(-z.re)) : clog(z);
  return cadd(cadd(cx(EULER_GAMMA), l), sum);
}

/** E1(z) = -gamma - log z - sum (-z)^k/(k k!) */
function cE1(z: C): C {
  let sum = cx(0);
  let term = cx(1);
  const mz = cmul(cx(-1), z);
  for (let k = 1; k < 500; k++) {
    term = cdiv(cmul(term, mz), cx(k));
    const t = cdiv(term, cx(k));
    sum = cadd(sum, t);
    if (Math.hypot(t.re, t.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
  }
  return cmul(cx(-1), cadd(cadd(cx(EULER_GAMMA), clog(z)), sum));
}

function cExpint(n: number, z: C): C {
  if (n === 0) return cdiv(cexp(cmul(cx(-1), z)), z);
  let e = cE1(z);
  for (let k = 1; k < n; k++) e = cdiv(cadd(cexp(cmul(cx(-1), z)), cmul(cx(-1), cmul(z, e))), cx(k));
  return e;
}

/** Si, Ci, Shi, Chi by power series. */
function cSiCi(kind: 'Si' | 'Ci' | 'Shi' | 'Chi', z: C): C {
  const hyper = kind === 'Shi' || kind === 'Chi';
  const sgn = hyper ? 1 : -1;
  const z2 = cmul(z, z);
  let sum = cx(0);
  if (kind === 'Si' || kind === 'Shi') {
    let term = z; // z^(2k+1)/(2k+1)!
    for (let k = 0; k < 300; k++) {
      const t = cdiv(term, cx(2 * k + 1));
      sum = cadd(sum, t);
      if (Math.hypot(t.re, t.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
      term = cdiv(cmul(cmul(term, z2), cx(sgn)), cx((2 * k + 2) * (2 * k + 3)));
    }
    return sum;
  }
  let term = cdiv(cmul(z2, cx(sgn)), cx(2)); // z^(2k)/(2k)! for k = 1
  for (let k = 1; k < 300; k++) {
    const t = cdiv(term, cx(2 * k));
    sum = cadd(sum, t);
    if (Math.hypot(t.re, t.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
    term = cdiv(cmul(cmul(term, z2), cx(sgn)), cx((2 * k + 1) * (2 * k + 2)));
  }
  return cadd(cadd(cx(EULER_GAMMA), clog(z)), sum);
}

function cFresnel(kind: 'S' | 'C', z: C): C {
  const a = Math.PI / 2;
  let sum = cx(0);
  const z4 = cmul(cmul(z, z), cmul(z, z));
  let term = kind === 'S' ? cmul(cx(a), cmul(z, cmul(z, z))) : z; // (a^(2n+1) z^(4n+3))/(2n+1)! or a^(2n) z^(4n+1)/(2n)!
  for (let n = 0; n < 300; n++) {
    const d = kind === 'S' ? 4 * n + 3 : 4 * n + 1;
    const t = cdiv(term, cx(d));
    sum = cadd(sum, t);
    if (Math.hypot(t.re, t.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
    const f = kind === 'S' ? (2 * n + 2) * (2 * n + 3) : (2 * n + 1) * (2 * n + 2);
    term = cdiv(cmul(cmul(term, z4), cx(-a * a)), cx(f));
  }
  return sum;
}

function zetaReal(s: number): number {
  // Borwein's algorithm for Re(s) > 0, s != 1
  const n = 40;
  const d: number[] = [];
  let sum = 0;
  for (let i = 0; i <= n; i++) {
    let t = 0;
    for (let k = 0; k <= i; k++) {
      t += (factorialN(n + k - 1) * 4 ** k) / (factorialN(n - k) * factorialN(2 * k));
    }
    d.push(n * t);
  }
  const dn = at(d, n);
  for (const [k, dk] of d.slice(0, n).entries()) sum += ((-1) ** k * (dk - dn)) / (k + 1) ** s;
  return -sum / (dn * (1 - 2 ** (1 - s)));
}

function factorialN(n: number): number {
  let r = 1;
  for (let i = 2; i <= n; i++) r *= i;
  return r;
}

function lowergammaNum(s: C, x: C): C {
  // x^s e^-x sum x^k / (s (s+1) ... (s+k))
  let term = cdiv(cx(1), s);
  let sum = term;
  let den = s;
  for (let k = 1; k < 500; k++) {
    den = cadd(den, cx(1));
    term = cdiv(cmul(term, x), den);
    sum = cadd(sum, term);
    if (Math.hypot(term.re, term.im) < 1e-17 * Math.hypot(sum.re, sum.im)) break;
  }
  return cmul(cmul(cpow(x, s), cexp(cmul(cx(-1), x))), sum);
}

// ---------------------------------------------------------------------------
// registration
// ---------------------------------------------------------------------------

/** The integrand t**(a - 1)*(1 - t)**(b - 1) of betainc at its limit x1 (i = 2, with a minus sign) or x2 (i = 3). */
function betaincIntegrand(args: readonly Expr[], i: number): Expr {
  const [a, b, x] = [at(args, 0), at(args, 1), at(args, i)];
  return mul(i === 2 ? -1 : 1, pow(add(1, neg(x)), add(b, -1)), pow(x, add(a, -1)));
}

/** B(a, b) = Gamma(a)*Gamma(b)/Gamma(a + b). */
const mpBeta = (a: Mpc, b: Mpc, wp: number): Mpc => M.cdiv(M.cmul(SP.cgamma(a, wp), SP.cgamma(b, wp), wp), SP.cgamma(M.cadd(a, b, wp), wp), wp);
const mpIsZero = (z: Mpc): boolean => F.isZero(z[0]) && F.isZero(z[1]);
const mpEq = (u: Mpc, v: Mpc): boolean => F.cmp(u[0], v[0]) === 0 && F.cmp(u[1], v[1]) === 0;

/**
 * The incomplete beta function B(a, b; x1, x2) = (x2**a 2F1(a, 1 - b; a + 1; x2)
 * - x1**a 2F1(a, 1 - b; a + 1; x1))/a, divided by B(a, b) when regularized
 * (mpmath betainc, with SymPy's betainc_mpmath_fix for x1 = x2).
 */
function mpBetainc(args: Mpc[], prec: number, regularized: boolean): Mpc {
  const [a, b, x1, x2] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3)];
  const wp = prec + 30;
  if (mpEq(x1, x2)) return M.C0;
  const term = (x: Mpc): Mpc => (mpIsZero(x) ? M.C0 : M.cmul(M.cpow(x, a, wp), chyp2f1(a, M.csub(M.C1, b, wp), M.cadd(a, M.C1, wp), x, wp), wp));
  const v = mpIsZero(x1) && mpEq(x2, M.C1) ? mpBeta(a, b, wp) : M.cdiv(M.csub(term(x2), term(x1), wp), a, wp);
  const r = regularized ? M.cdiv(v, mpBeta(a, b, wp), wp) : v;
  return [F.round(r[0], prec), F.round(r[1], prec)];
}
mpFns['betainc'] = (args, prec) => mpBetainc(args, prec, false);
mpFns['betainc_regularized'] = (args, prec) => mpBetainc(args, prec, true);

type Spec = {
  eval?: (...args: Expr[]) => Expr | undefined;
  partials?: (args: readonly Expr[], i: number) => Expr;
  numeric?: (args: C[]) => C;
  conjugate?: boolean;
};

const twoOverSqrtPi = () => mul(2, pow(sqrt(S.Pi), -1));
/** A spec function of the single argument. */
const unary =
  <T, R>(f: (x: T) => R) =>
  (args: readonly T[]): R =>
    f(first(args));
/** A spec function of the two arguments (and, for partials, the index of the differentiated one). */
const binary =
  <T, R>(f: (x: T, y: T, i: number) => R) =>
  (args: readonly T[], i = 0): R => {
    const [x, y] = pair(args);
    return f(x, y, i);
  };
const realC = (f: (x: number) => number) => unary((z: C) => cx(f(z.re)));

const SPECS: Partial<Record<FnName, Spec>> = {
  factorial: {
    eval: evalFactorial,
    partials: unary((n) => mul(fnN('gamma', add(n, 1)), fnN('polygamma', 0, add(n, 1)))),
    numeric: unary((n) => cgamma(cadd(n, cx(1)))),
    conjugate: true,
  },
  factorial2: {
    eval: evalFactorial2,
    numeric: unary((n) => {
      const v = n.re;
      if (Number.isInteger(v)) {
        let r = 1;
        for (let i = v; i > 1; i -= 2) r *= i;
        return cx(r);
      }
      throw new RangeError('factorial2: non-integer');
    }),
  },
  binomial: {
    eval: evalBinomial,
    numeric: binary((n, k) =>
      cdiv(cgamma(cadd(n, cx(1))), cmul(cgamma(cadd(k, cx(1))), cgamma(cadd(cadd(n, cmul(cx(-1), k)), cx(1))))),
    ),
    conjugate: true,
  },
  ff: { eval: evalFF, numeric: binary((x, k) => cdiv(cgamma(cadd(x, cx(1))), cgamma(cadd(cadd(x, cmul(cx(-1), k)), cx(1))))) },
  rf: { eval: evalRF, numeric: binary((x, k) => cdiv(cgamma(cadd(x, k)), cgamma(x))) },
  subfactorial: { eval: evalSubfactorial },
  harmonic: {
    // SymPy: harmonic(n, 1) is harmonic(n)
    eval: (n, m?: Expr) => (m instanceof Rational && m.isOne ? fnN('harmonic', n) : evalHarmonic(n, m)),
    numeric: (args) => {
      const n = first(args);
      const m = args[1];
      if (m === undefined || m.re === 1) return cadd(cdigamma(cadd(n, cx(1))), cx(EULER_GAMMA));
      throw new NotImplementedError('harmonic: unsupported');
    },
  },
  catalan: {
    eval: evalCatalan,
    partials: unary((n) =>
      mul(
        add(fnN('polygamma', 0, add(n, S.Half)), mul(-1, fnN('polygamma', 0, add(n, 2))), log(4)),
        fnN('catalan', n),
      ),
    ),
    numeric: unary((n) =>
      cdiv(cmul(cpow(cx(4), n), cgamma(cadd(n, cx(0.5)))), cmul(cx(Math.sqrt(Math.PI)), cgamma(cadd(n, cx(2))))),
    ),
  },
  gamma: {
    eval: evalGamma,
    partials: unary((x) => mul(fnN('gamma', x), fnN('polygamma', 0, x))),
    numeric: unary(cgamma),
    conjugate: true,
  },
  loggamma: {
    eval: evalLoggamma,
    partials: unary((x) => fnN('polygamma', 0, x)),
    numeric: unary(cloggamma),
    conjugate: true,
  },
  polygamma: {
    eval: evalPolygamma,
    partials: binary((n, x, i) => {
      if (i === 1) return fnN('polygamma', add(n, 1), x);
      throw new NotImplementedError('diff: polygamma w.r.t. its order');
    }),
    numeric: binary((n, z) => cpolygamma(n.re, z)),
    conjugate: true,
  },
  lowergamma: {
    eval: evalLowergamma,
    partials: binary((s, x, i) => {
      if (i === 1) return mul(pow(x, add(s, -1)), exp(neg(x)));
      throw new NotImplementedError('diff: lowergamma w.r.t. s');
    }),
    numeric: binary((s, x) => lowergammaNum(s, x)),
  },
  uppergamma: {
    eval: evalUppergamma,
    partials: binary((s, x, i) => {
      if (i === 1) return mul(-1, pow(x, add(s, -1)), exp(neg(x)));
      throw new NotImplementedError('diff: uppergamma w.r.t. s');
    }),
    numeric: binary((s, x) => cadd(cgamma(s), cmul(cx(-1), lowergammaNum(s, x)))),
  },
  beta: {
    partials: binary((a, b, i) =>
      i === 0
        ? mul(fnN('beta', a, b), add(fnN('polygamma', 0, a), mul(-1, fnN('polygamma', 0, add(a, b)))))
        : mul(fnN('beta', a, b), add(fnN('polygamma', 0, b), mul(-1, fnN('polygamma', 0, add(a, b))))),
    ),
    numeric: binary((a, b) => cdiv(cmul(cgamma(a), cgamma(b)), cgamma(cadd(a, b)))),
    conjugate: true,
  },
  betainc: {
    // d/dx1 = -(1 - x1)**(b - 1)*x1**(a - 1), d/dx2 = (1 - x2)**(b - 1)*x2**(a - 1)
    partials: (args, i) => (i < 2 ? noPartial('betainc', args, i) : betaincIntegrand(args, i)),
    numeric: (args) => mpNumeric('betainc', args),
    conjugate: true,
  },
  betainc_regularized: {
    partials: (args, i) => (i < 2 ? noPartial('betainc_regularized', args, i) : mul(betaincIntegrand(args, i), pow(fnN('beta', at(args, 0), at(args, 1)), -1))),
    numeric: (args) => mpNumeric('betainc_regularized', args),
    conjugate: true,
  },
  zeta: {
    eval: evalZetaHurwitz,
    // d/da zeta(s, a) = -s*zeta(s + 1, a); no derivative in s (SymPy ArgumentIndexError)
    partials: (args, i) => {
      const [s, a] = args;
      if (i === 1 && s !== undefined && a !== undefined) return mul(-1, s, fnN('zeta', add(s, 1), a));
      return noPartial('zeta', args, i);
    },
    numeric: (args) => (args.length > 1 ? mpNumeric('zeta', args) : realC(zetaReal)(args)),
  },
  erf: { eval: evalErf, partials: unary((z) => mul(twoOverSqrtPi(), exp(neg(pow(z, 2))))), numeric: unary(cerf), conjugate: true },
  erfc: {
    eval: evalErfc,
    partials: unary((z) => mul(-1, twoOverSqrtPi(), exp(neg(pow(z, 2))))),
    numeric: unary(cerfc),
    conjugate: true,
  },
  erfi: { eval: evalErfi, partials: unary((z) => mul(twoOverSqrtPi(), exp(pow(z, 2)))), numeric: unary(cerfi), conjugate: true },
  erf2: {
    eval: evalErf2,
    partials: binary((x, y, i) =>
      i === 0 ? mul(-1, twoOverSqrtPi(), exp(neg(pow(x, 2)))) : mul(twoOverSqrtPi(), exp(neg(pow(y, 2)))),
    ),
    numeric: binary((x, y) => cadd(cerf(y), cmul(cx(-1), cerf(x)))),
    conjugate: true,
  },
  erfinv: {
    eval: evalErfinv,
    partials: unary((x) => mul(S.Half, sqrt(S.Pi), exp(pow(fnN('erfinv', x), 2)))),
    numeric: realC(erfinvReal),
  },
  erfcinv: {
    eval: evalErfcinv,
    partials: unary((x) => mul(S.NegHalf, sqrt(S.Pi), exp(pow(fnN('erfcinv', x), 2)))),
    numeric: realC((y) => erfinvReal(1 - y)),
  },
  erf2inv: {
    eval: evalErf2inv,
    partials: binary((x, y, i) =>
      i === 0
        ? exp(add(neg(pow(x, 2)), pow(fnN('erf2inv', x, y), 2)))
        : mul(S.Half, sqrt(S.Pi), exp(pow(fnN('erf2inv', x, y), 2))),
    ),
    numeric: binary((x, y) => {
      // erf(x) + y outside [-1, 1] has no value (SymPy keeps erf2inv unevaluated)
      const v = erfReal(x.re) + y.re;
      if (Math.abs(v) > 1) throw new RangeError('erf2inv: erf(x) + y outside [-1, 1]');
      return cx(erfinvReal(v));
    }),
  },
  LambertW: {
    eval: evalLambertW,
    partials: (args) => {
      const x = first(args);
      const k = args[1];
      const w = k === undefined ? fnN('LambertW', x) : fnN('LambertW', x, k);
      return mul(w, pow(mul(x, add(w, 1)), -1));
    },
    numeric: (args) => {
      const k = args[1];
      return cLambertW(first(args), k === undefined ? 0 : Math.round(k.re));
    },
  },
  Ei: { eval: evalEi, partials: unary((z) => mul(exp(z), pow(z, -1))), numeric: unary(cEi), conjugate: true },
  li: { eval: evalLi, partials: unary((z) => pow(log(z), -1)), numeric: unary((z) => cEi(clog(z))), conjugate: true },
  Li: {
    eval: evalLiOffset,
    partials: unary((z) => pow(log(z), -1)),
    numeric: unary((z) => cadd(cEi(clog(z)), cx(-1.045163780117493))),
    conjugate: true,
  },
  Si: { eval: evalSi, partials: unary((z) => mul(sin(z), pow(z, -1))), numeric: unary((z) => cSiCi('Si', z)), conjugate: true },
  Ci: { eval: evalCi, partials: unary((z) => mul(cos(z), pow(z, -1))), numeric: unary((z) => cSiCi('Ci', z)) },
  Shi: { eval: evalShi, partials: unary((z) => mul(sinh(z), pow(z, -1))), numeric: unary((z) => cSiCi('Shi', z)), conjugate: true },
  Chi: { eval: evalChi, partials: unary((z) => mul(cosh(z), pow(z, -1))), numeric: unary((z) => cSiCi('Chi', z)) },
  expint: {
    eval: evalExpint,
    // d/dz only: hyper.ts registers d/dnu (a meijerg expression) on top of this
    partials: binary((nu, z) => mul(-1, fnN('expint', add(nu, -1), z))),
    numeric: binary((n, z) => cExpint(n.re, z)),
  },
  fresnels: {
    eval: (z) => evalFresnel('fresnels', z),
    partials: unary((z) => sin(mul(S.Half, S.Pi, pow(z, 2)))),
    numeric: unary((z) => cFresnel('S', z)),
    conjugate: true,
  },
  fresnelc: {
    eval: (z) => evalFresnel('fresnelc', z),
    partials: unary((z) => cos(mul(S.Half, S.Pi, pow(z, 2)))),
    numeric: unary((z) => cFresnel('C', z)),
    conjugate: true,
  },
  sign: { eval: evalSign, numeric: unary((z) => (z.re === 0 && z.im === 0 ? cx(0) : cdiv(z, cx(Math.hypot(z.re, z.im))))) },
  floor: { eval: (x) => evalFloorCeil('floor', x), numeric: unary((z) => cx(Math.floor(z.re))) },
  ceiling: { eval: (x) => evalFloorCeil('ceiling', x), numeric: unary((z) => cx(Math.ceil(z.re))) },
  atan2: {
    eval: evalAtan2,
    partials: binary((y, x, i) =>
      i === 0 ? mul(x, pow(add(pow(x, 2), pow(y, 2)), -1)) : mul(-1, y, pow(add(pow(x, 2), pow(y, 2)), -1)),
    ),
    numeric: binary((y, x) => cx(Math.atan2(y.re, x.re))),
  },
  Min: { eval: (...a) => evalMinMax('Min', ...a), numeric: (a) => cx(Math.min(...a.map((v) => v.re))) },
  Max: { eval: (...a) => evalMinMax('Max', ...a), numeric: (a) => cx(Math.max(...a.map((v) => v.re))) },
};

forEachEntry(SPECS, (name, spec) => {
  if (spec.eval) evaluators[name] = spec.eval;
  if (spec.partials) fnPartials[name] = spec.partials;
  if (spec.numeric) numericFns[name] = spec.numeric;
  if (spec.conjugate) conjugateCommutes.add(name);
});

// ---------------------------------------------------------------------------
// public constructors
// ---------------------------------------------------------------------------

export const factorial = (n: ExprLike): Expr => fn('factorial', [n]);
export const factorial2 = (n: ExprLike): Expr => fn('factorial2', [n]);
export const binomial = (n: ExprLike, k: ExprLike): Expr => fn('binomial', [n, k]);
export const ff = (x: ExprLike, k: ExprLike): Expr => fn('ff', [x, k]);
export const rf = (x: ExprLike, k: ExprLike): Expr => fn('rf', [x, k]);
export const subfactorial = (n: ExprLike): Expr => fn('subfactorial', [n]);
export const harmonic = (n: ExprLike, m?: ExprLike): Expr => (m === undefined ? fn('harmonic', [n]) : fn('harmonic', [n, m]));
export const catalan = (n: ExprLike): Expr => fn('catalan', [n]);
export const gamma = (x: ExprLike): Expr => fn('gamma', [x]);
export const loggamma = (x: ExprLike): Expr => fn('loggamma', [x]);
export const polygamma = (n: ExprLike, x: ExprLike): Expr => fn('polygamma', [n, x]);
/** SymPy digamma(x) = polygamma(0, x); with `{ evaluate: false }` the unevaluated digamma(x). */
export const digamma = (x: ExprLike, opts: { evaluate?: boolean } = {}): Expr =>
  opts.evaluate === false ? new Fn('digamma', [sympify(x)]) : fn('polygamma', [0, x]);
/** SymPy trigamma(x) = polygamma(1, x); with `{ evaluate: false }` the unevaluated trigamma(x). */
export const trigamma = (x: ExprLike, opts: { evaluate?: boolean } = {}): Expr =>
  opts.evaluate === false ? new Fn('trigamma', [sympify(x)]) : fn('polygamma', [1, x]);
export const lowergamma = (s: ExprLike, x: ExprLike): Expr => fn('lowergamma', [s, x]);
export const uppergamma = (s: ExprLike, x: ExprLike): Expr => fn('uppergamma', [s, x]);
export const beta = (a: ExprLike, b: ExprLike): Expr => fn('beta', [a, b]);
/** SymPy betainc(a, b, x1, x2): the generalized incomplete beta function, the integral of t**(a - 1)*(1 - t)**(b - 1) from x1 to x2. */
export const betainc = (a: ExprLike, b: ExprLike, x1: ExprLike, x2: ExprLike): Expr => fn('betainc', [a, b, x1, x2]);
/** SymPy betainc_regularized(a, b, x1, x2): betainc(a, b, x1, x2)/beta(a, b). */
export const betaincRegularized = (a: ExprLike, b: ExprLike, x1: ExprLike, x2: ExprLike): Expr => fn('betainc_regularized', [a, b, x1, x2]);
/** SymPy zeta(s) (Riemann) and zeta(s, a) (Hurwitz). */
export const zeta = (s: ExprLike, a?: ExprLike): Expr => fn('zeta', a === undefined ? [s] : [s, a]);
export const erf = (z: ExprLike): Expr => fn('erf', [z]);
export const erfc = (z: ExprLike): Expr => fn('erfc', [z]);
export const erfi = (z: ExprLike): Expr => fn('erfi', [z]);
export const erf2 = (x: ExprLike, y: ExprLike): Expr => fn('erf2', [x, y]);
export const erfinv = (z: ExprLike): Expr => fn('erfinv', [z]);
export const erfcinv = (z: ExprLike): Expr => fn('erfcinv', [z]);
export const erf2inv = (x: ExprLike, y: ExprLike): Expr => fn('erf2inv', [x, y]);
export const Ei = (z: ExprLike): Expr => fn('Ei', [z]);
export const LambertW = (x: ExprLike, k?: ExprLike): Expr => fn('LambertW', k === undefined ? [x] : [x, k]);
impl.lambertW = (x, k) => LambertW(x, k);
export const li = (z: ExprLike): Expr => fn('li', [z]);
export const Li = (z: ExprLike): Expr => fn('Li', [z]);
export const Si = (z: ExprLike): Expr => fn('Si', [z]);
export const Ci = (z: ExprLike): Expr => fn('Ci', [z]);
export const Shi = (z: ExprLike): Expr => fn('Shi', [z]);
export const Chi = (z: ExprLike): Expr => fn('Chi', [z]);
export const expint = (nu: ExprLike, z: ExprLike): Expr => fn('expint', [nu, z]);
export const E1 = (z: ExprLike): Expr => fn('expint', [1, z]);
export const fresnels = (z: ExprLike): Expr => fn('fresnels', [z]);
export const fresnelc = (z: ExprLike): Expr => fn('fresnelc', [z]);
export const sign = (x: ExprLike): Expr => fn('sign', [x]);
export const floor = (x: ExprLike): Expr => fn('floor', [x]);

/** SymPy Rem(p, q): the remainder of truncated division (sign of p); unevaluated for symbols. */
export const Rem = (p: ExprLike, q: ExprLike): Expr => fn('Rem', [p, q]);
evaluators.Rem = (p, q) => {
  if (p instanceof Rational && q instanceof Rational && p.isInteger && q.isInteger && q.p !== 0n) return Rational.of(p.p % q.p);
  if (p.key === q.key) return S.Zero;
  return undefined;
};
export const ceiling = (x: ExprLike): Expr => fn('ceiling', [x]);
export const atan2 = (y: ExprLike, x: ExprLike): Expr => fn('atan2', [y, x]);
export const Min = (...xs: ExprLike[]): Expr => fn('Min', xs);
export const Max = (...xs: ExprLike[]): Expr => fn('Max', xs);

/**
 * Per-function rules of expand_func (SymPy _eval_expand_func), registered by
 * the modules defining the functions; undefined leaves the call unchanged.
 * @internal
 */
export const funcExpanders: Partial<Record<FnName, (args: readonly Expr[]) => Expr | undefined>> = {};

/**
 * SymPy _eval_expand_func of the functions defined in other modules, by
 * function (or extension node) name: the expanded form, or undefined when
 * the function stays.
 */
export const expandFuncRules: Partial<Record<string, (e: Expr) => Expr | undefined>> = {};

/** SymPy expand_func: rewrite special functions into elementary terms where possible. */
export function expandFunc(e: Expr): Expr {
  const go = (x: Expr): Expr => {
    if (x instanceof Constant && x.name === 'GoldenRatio') return add(S.Half, mul(S.Half, sqrt(5)));
    if (x instanceof Constant && x.name === 'TribonacciConstant') {
      const s33 = mul(3, sqrt(33));
      return mul(R(1n, 3n), add(1, pow(add(19, neg(s33)), R(1n, 3n)), pow(add(19, s33), R(1n, 3n))));
    }
    const args = x.args.map(go);
    const changed = args.some((a, i) => a !== x.args[i]);
    const y = !changed ? x : x instanceof Fn ? fn(x.name, args) : rebuild(x, args);
    const rule = y instanceof Fn || y instanceof ExtensionExpr ? expandFuncRules[y.name] : undefined;
    const r = rule?.(y);
    if (r !== undefined) return r;
    const expander = y instanceof Fn ? funcExpanders[y.name] : undefined;
    const expanded = expander?.(y.args);
    if (expanded !== undefined) return expanded;
    if (y instanceof Fn && y.name === 'gamma') {
      const a = first(y.args);
      if (a instanceof Rational && (a.p < 0n ? -a.p : a.p) > a.q) {
        const n = a.p >= 0n ? a.p / a.q : -((-a.p + a.q - 1n) / a.q);
        const frac = R(a.p - n * a.q, a.q);
        return mul(fn('gamma', [frac]), fn('rf', [frac, R(n)]));
      }
      const a0 = a.args[0];
      if (a instanceof Add && a0 instanceof Rational) {
        let coeff = a0;
        let tail: Expr[] = a.args.slice(1);
        if (coeff.q !== 1n) {
          const ip = R(coeff.p >= 0n ? coeff.p / coeff.q : -((-coeff.p + coeff.q - 1n) / coeff.q));
          tail = [add(coeff, neg(ip)), ...tail];
          coeff = ip;
        }
        const t = add(...tail);
        return mul(fn('gamma', [t]), fn('rf', [t, coeff]));
      }
    }
    if (y instanceof Fn) {
      if (y.name === 'binomial') {
        const [n, k] = y.args;
        if (n !== undefined && k !== undefined && isInt(k) && k.isPositive) {
          return mul(...Array.from({ length: Number(k.p) }, (_, i) => add(n, -i)), R(1n, factorialBig(k.p)));
        }
      }
      if (y.name === 'harmonic' && y.args.length === 1) {
        const [c, rest] = splitAddInt(first(y.args));
        if (c !== 0n) {
          const base = fn('harmonic', [rest]);
          const terms: Expr[] = [base];
          if (c > 0n) for (let k = 1n; k <= c; k++) terms.push(pow(add(rest, R(k)), -1));
          else for (let k = 0n; k < -c; k++) terms.push(mul(-1, pow(add(rest, R(-k)), -1)));
          return add(...terms);
        }
      }
      const [y0, y1] = y.args;
      if (y.name === 'expint' && y0 !== undefined && y1 !== undefined && isInt(y0) && y0.p > 1n) {
        const n = y0.p;
        const z = y1;
        // E_n(z) = (-z)^(n-1)/(n-1)! E_1(z) + e^-z/(n-1)! sum_{k=0}^{n-2} (n-k-2)! (-z)^k
        const f = factorialBig(n - 1n);
        const sumTerms: Expr[] = [];
        for (let k = 0n; k <= n - 2n; k++) sumTerms.push(mul(R(factorialBig(n - k - 2n)), pow(neg(z), Number(k))));
        return add(
          mul(pow(neg(z), Number(n - 1n)), R(1n, f), fn('expint', [1, z])),
          mul(exp(neg(z)), R(1n, f), add(...sumTerms)),
        );
      }
    }
    return y;
  };
  return go(e);
}

function splitAddInt(e: Expr): [bigint, Expr] {
  const c = e.args[0];
  if (e instanceof Add && c !== undefined && isInt(c)) return [c.p, add(...e.args.slice(1))];
  return [0n, e];
}

impl.expandFunc = expandFunc;
impl.sign = sign;
