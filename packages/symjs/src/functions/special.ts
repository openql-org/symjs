// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Combinatorial and special functions with SymPy-compatible
 * evaluation rules, derivatives, conjugation and numeric evaluation.
 */

import '../numeric/mpspecialfns';
import { isIntegerQ, isNegative, isPositive } from '../core/assumptions';
import {
  Add,
  ComplexValue as C,
  Constant,
  Expr,
  ExprLike,
  Fn,
  FnName,
  Mul,
  Rational,
  S,
  Special,
  isNum,
} from '../core/nodes';
import { numAdd, numMul } from '../core/num';
import { add, couldExtractMinusSign, exp, mul, neg, pow, splitCoeff, sqrt, sympify } from '../core/ops';
import { fnPartials } from '../calculus/diff';
import { rebuild } from '../core/traverse';
import { impl } from '../core/nodes';
import { c as cx, cadd, cdiv, cexp, clog, cLambertW, cmul, cpow, csin } from '../numeric/complex';
import { numericFns } from '../numeric/evalf';
import { compareKeys, sortKey } from '../printing/sortkey';
import { conjugateCommutes, cos, cosh, evaluators, fn, log, sin, sinh } from './elementary';

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const R = (p: bigint | number, q: bigint | number = 1) => Rational.of(p, q);
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
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
  if (bernoulliCache[n]) return bernoulliCache[n]!;
  const a: Rational[] = [];
  for (let m = 0; m <= n; m++) {
    a[m] = R(1, m + 1);
    for (let j = m; j >= 1; j--) {
      a[j - 1] = numMul(R(j), numAdd(a[j - 1]!, numMul(R(-1), a[j]!))) as Rational;
    }
  }
  bernoulliCache[n] = a[0]!;
  return a[0]!;
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

function evalFactorial2(n: Expr): Expr | undefined {
  if (!isInt(n)) return undefined;
  if (n.p >= 0n) {
    let r = 1n;
    for (let i = n.p; i > 1n; i -= 2n) r *= i;
    return R(r);
  }
  if (n.p % 2n === 0n) return S.ComplexInfinity;
  // negative odd: n!! = (n + 2)!! / (n + 2)
  let v: Rational = S.One;
  for (let k = -1n; k > n.p; k -= 2n) v = numMul(v, R(1n, k)) as Rational;
  return v;
}

function evalBinomial(n: Expr, k: Expr): Expr | undefined {
  if (isInt(k)) {
    if (k.isNegative) return S.Zero;
    if (k.isZero) return S.One;
    if (isInt(n) && !n.isNegative && k.p > n.p) return S.Zero;
    if (n instanceof Rational) {
      // very large k: keep binomial(n, k) unevaluated instead of looping k times
      if (k.p > 100000n && !(isInt(n) && n.p - k.p <= 100000n && n.p - k.p >= 0n)) return undefined;
      if (isInt(n) && n.p >= 0n && n.p - k.p < k.p) {
        // binomial(n, k) = binomial(n, n - k)
        return evalBinomial(n, R(n.p - k.p));
      }
      let num: Rational = S.One;
      for (let i = 0n; i < k.p; i++) num = numMul(num, numAdd(n, R(-i))) as Rational;
      return numMul(num, R(1n, factorialBig(k.p)));
    }
    if (k.isOne) return n;
    return undefined;
  }
  if (k.key === n.key && isIntegerQ(n) === true) return S.One;
  return undefined;
}

function evalFF(x: Expr, k: Expr): Expr | undefined {
  if (isInt(k)) {
    if (k.isZero) return S.One;
    if (k.isPositive) return mul(...Array.from({ length: Number(k.p) }, (_, i) => add(x, -i)));
    return mul(...Array.from({ length: Number(-k.p) }, (_, i) => pow(add(x, i + 1), -1)));
  }
  if (k.key === x.key) return fnN('factorial', x);
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

function evalHarmonic(n: Expr, m: Expr = S.One): Expr | undefined {
  if (isOo(n)) {
    if (m instanceof Rational && m.isOne) return S.Infinity;
    if (isInt(m) && m.p > 1n) return fnN('zeta', m);
    if (isNegative(m) === true) return S.NaN;
    if (isPositive(add(m, -1)) === true) return fnN('zeta', m);
    if (isNegative(add(m, -1)) === true || (isPositive(m) === false && isNegative(m) === false)) return S.Infinity;
    return undefined;
  }
  if (isInt(n) && !n.isNegative && isInt(m)) {
    let s: Rational = S.Zero;
    for (let k = 1n; k <= n.p; k++) s = numAdd(s, numMul(S.One, R(1n, k ** m.p))) as Rational;
    return s;
  }
  if (isInt(n) && n.isZero) return S.Zero;
  return undefined;
}

function evalCatalan(n: Expr): Expr | undefined {
  if (isInt(n) && !n.isNegative) {
    const c = factorialBig(2n * n.p) / (factorialBig(n.p) * factorialBig(n.p + 1n));
    return R(c);
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
  if (x instanceof Rational && x.q === 2n) return log(gammaHalf((x.p - 1n) / 2n));
  // half of a positive integer symbol: log(sqrt(pi)*2**(1 - p)*gamma(p)/gamma((p + 1)/2))
  if (x instanceof Mul && x.args.length === 2 && x.args[0] instanceof Rational && x.args[0].p === 1n && x.args[0].q === 2n) {
    const p = x.args[1]!;
    if (isIntegerQ(p) === true && isPositive(p) === true) {
      return log(mul(sqrt(S.Pi), pow(2, add(1, neg(p))), fnN('gamma', p), pow(fnN('gamma', mul(add(p, 1), S.Half)), -1)));
    }
  }
  if (isOo(x)) return S.Infinity;
  if (isNegOo(x)) return S.ComplexInfinity;
  if (isIntegerQ(x) === true) {
    if (isPositive(x) === true) return log(fnN('gamma', x));
    if (isNegative(neg(x)) === true || isNegative(x) === true) return S.Infinity;
  }
  return undefined;
}

function evalPolygamma(n: Expr, x: Expr): Expr | undefined {
  if (isOo(x) || isNegOo(x) || isIOo(x) || isNegIOo(x)) {
    if (n instanceof Rational && n.isZero) return S.Infinity;
    if (isInt(n) && n.isPositive) return S.Zero;
  }
  if (!isInt(n) || n.isNegative) return undefined;
  if (isInt(x) && !x.isPositive) return S.ComplexInfinity;
  if (n.isZero) {
    if (isInt(x)) {
      if (!x.isPositive) return S.ComplexInfinity;
      const h = evalHarmonic(R(x.p - 1n))!;
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
    for (let k = 1n; k < x.p; k++) partial = numAdd(partial, R(1n, k ** (n.p + 1n))) as Rational;
    const sign = n.p % 2n === 0n ? -1n : 1n;
    return mul(R(sign * factorialBig(n.p)), add(z, mul(-1, partial)));
  }
  return undefined;
}

/** digamma(p/q) by Gauss's theorem (SymPy polygamma._eval_expand_func, J. Choi 2007). */
function digammaRational(z: Rational): Expr {
  const p = z.p;
  const q = Number(z.q);
  const terms: Expr[] = [
    mul(-1, S.EulerGamma),
    mul(-1, S.Pi, fnN('cot', mul(R(p, z.q), S.Pi)), S.Half),
    mul(-1, log(R(z.q))),
  ];
  for (let k = 1; k < q; k++) {
    terms.push(mul(cos(mul(R(2n * BigInt(k) * p, z.q), S.Pi)), log(mul(2, sin(mul(R(k, q), S.Pi))))));
  }
  if (z.isPositive) {
    const n = z.p / z.q;
    const z0 = numAdd(z, R(-n)) as Rational;
    for (let k = 0n; k < n; k++) terms.push(pow(numAdd(z0, R(k)), -1));
  } else {
    const n = (z.q - z.p) / z.q; // floor(1 - z)
    const z0 = numAdd(z, R(n)) as Rational;
    for (let k = 0n; k < n; k++) terms.push(mul(-1, pow(numAdd(z0, R(-1n - k)), -1)));
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

function evalUppergamma(s: Expr, x: Expr): Expr | undefined {
  if (x instanceof Rational && x.isZero) return evalGamma(s);
  if (isInt(s)) {
    if (s.isPositive) {
      const f = R(factorialBig(s.p - 1n));
      return mul(f, sumSeries(x, Number(s.p)), exp(neg(x)));
    }
    // uppergamma(s, x) = x**s * expint(1 - s, x)
    return mul(pow(x, s), fnN('expint', R(1n - s.p), x));
  }
  if (s instanceof Rational && s.q === 2n) {
    // start from uppergamma(1/2, x) = sqrt(pi) erfc(sqrt(x)) and use the recurrence
    let k = R(1n, 2n);
    let v: Expr = mul(sqrt(S.Pi), fnN('erfc', sqrt(x)));
    while (numAdd(s, numMul(k, R(-1))).isPositive) {
      // uppergamma(k + 1) = k uppergamma(k) + x^k e^-x
      v = add(mul(k, v), mul(pow(x, k), exp(neg(x))));
      k = numAdd(k, S.One) as Rational;
    }
    while (numAdd(k, numMul(s, R(-1))).isPositive) {
      // uppergamma(k - 1) = (uppergamma(k) - x^(k-1) e^-x)/(k - 1)
      const km1 = numAdd(k, R(-1)) as Rational;
      v = mul(add(v, mul(-1, pow(x, km1), exp(neg(x)))), pow(km1, -1));
      k = km1;
    }
    return v;
  }
  return undefined;
}

function evalLowergamma(s: Expr, x: Expr): Expr | undefined {
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (isInt(s) && s.isPositive) {
    const f = R(factorialBig(s.p - 1n));
    return add(f, mul(neg(f), sumSeries(x, Number(s.p)), exp(neg(x))));
  }
  if (s instanceof Rational && s.q === 2n) {
    let k = R(1n, 2n);
    let v: Expr = mul(sqrt(S.Pi), fnN('erf', sqrt(x)));
    while (numAdd(s, numMul(k, R(-1))).isPositive) {
      // lowergamma(k + 1) = k lowergamma(k) - x^k e^-x
      v = add(mul(k, v), mul(-1, pow(x, k), exp(neg(x))));
      k = numAdd(k, S.One) as Rational;
    }
    while (numAdd(k, numMul(s, R(-1))).isPositive) {
      const km1 = numAdd(k, R(-1)) as Rational;
      v = mul(add(v, mul(pow(x, km1), exp(neg(x)))), pow(km1, -1));
      k = km1;
    }
    return v;
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
  if (z instanceof Fn && z.name === 'erf' && (isNum(z.args[0]!) || false)) return z.args[0];
  return odd('erfinv', z);
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
  if (y instanceof Rational && y.isZero) return x;
  if (x instanceof Rational && x.isZero) return fnN('erfinv', y);
  if (isOo(x)) return fnN('erfcinv', neg(y));
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

function evalCi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.NegativeInfinity;
  if (isOo(z)) return S.Zero;
  return undefined;
}

function evalChi(z: Expr): Expr | undefined {
  if (z instanceof Rational && z.isZero) return S.NegativeInfinity;
  if (isOo(z)) return S.Infinity;
  return undefined;
}

function evalExpint(nu: Expr, z: Expr): Expr | undefined {
  if (isInt(nu)) {
    if (nu.isZero) return mul(exp(neg(z)), pow(z, -1));
    if (nu.isNegative) {
      // E_n = (e^-z - n E_{n+1}) / z, starting from E_0
      let v: Expr = mul(exp(neg(z)), pow(z, -1));
      for (let n = -1n; n >= nu.p; n--) {
        v = add(mul(exp(neg(z)), pow(z, -1)), mul(-n, v, pow(z, -1)));
      }
      return v;
    }
    return undefined;
  }
  if (nu instanceof Rational && nu.p === 1n && nu.q === 2n) {
    return mul(sqrt(S.Pi), fnN('erfc', sqrt(z)), pow(sqrt(z), -1));
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
  if (w !== undefined && !(w instanceof Rational && w.isOne && false)) {
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
    if (!(c instanceof Rational && c.isOne)) return mul(evalSign(c)!, fnN('sign', r));
  }
  return undefined;
}

function numericReal(x: Expr): number | undefined {
  if (x.freeSymbols().size > 0) return undefined;
  try {
    const v = x.toComplex();
    return Math.abs(v.im) < 1e-300 ? v.re : undefined;
  } catch {
    return undefined;
  }
}

function evalFloorCeil(name: 'floor' | 'ceiling', x: Expr): Expr | undefined {
  const w = imagFactor(x);
  if (w !== undefined && w instanceof Rational) return mul(S.I, evalFloorCeil(name, w) ?? fnN(name, w));
  if (x instanceof Add && x.args.length === 2 && x.args[0] instanceof Rational) {
    const iw = imagFactor(x.args[1]!);
    if (iw instanceof Rational) return add(evalFloorCeil(name, x.args[0])!, mul(S.I, evalFloorCeil(name, iw)!));
  }
  if (x instanceof Rational) {
    const f = x.p / x.q - (x.p % x.q !== 0n && x.p < 0n ? 1n : 0n);
    if (name === 'floor' || x.isInteger) return R(f);
    return R(f + 1n);
  }
  if (isIntegerQ(x) === true) return x;
  if (x instanceof Add) {
    const ints = x.args.filter((a) => isIntegerQ(a) === true);
    if (ints.length && ints.length < x.args.length) {
      return add(...ints, fnN(name, add(...x.args.filter((a) => isIntegerQ(a) !== true))));
    }
  }
  const v = numericReal(x);
  if (v !== undefined && Number.isFinite(v)) {
    const r = name === 'floor' ? Math.floor(v) : Math.ceil(v);
    // guard against floating point at integer boundaries
    if (Math.abs(v - Math.round(v)) > 1e-9) return R(BigInt(r));
  }
  return undefined;
}

function evalAtan2(y: Expr, x: Expr): Expr | undefined {
  const yv = numericReal(y);
  const xv = numericReal(x);
  if (y instanceof Rational && y.isZero) {
    if (isPositive(x) === true) return S.Zero;
    if (isNegative(x) === true) return S.Pi;
  }
  if (x instanceof Rational && x.isZero) {
    if (isPositive(y) === true) return mul(S.Half, S.Pi);
    if (isNegative(y) === true) return mul(S.NegHalf, S.Pi);
  }
  if (yv !== undefined && xv !== undefined) {
    const at = fnN('atan', mul(y, pow(x, -1)));
    if (xv > 0) return at;
    if (xv < 0) return yv >= 0 ? add(at, S.Pi) : add(at, neg(S.Pi));
  }
  if (isPositive(x) === true) return fnN('atan', mul(y, pow(x, -1)));
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
  for (const n of nums) {
    if (best === undefined) best = n;
    else {
      const bv = numericReal(best)!;
      const nv = numericReal(n)!;
      if (name === 'Min' ? nv < bv : nv > bv) best = n;
    }
  }
  const rest = collapseMinMax(name, [...(best ? [best] : []), ...uniq(syms)]);
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
  const build = (n: string, xs: Expr[]) => new Fn(n as FnName, [...xs].sort((u, v) => compareKeys(sortKey(u), sortKey(v))));
  const doIt = (ai: Expr, a: Expr): Expr => {
    if (!isMM(ai)) return ai;
    if (!ai.args.some((t) => t.key === a.key)) return build(ai.name, ai.args.map((t) => doIt(t, a)));
    if (ai.name === name) return build(ai.name, ai.args.filter((t) => t.key !== a.key).map((t) => doIt(t, a)));
    return a;
  };
  for (let i = 0; i < args.length; i++) {
    for (let j = i + 1; j < args.length; j++) args[j] = doIt(args[j]!, args[i]!);
  }
  return args;
}

// ---------------------------------------------------------------------------
// numerics (double precision)
// ---------------------------------------------------------------------------

const LANCZOS = [
  0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
  12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7,
];

export function cgamma(z: C): C {
  if (z.re < 0.5) {
    // reflection: gamma(z) gamma(1 - z) = pi / sin(pi z)
    const s = csin(cmul(cx(Math.PI), z));
    return cdiv(cx(Math.PI), cmul(s, cgamma(cadd(cx(1), cmul(cx(-1), z)))));
  }
  const zz = cadd(z, cx(-1));
  let a = cx(LANCZOS[0]!);
  const t = cadd(zz, cx(7.5));
  for (let i = 1; i < 9; i++) a = cadd(a, cdiv(cx(LANCZOS[i]!), cadd(zz, cx(i))));
  const r = cmul(cmul(cx(Math.sqrt(2 * Math.PI)), cpow(t, cadd(zz, cx(0.5)))), cmul(cexp(cmul(cx(-1), t)), a));
  return r;
}

export function cloggamma(z: C): C {
  if (z.im === 0 && z.re > 0) return cx(Math.log(Math.abs(cgamma(z).re)));
  return clog(cgamma(z));
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
  for (let k = 1; k <= B.length; k++) {
    let num = 1;
    for (let i = 2; i <= 2 * k + n - 1; i++) num *= i;
    let den = 1;
    for (let i = 2; i <= 2 * k; i++) den *= i;
    s = cadd(s, cdiv(cx((B[k - 1]! * num) / den), cpow(w, cx(2 * k + n))));
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
  let f = x;
  let Cc = x;
  let D = 0;
  const tiny = 1e-300;
  for (let n = 1; n < 500; n++) {
    const a = n / 2;
    D = x + a * D;
    D = D === 0 ? tiny : D;
    Cc = x + a / Cc;
    Cc = Cc === 0 ? tiny : Cc;
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
  for (let k = 0; k < n; k++) sum += ((-1) ** k * (d[k]! - d[n]!)) / (k + 1) ** s;
  return -sum / (d[n]! * (1 - 2 ** (1 - s)));
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

type Spec = {
  eval?: (...args: Expr[]) => Expr | undefined;
  partials?: (args: readonly Expr[], i: number) => Expr;
  numeric?: (args: C[]) => C;
  conjugate?: boolean;
};

const twoOverSqrtPi = () => mul(2, pow(sqrt(S.Pi), -1));
const realC = (f: (x: number) => number) => (a: C[]) => cx(f(a[0]!.re));

const SPECS: Partial<Record<FnName, Spec>> = {
  factorial: {
    eval: evalFactorial,
    partials: ([n]) => mul(fnN('gamma', add(n!, 1)), fnN('polygamma', 0, add(n!, 1))),
    numeric: ([n]) => cgamma(cadd(n!, cx(1))),
    conjugate: true,
  },
  factorial2: {
    eval: evalFactorial2,
    numeric: ([n]) => {
      const v = n!.re;
      if (Number.isInteger(v)) {
        let r = 1;
        for (let i = v; i > 1; i -= 2) r *= i;
        return cx(r);
      }
      throw new Error('factorial2: non-integer');
    },
  },
  binomial: {
    eval: evalBinomial,
    numeric: ([n, k]) =>
      cdiv(cgamma(cadd(n!, cx(1))), cmul(cgamma(cadd(k!, cx(1))), cgamma(cadd(cadd(n!, cmul(cx(-1), k!)), cx(1))))),
    conjugate: true,
  },
  ff: { eval: evalFF, numeric: ([x, k]) => cdiv(cgamma(cadd(x!, cx(1))), cgamma(cadd(cadd(x!, cmul(cx(-1), k!)), cx(1)))) },
  rf: { eval: evalRF, numeric: ([x, k]) => cdiv(cgamma(cadd(x!, k!)), cgamma(x!)) },
  subfactorial: { eval: evalSubfactorial },
  harmonic: {
    eval: (n, m) => evalHarmonic(n, m ?? S.One),
    numeric: ([n, m]) => {
      if (m === undefined || m.re === 1) return cadd(cdigamma(cadd(n!, cx(1))), cx(EULER_GAMMA));
      throw new Error('harmonic: unsupported');
    },
  },
  catalan: {
    eval: evalCatalan,
    partials: ([n]) =>
      mul(
        add(fnN('polygamma', 0, add(n!, S.Half)), mul(-1, fnN('polygamma', 0, add(n!, 2))), log(4)),
        fnN('catalan', n!),
      ),
    numeric: ([n]) =>
      cdiv(cmul(cpow(cx(4), n!), cgamma(cadd(n!, cx(0.5)))), cmul(cx(Math.sqrt(Math.PI)), cgamma(cadd(n!, cx(2))))),
  },
  gamma: {
    eval: evalGamma,
    partials: ([x]) => mul(fnN('gamma', x!), fnN('polygamma', 0, x!)),
    numeric: ([z]) => cgamma(z!),
    conjugate: true,
  },
  loggamma: {
    eval: evalLoggamma,
    partials: ([x]) => fnN('polygamma', 0, x!),
    numeric: ([z]) => cloggamma(z!),
    conjugate: true,
  },
  polygamma: {
    eval: evalPolygamma,
    partials: ([n, x], i) => {
      if (i === 1) return fnN('polygamma', add(n!, 1), x!);
      throw new Error('diff: polygamma w.r.t. its order');
    },
    numeric: ([n, z]) => cpolygamma(n!.re, z!),
    conjugate: true,
  },
  lowergamma: {
    eval: evalLowergamma,
    partials: ([s, x], i) => {
      if (i === 1) return mul(pow(x!, add(s!, -1)), exp(neg(x!)));
      throw new Error('diff: lowergamma w.r.t. s');
    },
    numeric: ([s, x]) => lowergammaNum(s!, x!),
  },
  uppergamma: {
    eval: evalUppergamma,
    partials: ([s, x], i) => {
      if (i === 1) return mul(-1, pow(x!, add(s!, -1)), exp(neg(x!)));
      throw new Error('diff: uppergamma w.r.t. s');
    },
    numeric: ([s, x]) => cadd(cgamma(s!), cmul(cx(-1), lowergammaNum(s!, x!))),
  },
  beta: {
    partials: ([a, b], i) =>
      i === 0
        ? mul(fnN('beta', a!, b!), add(fnN('polygamma', 0, a!), mul(-1, fnN('polygamma', 0, add(a!, b!)))))
        : mul(fnN('beta', a!, b!), add(fnN('polygamma', 0, b!), mul(-1, fnN('polygamma', 0, add(a!, b!))))),
    numeric: ([a, b]) => cdiv(cmul(cgamma(a!), cgamma(b!)), cgamma(cadd(a!, b!))),
    conjugate: true,
  },
  zeta: { eval: evalZeta, numeric: realC(zetaReal) },
  erf: { eval: evalErf, partials: ([z]) => mul(twoOverSqrtPi(), exp(neg(pow(z!, 2)))), numeric: ([z]) => cerf(z!), conjugate: true },
  erfc: {
    eval: evalErfc,
    partials: ([z]) => mul(-1, twoOverSqrtPi(), exp(neg(pow(z!, 2)))),
    numeric: ([z]) => cerfc(z!),
    conjugate: true,
  },
  erfi: { eval: evalErfi, partials: ([z]) => mul(twoOverSqrtPi(), exp(pow(z!, 2))), numeric: ([z]) => cerfi(z!), conjugate: true },
  erf2: {
    eval: evalErf2,
    partials: ([x, y], i) =>
      i === 0 ? mul(-1, twoOverSqrtPi(), exp(neg(pow(x!, 2)))) : mul(twoOverSqrtPi(), exp(neg(pow(y!, 2)))),
    numeric: ([x, y]) => cadd(cerf(y!), cmul(cx(-1), cerf(x!))),
    conjugate: true,
  },
  erfinv: {
    eval: evalErfinv,
    partials: ([x]) => mul(S.Half, sqrt(S.Pi), exp(pow(fnN('erfinv', x!), 2))),
    numeric: realC(erfinvReal),
  },
  erfcinv: {
    eval: evalErfcinv,
    partials: ([x]) => mul(S.NegHalf, sqrt(S.Pi), exp(pow(fnN('erfcinv', x!), 2))),
    numeric: realC((y) => erfinvReal(1 - y)),
  },
  erf2inv: {
    eval: evalErf2inv,
    partials: ([x, y], i) =>
      i === 0
        ? exp(add(neg(pow(x!, 2)), pow(fnN('erf2inv', x!, y!), 2)))
        : mul(S.Half, sqrt(S.Pi), exp(pow(fnN('erf2inv', x!, y!), 2))),
    numeric: ([x, y]) => cx(erfinvReal(erfReal(x!.re) + y!.re)),
  },
  LambertW: {
    eval: evalLambertW,
    partials: ([x, k]) => {
      const w = k === undefined ? fnN('LambertW', x!) : fnN('LambertW', x!, k);
      return mul(w, pow(mul(x!, add(w, 1)), -1));
    },
    numeric: ([x, k]) => cLambertW(x!, k === undefined ? 0 : Math.round(k.re)),
  },
  Ei: { eval: evalEi, partials: ([z]) => mul(exp(z!), pow(z!, -1)), numeric: ([z]) => cEi(z!), conjugate: true },
  li: { eval: evalLi, partials: ([z]) => pow(log(z!), -1), numeric: ([z]) => cEi(clog(z!)), conjugate: true },
  Li: {
    eval: evalLiOffset,
    partials: ([z]) => pow(log(z!), -1),
    numeric: ([z]) => cadd(cEi(clog(z!)), cx(-1.045163780117493)),
    conjugate: true,
  },
  Si: { eval: evalSi, partials: ([z]) => mul(sin(z!), pow(z!, -1)), numeric: ([z]) => cSiCi('Si', z!), conjugate: true },
  Ci: { eval: evalCi, partials: ([z]) => mul(cos(z!), pow(z!, -1)), numeric: ([z]) => cSiCi('Ci', z!) },
  Shi: { eval: evalShi, partials: ([z]) => mul(sinh(z!), pow(z!, -1)), numeric: ([z]) => cSiCi('Shi', z!), conjugate: true },
  Chi: { eval: evalChi, partials: ([z]) => mul(cosh(z!), pow(z!, -1)), numeric: ([z]) => cSiCi('Chi', z!) },
  expint: {
    eval: evalExpint,
    partials: ([nu, z], i) => {
      if (i === 1) return mul(-1, fnN('expint', add(nu!, -1), z!));
      throw new Error('diff: expint w.r.t. its order');
    },
    numeric: ([n, z]) => cExpint(n!.re, z!),
  },
  fresnels: {
    eval: (z) => evalFresnel('fresnels', z),
    partials: ([z]) => sin(mul(S.Half, S.Pi, pow(z!, 2))),
    numeric: ([z]) => cFresnel('S', z!),
    conjugate: true,
  },
  fresnelc: {
    eval: (z) => evalFresnel('fresnelc', z),
    partials: ([z]) => cos(mul(S.Half, S.Pi, pow(z!, 2))),
    numeric: ([z]) => cFresnel('C', z!),
    conjugate: true,
  },
  sign: { eval: evalSign, numeric: ([z]) => (z!.re === 0 && z!.im === 0 ? cx(0) : cdiv(z!, cx(Math.hypot(z!.re, z!.im)))) },
  floor: { eval: (x) => evalFloorCeil('floor', x), numeric: ([z]) => cx(Math.floor(z!.re)) },
  ceiling: { eval: (x) => evalFloorCeil('ceiling', x), numeric: ([z]) => cx(Math.ceil(z!.re)) },
  atan2: {
    eval: evalAtan2,
    partials: ([y, x], i) =>
      i === 0 ? mul(x!, pow(add(pow(x!, 2), pow(y!, 2)), -1)) : mul(-1, y!, pow(add(pow(x!, 2), pow(y!, 2)), -1)),
    numeric: ([y, x]) => cx(Math.atan2(y!.re, x!.re)),
  },
  Min: { eval: (...a) => evalMinMax('Min', ...a), numeric: (a) => cx(Math.min(...a.map((v) => v.re))) },
  Max: { eval: (...a) => evalMinMax('Max', ...a), numeric: (a) => cx(Math.max(...a.map((v) => v.re))) },
};

for (const [name, spec] of Object.entries(SPECS) as [FnName, Spec][]) {
  if (spec.eval) evaluators[name] = spec.eval;
  if (spec.partials) fnPartials[name] = spec.partials;
  if (spec.numeric) numericFns[name] = spec.numeric;
  if (spec.conjugate) conjugateCommutes.add(name);
}

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
export const zeta = (s: ExprLike): Expr => fn('zeta', [s]);
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
  if (p!.key === q!.key) return S.Zero;
  return undefined;
};
export const ceiling = (x: ExprLike): Expr => fn('ceiling', [x]);
export const atan2 = (y: ExprLike, x: ExprLike): Expr => fn('atan2', [y, x]);
export const Min = (...xs: ExprLike[]): Expr => fn('Min', xs);
export const Max = (...xs: ExprLike[]): Expr => fn('Max', xs);

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
    if (y instanceof Fn && y.name === 'gamma') {
      const a = y.args[0]!;
      if (a instanceof Rational && (a.p < 0n ? -a.p : a.p) > a.q) {
        const n = a.p >= 0n ? a.p / a.q : -((-a.p + a.q - 1n) / a.q);
        const frac = R(a.p - n * a.q, a.q);
        return mul(fn('gamma', [frac]), fn('rf', [frac, R(n)]));
      }
      if (a instanceof Add && isNum(a.args[0]!)) {
        let coeff = a.args[0] as Rational;
        let tail: Expr[] = a.args.slice(1) as Expr[];
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
        if (isInt(k!) && k.isPositive) {
          return mul(...Array.from({ length: Number(k.p) }, (_, i) => add(n!, -i)), R(1n, factorialBig(k.p)));
        }
      }
      if (y.name === 'harmonic' && y.args.length === 1) {
        const [c, rest] = splitAddInt(y.args[0]!);
        if (c !== 0n) {
          const base = fn('harmonic', [rest]);
          const terms: Expr[] = [base];
          if (c > 0n) for (let k = 1n; k <= c; k++) terms.push(pow(add(rest, R(k)), -1));
          else for (let k = 0n; k < -c; k++) terms.push(mul(-1, pow(add(rest, R(-k)), -1)));
          return add(...terms);
        }
      }
      if (y.name === 'expint' && isInt(y.args[0]!) && (y.args[0] as Rational).p > 1n) {
        const n = (y.args[0] as Rational).p;
        const z = y.args[1]!;
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
  if (e instanceof Add && isInt(e.args[0]!)) return [(e.args[0] as Rational).p, add(...e.args.slice(1))];
  return [0n, e];
}

impl.expandFunc = expandFunc;
impl.sign = sign;
