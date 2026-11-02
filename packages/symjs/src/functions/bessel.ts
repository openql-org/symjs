// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Bessel and Airy functions (SymPy functions/special/bessel.py):
 * besselj, bessely, besseli, besselk, airyai, airybi, airyaiprime and
 * airybiprime with SymPy's evaluation rules, derivatives and numerics.
 */

import '../numeric/mpspecialfns';
import { isIntegerQ, isPositive } from '../core/assumptions';
import { ComplexValue as C, Expr, ExprLike, Rational, S, Special } from '../core/nodes';
import { add, couldExtractMinusSign, mul, neg, pow } from '../core/ops';
import { fnPartials } from '../calculus/diff';
import { c as cx, cadd, cdiv, clog, cmul, cpow } from '../numeric/complex';
import { numericFns } from '../numeric/evalf';
import { conjugateCommutes, evaluators, fn } from './elementary';
import { cgamma } from './special';

type BName = 'besselj' | 'bessely' | 'besseli' | 'besselk';
const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const isZero = (e: Expr) => e instanceof Rational && e.isZero;
const isOo = (e: Expr) => e instanceof Special && (e.name === 'oo' || e.name === '-oo');

function evalBessel(name: BName) {
  return (nu: Expr, z: Expr): Expr | undefined => {
    if (isZero(z)) {
      if (name === 'besselj' || name === 'besseli') {
        if (isZero(nu)) return S.One;
        if ((nu instanceof Rational && nu.isPositive) || isPositive(nu) === true) return S.Zero;
        return undefined;
      }
      if (name === 'bessely' && isZero(nu)) return S.NegativeInfinity;
      if (name === 'besselk' && isZero(nu)) return S.Infinity;
      return undefined;
    }
    if ((name === 'besselj' || name === 'bessely') && isOo(z) && isInt(nu)) return S.Zero;
    // negative integer order
    if (couldExtractMinusSign(nu) && isIntegerQ(nu) === true) {
      const m = neg(nu);
      if (name === 'besseli' || name === 'besselk') return fn(name, [m, z]);
      return mul(pow(-1, m), fn(name, [m, z]));
    }
    // integer order and negated argument: J_n(-z) = (-1)**n J_n(z), I_n(-z) = (-1)**n I_n(z)
    if ((name === 'besselj' || name === 'besseli') && isInt(nu) && couldExtractMinusSign(z)) {
      return mul(pow(-1, nu), fn(name, [nu, neg(z)]));
    }
    return undefined;
  };
}

// ---- numerics (double precision series) -------------------------------------------

const cabs = (a: C) => Math.hypot(a.re, a.im);

/** sum_k s**k (z/2)**(2k + nu) / (k! Gamma(k + nu + 1)) with s = -1 (J) or 1 (I). */
function besselSeries(nu: C, z: C, sign: number): C {
  const h = cmul(z, cx(0.5));
  const h2 = cmul(h, h);
  let term = cdiv(cpow(h, nu), cgamma(cadd(nu, cx(1))));
  let sum = term;
  for (let k = 1; k < 500; k++) {
    term = cdiv(cmul(cmul(term, h2), cx(sign)), cmul(cx(k), cadd(nu, cx(k))));
    sum = cadd(sum, term);
    if (cabs(term) < 1e-17 * Math.max(cabs(sum), 1e-300)) break;
  }
  return sum;
}

function digammaInt(n: number): number {
  let s = -0.5772156649015329;
  for (let k = 1; k < n; k++) s += 1 / k;
  return s;
}

/** Y_n and K_n for integer n (limit formulas). */
function besselYKint(n: number, z: C, kind: 'Y' | 'K'): C {
  const h = cmul(z, cx(0.5));
  const lg = clog(h);
  const sign = kind === 'Y' ? -1 : 1;
  const Jn = besselSeries(cx(n), z, sign);
  const fact = (m: number) => {
    let r = 1;
    for (let i = 2; i <= m; i++) r *= i;
    return r;
  };
  let s1 = cx(0);
  for (let k = 0; k < n; k++) {
    const t = cmul(cx((kind === 'K' && k % 2 ? -1 : 1) * fact(n - k - 1) / fact(k)), cpow(h, cx(2 * k - n)));
    s1 = cadd(s1, t);
  }
  let s2 = cx(0);
  const h2 = cmul(h, h);
  let pw = cpow(h, cx(n));
  for (let k = 0; k < 300; k++) {
    const coeff = (digammaInt(k + 1) + digammaInt(n + k + 1)) / (fact(k) * fact(n + k));
    const t = cmul(cx(coeff * (kind === 'Y' ? (k % 2 ? -1 : 1) : 1)), pw);
    s2 = cadd(s2, t);
    pw = cmul(pw, h2);
    if (cabs(t) < 1e-17 * Math.max(cabs(s2), 1e-300) && k > 2) break;
  }
  if (kind === 'Y') {
    // Y_n = (2/pi) J_n ln(z/2) - (1/pi) s1 - (1/pi) s2
    return cadd(cmul(cx(2 / Math.PI), cmul(Jn, lg)), cmul(cx(-1 / Math.PI), cadd(s1, s2)));
  }
  // K_n = (-1)**(n+1) ln(z/2) I_n + s1/2 + (-1)**n s2/2
  const sg = n % 2 ? -1 : 1;
  return cadd(cadd(cmul(cx(-sg), cmul(lg, Jn)), cmul(cx(0.5), s1)), cmul(cx(0.5 * sg), s2));
}

function besselNumeric(name: BName, nu: C, z: C): C {
  if (name === 'besselj') return besselSeries(nu, z, -1);
  if (name === 'besseli') return besselSeries(nu, z, 1);
  const n = Math.round(nu.re);
  if (nu.im === 0 && Math.abs(nu.re - n) < 1e-14) return besselYKint(Math.abs(n), z, name === 'bessely' ? 'Y' : 'K');
  const s = Math.sin(Math.PI * nu.re);
  const negNu = cmul(cx(-1), nu);
  if (name === 'bessely') {
    const j = besselSeries(nu, z, -1);
    const jm = besselSeries(negNu, z, -1);
    return cdiv(cadd(cmul(j, cx(Math.cos(Math.PI * nu.re))), cmul(cx(-1), jm)), cx(s));
  }
  const i = besselSeries(nu, z, 1);
  const im = besselSeries(negNu, z, 1);
  return cmul(cx(Math.PI / 2 / s), cadd(im, cmul(cx(-1), i)));
}

/** Airy functions by their power series (f, g with Ai = c1 f - c2 g, Bi = sqrt(3) (c1 f + c2 g)). */
function airyNumeric(kind: 'ai' | 'bi' | 'aip' | 'bip', z: C): C {
  const c1 = 1 / (Math.pow(3, 2 / 3) * 1.3541179394264005); // Gamma(2/3)
  const c2 = 1 / (Math.pow(3, 1 / 3) * 2.678938534707747); // Gamma(1/3)
  const deriv = kind === 'aip' || kind === 'bip';
  // f = sum 3**k (1/3)_k z**(3k)/(3k)!, g = sum 3**k (2/3)_k z**(3k+1)/(3k+1)!
  let f = cx(0);
  let g = cx(0);
  const z3 = cmul(cmul(z, z), z);
  let tf = cx(1);
  let tg = z;
  for (let k = 0; k < 400; k++) {
    if (deriv) {
      // f' = sum 3**k (1/3)_k (3k) z**(3k-1)/(3k)!, g' = sum ... (3k+1) z**(3k)/(3k+1)!
      if (k > 0) f = cadd(f, cmul(cx(3 * k), cdiv(tf, z)));
      g = cadd(g, cmul(cx(3 * k + 1), cdiv(tg, z)));
    } else {
      f = cadd(f, tf);
      g = cadd(g, tg);
    }
    const nf = cmul(tf, cmul(z3, cx((3 * (k + 1 / 3)) / ((3 * k + 1) * (3 * k + 2) * (3 * k + 3)))));
    const ng = cmul(tg, cmul(z3, cx((3 * (k + 2 / 3)) / ((3 * k + 2) * (3 * k + 3) * (3 * k + 4)))));
    tf = nf;
    tg = ng;
    if (cabs(tf) + cabs(tg) < 1e-18 * (cabs(f) + cabs(g) + 1e-300)) break;
  }
  if (kind === 'ai' || kind === 'aip') return cadd(cmul(cx(c1), f), cmul(cx(-c2), g));
  return cmul(cx(Math.sqrt(3)), cadd(cmul(cx(c1), f), cmul(cx(c2), g)));
}

// ---- registration -------------------------------------------------------------------

for (const name of ['besselj', 'bessely', 'besseli', 'besselk'] as const) {
  evaluators[name] = evalBessel(name);
  numericFns[name] = ([nu, z]) => besselNumeric(name, nu!, z!);
  fnPartials[name] = ([nu, z], i) => {
    if (i === 0) throw new Error(`diff: ${name} w.r.t. its order`);
    const lo = fn(name, [add(nu!, -1), z!]);
    const hi = fn(name, [add(nu!, 1), z!]);
    if (name === 'besseli') return add(mul(S.Half, lo), mul(S.Half, hi));
    if (name === 'besselk') return add(mul(S.NegHalf, lo), mul(S.NegHalf, hi));
    return add(mul(S.Half, lo), mul(S.NegHalf, hi));
  };
}

evaluators.airyai = (z) => {
  if (isZero(z)) return mul(pow(3, Rational.of(1, 3)), pow(mul(3, fn('gamma', [Rational.of(2, 3)])), -1));
  if (z instanceof Special && z.name === 'oo') return S.Zero;
  return undefined;
};
evaluators.airybi = (z) => {
  if (isZero(z)) return mul(pow(3, Rational.of(5, 6)), pow(mul(3, fn('gamma', [Rational.of(2, 3)])), -1));
  if (z instanceof Special && z.name === 'oo') return S.Infinity;
  return undefined;
};
evaluators.airyaiprime = (z) => (isZero(z) ? mul(-1, pow(3, Rational.of(2, 3)), pow(mul(3, fn('gamma', [Rational.of(1, 3)])), -1)) : undefined);
evaluators.airybiprime = (z) => (isZero(z) ? mul(pow(3, Rational.of(1, 6)), pow(fn('gamma', [Rational.of(1, 3)]), -1)) : undefined);
fnPartials.airyai = ([z]) => fn('airyaiprime', [z!]);
fnPartials.airybi = ([z]) => fn('airybiprime', [z!]);
fnPartials.airyaiprime = ([z]) => mul(z!, fn('airyai', [z!]));
fnPartials.airybiprime = ([z]) => mul(z!, fn('airybi', [z!]));
numericFns.airyai = ([z]) => airyNumeric('ai', z!);
numericFns.airybi = ([z]) => airyNumeric('bi', z!);
numericFns.airyaiprime = ([z]) => airyNumeric('aip', z!);
numericFns.airybiprime = ([z]) => airyNumeric('bip', z!);
for (const n of ['airyai', 'airybi', 'airyaiprime', 'airybiprime'] as const) conjugateCommutes.add(n);


export const besselj = (nu: ExprLike, z: ExprLike): Expr => fn('besselj', [nu, z]);
export const bessely = (nu: ExprLike, z: ExprLike): Expr => fn('bessely', [nu, z]);
export const besseli = (nu: ExprLike, z: ExprLike): Expr => fn('besseli', [nu, z]);
export const besselk = (nu: ExprLike, z: ExprLike): Expr => fn('besselk', [nu, z]);
export const airyai = (z: ExprLike): Expr => fn('airyai', [z]);
export const airybi = (z: ExprLike): Expr => fn('airybi', [z]);
export const airyaiprime = (z: ExprLike): Expr => fn('airyaiprime', [z]);
export const airybiprime = (z: ExprLike): Expr => fn('airybiprime', [z]);
