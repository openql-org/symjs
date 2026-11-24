// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Bessel and Airy functions (SymPy functions/special/bessel.py):
 * besselj, bessely, besseli, besselk, hankel1, hankel2, airyai, airybi,
 * airyaiprime, airybiprime and marcumq with SymPy's evaluation rules,
 * derivatives, rewrites and numerics.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import { NotImplementedError } from '../../core/errors';
import { at, defined, first, pair } from '../../core/guard';
import '../../numeric/mpspecialfns';
import { isIntegerQ, isNegative, isPositive, isReal, isZero as isZeroQ } from '../../core/assumptions';
import type { ComplexValue as C, Expr, ExprLike } from '../../core/nodes';
import { Fn, Integral, Mul, Pow, Rational, S, Special, Sym, Dummy, registerFunctionHeads } from '../../core/nodes';
import { derivative } from '../../core/undef';
import { Sum } from '../../core/concrete';
import { SubsNode } from '../../core/subsnode';
import { add, couldExtractMinusSign, exp, mul, neg, pow, sqrt } from '../../core/ops';
import { fnPartials, fnTaylorAtZero } from '../../calculus/diff';
import { c as cx, cadd, cdiv, clog, cmul, cpow } from '../../numeric/complex';
import { numericFns } from '../../numeric/evalf';
import { mpFns } from '../../numeric/mpeval';
import * as M from '../../numeric/mpfun';
import { registerRewrite } from '../../simplify/rewrite';
import { expandMul } from '../../simplify/expand';
import { Ne, piecewise } from '../../core/logic';
import { abs, conjugate, conjugateCommutes, conjugateRules, evaluators, fn, log, re } from '../elementary/elementary';
import { extractBranchFactor, unpolarify } from '../elementary/complexes';
import { cgamma, funcExpanders } from './special';

type BName = 'besselj' | 'bessely' | 'besseli' | 'besselk';
type HName = 'hankel1' | 'hankel2';
/**
 * Extracts the order parameter from the Bessel function.
 *
 * @param e - The Bessel function application.
 * @returns The order of the Bessel function.
 * @throws TypeError when the expression is not a supported Bessel function.
 * @see SymPy `sympy.functions.special.bessel.BesselBase.order`
 */
export function order(e: Expr): Expr {
  if (!(e instanceof Fn) || !['besselj', 'bessely', 'besseli', 'besselk', 'hankel1', 'hankel2', 'jn', 'yn', 'hn1', 'hn2'].includes(e.name)) throw new TypeError('expected a Bessel function');
  return at(e.args, 0);
}
/**
 * Extracts the argument at which the Bessel function is evaluated.
 *
 * @param e - The Bessel function application.
 * @returns The argument of the Bessel function.
 * @throws TypeError when the expression is not a supported Bessel function.
 * @see SymPy `sympy.functions.special.bessel.BesselBase.argument`
 */
export function argument(e: Expr): Expr {
  order(e);
  return at(e.args, 1);
}
const isZero = (e: Expr) => e instanceof Rational && e.isZero;
const isOo = (e: Expr) => e instanceof Special && (e.name === 'oo' || e.name === '-oo');

/** w with z = I*w, or undefined (SymPy z.extract_multiplicatively(I)). */
function imagPart(z: Expr): Expr | undefined {
  if (z.key === S.I.key) return S.One;
  if (z instanceof Mul && z.args.some((a) => a.key === S.I.key)) return mul(...z.args.filter((a) => a.key !== S.I.key));
  return undefined;
}

/** SymPy besselj/bessely/besseli/besselk.eval. */
function evalBessel(name: BName) {
  const first = name === 'besselj' || name === 'besseli';
  return (nu: Expr, z: Expr): Expr | undefined => {
    if (isZeroQ(z) === true) {
      const reNu = re(nu);
      if (isZero(nu)) return first ? S.One : name === 'bessely' ? S.NegativeInfinity : S.Infinity;
      if (first) {
        if ((isIntegerQ(nu) === true && isZeroQ(nu) === false) || isPositive(reNu) === true) return S.Zero;
        if (isNegative(reNu) === true && isIntegerQ(nu) !== true) return S.ComplexInfinity;
        if (isZeroQ(reNu) === true && isZeroQ(nu) === false) return S.NaN;
        return undefined;
      }
      if (isZeroQ(reNu) === false) return S.ComplexInfinity;
      if (isZeroQ(reNu) === true) return S.NaN;
      return undefined;
    }
    const iz = imagPart(z);
    if (name === 'besselk' && !(nu instanceof Special) && isNegative(nu) === true) return fn(name, [neg(nu), z]);
    if (name === 'besselj' || name === 'bessely') {
      if (isOo(z)) return S.Zero;
      if (name === 'bessely' && iz !== undefined && isOo(iz)) {
        const s = iz instanceof Special && iz.name === 'oo' ? 1 : -1;
        return mul(exp(mul(s, S.I, S.Pi, add(nu, 1), S.Half)), S.Infinity);
      }
    } else if (name === 'besseli') {
      if (iz !== undefined && isOo(iz)) return S.Zero;
      if (z instanceof Special && z.name === 'oo') return S.Infinity;
      if (z instanceof Special && z.name === '-oo') return mul(pow(-1, nu), S.Infinity);
    } else if (isOo(z) || (iz !== undefined && isOo(iz))) {
      if (!(z instanceof Special && z.name === '-oo')) return S.Zero;
    }
    if (first && couldExtractMinusSign(z)) {
      // J_nu(-z) = z**nu (-z)**(-nu) J_nu(z), likewise I_nu
      return mul(pow(z, nu), pow(neg(z), neg(nu)), fn(name, [nu, neg(z)]));
    }
    if (isIntegerQ(nu) === true) {
      if (couldExtractMinusSign(nu)) {
        const m = neg(nu);
        if (name === 'besseli' || name === 'besselk') return fn(name, [m, z]);
        return mul(pow(-1, m), fn(name, [m, z]));
      }
      // J_n(I w) = I**n I_n(w) and I_n(I w) = I**(-n) J_n(-w)
      if (name === 'besselj' && iz !== undefined) return mul(pow(S.I, nu), fn('besseli', [nu, iz]));
      if (name === 'besseli' && iz !== undefined) return mul(pow(S.I, neg(nu)), fn('besselj', [nu, neg(iz)]));
    }
    if (!first) return undefined;
    // branch handling of polar arguments: J_nu(exp_polar(2*pi*I*n) z) = exp(2*pi*I*n*nu) J_nu(z), likewise I_nu
    if (isIntegerQ(nu) === true) {
      const nz = unpolarify(z);
      if (nz.key !== z.key) return fn(name, [nu, nz]);
    } else {
      const [nz, n] = extractBranchFactor(z);
      if (!isZero(n)) return mul(exp(mul(2, n, S.Pi, nu, S.I)), fn(name, [nu, nz]));
    }
    const nnu = unpolarify(nu);
    return nnu.key === nu.key ? undefined : fn(name, [nnu, z]);
  };
}

/** Local Frobenius expansions at zero, with z of valuation d. */
export function besselLocalExpansion(name: BName, order: Rational, z: Expr, d: number, n: number,
  monomial?: { base: Expr; coefficient: Expr; exponent: Expr }): Expr {
  const r = mul(S.Half, monomial?.coefficient ?? z);
  const power = (p: Expr): Expr => monomial === undefined ? pow(r, p) : mul(pow(r, p), pow(monomial.base, mul(monomial.exponent, p)));
  const nu = order.toNumber();
  const gamma = (a: Expr) => fn('gamma', [a]);
  const psi = (k: number) => fn('polygamma', [0, k + 1]);
  const terms: Expr[] = [];
  if (name === 'besselk' && !order.isInteger) {
    for (const a of [order, Rational.of(-order.p, order.q)]) {
      let c = mul(S.Half, gamma(a));
      for (let k = 0; d * (2 * k - a.value) < n; k++) {
        terms.push(mul(c, power(add(2 * k, neg(a)))));
        c = mul(c, pow(mul(k + 1, add(k + 1, neg(a))), -1));
      }
    }
    return add(...terms);
  }
  const y = name === 'bessely', kFunction = name === 'besselk';
  const j = name === 'besselj' || y;
  const sign = kFunction ? pow(-1, order) : S.One;
  if (y || kFunction) {
    let c = mul(gamma(order), y ? neg(pow(S.Pi, -1)) : S.Half);
    for (let k = 0; k < nu; k++) {
      terms.push(mul(c, power(Rational.of(2 * k - nu))));
      if (k + 1 < nu) c = mul(c, Rational.of(kFunction ? -1 : 1, (k + 1) * (nu - k - 1)));
    }
  }
  let c = pow(gamma(add(order, 1)), -1);
  const logr = monomial === undefined ? log(r) : add(log(r), mul(monomial.exponent, log(monomial.base)));
  for (let k = 0; d * (nu + 2 * k) < n; k++) {
    const p = add(order, 2 * k);
    if (y || kFunction) {
      const psiSum = add(psi(k), psi(nu + k));
      const factor = y ? neg(pow(S.Pi, -1)) : mul(S.Half, sign);
      if (monomial === undefined) terms.push(mul(c, factor, power(p), add(mul(-2, logr), psiSum)));
      else {
        const cp = mul(c, factor, pow(r, p));
        const coefficient = add(expandMul(mul(-2, cp, logr)), mul(cp, psiSum));
        terms.push(mul(pow(monomial.base, mul(monomial.exponent, p)), coefficient));
      }
    } else terms.push(mul(c, power(p)));
    c = mul(c, j ? -1 : 1, pow(mul(k + 1, add(order, k + 1)), -1));
  }
  return add(...terms);
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
  numericFns[name] = (args) => besselNumeric(name, ...pair(args));
  fnPartials[name] = (args, i) => {
    const [nu, z] = pair(args);
    if (i === 0) {
      if (nu instanceof Sym) return derivative(fn(name, [nu, z]), [[nu, 1]], true);
      const v = new Dummy('xi_1');
      return new SubsNode([derivative(fn(name, [v, z]), [[v, 1]], true), v, nu]);
    }
    const lo = fn(name, [add(nu, -1), z]);
    const hi = fn(name, [add(nu, 1), z]);
    if (name === 'besseli') return add(mul(S.Half, lo), mul(S.Half, hi));
    if (name === 'besselk') return add(mul(S.NegHalf, lo), mul(S.NegHalf, hi));
    return add(mul(S.Half, lo), mul(S.NegHalf, hi));
  };
}

evaluators.airyai = (z) => {
  if (isZero(z)) return mul(pow(3, Rational.of(1, 3)), pow(mul(3, fn('gamma', [Rational.of(2, 3)])), -1));
  if (isOo(z)) return S.Zero;
  return undefined;
};
evaluators.airybi = (z) => {
  if (isZero(z)) return mul(pow(3, Rational.of(5, 6)), pow(mul(3, fn('gamma', [Rational.of(2, 3)])), -1));
  if (z instanceof Special && z.name === 'oo') return S.Infinity;
  if (z instanceof Special && z.name === '-oo') return S.Zero;
  return undefined;
};
evaluators.airyaiprime = (z) => {
  if (isZero(z)) return mul(-1, pow(3, Rational.of(2, 3)), pow(mul(3, fn('gamma', [Rational.of(1, 3)])), -1));
  if (z instanceof Special && z.name === 'oo') return S.Zero;
  return undefined;
};
evaluators.airybiprime = (z) => {
  if (isZero(z)) return mul(pow(3, Rational.of(1, 6)), pow(fn('gamma', [Rational.of(1, 3)]), -1));
  if (z instanceof Special && z.name === 'oo') return S.Infinity;
  if (z instanceof Special && z.name === '-oo') return S.Zero;
  return undefined;
};
fnPartials.airyai = (args) => fn('airyaiprime', [first(args)]);
fnPartials.airybi = (args) => fn('airybiprime', [first(args)]);
fnPartials.airyaiprime = (args) => mul(first(args), fn('airyai', [first(args)]));
fnPartials.airybiprime = (args) => mul(first(args), fn('airybi', [first(args)]));
numericFns.airyai = (args) => airyNumeric('ai', first(args));
numericFns.airybi = (args) => airyNumeric('bi', first(args));
numericFns.airyaiprime = (args) => airyNumeric('aip', first(args));
numericFns.airybiprime = (args) => airyNumeric('bip', first(args));
for (const n of ['airyai', 'airybi', 'airyaiprime', 'airybiprime'] as const) conjugateCommutes.add(n);
// Maclaurin coefficients (SymPy airyai.taylor_term and airybi.taylor_term without previous terms):
// Ai: 3**(n/3)/(3**(2/3)*pi) * gamma((n + 1)/3) * sin(2*pi*(n + 1)/3)/n!, Bi: 3**(n/3)/(3**(1/6)*pi) * gamma((n + 1)/3) * |sin(2*pi*(n + 1)/3)|/n!
const airyTaylor = (kind: 'ai' | 'bi') => (n: number): Expr => {
  const s = fn('sin', [mul(Rational.of(2 * (n + 1), 3), S.Pi)]);
  const pre = kind === 'ai' ? pow(mul(pow(3, Rational.of(2, 3)), S.Pi), -1) : pow(mul(pow(3, Rational.of(1, 6)), S.Pi), -1);
  return mul(pre, fn('gamma', [Rational.of(n + 1, 3)]), kind === 'ai' ? s : abs(s), pow(fn('factorial', [n]), -1), pow(pow(3, Rational.of(1, 3)), n));
};
fnTaylorAtZero.airyai = airyTaylor('ai');
fnTaylorAtZero.airybi = airyTaylor('bi');

// ---- Hankel functions ----------------------------------------------------------------

for (const name of ['hankel1', 'hankel2'] as const) {
  // d/dz H(nu, z) = H(nu - 1, z)/2 - H(nu + 1, z)/2 (SymPy BesselBase.fdiff with _a = _b = 1)
  fnPartials[name] = (args, i) => {
    if (i === 0) throw new NotImplementedError(`diff: ${name} w.r.t. its order`);
    const [nu, z] = pair(args);
    return add(mul(S.Half, fn(name, [add(nu, -1), z])), mul(S.NegHalf, fn(name, [add(nu, 1), z])));
  };
  const sign = name === 'hankel1' ? 1 : -1;
  // H(1,2)(nu, z) = J(nu, z) +- I*Y(nu, z)
  numericFns[name] = (args) => {
    const [nu, z] = pair(args);
    return cadd(besselNumeric('besselj', nu, z), cmul(cx(0, sign), besselNumeric('bessely', nu, z)));
  };
  mpFns[name] = (args, p) => {
    const wp = p + 10;
    const j = defined(mpFns['besselj'], 'mp besselj')(args, wp);
    const y = defined(mpFns['bessely'], 'mp bessely')(args, wp);
    return M.cadd(j, M.cmul(sign === 1 ? M.CI : M.cneg(M.CI), y, wp), p);
  };
}

/** SymPy BesselBase._eval_conjugate: f(conjugate(nu), conjugate(z)) unless z may be negative (hankel1 and hankel2 swap). */
const besselConjugate = (name: BName | HName, target: BName | HName) => (args: readonly Expr[]): Expr => {
  const [nu, z] = pair(args);
  if (isNegative(z) === false) return fn(target, [conjugate(nu), conjugate(z)]);
  return new Fn('conjugate', [new Fn(name, args)]);
};
for (const name of ['besselj', 'bessely', 'besseli', 'besselk'] as const) conjugateRules[name] = besselConjugate(name, name);
conjugateRules.hankel1 = besselConjugate('hankel1', 'hankel2');
conjugateRules.hankel2 = besselConjugate('hankel2', 'hankel1');

// ---- rewrites ----------------------------------------------------------------------

/** sqrt(2*z/pi) * f(nu - 1/2, z): besselj and bessely in terms of jn and yn. */
const asSpherical = (target: 'jn' | 'yn') => (args: readonly Expr[]): Expr => {
  const [nu, z] = pair(args);
  return mul(sqrt(mul(2, z, pow(S.Pi, -1))), fn(target, [add(nu, S.NegHalf), z]));
};
// SymPy sin, cos, tan, cot, sec and csc _eval_rewrite_as_besselj
const besselHalf = (z: Expr, nu: Expr): Expr => fn('besselj', [nu, z]);
const sqrtHalfPi = (z: Expr): Expr => sqrt(mul(S.Pi, z, S.Half));
registerRewrite('sin', 'besselj', ([z]) => z && mul(sqrtHalfPi(z), besselHalf(z, S.Half)));
registerRewrite('cos', 'besselj', ([z]) => z && piecewise([mul(sqrtHalfPi(z), besselHalf(z, neg(S.Half))), Ne(z, 0)], [1, true]));
registerRewrite('tan', 'besselj', ([z]) => z && mul(besselHalf(z, S.Half), pow(besselHalf(z, neg(S.Half)), -1)));
registerRewrite('cot', 'besselj', ([z]) => z && mul(besselHalf(z, neg(S.Half)), pow(besselHalf(z, S.Half), -1)));
registerRewrite('sec', 'besselj', ([z]) => z && piecewise([pow(mul(sqrt(mul(S.Pi, z)), pow(sqrt(2), -1), besselHalf(z, neg(S.Half))), -1), Ne(z, 0)], [1, true]));
registerRewrite('csc', 'besselj', ([z]) => z && mul(sqrt(mul(2, pow(S.Pi, -1))), pow(mul(sqrt(z), besselHalf(z, S.Half)), -1)));
registerRewrite('besselj', 'jn', asSpherical('jn'));
registerRewrite('bessely', 'yn', asSpherical('yn'));
// besselj(nu, z) = csc(pi*nu)*bessely(-nu, z) - cot(pi*nu)*bessely(nu, z) and bessely in terms of besselj (nu not an integer)
registerRewrite('besselj', 'bessely', (args) => {
  const [nu, z] = pair(args);
  if (isIntegerQ(nu) !== false) return undefined;
  const t = mul(S.Pi, nu);
  return add(mul(fn('csc', [t]), fn('bessely', [neg(nu), z])), mul(-1, fn('cot', [t]), fn('bessely', [nu, z])));
});
registerRewrite('bessely', 'besselj', (args) => {
  const [nu, z] = pair(args);
  if (isIntegerQ(nu) !== false) return undefined;
  const t = mul(S.Pi, nu);
  return mul(fn('csc', [t]), add(mul(fn('cos', [t]), fn('besselj', [nu, z])), mul(-1, fn('besselj', [neg(nu), z]))));
});
// besselk(nu, z) = pi*csc(pi*nu)*(besseli(-nu, z) - besseli(nu, z))/2 (nu not an integer)
registerRewrite('besselk', 'besseli', (args) => {
  const [nu, z] = pair(args);
  if (isIntegerQ(nu) !== false) return undefined;
  return mul(S.Pi, S.Half, fn('csc', [mul(S.Pi, nu)]), add(fn('besseli', [neg(nu), z]), mul(-1, fn('besseli', [nu, z]))));
});

// SymPy besselj/besseli._eval_rewrite_as_besseli/besselj.
registerRewrite('besselj', 'besseli', (args) => {
  const [nu, z] = pair(args);
  return mul(exp(mul(S.Half, S.I, S.Pi, nu)), fn('besseli', [nu, mul(fn('exp_polar', [mul(S.NegHalf, S.I, S.Pi)]), z)]));
});
registerRewrite('besseli', 'besselj', (args) => {
  const [nu, z] = pair(args);
  return mul(exp(mul(S.NegHalf, S.I, S.Pi, nu)), fn('besselj', [nu, mul(fn('exp_polar', [mul(S.Half, S.I, S.Pi)]), z)]));
});

// ---- expand_func ----------------------------------------------------------------------

/** The recurrence coefficients (_a, _b) of SymPy's Bessel classes. */
const RECURRENCE: Record<BName | HName, [number, number]> = { besselj: [1, 1], bessely: [1, 1], besseli: [-1, 1], besselk: [1, -1], hankel1: [1, 1], hankel2: [1, 1] };

/** SymPy BesselBase._eval_expand_func: reduce a real order to (-1, 1] by the recurrence. */
function expandBessel(name: BName | HName, nu: Expr, z: Expr): Expr {
  const [a, b] = RECURRENCE[name];
  const f = (k: number) => expandBessel(name, add(nu, k), z);
  if (isReal(nu) === true && !isOo(nu)) {
    if (isPositive(add(nu, -1)) === true) return add(mul(-a * b, f(-2)), mul(mul(2 * a, add(nu, -1), f(-1)), pow(z, -1)));
    if (isNegative(add(nu, 1)) === true) return add(mul(mul(2 * b, add(nu, 1), f(1)), pow(z, -1)), mul(-a * b, f(2)));
  }
  return fn(name, [nu, z]);
}
for (const name of ['besselj', 'bessely', 'besseli', 'besselk', 'hankel1', 'hankel2'] as const) funcExpanders[name] = (args) => expandBessel(name, ...pair(args));

// ---- Marcum Q-function -----------------------------------------------------------------

/** SymPy marcumq.eval. */
evaluators.marcumq = (m, ...ab) => {
  const [a, b] = pair(ab);
  const bothZero = isZeroQ(m) === true && isZeroQ(b) === true;
  if (isZeroQ(a) === true) {
    if (bothZero) return S.Zero;
    return mul(fn('uppergamma', [m, mul(pow(b, 2), S.Half)]), pow(fn('gamma', [m]), -1));
  }
  if (bothZero) return add(1, mul(-1, pow(exp(mul(pow(a, 2), S.Half)), -1)));
  if (a.key === b.key) {
    const a2 = pow(a, 2);
    const e = exp(neg(a2));
    if (m.key === S.One.key) return mul(S.Half, add(1, mul(e, fn('besseli', [0, a2]))));
    if (m.key === Rational.of(2).key) return add(S.Half, mul(S.Half, e, fn('besseli', [0, a2])), mul(e, fn('besseli', [1, a2])));
  }
  return undefined;
};
fnPartials.marcumq = (args, i) => {
  const [m, a, b] = [at(args, 0), at(args, 1), at(args, 2)];
  // d/da Q = a*(Q(m + 1) - Q(m)), d/db Q = -b**m/a**(m - 1)*exp(-(a**2 + b**2)/2)*besseli(m - 1, a*b)
  if (i === 1) return mul(a, add(mul(-1, fn('marcumq', [m, a, b])), fn('marcumq', [add(1, m), a, b])));
  if (i === 2) return mul(-1, pow(b, m), pow(pow(a, add(m, -1)), -1), exp(mul(-1, add(pow(a, 2), pow(b, 2)), S.Half)), fn('besseli', [add(m, -1), mul(a, b)]));
  throw new NotImplementedError('diff: marcumq w.r.t. its order');
};
// marcumq(m, a, a) = 1/2 + exp(-a**2)*besseli(0, a**2)/2 + exp(-a**2)*sum(besseli(i, a**2), (i, 1, m - 1)) for an integer m >= 1
registerRewrite('marcumq', 'Integral', (args, _self, hints) => {
  const [m, a, b] = [at(args, 0), at(args, 1), at(args, 2)];
  const x = hints?.['x'] ?? new Dummy('x');
  return mul(pow(a, add(1, neg(m))), new Integral([
    mul(pow(x, m), exp(add(mul(S.NegHalf, pow(x, 2)), mul(S.NegHalf, pow(a, 2)))), besseli(add(m, -1), mul(a, x))), x, b, S.Infinity,
  ]));
});
registerRewrite('marcumq', 'Sum', (args, _self, hints) => {
  const [m, a, b] = [at(args, 0), at(args, 1), at(args, 2)];
  const k = hints?.['k'] ?? new Dummy('k');
  return mul(exp(mul(S.NegHalf, add(pow(a, 2), pow(b, 2)))), Sum(mul(pow(mul(a, pow(b, -1)), k), besseli(k, mul(a, b))), [k, add(1, neg(m)), S.Infinity]));
});
registerRewrite('marcumq', 'besseli', (args) => {
  const [m, a, b] = [at(args, 0), at(args, 1), at(args, 2)];
  if (a.key !== b.key || !(m instanceof Rational && m.isInteger && m.p >= 1n)) return undefined;
  const a2 = pow(a, 2);
  const e = exp(neg(a2));
  const terms = Array.from({ length: Number(m.p) - 1 }, (_, k) => fn('besseli', [k + 1, a2]));
  return add(S.Half, mul(S.Half, e, fn('besseli', [0, a2])), mul(e, add(...terms)));
});

for (const name of ['airyai', 'airybi', 'airyaiprime', 'airybiprime'] as const) {
  const prime = name.endsWith('prime'), bi = name.startsWith('airybi');
  const nu = Rational.of(prime ? 2 : 1, 3);
  const twoThirds = Rational.of(2, 3), threeHalves = Rational.of(3, 2);
  const scale = bi ? pow(3, S.NegHalf) : Rational.of(1, 3);
  registerRewrite(name, 'besselj', (args) => {
    const z = first(args);
    if (isNegative(re(z)) !== true) return undefined;
    const t = mul(twoThirds, pow(neg(z), threeHalves));
    const factor = prime ? bi ? neg(z) : z : sqrt(neg(z));
    return mul(scale, factor, add(besselj(neg(nu), t), mul(prime !== bi ? -1 : 1, besselj(nu, t))));
  });
  registerRewrite(name, 'besseli', (args) => {
    const z = first(args), a = pow(z, threeHalves), t = mul(twoThirds, a);
    if (isPositive(re(z)) === true) return mul(scale, prime ? z : sqrt(z),
      add(mul(!bi && prime ? -1 : 1, besseli(neg(nu), t)), mul(!bi && !prime ? -1 : 1, besseli(nu, t))));
    const low = pow(a, nu);
    const high = mul(pow(z, prime ? 2 : 1), pow(a, neg(nu)));
    return mul(scale, add(mul(!bi && prime ? -1 : 1, low, besseli(neg(nu), t)), mul(!bi && !prime ? -1 : 1, high, besseli(nu, t))));
  });
  funcExpanders[name] = (args) => {
    const z = first(args), symbols = z.freeSymbols();
    if (symbols.size !== 1) return undefined;
    const x = first([...symbols]);
    const factors = z instanceof Mul ? z.args : [z];
    const nested = factors.find((factor) => factor.has(x));
    if (!(nested instanceof Pow && nested.exp instanceof Rational && 3n * nested.exp.p % nested.exp.q === 0n)) return undefined;
    if (factors.some((factor) => factor !== nested && factor.has(x))) return undefined;
    const bases = nested.base instanceof Mul ? nested.base.args : [nested.base];
    const power = bases.find((base) => base.has(x));
    if (power === undefined || bases.some((base) => base !== power && base.has(x))) return undefined;
    const exponent = power.key === x.key ? S.One : power instanceof Pow && power.base.key === x.key && !power.exp.has(x) ? power.exp : undefined;
    if (exponent === undefined) return undefined;
    const principal = mul(pow(mul(...bases.filter((base) => base !== power)), nested.exp), pow(x, mul(exponent, nested.exp)));
    if (principal.key === nested.key) return undefined;
    const ratio = prime ? mul(principal, pow(nested, -1)) : mul(nested, pow(principal, -1));
    const argument = mul(principal, ...factors.filter((factor) => factor !== nested));
    const other = bi ? prime ? 'airyaiprime' : 'airyai' : prime ? 'airybiprime' : 'airybi';
    const coefficient = mul(bi ? sqrt(3) : pow(3, S.NegHalf), prime ? add(ratio, -1) : add(1, neg(ratio)));
    return mul(S.Half, add(mul(add(1, ratio), fn(name, [argument])), mul(coefficient, fn(other, [argument]))));
  };
}

/**
 * Computes the Bessel function of the first kind.
 *
 * @param nu - The order of the function.
 * @param z - The argument of the function.
 * @returns The Bessel J expression.
 * @see SymPy `sympy.functions.special.bessel.besselj`
 * @example
 * ```ts
 * import { besselj } from '@symjs/symjs';
 *
 * besselj(0, 0); // => 1
 * ```
 */
export const besselj = (nu: ExprLike, z: ExprLike): Expr => fn('besselj', [nu, z]);
/**
 * Computes the Bessel function of the second kind.
 *
 * @param nu - The order of the function.
 * @param z - The argument of the function.
 * @returns The Bessel Y expression.
 * @see SymPy `sympy.functions.special.bessel.bessely`
 * @example
 * ```ts
 * import { bessely } from '@symjs/symjs';
 *
 * bessely(0, 0); // => -oo
 * ```
 */
export const bessely = (nu: ExprLike, z: ExprLike): Expr => fn('bessely', [nu, z]);
/**
 * Computes the modified Bessel function of the first kind.
 *
 * @param nu - The order of the function.
 * @param z - The argument of the function.
 * @returns The modified Bessel I expression.
 * @see SymPy `sympy.functions.special.bessel.besseli`
 * @example
 * ```ts
 * import { besseli } from '@symjs/symjs';
 *
 * besseli(0, 0); // => 1
 * ```
 */
export const besseli = (nu: ExprLike, z: ExprLike): Expr => fn('besseli', [nu, z]);
/**
 * Computes the modified Bessel function of the second kind.
 *
 * @param nu - The order of the function.
 * @param z - The argument of the function.
 * @returns The modified Bessel K expression.
 * @see SymPy `sympy.functions.special.bessel.besselk`
 * @example
 * ```ts
 * import { besselk } from '@symjs/symjs';
 *
 * besselk(0, 0); // => oo
 * ```
 */
export const besselk = (nu: ExprLike, z: ExprLike): Expr => fn('besselk', [nu, z]);
/**
 * Computes the Airy Ai function.
 *
 * @param z - The argument of the function.
 * @returns The Ai expression.
 * @see SymPy `sympy.functions.special.bessel.airyai`
 * @example
 * ```ts
 * import { airyai, ex } from '@symjs/symjs';
 *
 * airyai(ex`oo`); // => 0
 * airyai(ex`-oo`); // => 0
 * ```
 */
export const airyai = (z: ExprLike): Expr => fn('airyai', [z]);
/**
 * Computes the Airy Bi function.
 *
 * @param z - The argument of the function.
 * @returns The Bi expression.
 * @see SymPy `sympy.functions.special.bessel.airybi`
 * @example
 * ```ts
 * import { airybi, ex } from '@symjs/symjs';
 *
 * airybi(ex`oo`); // => oo
 * airybi(ex`-oo`); // => 0
 * ```
 */
export const airybi = (z: ExprLike): Expr => fn('airybi', [z]);
/**
 * Computes the first derivative of the Airy Ai function.
 *
 * @param z - The argument of the function.
 * @returns The Ai derivative.
 * @see SymPy `sympy.functions.special.bessel.airyaiprime`
 * @example
 * ```ts
 * import { airyaiprime, ex } from '@symjs/symjs';
 *
 * airyaiprime(ex`oo`); // => 0
 * airyaiprime(ex`z`); // => airyaiprime(z)
 * ```
 */
export const airyaiprime = (z: ExprLike): Expr => fn('airyaiprime', [z]);
/**
 * Computes the first derivative of the Airy Bi function.
 *
 * @param z - The argument of the function.
 * @returns The Bi derivative.
 * @see SymPy `sympy.functions.special.bessel.airybiprime`
 * @example
 * ```ts
 * import { airybiprime, ex } from '@symjs/symjs';
 *
 * airybiprime(ex`oo`); // => oo
 * airybiprime(ex`-oo`); // => 0
 * ```
 */
export const airybiprime = (z: ExprLike): Expr => fn('airybiprime', [z]);
/**
 * Evaluates the Hankel function of the first kind.
 *
 * @param nu - The order of the function.
 * @param z - The argument of the function.
 * @returns The value of the specified Hankel function.
 * @see SymPy `sympy.functions.special.bessel.hankel1`
 * @example
 * ```ts
 * import { ex, hankel1 } from '@symjs/symjs';
 *
 * hankel1(ex`nu`, ex`z`); // => hankel1(nu, z)
 * ```
 */
export const hankel1 = (nu: ExprLike, z: ExprLike): Expr => fn('hankel1', [nu, z]);
/**
 * Evaluates the Hankel function of the second kind.
 *
 * @param nu - The order of the function.
 * @param z - The argument of the function.
 * @returns The value of the specified Hankel function.
 * @see SymPy `sympy.functions.special.bessel.hankel2`
 * @example
 * ```ts
 * import { ex, hankel2 } from '@symjs/symjs';
 *
 * hankel2(ex`nu`, ex`z`); // => hankel2(nu, z)
 * ```
 */
export const hankel2 = (nu: ExprLike, z: ExprLike): Expr => fn('hankel2', [nu, z]);
/**
 * Evaluates the generalized Marcum Q-function.
 *
 * @param m - The order.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The Marcum Q expression.
 * @see SymPy `sympy.functions.special.bessel.marcumq`
 * @example
 * ```ts
 * import { ex, marcumq } from '@symjs/symjs';
 *
 * marcumq(0, 0, 0); // => 0
 * marcumq(0, ex`a`, 0); // => 1 - exp(-a**2/2)
 * ```
 */
export const marcumq = (m: ExprLike, a: ExprLike, b: ExprLike): Expr => fn('marcumq', [m, a, b]);

registerFunctionHeads([
  ['besselj', besselj],
  ['bessely', bessely],
  ['besseli', besseli],
  ['besselk', besselk],
  ['airyai', airyai],
  ['airybi', airybi],
  ['airyaiprime', airyaiprime],
  ['airybiprime', airybiprime],
  ['hankel1', hankel1],
  ['hankel2', hankel2],
  ['marcumq', marcumq],
]);
