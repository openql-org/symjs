// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Three-valued assumption queries (true / false / undefined = unknown).
 */

import type { Expr } from './nodes';
import { Add, Constant, ExtensionExpr, Fn, Float, Mul, Piecewise, Pow, Rational, S, Special, Sym, impl } from './nodes';
import { at, pair } from './guard';

export type Tri = boolean | undefined;

const all = (xs: readonly Expr[], f: (e: Expr) => Tri): Tri => {
  let unknown = false;
  for (const x of xs) {
    const r = f(x);
    if (r === false) return false;
    if (r === undefined) unknown = true;
  }
  return unknown ? undefined : true;
};

/** Max and Min are one of their arguments (SymPy MinMaxBase): a property every argument has or none has. */
export const isMinMax = (e: Expr): e is Fn => e instanceof Fn && (e.name === 'Max' || e.name === 'Min');

/** SymPy _torf: true when every value is true, false when every value is false, else unknown. */
export function torf(xs: readonly Expr[], f: (e: Expr) => Tri): Tri {
  const vs = xs.map(f);
  if (vs.every((v) => v === true)) return true;
  return vs.every((v) => v === false) ? false : undefined;
}

export function isZero(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return e.isZero;
  if (e instanceof Special) return e.name === 'nan' ? undefined : false;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.zero;
  if (e instanceof Pow && e.base instanceof Constant && e.base.name === 'E') return false;
  // SymPy sign._eval_is_zero
  if (e instanceof Fn && e.name === 'sign') return isZero(at(e.args, 0));
  if (e instanceof Piecewise) return piecewiseTorf(e, isZero);
  if (e instanceof Fn && e.args.length === 1) {
    const a = at(e.args, 0);
    // functions vanishing exactly at 0 (and sin at the multiples of pi, cos between them)
    if (ZERO_AT_ZERO.has(e.name) && isZero(a) === true) return true;
    if (e.name === 'abs' || e.name === 'asinh' || e.name === 'atanh' || e.name === 'asin' || e.name === 'atan') {
      const z = isZero(a);
      if (z !== undefined) return z;
    }
    // a/pi, distributed over the terms of a
    const piMultiple = (): Expr => (a instanceof Add ? impl.add(...a.args.map((t) => impl.mul(t, impl.pow(S.Pi, -1)))) : impl.mul(a, impl.pow(S.Pi, -1)));
    if (e.name === 'sin' && isIntegerQ(piMultiple()) === true) return true;
    if (e.name === 'sinc') {
      const z = isZero(a);
      if (z === true) return false;
      if (z === false && isIntegerQ(piMultiple()) === true) return true;
    }
    if (e.name === 'cos' && isIntegerQ(impl.add(piMultiple(), Rational.of(-1n, 2n))) === true) return true;
    if (e.name === 'cos' && a instanceof Fn && a.name === 'asin') {
      const value = at(a.args, 0);
      if (value instanceof Rational && (value.isOne || value.equals(S.NegOne))) return true;
    }
    // SymPy log._eval_is_zero: log(a) = 0 exactly for a = 1
    if (e.name === 'log') {
      const d = isZero(impl.add(a, -1));
      if (d !== undefined) return d;
    }
    const v = numericValue(e);
    if (v !== undefined && Math.hypot(v.re, v.im) > 1e-8) return false;
  }
  // a function known to be positive or negative is not 0
  if (e instanceof Fn && (ODD_SIGN.has(e.name) || e.name === 'cosh' || e.name === 'sech' || isMinMax(e)) && (isPositive(e) === true || isNegative(e) === true)) return false;
  // SymPy frac._eval_is_zero: frac(x) = 0 exactly for an integer x
  if (e instanceof Fn && e.name === 'frac') {
    const a = at(e.args, 0);
    const z = isZero(a);
    const n = isIntegerQ(a);
    return z === true || n === true ? true : z === false && n === false ? false : undefined;
  }
  // SymPy LambertW._eval_is_zero: W_k(x) = 0 only for x = 0 on the principal branch
  if (e instanceof Fn && e.name === 'LambertW') {
    const z = isZero(at(e.args, 0));
    const k = e.args[1];
    if (k === undefined) return z;
    return z === false || isZero(k) === false ? false : undefined;
  }
  // SymPy Mul._eval_is_zero: a product of nonzero (finite) factors is not 0
  if (e instanceof Mul && all(e.args, isNonZero) === true) return false;
  // SymPy Pow._eval_is_zero: a nonzero finite base to a finite power is not 0
  if (e instanceof Pow && e.exp instanceof Rational && isNonZero(e.base) === true) return false;
  // SymPy Add._eval_is_zero: a sum of symbols known to be positive, negative or not an integer
  if (e instanceof Add && impl.freeSymbols(e).size > 0) {
    if (isIntegerQ(e) === false || isPositive(e) === true || isNegative(e) === true) return false;
  }
  return undefined;
}

export function isReal(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return true;
  // extended reals: oo and -oo behave as real for simplification purposes
  if (e instanceof Special) return e.name === 'oo' || e.name === '-oo' ? true : undefined;
  if (e instanceof Constant) return e.name !== 'I';
  if (e instanceof Sym) return e.assumptions.real;
  if (e instanceof Add) return all(e.args, isReal) ? true : undefined;
  if (e instanceof Mul) {
    // a product of reals and imaginary factors (I or imaginary symbols) is real for an even count of
    // imaginary factors, and not real for an odd count when every factor is nonzero
    let imaginary = 0;
    for (const a of e.args) {
      const r = isReal(a);
      if (r === true) continue;
      if (!((a instanceof Constant && a.name === 'I') || (a instanceof Sym && a.assumptions.imaginary === true))) return undefined;
      imaginary++;
    }
    if (imaginary % 2 === 0) return true;
    return all(e.args.filter((a) => !(a instanceof Constant)), isNonZero) ? false : undefined;
  }
  if (e instanceof Pow) {
    const [b, x] = e.args;
    if (isReal(b) && isIntegerQ(x)) return isZero(b) && isNegative(x) ? undefined : true;
    if (isPositive(b) && isReal(x)) return true;
    if (isNonNegative(b) && isPositive(x)) return true;
    return undefined;
  }
  if (e instanceof ExtensionExpr) return e.isRealSelf();
  // (oo, -oo and zoo are not real numbers, although isReal counts oo and -oo as extended reals)
  if (e instanceof Piecewise) return piecewiseTorf(e, (x) => (x instanceof Special ? (x.name === 'nan' ? undefined : false) : isReal(x)));
  if (e instanceof Fn) {
    const a = at(e.args, 0);
    switch (e.name) {
      case 'abs':
      case 're':
      case 'im':
      case 'arg':
        return true;
      case 'sin':
      case 'cos':
      case 'tan':
      case 'cot':
      case 'atan':
      case 'sinh':
      case 'conjugate':
      case 'asinh':
      case 'acot':
      case 'sech':
        return isReal(a) ? true : undefined;
      case 'cosh':
      case 'tanh': {
        if (isReal(a) === true) return true;
        if (e.name === 'tanh' && a instanceof Sym && a.assumptions0.get('extended_real') === true) return true;
        if (e.name === 'cosh' && isImaginaryValue(a)) return true;
        const apply = impl.fn;
        if (apply === undefined) return undefined;
        const y = apply('im', [a]);
        const angle = e.name === 'cosh' ? y : impl.mul(2, y);
        const vanishes = isZero(apply('sin', [angle]));
        return e.name === 'tanh' && vanishes === true && isZero(apply('re', [a])) !== false
          ? undefined : vanishes;
      }
      case 'sinc':
        return isReal(a) === true || isReal(impl.mul(S.I, a)) === true ? true : undefined;
      case 'log':
        return isPositive(a) ? true : undefined;
      // SymPy coth and csch: real for a real argument away from the pole at 0
      case 'coth':
      case 'csch':
        return isReal(a) === true && isNonZero(a) === true ? true : undefined;
      // SymPy sign._eval_is_integer and _eval_is_imaginary
      case 'sign':
        return isReal(a) === true ? true : isImaginaryValue(a) ? false : undefined;
      // the inverse functions on the part of the real axis where their values are finite and real
      case 'asin':
      case 'acos':
        return realOn(a, [-1, 'closed'], [1, 'closed']);
      case 'atanh':
        return realOn(a, [-1, 'open'], [1, 'open']);
      case 'acosh':
        return realOn(a, [1, 'closed'], undefined);
      case 'asech':
        return realOn(a, [0, 'open'], [1, 'closed']);
      case 'asec':
      case 'acsc': {
        const real = isReal(a);
        if (real !== true) return real;
        if (isIntegerQ(a) === true && isNonZero(a) === true) return true;
        return realOn(impl.pow(a, -1), [-1, 'closed'], [1, 'closed']);
      }
      case 'acoth': {
        if (isReal(a) !== true) return undefined;
        if (isPositive(add1(a, -1)) === true || isNegative(add1(a, 1)) === true) return true;
        return isNegative(add1(a, -1)) === true && isPositive(add1(a, 1)) === true ? false : undefined;
      }
      case 'LambertW':
        return lambertWReal(a, e.args[1]);
      case 'Max':
      case 'Min':
        return torf(e.args, isReal);
      // SymPy RoundFunction._eval_is_real and frac._eval_is_real
      case 'floor':
      case 'ceiling':
      case 'frac':
        return isReal(a);
      default:
        return numericNonReal(e);
    }
  }
  return undefined;
}

const add1 = (x: Expr, c: number): Expr => impl.add(x, c);
/** A nonzero imaginary value: I times a nonzero real, or an imaginary symbol. */
const isImaginaryValue = (x: Expr): boolean =>
  (x instanceof Sym && x.assumptions.imaginary === true) || (isReal(impl.mul(S.I, x)) === true && isNonZero(x) === true);

/**
 * Whether a function whose real values are those of a real argument within the bounds is real
 * there: true inside, false for a real argument outside, else undefined.
 */
function realOn(a: Expr, lo: readonly [number, 'open' | 'closed'], hi: readonly [number, 'open' | 'closed'] | undefined): Tri {
  if (isReal(a) !== true) return undefined;
  const above = (b: readonly [number, 'open' | 'closed']): Tri => (b[1] === 'open' ? isPositive : isNonNegative)(add1(a, -b[0]));
  const below = (b: readonly [number, 'open' | 'closed']): Tri => (b[1] === 'open' ? isNegative : isNonPositive)(add1(a, -b[0]));
  const inLo = above(lo);
  const inHi = hi === undefined ? true : below(hi);
  if (inLo === true && inHi === true) return true;
  if (inLo === false || inHi === false || isNegative(add1(a, -lo[0])) === true
    || hi !== undefined && isPositive(add1(a, -hi[0])) === true) return false;
  return undefined;
}

/** cosh(a + I*b) is real when sin(b)*sinh(a) vanishes. */
function coshSign(a: Expr, sign: 1 | -1): Tri {
  if (isReal(a) === true) return sign === 1;
  const apply = impl.fn;
  if (apply === undefined) return undefined;
  const y = apply('im', [a]);
  if (isIntegerQ(impl.mul(y, impl.pow(impl.mul(2, S.Pi), -1))) === true) return sign === 1;
  const cosine = apply('cos', [y]);
  if (cosine.equals(S.One) || cosine.equals(S.NegOne)) return cosine.equals(S.One) === (sign === 1);
  if (isZero(apply('re', [a])) === true) return (sign === 1 ? isPositive : isNegative)(cosine);
  return undefined;
}

/** Functions with the sign of a real argument (SymPy sinh, tanh, coth, csch, atan and sign _eval_is_positive/_eval_is_negative). */
const ODD_SIGN = new Set(['sinh', 'tanh', 'coth', 'csch', 'atan', 'sign']);
const oddSign = (e: Fn, f: (x: Expr) => Tri): Tri => {
  const a = at(e.args, 0);
  return ODD_SIGN.has(e.name) && e.args.length === 1 && isReal(a) === true ? f(a) : undefined;
};

/**
 * SymPy Max and Min signs: Max is positive when one argument is and negative when all are (Min
 * the other way round); `some` names the function for which one argument decides.
 */
function minMaxSign(e: Fn, f: (x: Expr) => Tri, some: 'Max' | 'Min'): Tri {
  if (!isMinMax(e)) return undefined;
  const vs = e.args.map(f);
  if (e.name === some) return vs.includes(true) ? true : vs.every((v) => v === false) ? false : undefined;
  return vs.every((v) => v === true) ? true : vs.includes(false) ? false : undefined;
}

/** The value of a function of numbers, when it can be computed (undefined otherwise). */
function numericValue(e: Fn): { re: number; im: number } | undefined {
  if (numericValues.has(e)) return numericValues.get(e);
  let r: { re: number; im: number } | undefined;
  if (impl.freeSymbols(e).size === 0) {
    try {
      const v = impl.toComplex(e);
      r = Number.isFinite(v.re) && Number.isFinite(v.im) ? v : undefined;
    } catch {
      r = undefined;
    }
  }
  numericValues.set(e, r);
  return r;
}
const numericValues = new WeakMap<Expr, { re: number; im: number } | undefined>();

/** false for a function of numbers whose value has a clearly nonzero imaginary part, else undefined (also for polar numbers). */
function numericNonReal(e: Fn): Tri {
  if (isPolar(e)) return undefined;
  const v = numericValue(e);
  return v !== undefined && Math.abs(v.im) > 1e-8 * Math.max(1, Math.abs(v.re)) ? false : undefined;
}

/** The arguments of a Piecewise all have the property (true), none has it (false), else undefined (SymPy _eval_template_is_attr). */
const piecewiseTorf = (e: Piecewise, f: (x: Expr) => Tri): Tri => torf(e.pairs.map(([x]) => x), f);

/** Functions with f(0) = 0. */
const ZERO_AT_ZERO = new Set(['sin', 'tan', 'sinh', 'tanh', 'asin', 'atan', 'asinh', 'atanh', 'abs', 're', 'im']);

/** x <= 0 is known. */
const isNonPositive = (x: Expr): Tri => (isNegative(x) || isZero(x) || (x instanceof Sym && x.assumptions.nonpositive === true) ? true : isPositive(x) === true ? false : undefined);

/** SymPy LambertW._eval_is_extended_real for the branch k (undefined: the principal branch). */
function lambertWReal(x: Expr, k: Expr | undefined): Tri {
  // x + 1/e
  const shifted = impl.add(x, impl.pow(S.E, -1));
  if (k === undefined || isZero(k) === true) {
    if (isPositive(shifted) === true) return true;
    return isNonPositive(shifted) === true ? false : undefined;
  }
  if (k instanceof Rational && k.p === -1n && k.q === 1n) {
    if (isNegative(x) === true && isPositive(shifted) === true) return true;
    return isNonPositive(x) === true || isNonNegative(shifted) === true ? false : undefined;
  }
  return isNonZero(k) === true && isNonZero(impl.add(k, 1)) === true && isReal(x) === true ? false : undefined;
}

/**
 * The sign of log(a) and LambertW for isPositive (1) and isNegative (-1):
 * SymPy log._eval_is_extended_positive (a - 1 > 0) and log is real for a > 0;
 * a LambertW that is not real is neither positive nor negative, a real one
 * of numbers has the sign of its value (SymPy
 * Expr._eval_is_extended_positive_negative).
 */
function fnSign(e: Fn, sign: 1 | -1): Tri {
  if (e.name === 'log' && e.args.length === 1) {
    const a = at(e.args, 0);
    const d = impl.add(a, -1);
    if (sign === 1) return isPositive(d);
    return isPositive(a) === true ? isNegative(d) : isNonNegative(d) === true ? false : undefined;
  }
  if (e.name === 'LambertW') {
    // (a real LambertW of numbers is not 0: W(0) evaluates to 0)
    const real = isReal(e);
    if (real !== true || impl.freeSymbols(e).size > 0) return real === false ? false : undefined;
    const v = impl.toComplex(e).re;
    return sign === 1 ? v > 0 : v < 0;
  }
  const v = numericSign(e);
  if (v === undefined) return undefined;
  // SymPy is_positive = is_extended_positive and is_finite: an extended sign that holds is only
  // decided for a function SymPy knows to be finite there (besselj(1, 5).is_negative is None)
  return v === sign ? (FINITE_FNS.has(e.name) ? true : undefined) : false;
}

/** Functions whose real values SymPy knows to be finite (through _eval_is_finite or _eval_is_real). */
const FINITE_FNS = new Set([
  'sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'asin', 'acos', 'atan', 'acot', 'asec', 'acsc', 'sinc',
  'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch',
  'exp', 'log', 'erf', 'erfc', 'gamma', 'loggamma', 'polygamma', 'zeta', 'elliptic_k', 'elliptic_e',
  'fresnels', 'fresnelc', 'catalan', 'floor', 'ceiling', 'frac', 're', 'im',
]);

const numericSigns = new WeakMap<Expr, 1 | -1 | undefined>();

/**
 * SymPy Expr._eval_is_extended_positive_negative for a function of numbers: the sign of its real
 * value (evalf); undefined when the value is not a real Float (SymPy: a complex value has no
 * _prec and gives None) or cannot be computed.
 */
function numericSign(e: Fn): 1 | -1 | undefined {
  if (impl.freeSymbols(e).size > 0) return undefined;
  if (numericSigns.has(e)) return numericSigns.get(e);
  // (undecided while the value is computed, in case evalf asks for the sign again)
  numericSigns.set(e, undefined);
  let r: 1 | -1 | undefined;
  try {
    const v = impl.evalf(e, 15);
    if (v instanceof Float && !v.isZero) r = v.isPositive ? 1 : -1;
  } catch {
    r = undefined;
  }
  numericSigns.set(e, r);
  return r;
}

export function isNonZero(e: Expr): Tri {
  const z = isZero(e);
  if (z !== undefined) return !z;
  if (isPositive(e) || isNegative(e)) return true;
  if (e instanceof Mul && e.args.some((a) => isZero(a) === true)) return false;
  if (e instanceof Pow) return isNonZero(e.base);
  return undefined;
}

/**
 * SymPy is_polar: polar symbols, exp_polar, polar_lift and principal_branch, powers of a polar
 * base and products of polar and positive factors with at least one polar factor.
 */
export function isPolar(e: Expr): boolean {
  if (e instanceof Sym) return e.assumptions.polar === true;
  if (e instanceof Fn) return e.name === 'polar_lift' || e.name === 'principal_branch' || e.name === 'exp_polar';
  if (e instanceof Pow) return isPolar(e.base);
  return e instanceof Mul && e.args.some(isPolar) && e.args.every((f) => isPolar(f) || isPositive(f) === true);
}

/**
 * The sign of a sum without symbols, decided numerically as SymPy's
 * Expr._eval_is_extended_positive_negative does: 1 or -1 for a real value clearly away
 * from 0, 0 for a value that is clearly not real (neither positive nor negative), and
 * undefined when the value is too close to 0 relative to its terms (or cannot be computed).
 */
function numberSign(e: Add): 1 | -1 | 0 | undefined {
  if (impl.freeSymbols(e).size > 0) return undefined;
  let re = 0;
  let im = 0;
  let scale = 1;
  try {
    for (const a of e.args) {
      const v = impl.toComplex(a);
      re += v.re;
      im += v.im;
      scale = Math.max(scale, Math.abs(v.re), Math.abs(v.im));
    }
  } catch {
    return undefined;
  }
  if (!Number.isFinite(re) || !Number.isFinite(im)) return undefined;
  const tol = 1e-10 * scale;
  if (Math.abs(im) > tol) return 0;
  if (Math.abs(im) > 0 || Math.abs(re) <= tol) return undefined;
  return re > 0 ? 1 : -1;
}

/**
 * SymPy _monotonic_sign for a symbol s or its negation -s, as [v, eps, nonneg, nonpos]: the
 * value is at least v (or more than v when eps is 1) when it is nonnegative, at most v (or less
 * than v when eps is -1) when it is nonpositive; 1 for a positive integer, -1 for a negative
 * integer, an infinitesimal for other signed symbols and 0 for nonnegative or nonpositive ones.
 */
type Bound = [v: Rational, eps: -1 | 0 | 1, nonneg: boolean, nonpos: boolean];
function monotonicSign(e: Expr): Bound | undefined {
  if (e instanceof Mul && e.args.length === 2) {
    const [c, s] = e.args;
    if (c instanceof Rational && c.p === -1n && c.q === 1n && s instanceof Sym) {
      const b = monotonicSign(s);
      return b && [Rational.of(-b[0].p, b[0].q), b[1] === 0 ? 0 : b[1] === 1 ? -1 : 1, b[3], b[2]];
    }
  }
  if (!(e instanceof Sym) || e.assumptions.commutative === false) return undefined;
  const a = e.assumptions;
  if (a.positive) return a.integer ? [Rational.of(1n), 0, true, false] : [Rational.of(0n), 1, true, false];
  if (a.negative) return a.integer ? [Rational.of(-1n), 0, false, true] : [Rational.of(0n), -1, false, true];
  if (a.nonnegative || a.nonpositive) return [Rational.of(0n), 0, a.nonnegative === true, a.nonpositive === true];
  return undefined;
}

/**
 * SymPy Add._eval_is_extended_positive (negative, nonnegative, nonpositive) for c + a with a
 * rational c and a signed symbol a: the sign of c + _monotonic_sign(a). 1 when the sum is
 * positive, -1 when negative, 0.5 when nonnegative, -0.5 when nonpositive, undefined otherwise.
 */
function addBoundSign(e: Add): 1 | -1 | 0.5 | -0.5 | undefined {
  if (e.args.length !== 2) return undefined;
  const [c, a] = pair(e.args);
  if (!(c instanceof Rational)) return undefined;
  const b = monotonicSign(a);
  if (b === undefined) return undefined;
  const [v, eps, nonneg, nonpos] = b;
  // the sign of v + c + eps (c is nonzero in a canonical Add)
  const num = v.p * c.q + c.p * v.q;
  const sg = num > 0n ? 1 : num < 0n ? -1 : eps;
  if (nonneg && sg > 0) return 1;
  if (nonpos && sg < 0) return -1;
  if (sg === 0) return nonneg ? 0.5 : -0.5;
  return undefined;
}

export function isPositive(e: Expr): Tri {
  if (e instanceof Piecewise) return piecewiseTorf(e, isPositive);
  if (e instanceof Rational || e instanceof Float) return e.isPositive;
  if (e instanceof Special) return e.name === 'oo' ? true : e.name === '-oo' ? false : undefined;
  if (e instanceof Constant) return e.name === 'I' ? false : true;
  if (e instanceof Sym) return e.assumptions.positive ? true : e.assumptions.nonpositive ? false : undefined;
  if (e instanceof Add) {
    if (all(e.args, isPositive)) return true;
    const bs = addBoundSign(e);
    if (bs !== undefined) return bs === 1 ? true : bs < 0 ? false : undefined;
    const sg = numberSign(e);
    return sg === undefined ? undefined : sg === 1;
  }
  if (e instanceof Mul) {
    let neg = 0;
    for (const a of e.args) {
      if (isPositive(a)) continue;
      if (isNegative(a)) neg++;
      else return undefined;
    }
    return neg % 2 === 0;
  }
  if (e instanceof Pow) {
    const [b, x] = e.args;
    if (isPositive(b) && isReal(x)) return true;
    if (isReal(b) && isNonZero(b) && x instanceof Rational && x.isInteger && x.p % 2n === 0n) return true;
    // SymPy Pow._eval_is_extended_positive: a negative base to an odd power is negative
    if (isNegative(b) && x instanceof Rational && x.isInteger) return false;
    return undefined;
  }
  if (e instanceof Fn) {
    if (e.name === 'abs') return isNonZero(at(e.args, 0)) ? true : undefined;
    // SymPy ceiling._eval_is_positive
    if (e.name === 'ceiling') return isPositive(at(e.args, 0));
    const s = oddSign(e, isPositive) ?? minMaxSign(e, isPositive, 'Max');
    if (s !== undefined) return s;
    // SymPy cosh and sech of a real argument
    if (e.name === 'cosh') return coshSign(at(e.args, 0), 1) ?? fnSign(e, 1);
    if (e.name === 'sech' && isReal(at(e.args, 0)) === true) return true;
    // SymPy acot._eval_is_positive: acot(0) = pi/2
    if (e.name === 'acot' && isReal(at(e.args, 0)) === true) return isNonNegative(at(e.args, 0));
    return fnSign(e, 1);
  }
  return undefined;
}

export function isNegative(e: Expr): Tri {
  if (e instanceof Piecewise) return piecewiseTorf(e, isNegative);
  if (e instanceof Rational || e instanceof Float) return e.isNegative;
  if (e instanceof Special) return e.name === '-oo' ? true : e.name === 'oo' ? false : undefined;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.negative ? true : e.assumptions.nonnegative ? false : undefined;
  if (e instanceof Add) {
    if (all(e.args, isNegative)) return true;
    const bs = addBoundSign(e);
    if (bs !== undefined) return bs === -1 ? true : bs > 0 ? false : undefined;
    const sg = numberSign(e);
    return sg === undefined ? undefined : sg === -1;
  }
  if (e instanceof Mul) {
    let neg = 0;
    for (const a of e.args) {
      if (isPositive(a)) continue;
      if (isNegative(a)) neg++;
      else return undefined;
    }
    return neg % 2 === 1;
  }
  if (e instanceof Pow) {
    // SymPy Pow._eval_is_extended_negative: 1/q < 0 for q < 0, b**x >= 0 for b > 0 and real x
    const [b, x] = e.args;
    if (x instanceof Rational && x.p === 1n && x.q === 2n) return false;
    if (isNegative(b) && x instanceof Rational && x.isInteger) return x.p % 2n !== 0n;
    if (isPositive(b) && isReal(x)) return false;
    if (isReal(b) && x instanceof Rational && x.isInteger && x.p % 2n === 0n) return false;
    return undefined;
  }
  if (e instanceof Fn) {
    // SymPy floor._eval_is_negative and frac._eval_is_negative
    if (e.name === 'floor') return isNegative(at(e.args, 0));
    if (e.name === 'frac') return false;
    const s = oddSign(e, isNegative) ?? minMaxSign(e, isNegative, 'Min');
    if (s !== undefined) return s;
    if (e.name === 'cosh') return coshSign(at(e.args, 0), -1) ?? fnSign(e, -1);
    if (e.name === 'sech' && isReal(at(e.args, 0)) === true) return false;
    if (e.name === 'acot' && isReal(at(e.args, 0)) === true) return isNegative(at(e.args, 0));
    return fnSign(e, -1);
  }
  return undefined;
}

export function isNonNegative(e: Expr): Tri {
  if (isPositive(e) || isZero(e)) return true;
  if (e instanceof Sym && e.assumptions.nonnegative) return true;
  if (e instanceof Sym && e.assumptions.negative) return false;
  if (e instanceof Fn && e.name === 'abs') return true;
  if (e instanceof Fn && isMinMax(e)) {
    const s = minMaxSign(e, isNonNegative, 'Max');
    if (s !== undefined) return s;
  }
  // SymPy sign._eval_is_nonnegative
  if (e instanceof Fn && e.name === 'sign' && isNonNegative(at(e.args, 0)) === true) return true;
  // SymPy floor._eval_is_nonnegative; frac(x) >= 0 for a real x
  if (e instanceof Fn && e.name === 'floor') return isNonNegative(at(e.args, 0));
  if (e instanceof Fn && e.name === 'frac' && isReal(at(e.args, 0)) === true) return true;
  if (e instanceof Add && (all(e.args, isNonNegative) || addBoundSign(e) === 0.5)) return true;
  if (e instanceof Mul) {
    if (all(e.args, isNonNegative)) return true;
    // SymPy Mul._eval_is_extended_nonnegative: an even number of nonpositive factors, the others nonnegative
    let nonpositive = 0;
    for (const a of e.args) {
      if (isNonNegative(a) === true) continue;
      if (isNonPositive(a) !== true) return undefined;
      nonpositive++;
    }
    return nonpositive % 2 === 0 ? true : undefined;
  }
  if (e instanceof Pow && isNonNegative(e.base) && isReal(e.exp)) return true;
  if (e instanceof Pow && isReal(e.base) && e.exp instanceof Rational && e.exp.isInteger && e.exp.p % 2n === 0n) {
    return true;
  }
  const n = isNegative(e);
  return n === true ? false : undefined;
}

export function isIntegerQ(e: Expr): Tri {
  if (e instanceof Rational) return e.isInteger;
  if (e instanceof Special) return false;
  if (e instanceof Float) return false;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.integer;
  if (e instanceof Add) {
    // SymPy Add._eval_is_integer: integers plus exactly one non-integer is not an integer
    const known = e.args.map(isIntegerQ);
    if (known.every((k) => k === true)) return true;
    return known.filter((k) => k === false).length === 1 && known.every((k) => k !== undefined) ? false : undefined;
  }
  if (e instanceof Mul) return all(e.args, isIntegerQ) ? true : undefined;
  if (e instanceof Pow) {
    if (isIntegerQ(e.base) && isIntegerQ(e.exp) && isNonNegative(e.exp)) return true;
  }
  if (isMinMax(e)) return torf(e.args, isIntegerQ);
  // SymPy sign._eval_is_integer
  if (e instanceof Fn && e.name === 'sign') return isReal(at(e.args, 0)) === true ? true : isImaginaryValue(at(e.args, 0)) ? false : undefined;
  // SymPy RoundFunction._eval_is_integer and frac._eval_is_integer
  if (e instanceof Fn && (e.name === 'floor' || e.name === 'ceiling')) return isReal(at(e.args, 0)) === true ? true : undefined;
  if (e instanceof Fn && e.name === 'frac') return isIntegerQ(at(e.args, 0));
  return undefined;
}
impl.isReal = isReal;
