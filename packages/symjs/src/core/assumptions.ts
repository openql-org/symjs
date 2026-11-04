// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Three-valued assumption queries (true / false / undefined = unknown).
 */

import type { Expr } from './nodes';
import { Add, Constant, ExtensionExpr, Fn, Float, Mul, Pow, Rational, S, Special, Sym, impl } from './nodes';
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

export function isZero(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return e.isZero;
  if (e instanceof Special) return e.name === 'nan' ? undefined : false;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.zero;
  if (e instanceof Pow && e.base instanceof Constant && e.base.name === 'E') return false;
  // SymPy LambertW._eval_is_zero: W_k(x) = 0 only for x = 0 on the principal branch
  if (e instanceof Fn && e.name === 'LambertW') {
    const z = isZero(at(e.args, 0));
    const k = e.args[1];
    if (k === undefined) return z;
    return z === false || isZero(k) === false ? false : undefined;
  }
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
  if (e instanceof Sym) return e.assumptions.real ? true : undefined;
  if (e instanceof Add) return all(e.args, isReal) ? true : undefined;
  if (e instanceof Mul) {
    // a product of reals is real; exactly one imaginary-unit factor makes it non-real
    let nonReal = 0;
    for (const a of e.args) {
      const r = isReal(a);
      if (r === undefined) return undefined;
      // isReal is false only for the imaginary unit
      if (r === false) nonReal++;
    }
    if (nonReal === 0) return true;
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
      case 'atan':
      case 'sinh':
      case 'cosh':
      case 'tanh':
      case 'conjugate':
      case 'asinh':
      case 'acot':
      case 'sech':
      case 'sinc':
        return isReal(a) ? true : undefined;
      case 'log':
        return isPositive(a) ? true : undefined;
      case 'LambertW':
        return lambertWReal(a, e.args[1]);
      default:
        return undefined;
    }
  }
  return undefined;
}

/** x <= 0 is known. */
const isNonPositive = (x: Expr): Tri => (isNegative(x) || isZero(x) ? true : isPositive(x) === true ? false : undefined);

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
  return undefined;
}

export function isNonZero(e: Expr): Tri {
  const z = isZero(e);
  if (z !== undefined) return !z;
  if (isPositive(e) || isNegative(e)) return true;
  if (e instanceof Mul) return all(e.args, isNonZero);
  if (e instanceof Pow) return isNonZero(e.base);
  return undefined;
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
    return fnSign(e, 1);
  }
  return undefined;
}

export function isNegative(e: Expr): Tri {
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
  if (e instanceof Fn) return fnSign(e, -1);
  return undefined;
}

export function isNonNegative(e: Expr): Tri {
  if (isPositive(e) || isZero(e)) return true;
  if (e instanceof Sym && e.assumptions.nonnegative) return true;
  if (e instanceof Sym && e.assumptions.negative) return false;
  if (e instanceof Fn && e.name === 'abs') return true;
  if (e instanceof Add && (all(e.args, isNonNegative) || addBoundSign(e) === 0.5)) return true;
  if (e instanceof Mul) return all(e.args, isNonNegative) ? true : undefined;
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
  return undefined;
}
impl.isReal = isReal;
