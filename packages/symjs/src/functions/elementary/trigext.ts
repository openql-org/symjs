// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Reciprocal trigonometric and hyperbolic functions, inverse
 * hyperbolic functions, acot/asec/acsc and sinc, plus the SymPy
 * evaluation rules that connect trigonometric and hyperbolic functions
 * (sin(I*x) = I*sinh(x), compositions with inverse functions, shifts by
 * I*pi/2).
 */

import type { Expr, ExprLike, FnName } from '../../core/nodes';
import { defined, first, pair } from '../../core/guard';
import { Add, Float, Fn, Mul, Rational, S, Special, registerFunctionHeads } from '../../core/nodes';
import { add, couldExtractMinusSign, mul, neg, pow, splitCoeff, sqrt } from '../../core/ops';
import { asCoefficient, asIndependent } from '../../core/methods';
import { NotImplementedError } from '../../core/errors';
import { expandMul } from '../../simplify/expand';
import type { Sym } from '../../core/nodes';
import { ratMod } from '../../core/num';
import { AccumBounds } from '../../core/accumbounds';
import { isIntegerQ, isReal } from '../../core/assumptions';
import { fact } from '../../core/exprfacts';
import { mapBottomUp } from '../../core/traverse';
import { fnPartials } from '../../calculus/diff';
import { numericFns } from '../../numeric/evalf';
import { mpFns } from '../../numeric/mpeval';
import * as F from '../../numeric/mpf';
import * as M from '../../numeric/mpfun';
import type { Mpc } from '../../numeric/mpfun';
import type { Evaluator } from './elementary';
import { acos, asin, atan, conjugateCommutes, cos, cosh, evaluators, fn, forEachEntry, im, log, re, sin, sinh, splitPiTerm, tan, tanh } from './elementary';

/**
 * Computes the cotangent.
 *
 * @param x - The argument of the function.
 * @returns The cotangent.
 * @see SymPy `sympy.functions.elementary.trigonometric.cot`
 * @example
 * ```ts
 * import { cot, ex } from '@symjs/symjs';
 *
 * cot(ex`pi/12`); // => sqrt(3) + 2
 * ```
 */
export const cot = (x: ExprLike): Expr => fn('cot', [x]);
/**
 * Computes the secant.
 *
 * @param x - The argument of the function.
 * @returns The secant.
 * @see SymPy `sympy.functions.elementary.trigonometric.sec`
 * @example
 * ```ts
 * import { sec } from '@symjs/symjs';
 *
 * sec(0); // => 1
 * ```
 */
export const sec = (x: ExprLike): Expr => fn('sec', [x]);
/**
 * Computes the cosecant.
 *
 * @param x - The argument of the function.
 * @returns The cosecant.
 * @see SymPy `sympy.functions.elementary.trigonometric.csc`
 * @example
 * ```ts
 * import { csc, ex } from '@symjs/symjs';
 *
 * csc(ex`pi/2`); // => 1
 * ```
 */
export const csc = (x: ExprLike): Expr => fn('csc', [x]);
/**
 * Computes the inverse cotangent.
 *
 * @param x - The argument of the function.
 * @returns The inverse cotangent.
 * @see SymPy `sympy.functions.elementary.trigonometric.acot`
 * @example
 * ```ts
 * import { acot } from '@symjs/symjs';
 *
 * acot(0); // => pi/2
 * acot(1); // => pi/4
 * ```
 */
export const acot = (x: ExprLike): Expr => fn('acot', [x]);
/**
 * Computes the inverse secant.
 *
 * @param x - The argument of the function.
 * @returns The inverse secant.
 * @see SymPy `sympy.functions.elementary.trigonometric.asec`
 * @example
 * ```ts
 * import { asec } from '@symjs/symjs';
 *
 * asec(1); // => 0
 * asec(0); // => zoo
 * ```
 */
export const asec = (x: ExprLike): Expr => fn('asec', [x]);
/**
 * Computes the inverse cosecant.
 *
 * @param x - The argument of the function.
 * @returns The inverse cosecant.
 * @see SymPy `sympy.functions.elementary.trigonometric.acsc`
 * @example
 * ```ts
 * import { acsc } from '@symjs/symjs';
 *
 * acsc(0); // => zoo
 * acsc(1); // => pi/2
 * ```
 */
export const acsc = (x: ExprLike): Expr => fn('acsc', [x]);
/**
 * Computes the hyperbolic cotangent.
 *
 * @param x - The argument of the function.
 * @returns The hyperbolic cotangent.
 * @see SymPy `sympy.functions.elementary.hyperbolic.coth`
 * @example
 * ```ts
 * import { coth, ex } from '@symjs/symjs';
 *
 * coth(ex`x`); // => coth(x)
 * ```
 */
export const coth = (x: ExprLike): Expr => fn('coth', [x]);
/**
 * Computes the hyperbolic secant.
 *
 * @param x - The argument of the function.
 * @returns The hyperbolic secant.
 * @see SymPy `sympy.functions.elementary.hyperbolic.sech`
 * @example
 * ```ts
 * import { ex, sech } from '@symjs/symjs';
 *
 * sech(ex`x`); // => sech(x)
 * ```
 */
export const sech = (x: ExprLike): Expr => fn('sech', [x]);
/**
 * Computes the hyperbolic cosecant.
 *
 * @param x - The argument of the function.
 * @returns The hyperbolic cosecant.
 * @see SymPy `sympy.functions.elementary.hyperbolic.csch`
 * @example
 * ```ts
 * import { csch, ex } from '@symjs/symjs';
 *
 * csch(ex`x`); // => csch(x)
 * ```
 */
export const csch = (x: ExprLike): Expr => fn('csch', [x]);
/**
 * Computes the inverse hyperbolic sine.
 *
 * @param x - The argument of the function.
 * @returns The inverse hyperbolic sine.
 * @see SymPy `sympy.functions.elementary.hyperbolic.asinh`
 * @example
 * ```ts
 * import { asinh } from '@symjs/symjs';
 *
 * asinh(1); // => log(1 + sqrt(2))
 * ```
 */
export const asinh = (x: ExprLike): Expr => fn('asinh', [x]);
/**
 * Computes the inverse hyperbolic cosine.
 *
 * @param x - The argument of the function.
 * @returns The inverse hyperbolic cosine.
 * @see SymPy `sympy.functions.elementary.hyperbolic.acosh`
 * @example
 * ```ts
 * import { acosh } from '@symjs/symjs';
 *
 * acosh(1); // => 0
 * ```
 */
export const acosh = (x: ExprLike): Expr => fn('acosh', [x]);
/**
 * Computes the inverse hyperbolic tangent.
 *
 * @param x - The argument of the function.
 * @returns The inverse hyperbolic tangent.
 * @see SymPy `sympy.functions.elementary.hyperbolic.atanh`
 * @example
 * ```ts
 * import { atanh } from '@symjs/symjs';
 *
 * atanh(0); // => 0
 * ```
 */
export const atanh = (x: ExprLike): Expr => fn('atanh', [x]);
/**
 * Computes the inverse hyperbolic cotangent.
 *
 * @param x - The argument of the function.
 * @returns The inverse hyperbolic cotangent.
 * @see SymPy `sympy.functions.elementary.hyperbolic.acoth`
 * @example
 * ```ts
 * import { acoth, ex } from '@symjs/symjs';
 *
 * acoth(ex`oo`); // => 0
 * ```
 */
export const acoth = (x: ExprLike): Expr => fn('acoth', [x]);
/**
 * Computes the inverse hyperbolic secant.
 *
 * @param x - The argument of the function.
 * @returns The inverse hyperbolic secant.
 * @see SymPy `sympy.functions.elementary.hyperbolic.asech`
 * @example
 * ```ts
 * import { asech } from '@symjs/symjs';
 *
 * asech(1); // => 0
 * asech(2); // => I*pi/3
 * ```
 */
export const asech = (x: ExprLike): Expr => fn('asech', [x]);
/**
 * Computes the inverse hyperbolic cosecant.
 *
 * @param x - The argument of the function.
 * @returns The inverse hyperbolic cosecant.
 * @see SymPy `sympy.functions.elementary.hyperbolic.acsch`
 * @example
 * ```ts
 * import { acsch, ex } from '@symjs/symjs';
 *
 * acsch(ex`I`); // => -I*pi/2
 * acsch(1); // => log(1 + sqrt(2))
 * ```
 */
export const acsch = (x: ExprLike): Expr => fn('acsch', [x]);
/**
 * Computes the unnormalized sinc function, equal to `sin(x)/x` with value one at zero.
 *
 * @param x - The argument of the function.
 * @returns The unnormalized sinc function, equal to `sin(x)/x` with value one at zero.
 * @see SymPy `sympy.functions.elementary.trigonometric.sinc`
 * @example
 * ```ts
 * import { ex, sinc } from '@symjs/symjs';
 *
 * sinc(0); // => 1
 * sinc(ex`oo`); // => 0
 * ```
 */
export const sinc = (x: ExprLike): Expr => fn('sinc', [x]);

/** The periods of the trigonometric functions in their argument. */
const TRIG_PERIODS: Readonly<Record<string, Expr>> = { sin: mul(2, S.Pi), cos: mul(2, S.Pi), sec: mul(2, S.Pi), csc: mul(2, S.Pi), tan: S.Pi, cot: S.Pi };

/**
 * The period of a trigonometric function of
 * a*symbol + b (0 when the argument does not depend on the symbol, which defaults to the free
 * symbol of the argument); NotImplementedError for other arguments.
 *
 * @param e - The input expression.
 * @param symbol - The symbol to use for the requested operation.
 * @returns The period with respect to the symbol.
 * @throws TypeError when the expression is not a trigonometric function.
 * @throws NotImplementedError when the argument requires a general periodicity calculation.
 * @see SymPy `sympy.functions.elementary.trigonometric.sin.period`
 */
export function period(e: Expr, symbol?: Sym): Expr {
  const general = e instanceof Fn && e.args.length === 1 ? TRIG_PERIODS[e.name] : undefined;
  if (general === undefined) throw new TypeError(`period: ${e.toString()} is not a trigonometric function`);
  const f = expandMul(first(e.args));
  const x = symbol ?? [...f.freeSymbols()][0];
  if (x === undefined || !f.has(x)) return S.Zero;
  if (f.key === x.key) return general;
  if (f instanceof Mul || f instanceof Add) {
    const [c, h] = asIndependent(f, [x], { asAdd: f instanceof Add });
    const [g, t] = f instanceof Add ? asIndependent(h, [x], { asAdd: false }) : [c, h];
    if (t.key === x.key) return mul(general, pow(fn('abs', [g]), -1));
  }
  throw new NotImplementedError('Use the periodicity function instead.');
}

const I = S.I;
const pi = S.Pi;
const half = Rational.of(1, 2);
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));
const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isOne = (e: Expr): boolean => e instanceof Rational && e.isOne;
const isNegOne = (e: Expr): boolean => e instanceof Rational && e.p === -1n && e.q === 1n;
const isOo = (e: Expr): boolean => e instanceof Special && e.name === 'oo';
const isNegOo = (e: Expr): boolean => e instanceof Special && e.name === '-oo';
const isZoo = (e: Expr): boolean => e instanceof Special && e.name === 'zoo';
const isNan = (e: Expr): boolean => e instanceof Special && e.name === 'nan';
const isRealConst = (e: Expr): boolean => isReal(e) === true;
const isFn = (e: Expr, name: string): e is Fn => e instanceof Fn && e.name === name;
const isNegNumber = (e: Expr): boolean => (e instanceof Rational || e instanceof Float) && e.isNegative;

/** SymPy _imaginary_unit_as_coefficient: c with arg = c*I, else undefined. */
function iCoeff(arg: Expr): Expr | undefined {
  if (arg.kind === 'Float') return undefined;
  return asCoefficient(arg, I);
}

/** SymPy _peeloff_ipi: arg = x + m*I*pi with m a multiple of 1/2. */
function peeloffIpi(arg: Expr): [Expr, Rational] {
  if (!(arg instanceof Add)) return [arg, Rational.of(0n)];
  const ipi = mul(pi, I);
  for (const a of arg.args) {
    let K: Rational | undefined;
    if (a.key === ipi.key) K = Rational.of(1n);
    else if (a instanceof Mul) {
      const k = div(a, ipi);
      if (k instanceof Rational) K = k;
    }
    if (K) {
      // m1 = K mod 1/2, m2 = K - m1
      const twice = Rational.of(K.p * 2n, K.q);
      const fl = twice.p >= 0n ? twice.p / twice.q : -((-twice.p + twice.q - 1n) / twice.q);
      const m2 = Rational.of(fl, 2n);
      if (m2.isZero) return [arg, m2];
      return [add(...arg.args.filter((term) => term !== a), mul(add(K, neg(m2)), ipi)), m2];
    }
  }
  return [arg, Rational.of(0n)];
}

/** SymPy _peeloff_pi: arg = x + m*pi with m a multiple of 1/2. */
function peeloffPi(arg: Expr): [Expr, Rational] {
  const [rest, c] = splitPiTerm(arg);
  if (c.isZero || isZero(rest)) return [arg, Rational.of(0n)];
  const twice = Rational.of(c.p * 2n, c.q);
  const fl = twice.p >= 0n ? twice.p / twice.q : -((-twice.p + twice.q - 1n) / twice.q);
  const m2 = Rational.of(fl, 2n);
  if (m2.isZero) return [arg, m2];
  return [add(arg, neg(mul(m2, pi))), m2];
}

/** pi coefficient of a pure multiple of pi (SymPy _pi_coeff for rational multiples). */
function piCoeffOnly(arg: Expr): Rational | undefined {
  if (arg.key === pi.key) return Rational.of(1n);
  const [rest, c] = splitPiTerm(arg);
  if (isZero(rest) && !c.isZero) return c;
  if (isZero(arg)) return Rational.of(0n);
  return undefined;
}

/** Replace cos(u) by 1/sec(u) and sin(u) by 1/csc(u) (rewrite(sec)/rewrite(csc)). */
function recipRewrite(t: Expr, which: 'sec' | 'csc'): Expr {
  return mapBottomUp(pow(t, -1), (e) => {
    if (which === 'sec' && isFn(e, 'cos')) return pow(sec(first(e.args)), -1);
    if (which === 'csc' && isFn(e, 'sin')) return pow(csc(first(e.args)), -1);
    return e;
  });
}

// ---------------------------------------------------------------------------
// Compositions of trigonometric functions with inverse functions
// ---------------------------------------------------------------------------

function trigOfInverse(name: 'sin' | 'cos' | 'tan' | 'cot', arg: Expr): Expr | undefined {
  if (!(arg instanceof Fn)) return undefined;
  // the argument, read only for the one-argument inverse functions matched below
  const x = (): Expr => first(arg.args);
  const atan2Args = () => pair(arg.args);
  const s1mx2 = () => sqrt(add(1, neg(pow(x(), 2))));
  const s1m1x2 = () => sqrt(add(1, neg(pow(x(), -2))));
  // sin(asin(x)), cos(acos(x)) and tan(atan(x)) are already reduced by the evaluators of elementary.ts
  switch (`${name}:${arg.name}`) {
    case 'cot:acot':
      return x();
    case 'sin:atan':
      return div(x(), sqrt(add(1, pow(x(), 2))));
    case 'sin:atan2': {
      const [y2, x2] = atan2Args();
      return div(y2, sqrt(add(pow(x2, 2), pow(y2, 2))));
    }
    case 'sin:acos':
      return s1mx2();
    case 'sin:acot':
      return div(1, mul(sqrt(add(1, pow(x(), -2))), x()));
    case 'sin:acsc':
      return div(1, x());
    case 'sin:asec':
      return s1m1x2();
    case 'cos:atan':
      return div(1, sqrt(add(1, pow(x(), 2))));
    case 'cos:atan2': {
      const [y2, x2] = atan2Args();
      return div(x2, sqrt(add(pow(x2, 2), pow(y2, 2))));
    }
    case 'cos:asin':
      return s1mx2();
    case 'cos:acot':
      return div(1, sqrt(add(1, pow(x(), -2))));
    case 'cos:acsc':
      return s1m1x2();
    case 'cos:asec':
      return div(1, x());
    case 'tan:atan2': {
      const [y2, x2] = atan2Args();
      return div(y2, x2);
    }
    case 'tan:asin':
      return div(x(), s1mx2());
    case 'tan:acos':
      return div(s1mx2(), x());
    case 'tan:acot':
      return div(1, x());
    case 'tan:acsc':
      return div(1, mul(s1m1x2(), x()));
    case 'tan:asec':
      return mul(s1m1x2(), x());
    case 'cot:atan':
      return div(1, x());
    case 'cot:atan2': {
      const [y2, x2] = atan2Args();
      return div(x2, y2);
    }
    case 'cot:asin':
      return div(s1mx2(), x());
    case 'cot:acos':
      return div(x(), s1mx2());
    case 'cot:acsc':
      return mul(s1m1x2(), x());
    case 'cot:asec':
      return div(1, mul(s1m1x2(), x()));
  }
  return undefined;
}

function hypOfInverse(name: 'sinh' | 'cosh' | 'tanh' | 'coth', arg: Expr): Expr | undefined {
  if (!(arg instanceof Fn)) return undefined;
  // the argument, read only for the one-argument inverse functions matched below
  const x = (): Expr => first(arg.args);
  const sxm = () => mul(sqrt(add(x(), -1)), sqrt(add(x(), 1)));
  switch (`${name}:${arg.name}`) {
    case 'sinh:asinh':
    case 'cosh:acosh':
    case 'tanh:atanh':
    case 'coth:acoth':
      return x();
    case 'sinh:acosh':
      return sxm();
    case 'sinh:atanh':
      return div(x(), sqrt(add(1, neg(pow(x(), 2)))));
    case 'sinh:acoth':
      return div(1, sxm());
    case 'cosh:asinh':
      return sqrt(add(1, pow(x(), 2)));
    case 'cosh:atanh':
      return div(1, sqrt(add(1, neg(pow(x(), 2)))));
    case 'cosh:acoth':
      return div(x(), sxm());
    case 'tanh:asinh':
      return div(x(), sqrt(add(1, pow(x(), 2))));
    case 'tanh:acosh':
      return div(sxm(), x());
    case 'tanh:acoth':
      return div(1, x());
    case 'coth:asinh':
      return div(sqrt(add(1, pow(x(), 2))), x());
    case 'coth:acosh':
      return div(x(), sxm());
    case 'coth:atanh':
      return div(1, x());
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Strengthen sin/cos/tan/sinh/cosh/tanh/asin/atan
// ---------------------------------------------------------------------------

/** The evaluators of elementary.ts, captured before they are strengthened below. */
const base = {
  sin: defined(evaluators.sin),
  cos: defined(evaluators.cos),
  tan: defined(evaluators.tan),
  sinh: defined(evaluators.sinh),
  cosh: defined(evaluators.cosh),
  tanh: defined(evaluators.tanh),
  asin: defined(evaluators.asin),
  acos: defined(evaluators.acos),
  atan: defined(evaluators.atan),
};

evaluators.sin = (x) => {
  const r = base.sin(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, sinh(c));
  return trigOfInverse('sin', x);
};
evaluators.cos = (x) => {
  const r = base.cos(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return cosh(c);
  return trigOfInverse('cos', x);
};
/** tan/cot of a rational multiple of pi with even denominator via the half-angle formula (SymPy). */
function halfAngle(pc: Rational, sgn: 1 | -1): Expr | undefined {
  const narg = mul(Rational.of(pc.p * 2n, pc.q), pi);
  const cr = cos(narg);
  const sr = cos(add(narg, neg(div(pi, 2))));
  if (isFn(cr, 'cos') || isFn(sr, 'cos')) return undefined;
  if (isZero(sr)) return S.ComplexInfinity;
  return add(pow(sr, -1), mul(sgn, div(cr, sr)));
}

/** tan(n*pi/10) for n = 1..4 (SymPy table10: simplified values for multiples of pi/5 and pi/10). */
const TAN_TABLE10 = (n: bigint): Expr =>
  n === 1n
    ? sqrt(add(1, mul(Rational.of(-2n, 5n), sqrt(5))))
    : n === 2n
      ? sqrt(add(5, mul(-2, sqrt(5))))
      : n === 3n
        ? sqrt(add(1, mul(Rational.of(2n, 5n), sqrt(5))))
        : sqrt(add(5, mul(2, sqrt(5))));

/** tan of a rational multiple of pi with denominator 5 or 10. */
function tanTenth(pc: Rational): Expr | undefined {
  if (pc.q !== 5n && pc.q !== 10n) return undefined;
  const p = ((pc.p % pc.q) + pc.q) % pc.q;
  const n = (10n * p) / pc.q;
  return n > 5n ? neg(TAN_TABLE10(10n - n)) : TAN_TABLE10(n);
}

evaluators.tan = (x) => {
  const pc0 = piCoeffOnly(x);
  const t10 = pc0 === undefined ? undefined : tanTenth(pc0);
  if (t10 !== undefined) return t10;
  if (pc0 !== undefined && !pc0.isInteger && pc0.q % 2n === 0n) {
    if (pc0.isNegative) return neg(tan(neg(x)));
    const v = halfAngle(pc0, -1);
    if (v !== undefined) return v;
  }
  const [rest, m] = peeloffPi(x);
  if (!m.isZero && m.q === 2n) return neg(cot(rest));
  const r = base.tan(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  // SymPy: I*tanh(c); tanh extracts the minus sign of c itself
  if (c !== undefined) return mul(I, tanh(c));
  return trigOfInverse('tan', x);
};
evaluators.sinh = (x) => {
  if (isZoo(x)) return S.NaN;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, sin(c));
  const r = base.sinh(x);
  if (r !== undefined) return r;
  const [rest, m] = peeloffIpi(x);
  if (!m.isZero) {
    const mm = mul(m, pi, I);
    return add(mul(sinh(mm), cosh(rest)), mul(cosh(mm), sinh(rest)));
  }
  return hypOfInverse('sinh', x);
};
evaluators.cosh = (x) => {
  if (isZoo(x)) return S.NaN;
  const c = iCoeff(x);
  if (c !== undefined) return cos(c);
  const r = base.cosh(x);
  if (r !== undefined) return r;
  const [rest, m] = peeloffIpi(x);
  if (!m.isZero) {
    const mm = mul(m, pi, I);
    return add(mul(cosh(mm), cosh(rest)), mul(sinh(mm), sinh(rest)));
  }
  return hypOfInverse('cosh', x);
};
evaluators.tanh = (x) => {
  if (isZoo(x)) return S.NaN;
  const c = iCoeff(x);
  if (c !== undefined) return couldExtractMinusSign(c) ? neg(mul(I, tan(neg(c)))) : mul(I, tan(c));
  const r = base.tanh(x);
  if (r !== undefined) return r;
  const [rest, m] = peeloffIpi(x);
  if (!m.isZero) {
    const t = tanh(mul(m, pi, I));
    return isZoo(t) ? coth(rest) : tanh(rest);
  }
  return hypOfInverse('tanh', x);
};
evaluators.asin = (x) => {
  const r = base.asin(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, asinh(c));
  return undefined;
};
evaluators.acos = (x) => {
  const c = iCoeff(x);
  return c === undefined ? base.acos(x) : add(mul(half, pi), neg(asin(x)));
};
evaluators.atan = (x) => {
  const r = base.atan(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, atanh(c));
  return undefined;
};

// ---------------------------------------------------------------------------
// New functions
// ---------------------------------------------------------------------------

const evalCot: Evaluator = (x) => {
  if (isNan(x) || isZoo(x)) return S.NaN;
  if (isOo(x) || isNegOo(x)) return AccumBounds(S.NegativeInfinity, S.Infinity);
  if (isZero(x)) return S.ComplexInfinity;
  if (couldExtractMinusSign(x)) return neg(cot(neg(x)));
  const c = iCoeff(x);
  if (c !== undefined) return neg(mul(I, coth(c)));
  const multiple = asCoefficient(x, pi);
  if (multiple !== undefined) {
    if (isIntegerQ(multiple) === true) return S.ComplexInfinity;
    const [scale, factor] = splitCoeff(multiple);
    if (scale instanceof Float) {
      const [p, q] = F.toRational(scale.mpf);
      const remainder = p % q;
      // SymPy _pi_coeff recognizes integers and binary fractions with a single fractional bit.
      if ((remainder & (remainder - 1n)) === 0n) {
        const exact = mul(Rational.of(p, q), factor);
        if (fact(exact, 'integer') === true) return S.ComplexInfinity;
        const reduced = ratMod(Rational.of(p, q), S.One);
        if (fact(factor, 'integer') === true) return cot(mul(reduced, factor, pi));
        return cot(mul(exact, pi));
      }
    }
  }
  const pc = piCoeffOnly(x);
  if (pc !== undefined) {
    // cot((k + 1/2)*pi) = 0
    if (pc.q === 2n) return S.Zero;
    if (pc.q === 5n || pc.q === 10n) return tan(add(div(pi, 2), neg(x)));
    if (pc.q % 2n === 0n) {
      const v = halfAngle(pc, 1);
      if (v !== undefined) return v;
    }
    // SymPy: the coefficient reduced into [-1/2, 1/2)
    const r1 = ratMod(Rational.of(2n * pc.p + pc.q, 2n * pc.q), S.One);
    const n = Rational.of(2n * r1.p - r1.q, 2n * r1.q);
    const narg = mul(n, pi);
    const co = cos(narg);
    const si = cos(add(narg, neg(div(pi, 2))));
    if (!isFn(co, 'cos') && !isFn(si, 'cos')) return div(co, si);
    if (!n.equals(pc)) return cot(narg);
  }
  const [rest, m] = peeloffPi(x);
  if (!m.isZero) return m.isInteger ? cot(rest) : neg(tan(rest));
  return trigOfInverse('cot', x);
};

function reciprocalTrig(name: 'sec' | 'csc', recipOf: 'cos' | 'sin', inverse: string, even: boolean): Evaluator {
  const self = name === 'sec' ? sec : csc;
  return (x) => {
    if (couldExtractMinusSign(x)) return even ? self(neg(x)) : neg(self(neg(x)));
    const pc = piCoeffOnly(x);
    if (pc !== undefined && !Rational.of(pc.p * 2n, pc.q).isInteger) {
      const q = pc.q;
      // SymPy _pi_coeff: the coefficient reduced into [0, 2)
      const pr = ratMod(pc, S.Two);
      if (pr.p > q) return neg(self(mul(Rational.of(pr.p - q, q), pi)));
      if (2n * pr.p > q) {
        const narg = mul(Rational.of(q - pr.p, q), pi);
        return even ? neg(self(narg)) : self(narg);
      }
    }
    if (isFn(x, inverse)) return x.args[0];
    const t = defined(evaluators[recipOf], recipOf)(x);
    if (t === undefined) return undefined;
    if (isFn(t, 'cos') || isFn(neg(t), 'cos')) return recipRewrite(t, 'sec');
    if (isFn(t, 'sin') || isFn(neg(t), 'sin')) return recipRewrite(t, 'csc');
    return pow(t, -1);
  };
}

const evalCoth: Evaluator = (x) => {
  if (isNan(x) || isZoo(x)) return S.NaN;
  if (isOo(x)) return S.One;
  if (isNegOo(x)) return S.NegOne;
  if (isZero(x)) return S.ComplexInfinity;
  if (isNegNumber(x)) return neg(coth(neg(x)));
  const c = iCoeff(x);
  if (c !== undefined) return couldExtractMinusSign(c) ? mul(I, cot(neg(c))) : neg(mul(I, cot(c)));
  if (couldExtractMinusSign(x)) return neg(coth(neg(x)));
  const [rest, m] = peeloffIpi(x);
  if (!m.isZero) {
    const t = coth(mul(m, pi, I));
    return isZoo(t) ? coth(rest) : tanh(rest);
  }
  return hypOfInverse('coth', x);
};

function reciprocalHyp(name: 'sech' | 'csch', recipOf: 'cosh' | 'sinh', inverse: string, even: boolean): Evaluator {
  const self = name === 'sech' ? sech : csch;
  return (x) => {
    if (isNan(x)) return S.NaN;
    if (couldExtractMinusSign(x)) return even ? self(neg(x)) : neg(self(neg(x)));
    const t = defined(evaluators[recipOf], recipOf)(x);
    if (isFn(x, inverse)) return x.args[0];
    return t === undefined ? undefined : pow(t, -1);
  };
}

/* Generated from sympy.functions.elementary.hyperbolic (finite entries). */
const ACOSH_TABLE = (): [Expr, Expr][] => [
    [I, add(mul(Rational.of(1n, 2n), pi, I), log(add(Rational.of(1n), pow(Rational.of(2n), Rational.of(1n, 2n)))))],
    [mul(Rational.of(-1n), I), add(mul(Rational.of(-1n, 2n), pi, I), log(add(Rational.of(1n), pow(Rational.of(2n), Rational.of(1n, 2n)))))],
    [Rational.of(1n, 2n), mul(Rational.of(1n, 3n), pi)],
    [Rational.of(-1n, 2n), mul(Rational.of(2n, 3n), pi)],
    [mul(Rational.of(1n, 2n), pow(Rational.of(2n), Rational.of(1n, 2n))), mul(Rational.of(1n, 4n), pi)],
    [mul(Rational.of(-1n, 2n), pow(Rational.of(2n), Rational.of(1n, 2n))), mul(Rational.of(3n, 4n), pi)],
    [mul(Rational.of(1n, 2n), pow(Rational.of(3n), Rational.of(1n, 2n))), mul(Rational.of(1n, 6n), pi)],
    [mul(Rational.of(-1n, 2n), pow(Rational.of(3n), Rational.of(1n, 2n))), mul(Rational.of(5n, 6n), pi)],
    [mul(Rational.of(1n, 4n), pow(Rational.of(2n), Rational.of(1n, 2n)), add(Rational.of(-1n), pow(Rational.of(3n), Rational.of(1n, 2n)))), mul(Rational.of(5n, 12n), pi)],
    [mul(Rational.of(1n, 4n), pow(Rational.of(2n), Rational.of(1n, 2n)), add(Rational.of(1n), mul(Rational.of(-1n), pow(Rational.of(3n), Rational.of(1n, 2n))))), mul(Rational.of(7n, 12n), pi)],
    [mul(Rational.of(1n, 2n), pow(add(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n))), Rational.of(1n, 2n))), mul(Rational.of(1n, 8n), pi)],
    [mul(Rational.of(-1n, 2n), pow(add(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n))), Rational.of(1n, 2n))), mul(Rational.of(7n, 8n), pi)],
    [mul(Rational.of(1n, 2n), pow(add(Rational.of(2n), mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(3n, 8n), pi)],
    [mul(Rational.of(-1n, 2n), pow(add(Rational.of(2n), mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(5n, 8n), pi)],
    [mul(Rational.of(1n, 4n), pow(Rational.of(2n), Rational.of(1n, 2n)), add(Rational.of(1n), pow(Rational.of(3n), Rational.of(1n, 2n)))), mul(Rational.of(1n, 12n), pi)],
    [mul(Rational.of(1n, 4n), pow(Rational.of(2n), Rational.of(1n, 2n)), add(Rational.of(-1n), mul(Rational.of(-1n), pow(Rational.of(3n), Rational.of(1n, 2n))))), mul(Rational.of(11n, 12n), pi)],
    [add(Rational.of(1n, 4n), mul(Rational.of(1n, 4n), pow(Rational.of(5n), Rational.of(1n, 2n)))), mul(Rational.of(1n, 5n), pi)],
    [add(Rational.of(-1n, 4n), mul(Rational.of(-1n, 4n), pow(Rational.of(5n), Rational.of(1n, 2n)))), mul(Rational.of(4n, 5n), pi)],
];
const ASECH_TABLE = (): [Expr, Expr][] => [
    [I, add(mul(Rational.of(-1n, 2n), pi, I), log(add(Rational.of(1n), pow(Rational.of(2n), Rational.of(1n, 2n)))))],
    [mul(Rational.of(-1n), I), add(mul(Rational.of(1n, 2n), pi, I), log(add(Rational.of(1n), pow(Rational.of(2n), Rational.of(1n, 2n)))))],
    [add(pow(Rational.of(6n), Rational.of(1n, 2n)), mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n)))), mul(Rational.of(1n, 12n), pi)],
    [add(pow(Rational.of(2n), Rational.of(1n, 2n)), mul(Rational.of(-1n), pow(Rational.of(6n), Rational.of(1n, 2n)))), mul(Rational.of(11n, 12n), pi)],
    [pow(add(Rational.of(2n), mul(Rational.of(-2n, 5n), pow(Rational.of(5n), Rational.of(1n, 2n)))), Rational.of(1n, 2n)), mul(Rational.of(1n, 10n), pi)],
    [mul(Rational.of(-1n), pow(add(Rational.of(2n), mul(Rational.of(-2n, 5n), pow(Rational.of(5n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(9n, 10n), pi)],
    [mul(Rational.of(2n), pow(add(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n))), Rational.of(-1n, 2n))), mul(Rational.of(1n, 8n), pi)],
    [mul(Rational.of(-2n), pow(add(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n))), Rational.of(-1n, 2n))), mul(Rational.of(7n, 8n), pi)],
    [mul(Rational.of(2n, 3n), pow(Rational.of(3n), Rational.of(1n, 2n))), mul(Rational.of(1n, 6n), pi)],
    [mul(Rational.of(-2n, 3n), pow(Rational.of(3n), Rational.of(1n, 2n))), mul(Rational.of(5n, 6n), pi)],
    [add(Rational.of(-1n), pow(Rational.of(5n), Rational.of(1n, 2n))), mul(Rational.of(1n, 5n), pi)],
    [add(Rational.of(1n), mul(Rational.of(-1n), pow(Rational.of(5n), Rational.of(1n, 2n)))), mul(Rational.of(4n, 5n), pi)],
    [pow(Rational.of(2n), Rational.of(1n, 2n)), mul(Rational.of(1n, 4n), pi)],
    [mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n))), mul(Rational.of(3n, 4n), pi)],
    [pow(add(Rational.of(2n), mul(Rational.of(2n, 5n), pow(Rational.of(5n), Rational.of(1n, 2n)))), Rational.of(1n, 2n)), mul(Rational.of(3n, 10n), pi)],
    [mul(Rational.of(-1n), pow(add(Rational.of(2n), mul(Rational.of(2n, 5n), pow(Rational.of(5n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(7n, 10n), pi)],
    [Rational.of(2n), mul(Rational.of(1n, 3n), pi)],
    [Rational.of(-2n), mul(Rational.of(2n, 3n), pi)],
    [pow(add(Rational.of(4n), mul(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n)))), Rational.of(1n, 2n)), mul(Rational.of(3n, 8n), pi)],
    [mul(Rational.of(-1n), pow(add(Rational.of(4n), mul(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(5n, 8n), pi)],
    [add(Rational.of(1n), pow(Rational.of(5n), Rational.of(1n, 2n))), mul(Rational.of(2n, 5n), pi)],
    [add(Rational.of(-1n), mul(Rational.of(-1n), pow(Rational.of(5n), Rational.of(1n, 2n)))), mul(Rational.of(3n, 5n), pi)],
    [add(pow(Rational.of(2n), Rational.of(1n, 2n)), pow(Rational.of(6n), Rational.of(1n, 2n))), mul(Rational.of(5n, 12n), pi)],
    [add(mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n))), mul(Rational.of(-1n), pow(Rational.of(6n), Rational.of(1n, 2n)))), mul(Rational.of(7n, 12n), pi)],
];
const ACSCH_TABLE = (): [Expr, Expr][] => [
    [I, mul(Rational.of(-1n, 2n), pi)],
    [mul(I, add(pow(Rational.of(2n), Rational.of(1n, 2n)), pow(Rational.of(6n), Rational.of(1n, 2n)))), mul(Rational.of(-1n, 12n), pi)],
    [mul(I, add(Rational.of(1n), pow(Rational.of(5n), Rational.of(1n, 2n)))), mul(Rational.of(-1n, 10n), pi)],
    [mul(Rational.of(2n), I, pow(add(Rational.of(2n), mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n)))), Rational.of(-1n, 2n))), mul(Rational.of(-1n, 8n), pi)],
    [mul(Rational.of(2n), I), mul(Rational.of(-1n, 6n), pi)],
    [mul(I, pow(add(Rational.of(2n), mul(Rational.of(2n, 5n), pow(Rational.of(5n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(-1n, 5n), pi)],
    [mul(I, pow(Rational.of(2n), Rational.of(1n, 2n))), mul(Rational.of(-1n, 4n), pi)],
    [mul(I, add(Rational.of(-1n), pow(Rational.of(5n), Rational.of(1n, 2n)))), mul(Rational.of(-3n, 10n), pi)],
    [mul(Rational.of(2n, 3n), I, pow(Rational.of(3n), Rational.of(1n, 2n))), mul(Rational.of(-1n, 3n), pi)],
    [mul(Rational.of(2n), I, pow(add(Rational.of(2n), pow(Rational.of(2n), Rational.of(1n, 2n))), Rational.of(-1n, 2n))), mul(Rational.of(-3n, 8n), pi)],
    [mul(I, pow(add(Rational.of(2n), mul(Rational.of(-2n, 5n), pow(Rational.of(5n), Rational.of(1n, 2n)))), Rational.of(1n, 2n))), mul(Rational.of(-2n, 5n), pi)],
    [mul(I, add(pow(Rational.of(6n), Rational.of(1n, 2n)), mul(Rational.of(-1n), pow(Rational.of(2n), Rational.of(1n, 2n))))), mul(Rational.of(-5n, 12n), pi)],
    [Rational.of(2n), mul(Rational.of(-1n), I, log(add(Rational.of(1n, 2n), mul(Rational.of(1n, 2n), pow(Rational.of(5n), Rational.of(1n, 2n))))))],
];

function lookup(table: () => [Expr, Expr][], x: Expr): Expr | undefined {
  if (x.freeSymbols().size) return undefined;
  for (const [k, v] of table()) if (k.key === x.key) return v;
  return undefined;
}

/** I*AccumBounds(-pi/2, pi/2), the value of atanh and asech at zoo (an unevaluated product: the bounds are not real). */
const iHalfPiBounds = (): Expr => new Mul([I, AccumBounds(neg(div(pi, 2)), div(pi, 2))]);

/** Reduce a known numeric argument by integer multiples of the vertical period. */
function inverseHyperbolicBranch(arg: Expr, reflect: boolean): Expr | undefined {
  if (arg.freeSymbols().size > 0) return undefined;
  if (isReal(arg) === true) return arg;
  const real = re(arg);
  const imaginary = im(arg);
  if (isReal(real) !== true || isReal(imaginary) !== true) return undefined;
  const turns = fn('floor', [add(div(imaginary, pi), half)]);
  if (!(turns instanceof Rational && turns.isInteger)) return undefined;
  const reduced = add(real, mul(I, add(imaginary, mul(-turns.p, pi))));
  return reflect && turns.p % 2n !== 0n ? neg(reduced) : reduced;
}

const evalAsinh: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isOo(x) || isNegOo(x) || isZoo(x)) return x;
  if (isZero(x)) return S.Zero;
  if (isOne(x)) return log(add(sqrt(2), 1));
  if (isNegOne(x)) return log(add(sqrt(2), -1));
  if (isNegNumber(x)) return neg(asinh(neg(x)));
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, asin(c));
  if (couldExtractMinusSign(x)) return neg(asinh(neg(x)));
  if (isFn(x, 'sinh')) return inverseHyperbolicBranch(first(x.args), true);
  return undefined;
};

const evalAcosh: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isOo(x) || isNegOo(x)) return S.Infinity;
  if (isZoo(x)) return S.ComplexInfinity;
  if (isZero(x)) return mul(div(pi, 2), I);
  if (isOne(x)) return S.Zero;
  if (isNegOne(x)) return mul(pi, I);
  const t = lookup(ACOSH_TABLE, x);
  if (t !== undefined) return isRealConst(x) ? mul(t, I) : t;
  return undefined;
};

const evalAtanh: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isZero(x)) return S.Zero;
  if (isOne(x)) return S.Infinity;
  if (isNegOne(x)) return S.NegativeInfinity;
  if (isOo(x)) return neg(mul(I, div(pi, 2)));
  if (isNegOo(x)) return mul(I, div(pi, 2));
  if (isNegNumber(x)) return neg(atanh(neg(x)));
  if (isZoo(x)) return iHalfPiBounds();
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, atan(c));
  if (couldExtractMinusSign(x)) return neg(atanh(neg(x)));
  if (isFn(x, 'tanh')) return inverseHyperbolicBranch(first(x.args), false);
  return undefined;
};

const evalAcoth: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isOo(x) || isNegOo(x)) return S.Zero;
  if (isZero(x)) return mul(pi, I, half);
  if (isOne(x)) return S.Infinity;
  if (isNegOne(x)) return S.NegativeInfinity;
  if (isNegNumber(x)) return neg(acoth(neg(x)));
  if (isZoo(x)) return S.Zero;
  const c = iCoeff(x);
  if (c !== undefined) return neg(mul(I, acot(c)));
  if (couldExtractMinusSign(x)) return neg(acoth(neg(x)));
  return undefined;
};

const ACOT_TABLE = (): [Expr, Expr][] => [
  [sqrt(3), div(pi, 6)],
  [div(sqrt(3), 3), div(pi, 3)],
  [add(1, sqrt(2)), div(pi, 8)],
  [add(sqrt(2), -1), mul(Rational.of(3, 8), pi)],
  [add(2, sqrt(3)), div(pi, 12)],
  [add(2, neg(sqrt(3))), mul(Rational.of(5, 12), pi)],
];

const evalAcot: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isOo(x) || isNegOo(x)) return S.Zero;
  if (isZero(x)) return div(pi, 2);
  if (isOne(x)) return div(pi, 4);
  if (isNegOne(x)) return neg(div(pi, 4));
  if (isZoo(x)) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(acot(neg(x)));
  const c = iCoeff(x);
  if (c !== undefined) return neg(mul(I, acoth(c)));
  const nx = neg(x);
  for (const [k, v] of ACOT_TABLE()) {
    if (k.key === x.key) return v;
    if (k.key === nx.key) return neg(v);
  }
  return undefined;
};

const evalAsec: Evaluator = (x) => {
  if (isZero(x)) return S.ComplexInfinity;
  if (isOne(x)) return S.Zero;
  if (isNegOne(x)) return pi;
  if (isOo(x) || isNegOo(x) || isZoo(x)) return div(pi, 2);
  if (isNan(x)) return S.NaN;
  if (x.freeSymbols().size === 0 && !(x instanceof Special)) {
    const a = acos(pow(x, -1));
    if (!isFn(a, 'acos')) return a;
  }
  return undefined;
};

const evalAcsc: Evaluator = (x) => {
  if (isZero(x)) return S.ComplexInfinity;
  if (isOne(x)) return div(pi, 2);
  if (isNegOne(x)) return neg(div(pi, 2));
  if (isOo(x) || isNegOo(x) || isZoo(x)) return S.Zero;
  if (isNan(x)) return S.NaN;
  if (couldExtractMinusSign(x)) return neg(acsc(neg(x)));
  if (x.freeSymbols().size === 0 && !(x instanceof Special)) {
    const a = asin(pow(x, -1));
    if (!isFn(a, 'asin')) return a;
  }
  return undefined;
};

const evalAsech: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isZero(x)) return S.Infinity;
  if (isOne(x)) return S.Zero;
  if (isNegOne(x)) return mul(pi, I);
  if (isOo(x) || isNegOo(x)) return mul(pi, I, half);
  const t = lookup(ASECH_TABLE, x);
  if (t !== undefined) return isRealConst(x) ? mul(t, I) : t;
  if (isZoo(x)) return iHalfPiBounds();
  return undefined;
};

const evalAcsch: Evaluator = (x) => {
  if (isNan(x)) return S.NaN;
  if (isOo(x) || isNegOo(x)) return S.Zero;
  if (isZero(x)) return S.ComplexInfinity;
  if (isOne(x)) return log(add(1, sqrt(2)));
  if (isNegOne(x)) return neg(log(add(1, sqrt(2))));
  const t = lookup(ACSCH_TABLE, x);
  if (t !== undefined) return mul(t, I);
  if (isZoo(x)) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(acsch(neg(x)));
  return undefined;
};

const evalSinc: Evaluator = (x) => {
  if (isZero(x)) return S.One;
  if (isOo(x) || isNegOo(x)) return S.Zero;
  if (isNan(x) || isZoo(x)) return S.NaN;
  if (couldExtractMinusSign(x)) return sinc(neg(x));
  const pc = piCoeffOnly(x);
  if (pc !== undefined) {
    if (pc.isInteger) return S.Zero;
    if (Rational.of(pc.p * 2n, pc.q).isInteger) return div(pow(-1, add(pc, neg(half))), x);
  }
  return undefined;
};

// ---------------------------------------------------------------------------
// Registration: evaluation, derivatives, numerics, conjugation
// ---------------------------------------------------------------------------

type Spec = {
  eval: Evaluator;
  partial: (x: Expr) => Expr;
  mp: (z: Mpc, p: number) => Mpc;
  conjugate?: boolean;
};

const inv = (z: Mpc, p: number): Mpc => M.cdiv(M.C1, z, p);
const recipMp = (f: (z: Mpc, p: number) => Mpc) => (z: Mpc, p: number) => inv(f(z, p + 10), p);
const ofInverse = (f: (z: Mpc, p: number) => Mpc) => (z: Mpc, p: number) => f(inv(z, p + 10), p);

const SPECS: Partial<Record<FnName, Spec>> = {
  cot: { eval: evalCot, partial: (x) => add(neg(pow(cot(x), 2)), -1), mp: recipMp(M.ctan), conjugate: true },
  sec: { eval: reciprocalTrig('sec', 'cos', 'asec', true), partial: (x) => mul(tan(x), sec(x)), mp: recipMp(M.ccos), conjugate: true },
  csc: { eval: reciprocalTrig('csc', 'sin', 'acsc', false), partial: (x) => neg(mul(cot(x), csc(x))), mp: recipMp(M.csin), conjugate: true },
  coth: { eval: evalCoth, partial: (x) => neg(pow(sinh(x), -2)), mp: recipMp(M.ctanh), conjugate: true },
  sech: { eval: reciprocalHyp('sech', 'cosh', 'asech', true), partial: (x) => neg(mul(tanh(x), sech(x))), mp: recipMp(M.ccosh), conjugate: true },
  csch: { eval: reciprocalHyp('csch', 'sinh', 'acsch', false), partial: (x) => neg(mul(coth(x), csch(x))), mp: recipMp(M.csinh), conjugate: true },
  asinh: { eval: evalAsinh, partial: (x) => pow(add(pow(x, 2), 1), Rational.of(-1, 2)), mp: M.casinh },
  acosh: { eval: evalAcosh, partial: (x) => pow(mul(sqrt(add(x, -1)), sqrt(add(x, 1))), -1), mp: M.cacosh },
  atanh: { eval: evalAtanh, partial: (x) => pow(add(1, neg(pow(x, 2))), -1), mp: M.catanh },
  acoth: { eval: evalAcoth, partial: (x) => pow(add(1, neg(pow(x, 2))), -1), mp: ofInverse(M.catanh) },
  acot: {
    eval: evalAcot,
    partial: (x) => neg(pow(add(pow(x, 2), 1), -1)),
    mp: (z, p) => (F.isZero(z[0]) && F.isZero(z[1]) ? [F.ldexp(M.mpPi(p), -1), F.ZERO] : M.catan(inv(z, p + 10), p)),
  },
  asec: { eval: evalAsec, partial: (x) => pow(mul(pow(x, 2), sqrt(add(1, neg(pow(x, -2))))), -1), mp: ofInverse(M.cacos) },
  acsc: { eval: evalAcsc, partial: (x) => neg(pow(mul(pow(x, 2), sqrt(add(1, neg(pow(x, -2))))), -1)), mp: ofInverse(M.casin) },
  asech: { eval: evalAsech, partial: (x) => neg(pow(mul(x, sqrt(add(1, neg(pow(x, 2))))), -1)), mp: ofInverse(M.cacosh) },
  acsch: { eval: evalAcsch, partial: (x) => neg(pow(mul(pow(x, 2), sqrt(add(1, pow(x, -2)))), -1)), mp: ofInverse(M.casinh) },
  sinc: {
    eval: evalSinc,
    partial: (x) => add(div(cos(x), x), neg(div(sin(x), pow(x, 2)))),
    mp: (z, p) => (F.isZero(z[0]) && F.isZero(z[1]) ? M.C1 : M.cdiv(M.csin(z, p + 10), z, p)),
    conjugate: true,
  },
};

forEachEntry(SPECS, (name, spec) => {
  evaluators[name] = spec.eval;
  fnPartials[name] = (args) => spec.partial(first(args));
  mpFns[name] = (args, p) => spec.mp(first(args), p);
  numericFns[name] = (args) => {
    const z = first(args);
    const r = spec.mp([F.fromNumber(z.re), F.fromNumber(z.im)], 64);
    return { re: F.toNumber(r[0]), im: F.toNumber(r[1]) };
  };
  if (spec.conjugate) conjugateCommutes.add(name);
});

registerFunctionHeads([
  ['cot', cot],
  ['sec', sec],
  ['csc', csc],
  ['acot', acot],
  ['asec', asec],
  ['acsc', acsc],
  ['coth', coth],
  ['sech', sech],
  ['csch', csch],
  ['asinh', asinh],
  ['acosh', acosh],
  ['atanh', atanh],
  ['acoth', acoth],
  ['asech', asech],
  ['acsch', acsch],
  ['sinc', sinc],
]);
