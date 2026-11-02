// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Reciprocal trigonometric and hyperbolic functions, inverse
 * hyperbolic functions, acot/asec/acsc and sinc, plus the SymPy
 * evaluation rules that connect trigonometric and hyperbolic functions
 * (sin(I*x) = I*sinh(x), compositions with inverse functions, shifts by
 * I*pi/2).
 */

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, Float, Fn, Mul, Rational, S, Special } from '../core/nodes';
import { add, couldExtractMinusSign, mul, neg, pow, sqrt } from '../core/ops';
import { asCoefficient } from '../core/methods';
import { isReal } from '../core/assumptions';
import { mapBottomUp } from '../core/traverse';
import { fnPartials } from '../calculus/diff';
import { numericFns } from '../numeric/evalf';
import { mpFns } from '../numeric/mpeval';
import * as F from '../numeric/mpf';
import * as M from '../numeric/mpfun';
import type { Mpc } from '../numeric/mpfun';
import type { Evaluator } from './elementary';
import { acos, asin, atan, conjugateCommutes, cos, cosh, evaluators, fn, log, sin, sinh, splitPiTerm, tan, tanh } from './elementary';

export const cot = (x: ExprLike): Expr => fn('cot', [x]);
export const sec = (x: ExprLike): Expr => fn('sec', [x]);
export const csc = (x: ExprLike): Expr => fn('csc', [x]);
export const acot = (x: ExprLike): Expr => fn('acot', [x]);
export const asec = (x: ExprLike): Expr => fn('asec', [x]);
export const acsc = (x: ExprLike): Expr => fn('acsc', [x]);
export const coth = (x: ExprLike): Expr => fn('coth', [x]);
export const sech = (x: ExprLike): Expr => fn('sech', [x]);
export const csch = (x: ExprLike): Expr => fn('csch', [x]);
export const asinh = (x: ExprLike): Expr => fn('asinh', [x]);
export const acosh = (x: ExprLike): Expr => fn('acosh', [x]);
export const atanh = (x: ExprLike): Expr => fn('atanh', [x]);
export const acoth = (x: ExprLike): Expr => fn('acoth', [x]);
export const asech = (x: ExprLike): Expr => fn('asech', [x]);
export const acsch = (x: ExprLike): Expr => fn('acsch', [x]);
export const sinc = (x: ExprLike): Expr => fn('sinc', [x]);

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
      return [add(arg, neg(mul(m2, ipi))), m2];
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
    if (which === 'sec' && isFn(e, 'cos')) return pow(sec(e.args[0]!), -1);
    if (which === 'csc' && isFn(e, 'sin')) return pow(csc(e.args[0]!), -1);
    return e;
  });
}

// ---------------------------------------------------------------------------
// Compositions of trigonometric functions with inverse functions
// ---------------------------------------------------------------------------

function trigOfInverse(name: 'sin' | 'cos' | 'tan' | 'cot', arg: Expr): Expr | undefined {
  if (!(arg instanceof Fn)) return undefined;
  const x = arg.args[0]!;
  const s1mx2 = () => sqrt(add(1, neg(pow(x, 2))));
  const s1m1x2 = () => sqrt(add(1, neg(pow(x, -2))));
  switch (`${name}:${arg.name}`) {
    case 'sin:asin':
    case 'cos:acos':
    case 'tan:atan':
    case 'cot:acot':
      return x;
    case 'sin:atan':
      return div(x, sqrt(add(1, pow(x, 2))));
    case 'sin:atan2':
      return div(arg.args[0]!, sqrt(add(pow(arg.args[1]!, 2), pow(arg.args[0]!, 2))));
    case 'sin:acos':
      return s1mx2();
    case 'sin:acot':
      return div(1, mul(sqrt(add(1, pow(x, -2))), x));
    case 'sin:acsc':
      return div(1, x);
    case 'sin:asec':
      return s1m1x2();
    case 'cos:atan':
      return div(1, sqrt(add(1, pow(x, 2))));
    case 'cos:atan2':
      return div(arg.args[1]!, sqrt(add(pow(arg.args[1]!, 2), pow(arg.args[0]!, 2))));
    case 'cos:asin':
      return s1mx2();
    case 'cos:acot':
      return div(1, sqrt(add(1, pow(x, -2))));
    case 'cos:acsc':
      return s1m1x2();
    case 'cos:asec':
      return div(1, x);
    case 'tan:atan2':
      return div(arg.args[0]!, arg.args[1]!);
    case 'tan:asin':
      return div(x, s1mx2());
    case 'tan:acos':
      return div(s1mx2(), x);
    case 'tan:acot':
      return div(1, x);
    case 'tan:acsc':
      return div(1, mul(s1m1x2(), x));
    case 'tan:asec':
      return mul(s1m1x2(), x);
    case 'cot:atan':
      return div(1, x);
    case 'cot:atan2':
      return div(arg.args[1]!, arg.args[0]!);
    case 'cot:asin':
      return div(s1mx2(), x);
    case 'cot:acos':
      return div(x, s1mx2());
    case 'cot:acsc':
      return mul(s1m1x2(), x);
    case 'cot:asec':
      return div(1, mul(s1m1x2(), x));
  }
  return undefined;
}

function hypOfInverse(name: 'sinh' | 'cosh' | 'tanh' | 'coth', arg: Expr): Expr | undefined {
  if (!(arg instanceof Fn)) return undefined;
  const x = arg.args[0]!;
  const sxm = () => mul(sqrt(add(x, -1)), sqrt(add(x, 1)));
  switch (`${name}:${arg.name}`) {
    case 'sinh:asinh':
    case 'cosh:acosh':
    case 'tanh:atanh':
    case 'coth:acoth':
      return x;
    case 'sinh:acosh':
      return sxm();
    case 'sinh:atanh':
      return div(x, sqrt(add(1, neg(pow(x, 2)))));
    case 'sinh:acoth':
      return div(1, sxm());
    case 'cosh:asinh':
      return sqrt(add(1, pow(x, 2)));
    case 'cosh:atanh':
      return div(1, sqrt(add(1, neg(pow(x, 2)))));
    case 'cosh:acoth':
      return div(x, sxm());
    case 'tanh:asinh':
      return div(x, sqrt(add(1, pow(x, 2))));
    case 'tanh:acosh':
      return div(sxm(), x);
    case 'tanh:acoth':
      return div(1, x);
    case 'coth:asinh':
      return div(sqrt(add(1, pow(x, 2))), x);
    case 'coth:acosh':
      return div(x, sxm());
    case 'coth:atanh':
      return div(1, x);
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Strengthen sin/cos/tan/sinh/cosh/tanh/asin/atan
// ---------------------------------------------------------------------------

const base = { ...evaluators };

evaluators.sin = (x) => {
  const r = base.sin!(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, sinh(c));
  return trigOfInverse('sin', x);
};
evaluators.cos = (x) => {
  const r = base.cos!(x);
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

evaluators.tan = (x) => {
  const pc0 = piCoeffOnly(x);
  if (pc0 !== undefined && !pc0.isInteger && pc0.q % 2n === 0n) {
    if (pc0.isNegative) return neg(tan(neg(x)));
    const v = halfAngle(pc0, -1);
    if (v !== undefined) return v;
  }
  const [rest, m] = peeloffPi(x);
  if (!m.isZero && m.q === 2n) return neg(cot(rest));
  const r = base.tan!(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return couldExtractMinusSign(c) ? neg(mul(I, tanh(neg(c)))) : mul(I, tanh(c));
  return trigOfInverse('tan', x);
};
evaluators.sinh = (x) => {
  if (isZoo(x)) return S.NaN;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, sin(c));
  const r = base.sinh!(x);
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
  const r = base.cosh!(x);
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
  const r = base.tanh!(x);
  if (r !== undefined) return r;
  const [rest, m] = peeloffIpi(x);
  if (!m.isZero) {
    const t = tanh(mul(m, pi, I));
    return isZoo(t) ? coth(rest) : tanh(rest);
  }
  return hypOfInverse('tanh', x);
};
evaluators.asin = (x) => {
  const r = base.asin!(x);
  if (r !== undefined) return r;
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, asinh(c));
  return undefined;
};
evaluators.atan = (x) => {
  const r = base.atan!(x);
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
  if (isZero(x)) return S.ComplexInfinity;
  if (couldExtractMinusSign(x)) return neg(cot(neg(x)));
  const c = iCoeff(x);
  if (c !== undefined) return neg(mul(I, coth(c)));
  const pc = piCoeffOnly(x);
  if (pc !== undefined) {
    if (pc.isInteger) return S.ComplexInfinity;
    // cot((k + 1/2)*pi) = 0
    if (pc.q === 2n) return S.Zero;
    if (pc.q % 2n === 0n) {
      const v = halfAngle(pc, 1);
      if (v !== undefined) return v;
    }
    const co = cos(mul(pc, pi));
    const si = sin(mul(pc, pi));
    if (!isFn(co, 'cos') && !isFn(si, 'sin')) return div(co, si);
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
      const p = ((pc.p % (2n * q)) + 2n * q) % (2n * q);
      if (p > q) return neg(self(mul(add(pc, -1), pi)));
      if (2n * p > q) {
        const narg = mul(add(1, neg(pc)), pi);
        return even ? neg(self(narg)) : self(narg);
      }
    }
    if (isFn(x, inverse)) return x.args[0];
    const t = evaluators[recipOf]!(x);
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
    if (couldExtractMinusSign(x)) return even ? self(neg(x)) : neg(self(neg(x)));
    const t = evaluators[recipOf]!(x);
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
  if (isZoo(x)) return mul(I, S.NaN);
  const c = iCoeff(x);
  if (c !== undefined) return mul(I, atan(c));
  if (couldExtractMinusSign(x)) return neg(atanh(neg(x)));
  if (isFn(x, 'tanh')) return x.args[0]!.freeSymbols().size === 0 && x.args[0]!.kind !== 'Fn' ? x.args[0] : undefined;
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
  if (isZoo(x)) return mul(pi, I, half);
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

for (const [name, spec] of Object.entries(SPECS) as [FnName, Spec][]) {
  evaluators[name] = spec.eval;
  fnPartials[name] = ([x]) => spec.partial(x!);
  mpFns[name] = ([z], p) => spec.mp(z!, p);
  numericFns[name] = ([z]) => {
    const r = spec.mp([F.fromNumber(z!.re), F.fromNumber(z!.im)], 64);
    return { re: F.toNumber(r[0]), im: F.toNumber(r[1]) };
  };
  if (spec.conjugate) conjugateCommutes.add(name);
}
