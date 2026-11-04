// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/functions/special/elliptic_integrals.py), BSD
// 3-Clause License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file The complete and incomplete elliptic integrals of the first, second
 * and third kind (SymPy elliptic_k, elliptic_f, elliptic_e, elliptic_pi):
 * special values, derivatives, conjugation, series and rewrites in terms of
 * hyper and meijerg. The values are those of mpmath (numeric/mpelliptic).
 */

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Fn, Rational, S, Special } from '../core/nodes';
import { at, first, pair } from '../core/guard';
import { isIntegerQ, isNegative, isPositive, isReal, isZero } from '../core/assumptions';
import { add, couldExtractMinusSign, mul, neg, pow, sqrt } from '../core/ops';
import { fnPartials, fnTaylorAtZero } from '../calculus/diff';
import { numericFns } from '../numeric/evalf';
import { registerRewrite } from '../simplify/rewrite';
import { conjugate, conjugateRules, evaluators, fn, sin, tan } from './elementary';
import { mpNumeric, sign } from './special';
import { hyper, meijerg } from './hyper';

const R = (p: bigint | number, q: bigint | number = 1): Rational => Rational.of(p, q);
const isRat = (e: Expr, p: bigint, q = 1n): boolean => e instanceof Rational && e.p === p && e.q === q;
const isSpecial = (e: Expr, ...names: string[]): boolean => e instanceof Special && names.includes(e.name);
const isRealInfinite = (e: Expr): boolean => isSpecial(e, 'oo', '-oo');
/** m in (oo, -oo, I*oo, -I*oo, zoo). */
const isInfinite = (e: Expr): boolean =>
  isSpecial(e, 'oo', '-oo', 'zoo') || e.key === mul(S.I, S.Infinity).key || e.key === mul(S.I, S.NegativeInfinity).key;
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));
const sub = (a: ExprLike, b: ExprLike): Expr => add(a, neg(b));
/** sqrt(1 - m*sin(z)**2). */
const delta = (z: Expr, m: Expr): Expr => sqrt(sub(1, mul(m, pow(sin(z), 2))));

// ---- constructors ---------------------------------------------------------------------

/** SymPy elliptic_k(m): the complete elliptic integral of the first kind K(m). */
export const ellipticK = (m: ExprLike): Expr => fn('elliptic_k', [m]);
/** SymPy elliptic_f(z, m): the incomplete elliptic integral of the first kind F(z|m). */
export const ellipticF = (z: ExprLike, m: ExprLike): Expr => fn('elliptic_f', [z, m]);
/**
 * SymPy elliptic_e: elliptic_e(m) is the complete elliptic integral of the
 * second kind E(m), elliptic_e(z, m) the incomplete one E(z|m).
 */
export function ellipticE(m: ExprLike): Expr;
export function ellipticE(z: ExprLike, m: ExprLike): Expr;
export function ellipticE(a: ExprLike, b?: ExprLike): Expr {
  return fn('elliptic_e', b === undefined ? [a] : [a, b]);
}
/**
 * SymPy elliptic_pi: elliptic_pi(n, m) is the complete elliptic integral of
 * the third kind Pi(n|m), elliptic_pi(n, z, m) the incomplete one Pi(n; z|m).
 */
export function ellipticPi(n: ExprLike, m: ExprLike): Expr;
export function ellipticPi(n: ExprLike, z: ExprLike, m: ExprLike): Expr;
export function ellipticPi(n: ExprLike, a: ExprLike, b?: ExprLike): Expr {
  return fn('elliptic_pi', b === undefined ? [n, a] : [n, a, b]);
}

// ---- evaluation -----------------------------------------------------------------------

/** SymPy elliptic_k.eval. */
evaluators.elliptic_k = (m) => {
  if (isZero(m) === true) return mul(S.Pi, S.Half);
  if (isRat(m, 1n, 2n)) return div(mul(8, pow(S.Pi, R(3, 2))), pow(fn('gamma', [R(-1, 4)]), 2));
  if (isRat(m, 1n)) return S.ComplexInfinity;
  if (isRat(m, -1n)) return div(pow(fn('gamma', [R(1, 4)]), 2), mul(4, sqrt(mul(2, S.Pi))));
  if (isInfinite(m)) return S.Zero;
  return undefined;
};

/** SymPy elliptic_f.eval. */
evaluators.elliptic_f = (z, ...rest) => {
  const m = first(rest);
  if (isZero(z) === true) return S.Zero;
  if (isZero(m) === true) return z;
  const k = div(mul(2, z), S.Pi);
  if (isIntegerQ(k) === true) return mul(k, ellipticK(m));
  if (isRealInfinite(m)) return S.Zero;
  if (couldExtractMinusSign(z)) return neg(ellipticF(neg(z), m));
  return undefined;
};

/** SymPy elliptic_e.eval (the arguments are (m) or (z, m)). */
evaluators.elliptic_e = (a, ...rest) => {
  const b = rest[0];
  if (b !== undefined) {
    const [z, m] = [a, b];
    const k = div(mul(2, z), S.Pi);
    if (isZero(m) === true) return z;
    if (isZero(z) === true) return S.Zero;
    if (isIntegerQ(k) === true) return mul(k, ellipticE(m));
    if (isRealInfinite(m)) return S.ComplexInfinity;
    if (couldExtractMinusSign(z)) return neg(ellipticE(neg(z), m));
    return undefined;
  }
  const m = a;
  if (isZero(m) === true) return mul(S.Pi, S.Half);
  if (isRat(m, 1n)) return S.One;
  if (isSpecial(m, 'oo')) return mul(S.I, S.Infinity);
  if (isSpecial(m, '-oo')) return S.Infinity;
  if (isSpecial(m, 'zoo')) return S.ComplexInfinity;
  return undefined;
};

/** SymPy elliptic_pi.eval (the arguments are (n, m) or (n, z, m)). */
evaluators.elliptic_pi = (n, ...rest) => {
  const a = first(rest);
  const b = rest[1];
  if (b !== undefined) {
    const [z, m] = [a, b];
    if (isZero(n) === true) return ellipticF(z, m);
    if (isRat(n, 1n)) return add(ellipticF(z, m), div(sub(mul(delta(z, m), tan(z)), ellipticE(z, m)), sub(1, m)));
    const k = div(mul(2, z), S.Pi);
    if (isIntegerQ(k) === true) return mul(k, ellipticPi(n, m));
    if (isZero(m) === true) return div(fn('atanh', [mul(sqrt(sub(n, 1)), tan(z))]), sqrt(sub(n, 1)));
    if (n.key === m.key) return add(ellipticF(z, n), neg(ellipticPi(1, z, n)), div(tan(z), delta(z, n)));
    if (isRealInfinite(n) || isRealInfinite(m)) return S.Zero;
    if (couldExtractMinusSign(z)) return neg(ellipticPi(n, neg(z), m));
    return undefined;
  }
  const m = a;
  if (isZero(n) === true) return ellipticK(m);
  if (isRat(n, 1n)) return S.ComplexInfinity;
  if (isZero(m) === true) return div(S.Pi, mul(2, sqrt(sub(1, n))));
  if (isRat(m, 1n)) return div(S.NegativeInfinity, sign(sub(n, 1)));
  if (n.key === m.key) return div(ellipticE(n), sub(1, n));
  if (isRealInfinite(n) || isRealInfinite(m)) return S.Zero;
  return undefined;
};

// ---- derivatives ----------------------------------------------------------------------

fnPartials.elliptic_k = (args) => {
  const m = at(args, 0);
  return div(sub(ellipticE(m), mul(sub(1, m), ellipticK(m))), mul(2, m, sub(1, m)));
};

fnPartials.elliptic_f = (args, i) => {
  const [z, m] = pair(args);
  const fm = delta(z, m);
  if (i === 0) return pow(fm, -1);
  return add(div(ellipticE(z, m), mul(2, m, sub(1, m))), neg(div(ellipticF(z, m), mul(2, m))), neg(div(sin(mul(2, z)), mul(mul(4, sub(1, m)), fm))));
};

fnPartials.elliptic_e = (args, i) => {
  if (args.length === 2) {
    const [z, m] = pair(args);
    if (i === 0) return delta(z, m);
    return div(sub(ellipticE(z, m), ellipticF(z, m)), mul(2, m));
  }
  const m = at(args, 0);
  return div(sub(ellipticE(m), ellipticK(m)), mul(2, m));
};

fnPartials.elliptic_pi = (args, i) => {
  if (args.length === 3) {
    const [n, z, m] = [at(args, 0), at(args, 1), at(args, 2)];
    const fm = delta(z, m);
    const fn1 = sub(1, mul(n, pow(sin(z), 2)));
    if (i === 0) {
      const num = add(ellipticE(z, m), div(mul(sub(m, n), ellipticF(z, m)), n), div(mul(sub(pow(n, 2), m), ellipticPi(n, z, m)), n), neg(div(mul(n, fm, sin(mul(2, z))), mul(2, fn1))));
      return div(num, mul(mul(2, sub(m, n)), sub(n, 1)));
    }
    if (i === 1) return pow(mul(fm, fn1), -1);
    return div(add(div(ellipticE(z, m), sub(m, 1)), ellipticPi(n, z, m), neg(div(mul(m, sin(mul(2, z))), mul(mul(2, sub(m, 1)), fm)))), mul(2, sub(n, m)));
  }
  const [n, m] = pair(args);
  if (i === 0) return div(add(ellipticE(m), div(mul(sub(m, n), ellipticK(m)), n), div(mul(sub(pow(n, 2), m), ellipticPi(n, m)), n)), mul(mul(2, sub(m, n)), sub(n, 1)));
  return div(add(div(ellipticE(m), sub(m, 1)), ellipticPi(n, m)), mul(2, sub(n, m)));
};

// ---- series ---------------------------------------------------------------------------

/** ((1/2)_j/j!)**2 = (binomial(2j, j)/4**j)**2. */
function halfRatioSquared(j: number): Rational {
  let p = 1n;
  let q = 1n;
  for (let k = 1n; k <= BigInt(j); k++) {
    p *= 2n * k - 1n;
    q *= 2n * k;
  }
  return R(p * p, q * q);
}
// K(m) = pi/2 hyper((1/2, 1/2), (1,), m), E(m) = pi/2 hyper((-1/2, 1/2), (1,), m)
// (SymPy elliptic_k._eval_nseries; the derivatives at m = 0 are 0/0 forms)
fnTaylorAtZero.elliptic_k = (j) => mul(S.Pi, S.Half, halfRatioSquared(j));
fnTaylorAtZero.elliptic_e = (j) => mul(S.Pi, S.Half, halfRatioSquared(j), R(-1, 2 * j - 1));

// ---- conjugation ----------------------------------------------------------------------

/** (m.is_real and (m - 1).is_positive) is False: not on the branch cut m > 1. */
function offCut(m: Expr): boolean {
  const r = isReal(m);
  if (r === false) return true;
  const d = sub(m, 1);
  return r === true && (isPositive(d) === false || isNegative(d) === true);
}
const conjugateIf = (name: FnName, args: readonly Expr[], ok: boolean): Expr => (ok ? fn(name, args.map(conjugate)) : new Fn('conjugate', [new Fn(name, args)]));
conjugateRules.elliptic_k = (args) => conjugateIf('elliptic_k', args, offCut(at(args, 0)));
conjugateRules.elliptic_f = (args) => conjugateIf('elliptic_f', args, offCut(at(args, 1)));
conjugateRules.elliptic_e = (args) => conjugateIf('elliptic_e', args, offCut(at(args, args.length - 1)));
conjugateRules.elliptic_pi = (args) => conjugateIf('elliptic_pi', args, args.length === 2 || (offCut(at(args, 0)) && offCut(at(args, 2))));

// ---- rewrites -------------------------------------------------------------------------

registerRewrite('elliptic_k', 'hyper', (args) => mul(S.Pi, S.Half, hyper([S.Half, S.Half], [1], at(args, 0))));
registerRewrite('elliptic_k', 'meijerg', (args) => mul(S.Half, meijerg([S.Half, S.Half], [], [0], [0], neg(at(args, 0)))));
registerRewrite('elliptic_e', 'hyper', (args) => (args.length === 1 ? mul(S.Pi, S.Half, hyper([R(-1, 2), S.Half], [1], at(args, 0))) : undefined));
registerRewrite('elliptic_e', 'meijerg', (args) => (args.length === 1 ? mul(R(-1, 4), meijerg([S.Half, R(3, 2)], [], [0], [0], neg(at(args, 0)))) : undefined));

for (const name of ['elliptic_k', 'elliptic_e', 'elliptic_f', 'elliptic_pi'] as const) numericFns[name] = (args) => mpNumeric(name, args);
