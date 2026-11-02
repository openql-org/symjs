// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Trigonometric / exponential simplification via the exponential form.
 *
 * Strategy: rewrite sin/cos as complex exponentials, expand (products of
 * exponentials combine automatically), then convert each exp(I*y) back to
 * cos(y) + I*sin(y). This proves identities such as sin^2 + cos^2 = 1 and
 * collapses angle-addition patterns like cos(a)cos(b) - sin(a)sin(b) -> cos(a+b),
 * which are ubiquitous in products of rotation gates.
 */

import { Constant, Expr, ExprLike, Fn, Mul, Pow, S } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, neg, sympify } from '../core/ops';
import { countOps, mapBottomUp, some } from '../core/traverse';
import { cos, sin } from '../functions/elementary';
import { expandMul as expand } from './expand';

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
const isI = (e: Expr) => e instanceof Constant && e.name === 'I';

const isTrigFn = (x: Expr) => x instanceof Fn && (x.name === 'sin' || x.name === 'cos' || x.name === 'tan');

/** Contains sin/cos/tan. */
export const hasTrigFunctions = (e: Expr): boolean => some(e, isTrigFn);

/** Contains sin/cos/tan or exp. */
export const hasTrig = (e: Expr): boolean => some(e, (x) => isTrigFn(x) || (x instanceof Pow && isE(x.base)));

/** Combine all exp() factors of each product into a single exp (SymPy `powsimp` for exp). */
export function combineExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Mul)) return e;
    const exps = e.args.filter((f) => f instanceof Pow && isE(f.base)) as Pow[];
    if (exps.length < 2) return e;
    const others = e.args.filter((f) => !(f instanceof Pow && isE(f.base)));
    return mul(...others, exp(expand(add(...exps.map((f) => f.exp)))));
  });
}

/** Rewrite sin, cos (and tan) in terms of exp. */
export function rewriteExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Fn)) return e;
    const u = e.args[0]!;
    const ep = exp(mul(S.I, u));
    const em = exp(mul(-1, S.I, u));
    if (e.name === 'cos') return mul(S.Half, add(ep, em));
    if (e.name === 'sin') return mul(neg(S.I), S.Half, add(ep, mul(-1, em)));
    if (e.name === 'tan') return mul(neg(S.I), add(ep, mul(-1, em)), add(ep, em).pow(-1));
    return e;
  });
}

/** If e = exp(I*y) with I-free y, return y. */
function imaginaryExponent(e: Expr): Expr | undefined {
  if (!(e instanceof Pow && isE(e.base))) return undefined;
  const y = expand(mul(-1, S.I, e.exp));
  if (some(y, isI)) return undefined;
  return y;
}

/** Rewrite exp(I*y) as cos(y) + I*sin(y) (y chosen with a canonical sign). */
export function rewriteTrig(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    const y = imaginaryExponent(e);
    if (y === undefined) return e;
    if (couldExtractMinusSign(y)) {
      const z = neg(y);
      return add(cos(z), mul(-1, S.I, sin(z)));
    }
    return add(cos(y), mul(S.I, sin(y)));
  });
}

/** Rewrite to trigonometric form via exponentials (exp(I*y) -> cos(y) + I*sin(y)). */
export function exptotrig(ex: ExprLike): Expr {
  return expand(rewriteTrig(expsimp(ex)));
}

/**
 * Simplify expressions containing trigonometric functions. Like SymPy, an
 * expression without trigonometric functions is returned unchanged, and the
 * result is never more complex than the input.
 */
export function trigsimp(ex: ExprLike): Expr {
  const e = sympify(ex);
  if (!hasTrigFunctions(e)) return e;
  const t = exptotrig(e);
  // SymPy futrig objective: fewer trigonometric functions first, then count_ops
  const lt = trigCount(t);
  const le = trigCount(e);
  if (lt !== le) return lt < le && countOps(t) <= countOps(e) + 1 ? t : countOps(t) <= countOps(e) ? t : e;
  return countOps(t) <= countOps(e) ? t : e;
}

const TRIG_NAMES = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);
function trigCount(e: Expr): number {
  let n = 0;
  some(e, (x) => {
    if (x instanceof Fn && TRIG_NAMES.has(x.name)) n++;
    return false;
  });
  return n;
}

/** Exponential form: sin/cos rewritten as exponentials, expanded and combined. */
export function expsimp(ex: ExprLike): Expr {
  return combineExp(expand(rewriteExp(sympify(ex))));
}

