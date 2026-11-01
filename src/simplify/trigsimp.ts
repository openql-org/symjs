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

import { Constant, Expr, ExprLike, Fn, Pow, S } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, neg, sympify } from '../core/ops';
import { mapBottomUp, some } from '../core/traverse';
import { cos, sin } from '../functions/elementary';
import { expand } from './expand';

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
const isI = (e: Expr) => e instanceof Constant && e.name === 'I';

export const hasTrig = (e: Expr): boolean =>
  some(e, (x) => (x instanceof Fn && (x.name === 'sin' || x.name === 'cos' || x.name === 'tan')) || (x instanceof Pow && isE(x.base)));

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

/** Simplify trigonometric and complex-exponential expressions. */
export function trigsimp(ex: ExprLike): Expr {
  const e = sympify(ex);
  if (!hasTrig(e)) return e;
  return expand(rewriteTrig(expand(rewriteExp(e))));
}

/** Exponential form: sin/cos rewritten as exponentials and expanded. */
export function expsimp(ex: ExprLike): Expr {
  return expand(rewriteExp(sympify(ex)));
}

