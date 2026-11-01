// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Relations, boolean constants and Piecewise.
 */

import { BoolAtom, Expr, ExprLike, Float, Piecewise, Rational, Rel, RelOp, S, isNum } from './nodes';
import { numCmp } from './num';
import { add, mul, sympify } from './ops';

/** Create a relation, evaluating it to True/False when the difference is a number. */
export function rel(op: RelOp, a: ExprLike, b: ExprLike): Expr {
  const lhs = sympify(a);
  const rhs = sympify(b);
  const d = add(lhs, mul(-1, rhs));
  if (isNum(d)) {
    const c = d instanceof Rational ? numCmp(d, S.Zero) : Math.sign((d as Float).value);
    const v = { Eq: c === 0, Ne: c !== 0, Lt: c < 0, Le: c <= 0, Gt: c > 0, Ge: c >= 0 }[op];
    return v ? S.true : S.false;
  }
  if ((op === 'Eq' || op === 'Ne') && lhs.key === rhs.key) return op === 'Eq' ? S.true : S.false;
  return new Rel(op, lhs, rhs);
}

export const Eq = (a: ExprLike, b: ExprLike): Expr => rel('Eq', a, b);
export const Ne = (a: ExprLike, b: ExprLike): Expr => rel('Ne', a, b);
export const Lt = (a: ExprLike, b: ExprLike): Expr => rel('Lt', a, b);
export const Le = (a: ExprLike, b: ExprLike): Expr => rel('Le', a, b);
export const Gt = (a: ExprLike, b: ExprLike): Expr => rel('Gt', a, b);
export const Ge = (a: ExprLike, b: ExprLike): Expr => rel('Ge', a, b);

const isTrue = (c: Expr) => c instanceof BoolAtom && c.value;
const isFalse = (c: Expr) => c instanceof BoolAtom && !c.value;

/**
 * Piecewise((e1, c1), (e2, c2), ...). Pairs with a False condition are dropped,
 * pairs after a True condition are unreachable, and Piecewise((e, True)) is e.
 */
export function piecewise(...pairs: readonly (readonly [ExprLike, ExprLike | boolean])[]): Expr {
  const out: Expr[] = [];
  for (const [e, c0] of pairs) {
    const c = typeof c0 === 'boolean' ? (c0 ? S.true : S.false) : sympify(c0);
    if (isFalse(c)) continue;
    out.push(sympify(e), c);
    if (isTrue(c)) break;
  }
  if (out.length === 0) throw new Error('piecewise: no condition can be satisfied');
  if (out.length === 2 && isTrue(out[1]!)) return out[0]!;
  return new Piecewise(out);
}
