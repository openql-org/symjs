// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Relations, boolean constants and Piecewise.
 */

import { Special } from './nodes';
import type { Expr, ExprLike, RelOp } from './nodes';
import { BoolAtom, Piecewise, Rational, Rel, S, isNum } from './nodes';
import { numCmp } from './num';
import { add, mul, sympify } from './ops';
import { BoolOp } from './boolalg';

const isBoolean = (e: Expr): boolean => e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp;

/** Create a relation, evaluating it to True/False when the difference is a number. */
export function rel(op: RelOp, a: ExprLike, b: ExprLike): Expr {
  const lhs = sympify(a);
  const rhs = sympify(b);
  // nan is not equal to anything (SymPy Eq(nan, nan) is False)
  if ([lhs, rhs].some((x) => x instanceof Special && x.name === 'nan')) {
    if (op === 'Eq') return S.false;
    if (op === 'Ne') return S.true;
  }
  const d = add(lhs, mul(-1, rhs));
  if (isNum(d)) {
    const c = d instanceof Rational ? numCmp(d, S.Zero) : Math.sign((d).value);
    const v = { Eq: c === 0, Ne: c !== 0, Lt: c < 0, Le: c <= 0, Gt: c > 0, Ge: c >= 0 }[op];
    return v ? S.true : S.false;
  }
  if ((op === 'Eq' || op === 'Ne') && lhs.key === rhs.key) return op === 'Eq' ? S.true : S.false;
  // numeric expressions that are clearly different
  if ((op === 'Eq' || op === 'Ne') && d.freeSymbols().size === 0 && !(d instanceof Special)) {
    try {
      const v = d.toComplex();
      if (Math.hypot(v.re, v.im) > 1e-9) return op === 'Eq' ? S.false : S.true;
    } catch {
      // not numerically evaluable
    }
  }
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
    let c = typeof c0 === 'boolean' ? (c0 ? S.true : S.false) : sympify(c0);
    // a boolean Piecewise as a condition is the if-then-else ITE(c1, a, b) (SymPy rewrite(ITE))
    if (c instanceof Piecewise && c.args.length === 4 && isTrue(c.args[3]!) && isBoolean(c.args[0]!) && isBoolean(c.args[2]!)) {
      // the relations are canonical (a number on the right: 2 < y -> y > 2)
      const flip: Record<string, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
      const canon = (r: Expr): Expr => (r instanceof Rel && isNum(r.lhs) && !isNum(r.rhs) ? new Rel(flip[r.op]!, r.rhs, r.lhs) : r);
      c = new BoolOp('ITE', [canon(c.args[1]!), canon(c.args[0]!), canon(c.args[2]!)]);
    }
    if (isFalse(c)) continue;
    out.push(sympify(e), c);
    if (isTrue(c)) break;
  }
  if (out.length === 0) throw new RangeError('piecewise: no condition can be satisfied');
  if (out.length === 2 && isTrue(out[1]!)) return out[0]!;
  return new Piecewise(out);
}
