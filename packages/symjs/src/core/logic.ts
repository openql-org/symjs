// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Relations, boolean constants and Piecewise.
 */

import { Special } from './nodes';
import type { Expr, ExprLike, RelOp } from './nodes';
import { BoolAtom, Float, Piecewise, Rational, Rel, S, isNum } from './nodes';
import { numCmp } from './num';
import { add, mul, sympify } from './ops';
import { BoolOp } from './boolalg';
import { at } from './guard';
import { isNegative, isNonNegative, isPositive } from './assumptions';

const isBoolean = (e: Expr): boolean => e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp;
const isSpecial = (name: string) => (x: Expr): boolean => x instanceof Special && x.name === name;

/** Create a relation, evaluating it to True/False when the difference is a number. */
export function rel(op: RelOp, a: ExprLike, b: ExprLike): Expr {
  const lhs = sympify(a);
  const rhs = sympify(b);
  const equality = op === 'Eq' || op === 'Ne';
  // nan is not equal to anything (SymPy Eq(nan, nan) is False) and cannot be ordered
  if ([lhs, rhs].some(isSpecial('nan'))) {
    if (!equality) throw new TypeError('Invalid NaN comparison');
    return op === 'Eq' ? S.false : S.true;
  }
  if (!equality && [lhs, rhs].some(isSpecial('zoo'))) throw new TypeError('Invalid comparison of non-real zoo');
  const byCmp = (c: number): Expr => ({ Eq: c === 0, Ne: c !== 0, Lt: c < 0, Le: c <= 0, Gt: c > 0, Ge: c >= 0 }[op] ? S.true : S.false);
  // equal sides (such as oo and oo, whose difference is nan)
  if (lhs.key === rhs.key) return byCmp(0);
  const d = add(lhs, mul(-1, rhs));
  if (d instanceof Rational) return byCmp(numCmp(d, S.Zero));
  if (d instanceof Float) return byCmp(Math.sign(d.value));
  // the difference is oo or -oo for oo against a finite number (SymPy Lt(-oo, oo) is True)
  if (isSpecial('oo')(d) || isSpecial('-oo')(d)) return byCmp(isSpecial('oo')(d) ? 1 : -1);
  // zoo differs from every finite number and from oo (the difference is zoo or nan)
  if (equality && d instanceof Special) return op === 'Eq' ? S.false : S.true;
  // numeric expressions that are clearly different
  if (equality && d.freeSymbols().size === 0) {
    try {
      const v = d.toComplex();
      if (Math.hypot(v.re, v.im) > 1e-9) return op === 'Eq' ? S.false : S.true;
    } catch {
      // not numerically evaluable
    }
  }
  if (!equality) {
    const decided = orderTruth(op, d);
    if (decided !== undefined) return decided ? S.true : S.false;
  }
  return new Rel(op, lhs, rhs);
}

/**
 * SymPy is_lt/is_le/is_gt/is_ge of lhs - rhs = d: decided by the sign the
 * assumptions give d (which evaluate real numbers numerically); undefined
 * when it cannot be decided.
 */
function orderTruth(op: 'Lt' | 'Le' | 'Gt' | 'Ge', d: Expr): boolean | undefined {
  const lower = op === 'Lt' || op === 'Le';
  // Lt and Le ask about -d > 0 and -d >= 0
  const v = lower ? mul(-1, d) : d;
  const strict = op === 'Lt' || op === 'Gt';
  if ((strict ? isPositive(v) : isNonNegative(v)) === true) return true;
  if ((strict ? isNonNegative(mul(-1, v)) : isNegative(v)) === true) return false;
  return undefined;
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
    if (c instanceof Piecewise && c.args.length === 4 && isTrue(at(c.args, 3)) && isBoolean(at(c.args, 0)) && isBoolean(at(c.args, 2))) {
      // the relations are canonical (a number on the right: 2 < y -> y > 2)
      const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
      const canon = (r: Expr): Expr => (r instanceof Rel && isNum(r.lhs) && !isNum(r.rhs) ? new Rel(flip[r.op], r.rhs, r.lhs) : r);
      c = new BoolOp('ITE', [canon(at(c.args, 1)), canon(at(c.args, 0)), canon(at(c.args, 2))]);
    }
    if (isFalse(c)) continue;
    out.push(sympify(e), c);
    if (isTrue(c)) break;
  }
  // SymPy: no condition can hold, so the value is undefined (nan)
  if (out.length === 0) return S.NaN;
  if (out.length === 2 && isTrue(at(out, 1))) return at(out, 0);
  return new Piecewise(out);
}
