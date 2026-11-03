// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Small helpers shared by the matrix expression modules: fuzzy
 * comparisons of dimensions, precedence values of SymPy's printers and
 * slicing of index ranges.
 */

import type { Expr } from '../../core/nodes';
import { BoolAtom, Derivative, Float, Integral, Limit, Rational, S } from '../../core/nodes';
import { Concrete } from '../../core/concrete';
import { rel } from '../../core/logic';
import { isNegative, isPositive, isReal } from '../../core/assumptions';
import { add, mul } from '../../core/ops';
import type { Truth } from '../../core/truth';
import { precedence } from '../../printing/str';
import { at, expectType } from '../../core/guard';

/** SymPy precedence values (sympy.printing.precedence.PRECEDENCE). */
export const PRECEDENCE = { Add: 40, Mul: 50, Pow: 60, Atom: 1000 } as const;

/** An explicit integer (SymPy Integer). */
export const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;

/** A number (SymPy Number: Rational or Float). */
export const isNumber = (e: Expr): e is Rational | Float => e instanceof Rational || e instanceof Float;

/** Structural equality (SymPy ==). */
export const same = (a: Expr, b: Expr): boolean => a === b || a.key === b.key;

/** Structural equality of two lists of expressions. */
export const sameList = (a: readonly Expr[], b: readonly Expr[]): boolean => a.length === b.length && a.every((x, i) => same(x, at(b, i)));

/** The truth value of a relation (SymPy `(a < b) == True` and `== False`). */
export function relTruth(op: 'Eq' | 'Ne' | 'Lt' | 'Le' | 'Gt' | 'Ge', a: Expr, b: Expr): Truth {
  // SymPy leaves inequalities between expressions not known to be real unevaluated
  if (op !== 'Eq' && op !== 'Ne' && (isReal(a) !== true || isReal(b) !== true)) return 'unknown';
  const r = rel(op, a, b);
  if (r instanceof BoolAtom) return r.value;
  if (op === 'Eq' || op === 'Ne') return 'unknown';
  // the sign of the difference (SymPy is_lt: (n + i < n) is False for a nonnegative i)
  const d = add(a, mul(-1, b));
  const t = op === 'Lt' || op === 'Ge' ? isNegative(d) : isPositive(d);
  if (t === undefined) return 'unknown';
  return op === 'Lt' || op === 'Gt' ? t : !t;
}

/** A JavaScript integer from an explicit integer expression. */
export function toInt(e: Expr): number {
  return Number(expectType(e, (x): x is Rational => x instanceof Rational, 'integer').p);
}

/** SymPy precedence_traditional for scalar expressions (used by the LaTeX printer). */
export function scalarPrecTraditional(e: Expr): number {
  if (e instanceof Integral || e instanceof Concrete || e instanceof Limit || e instanceof Derivative) return PRECEDENCE.Mul;
  return precedence(e);
}

/** One as an expression (shorthand). */
export const ONE: Expr = S.One;
