// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy core.expr construction helpers. */
import { Expr, Piecewise, S } from './nodes';
import { sympify } from './ops';
import { sympyClassName } from './compare';

/** A Poly (structurally: core does not depend on polys). */
function isPolyLike(a: unknown): a is { asExpr(): Expr; gens: readonly Expr[] } {
  return typeof a === 'object' && a !== null && !(a instanceof Expr) && typeof Reflect.get(a, 'asExpr') === 'function' && Array.isArray(Reflect.get(a, 'gens'));
}

/**
 * Tests whether applying a constructor preserves the function and its arguments.
 *
 * @param func - The callable to inspect.
 * @param args - The arguments in positional order.
 * @returns True if applying the constructor preserves both the head and arguments.
 * @see SymPy `sympy.core.expr.unchanged`
 * @example
 * ```ts
 * import { ex, sin, unchanged } from '@symjs/symjs';
 *
 * unchanged(sin, ex`x`); // => True
 * ```
 */
export function unchanged<A extends unknown[]>(func: (...args: A) => Expr, ...args: A): boolean {
  const result = func(...args);
  const name = func.name.replace(/Node$/, '');
  const relationNames: Readonly<Record<string, string>> = { Eq: 'Equality', Ne: 'Unequality', Lt: 'StrictLessThan', Le: 'LessThan', Gt: 'StrictGreaterThan', Ge: 'GreaterThan' };
  if (sympyClassName(result).toLowerCase() !== (relationNames[name] ?? name).toLowerCase()) return false;
  // a polynomial argument is held as its SymPy args (the expression and the generators)
  const expected = (result instanceof Piecewise ? args.flat() : args).flatMap((a: unknown) => (isPolyLike(a) ? [a.asExpr(), ...a.gens] : [a]));
  return result.args.length === expected.length && result.args.every((e, i) => {
    const a: unknown = expected[i];
    if (typeof a === 'boolean') return e.equals(a ? S.true : S.false);
    return (a instanceof Expr || typeof a === 'number' || typeof a === 'bigint') && e.equals(sympify(a));
  });
}
