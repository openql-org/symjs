// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy core.expr construction helpers. */
import { Expr, Piecewise, S } from './nodes';
import { sympify } from './ops';
import { sympyClassName } from './compare';

/** SymPy unchanged(func, ...args): construction preserves the function and its arguments. */
export function unchanged<A extends unknown[]>(func: (...args: A) => Expr, ...args: A): boolean {
  const result = func(...args);
  const name = func.name.replace(/Node$/, '');
  if (sympyClassName(result).toLowerCase() !== name.toLowerCase()) return false;
  const expected = result instanceof Piecewise ? args.flat() : args;
  return result.args.length === expected.length && result.args.every((e, i) => {
    const a: unknown = expected[i];
    if (typeof a === 'boolean') return e.equals(a ? S.true : S.false);
    return (a instanceof Expr || typeof a === 'number' || typeof a === 'bigint') && e.equals(sympify(a));
  });
}
