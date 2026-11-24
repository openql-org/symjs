// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { ExprLike, FnName, Head } from './nodes';
import { E, Fn, Pow, S } from './nodes';
import { exp, sympify } from './ops';
import { NotImplementedError } from './errors';

const inverses: Partial<Record<FnName | 'exp', FnName | 'exp'>> = {
  exp: 'log', log: 'exp', conjugate: 'conjugate',
  sin: 'asin', cos: 'acos', tan: 'atan', cot: 'acot',
  asin: 'sin', acos: 'cos', atan: 'tan', acot: 'cot',
  sinh: 'asinh', tanh: 'atanh', coth: 'acoth',
  asinh: 'sinh', acosh: 'cosh', atanh: 'tanh', acoth: 'coth',
  asech: 'sech', acsch: 'csch',
  erf: 'erfinv', erfc: 'erfcinv', erfinv: 'erf', erfcinv: 'erfc',
};

/**
 * The inverse function head of a function application.
 *
 * @param f - The applied function.
 * @param argindex - The one-based index of the argument.
 * @returns The inverse function head.
 * @throws TypeError when the input is not a function application.
 * @throws RangeError when the argument index is invalid.
 * @throws NotImplementedError when the function has no registered inverse.
 * @see SymPy `sympy.functions.elementary.exponential.log.inverse`
 * @example
 * ```ts
 * import { ex, exp, inverse, log } from '@symjs/symjs';
 *
 * inverse(log(ex`x`)) === exp; // => True
 * ```
 */
export function inverse(f: ExprLike, argindex = 1): Head {
  const e = sympify(f);
  const functionName = e instanceof Fn ? e.name : e instanceof Pow && e.base.equals(E) ? 'exp' : undefined;
  if (functionName === undefined) throw new TypeError('inverse: expected a function application');
  if (argindex !== 1) throw new RangeError('inverse: invalid argument index');
  const name = inverses[functionName];
  if (name === undefined) throw new NotImplementedError(`inverse: no inverse for ${functionName}`);
  return name === 'exp' ? exp : new Fn(name, [S.Zero]).func;
}
