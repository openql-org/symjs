// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Mathieu functions (SymPy functions/special/mathieu_functions.py):
 * mathieus, mathieuc, mathieusprime and mathieucprime with SymPy's
 * evaluation rules, derivatives and conjugate. Like SymPy, they have no
 * numerical evaluation.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import { NotImplementedError } from '../../core/errors';
import { at } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { isNum, registerFunctionHeads } from '../../core/nodes';
import { isZero } from '../../core/assumptions';
import { add, couldExtractMinusSign, mul, neg, sqrt } from '../../core/ops';
import { fnPartials } from '../../calculus/diff';
import { conjugateCommutes, cos, evaluators, fn, sin } from '../elementary/elementary';

type MName = 'mathieus' | 'mathieuc' | 'mathieusprime' | 'mathieucprime';

/** [the value at q = 0, the parity in z (-1: odd), the derivative in z] of each function. */
const RULES: Record<MName, [(a: Expr, z: Expr) => Expr, 1 | -1, (a: Expr, q: Expr, z: Expr) => Expr]> = {
  mathieus: [(a, z) => sin(mul(sqrt(a), z)), -1, (a, q, z) => fn('mathieusprime', [a, q, z])],
  mathieuc: [(a, z) => cos(mul(sqrt(a), z)), 1, (a, q, z) => fn('mathieucprime', [a, q, z])],
  // d/dz mathieusprime = (2*q*cos(2*z) - a)*mathieus, likewise mathieucprime
  mathieusprime: [(a, z) => mul(sqrt(a), cos(mul(sqrt(a), z))), 1, (a, q, z) => mul(add(mul(2, q, cos(mul(2, z))), neg(a)), fn('mathieus', [a, q, z]))],
  mathieucprime: [(a, z) => mul(-1, sqrt(a), sin(mul(sqrt(a), z))), -1, (a, q, z) => mul(add(mul(2, q, cos(mul(2, z))), neg(a)), fn('mathieuc', [a, q, z]))],
};

for (const name of ['mathieus', 'mathieuc', 'mathieusprime', 'mathieucprime'] as const) {
  const [atZero, parity, derivative] = RULES[name];
  evaluators[name] = (a, ...qz) => {
    const [q, z] = [at(qz, 0), at(qz, 1)];
    if (isNum(q) && isZero(q) === true) return atZero(a, z);
    // pull out factors of -1
    if (couldExtractMinusSign(z)) return mul(parity, fn(name, [a, q, neg(z)]));
    return undefined;
  };
  fnPartials[name] = (args, i) => {
    if (i !== 2) throw new NotImplementedError(`diff: ${name} w.r.t. argument ${i + 1}`);
    return derivative(at(args, 0), at(args, 1), at(args, 2));
  };
  // (SymPy MathieuBase._eval_conjugate)
  conjugateCommutes.add(name);
}

/**
 * The Mathieu sine function.
 *
 * @param a - The characteristic value.
 * @param q - The Mathieu parameter.
 * @param z - The argument of the function.
 * @returns The Mathieu sine function.
 * @see SymPy `sympy.functions.special.mathieu_functions.mathieus`
 * @example
 * ```ts
 * import { ex, mathieus } from '@symjs/symjs';
 *
 * mathieus(ex`a`, 0, ex`z`); // => sin(sqrt(a)*z)
 * mathieus(ex`a`, ex`q`, ex`z`); // => mathieus(a, q, z)
 * ```
 */
export const mathieus = (a: ExprLike, q: ExprLike, z: ExprLike): Expr => fn('mathieus', [a, q, z]);
/**
 * The Mathieu cosine function.
 *
 * @param a - The characteristic value.
 * @param q - The Mathieu parameter.
 * @param z - The argument of the function.
 * @returns The Mathieu cosine function.
 * @see SymPy `sympy.functions.special.mathieu_functions.mathieuc`
 * @example
 * ```ts
 * import { ex, mathieuc } from '@symjs/symjs';
 *
 * mathieuc(ex`a`, 0, ex`z`); // => cos(sqrt(a)*z)
 * mathieuc(ex`a`, ex`q`, ex`z`); // => mathieuc(a, q, z)
 * ```
 */
export const mathieuc = (a: ExprLike, q: ExprLike, z: ExprLike): Expr => fn('mathieuc', [a, q, z]);
/**
 * The derivative of the Mathieu sine function.
 *
 * @param a - The characteristic value.
 * @param q - The Mathieu parameter.
 * @param z - The argument of the function.
 * @returns The derivative of the Mathieu sine function.
 * @see SymPy `sympy.functions.special.mathieu_functions.mathieusprime`
 * @example
 * ```ts
 * import { ex, mathieusprime } from '@symjs/symjs';
 *
 * mathieusprime(ex`a`, 0, ex`z`); // => sqrt(a)*cos(sqrt(a)*z)
 * mathieusprime(ex`a`, ex`q`, ex`z`); // => mathieusprime(a, q, z)
 * ```
 */
export const mathieusprime = (a: ExprLike, q: ExprLike, z: ExprLike): Expr => fn('mathieusprime', [a, q, z]);
/**
 * The derivative of the Mathieu cosine function.
 *
 * @param a - The characteristic value.
 * @param q - The Mathieu parameter.
 * @param z - The argument of the function.
 * @returns The derivative of the Mathieu cosine function.
 * @see SymPy `sympy.functions.special.mathieu_functions.mathieucprime`
 * @example
 * ```ts
 * import { ex, mathieucprime } from '@symjs/symjs';
 *
 * mathieucprime(ex`a`, 0, ex`z`); // => -sqrt(a)*sin(sqrt(a)*z)
 * mathieucprime(ex`a`, ex`q`, ex`z`); // => mathieucprime(a, q, z)
 * ```
 */
export const mathieucprime = (a: ExprLike, q: ExprLike, z: ExprLike): Expr => fn('mathieucprime', [a, q, z]);

registerFunctionHeads([
  ['mathieus', mathieus],
  ['mathieuc', mathieuc],
  ['mathieusprime', mathieusprime],
  ['mathieucprime', mathieucprime],
]);
