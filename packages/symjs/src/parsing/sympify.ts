// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy core.sympify's string helper, beside the parser to keep the kernel independent. */
import type { Expr } from '../core/nodes';
import { Add, Float, Mul, Rational } from '../core/nodes';
import { at } from '../core/guard';
import { rebuild } from '../core/traverse';
import { parse } from './parser';

/**
 * Parses and simplifies an expression while preserving numeric multiples of parenthesized sums.
 *
 * @param source - The source text to parse.
 * @returns The expression with grouped numeric multiples preserved.
 * @see SymPy `sympy.core.sympify.kernS`
 * @example
 * ```ts
 * import { kernS } from '@symjs/symjs';
 *
 * kernS('-(x + 1)'); // => -(x + 1)
 * kernS('2*(x + y)'); // => 2*(x + y)
 * ```
 */
export function kernS(source: string): Expr {
  const visit = (e: Expr): Expr => {
    const args = e.args.map(visit);
    if (e instanceof Mul && args.length === 2) {
      const a = at(args, 0), b = at(args, 1);
      if ((a instanceof Rational || a instanceof Float) && b instanceof Add) return new Mul(args);
    }
    return rebuild(e, args);
  };
  return visit(parse(source, { evaluate: false }));
}
