// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Schur numbers (SymPy sympy.combinatorics.schur_number): S(k), the
 * largest n for which [1, n] can be partitioned into k sum-free sets, and
 * a partition of [1, n] into sum-free sets.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Rational, S } from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { at } from '../core/guard';

const KNOWN = [0n, 1n, 4n, 13n, 44n, 160n];

/**
 * S(k) for k <= 5 (and S(oo) = oo, S(0) = 0); the
 * unevaluated SchurNumberNode otherwise, whose lowerBound() is a known lower bound.
 * @param kIn - The number of sum-free color classes.
 * @returns The resulting symbolic expression.
 * @throws RangeError when `k` is not a positive integer.
 * @see SymPy `sympy.combinatorics.schur_number.SchurNumber`
 * @example
 * ```ts
 * import { SchurNumber } from '@symjs/symjs';
 * SchurNumber(3); // => 13
 * ```
 */
export function SchurNumber(kIn: ExprLike): Expr {
  const k = sympify(kIn);
  if (k === S.Infinity) return S.Infinity;
  if (k instanceof Rational || k.isNumber) {
    if (!(k instanceof Rational) || k.q !== 1n || k.p < 0n) throw new RangeError('k should be a positive integer');
    if (k.p <= 5n) return Rational.of(at(KNOWN, Number(k.p)));
  }
  return new SchurNumberNode(k);
}

/**
 * The unevaluated SymPy SchurNumber(k).
 * @see SymPy `sympy.combinatorics.schur_number.SchurNumber`
 * @example
 * ```ts
 * import { SchurNumber, SchurNumberNode } from '@symjs/symjs';
 *
 * const s = SchurNumber(6);
 * s instanceof SchurNumberNode && s.lowerBound(); // => 536
 * ```
 */
export class SchurNumberNode extends ExtensionExpr {
  /**
   * Constructs a `SchurNumber`.
   * @param k - The number of sum-free color classes.
   * @internal
   */
  constructor(k: Expr) {
    super('SchurNumber', [k]);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return SchurNumber(at(args, 0));
  }
  /**
   * Computes a lower bound on the Schur number.
   * @returns A lower bound on the Schur number.
   * @see SymPy `sympy.combinatorics.schur_number.SchurNumber.lower_bound`
   */
  lowerBound(): Expr {
    const k = at(this.args, 0);
    if (k instanceof Rational && k.q === 1n) {
      if (k.p === 6n) return Rational.of(536n);
      if (k.p === 7n) return Rational.of(1680n);
      return sub(mul(3, new SchurNumberNode(Rational.of(k.p - 1n)).lowerBound()), 1);
    }
    return mul(add(pow(3, k), -1), Rational.of(1n, 2n));
  }
}

/** The number of sum-free subsets schur_partition uses for [1, n]. */
function subsetsNumber(n: number): number {
  if (n <= 3) return 1;
  // ceil(log_3(2*n + 1)), computed exactly
  let k = 0;
  for (let p = 1; p < 2 * n + 1; p *= 3) k++;
  return k;
}

function nextList(current: readonly number[][], n: number): number[][] {
  const out = current.map((item) => [...item.map((x) => 3 * x).filter((x) => x <= n), ...item.map((x) => 3 * x - 1).filter((x) => x <= n)]);
  const last: number[] = [];
  for (let k = 0; k <= current.length; k++) if (3 * k + 1 <= n) last.push(3 * k + 1);
  out.push(last);
  return out;
}

/**
 * Partitions the integers from one through the specified bound using the Schur-number construction.
 * @param nIn - The largest integer to include.
 * @returns The subsets of the initial integer interval.
 * @throws RangeError when the argument is infinite or the argument is nonnumeric or `n` is not a positive integer.
 * @see SymPy `sympy.combinatorics.schur_number.schur_partition`
 * @example
 * ```ts
 * import { schurPartition } from '@symjs/symjs';
 * schurPartition(5); // => [[3, 2], [5], [1, 4]]
 * ```
 */
export function schurPartition(nIn: ExprLike): number[][] {
  const e = sympify(nIn);
  if (e === S.Infinity) throw new RangeError('Input must be finite');
  if (!(e instanceof Rational) || e.q !== 1n) throw new RangeError('Input value must be a number');
  const n = Number(e.p);
  if (n <= 0) throw new RangeError('n must be a non-zero positive integer.');
  const count = subsetsNumber(n);
  let subsets: number[][] = n <= 3 ? [Array.from({ length: n }, (_x, i) => i + 1)] : [[1, 4], [2, 3]];
  while (subsets.length < count) {
    subsets = nextList(subsets, n);
    const lastSet = at(subsets, subsets.length - 1);
    for (let k = subsets.length; k <= Math.floor((n - 1) / 3); k++) lastSet.push(3 * k + 1);
  }
  return subsets;
}
