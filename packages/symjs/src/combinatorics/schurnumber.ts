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
 * SymPy SchurNumber(k): S(k) for k <= 5 (and S(oo) = oo, S(0) = 0); the
 * unevaluated SchurNumberNode otherwise, whose lowerBound() is a known lower bound.
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

/** The unevaluated SymPy SchurNumber(k). */
export class SchurNumberNode extends ExtensionExpr {
  /** @internal use SchurNumber(k) */
  constructor(k: Expr) {
    super('SchurNumber', [k]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return SchurNumber(at(args, 0));
  }
  /** SymPy lower_bound: 536 for S(6), 1680 for S(7), 3*lower_bound(S(k - 1)) - 1 for a larger integer k, else (3**k - 1)/2. */
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
 * SymPy schur_partition: a partition of [1, n] into the number of sum-free
 * subsets given by the lower bound of the Schur numbers.
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
