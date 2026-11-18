// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 series/acceleration.py (BSD-3-Clause; see LICENSE).
import type { Expr, ExprLike } from '../core/nodes';
import { impl } from '../core/nodes';
import { at, defined } from '../core/guard';
import { add, mul, pow, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { factorial } from '../functions/special/special';

const doit = (e: Expr): Expr => defined(impl.doit?.(e), 'calculus entry must be loaded');

function index(n: number): void {
  if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('Sequence indices must be nonnegative safe integers');
}

/** Richardson extrapolation of A(k) from n through n + N, with exact symbolic arithmetic. */
export function richardson(sequence: ExprLike, variable: ExprLike, n: number, N: number): Expr {
  index(n); index(N);
  const A = sympify(sequence), k = sympify(variable);
  const terms: Expr[] = [];
  for (let j = 0; j <= N; j++) {
    const point = BigInt(n) + BigInt(j);
    terms.push(mul(doit(subs(A, [[k, sympify(point)]])), pow(point, N), pow(-1, j + N), pow(mul(factorial(j), factorial(N - j)), -1)));
  }
  return add(...terms);
}

/** The m-fold recursive Shanks transformation of the symbolic sequence A(k) at n. */
export function shanks(sequence: ExprLike, variable: ExprLike, n: number, m = 1): Expr {
  index(n); index(m);
  const A = sympify(sequence), k = sympify(variable);
  let table = Array.from({ length: n + m + 2 }, (_, j) => doit(subs(A, [[k, sympify(j)]])));
  const next = [...table];
  for (let i = 1; i <= m; i++) {
    for (let j = i; j < n + m + 1; j++) {
      const x = at(table, j - 1), y = at(table, j), z = at(table, j + 1);
      next[j] = mul(add(mul(z, x), mul(-1, pow(y, 2))), pow(add(z, x, mul(-2, y)), -1));
    }
    table = [...next];
  }
  return at(table, n);
}
