// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Algebraic numbers given as polynomials in a primitive element
 * (a minimal port of SymPy AlgebraicNumber).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Rational } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { expandMul } from '../simplify/expand';

/**
 * An element of Q(theta) written as c[0]*theta**(n-1) + ... + c[n-1] for a
 * primitive element theta (SymPy AlgebraicNumber(theta, coeffs)).
 */
export class AlgebraicNumber {
  readonly root: Expr;
  readonly coeffList: readonly Expr[];
  constructor(root: ExprLike | AlgebraicNumber, coeffs: readonly ExprLike[] = [1, 0]) {
    const cs = coeffs.map((c) => sympify(c));
    if (root instanceof AlgebraicNumber) {
      // an element of an element: compose the polynomials in the inner primitive element
      this.root = root.root;
      const inner = root.asPolyExpr();
      const outer = cs.reduceRight<{ acc: Expr; k: number }>(
        (s, c) => ({ acc: add(s.acc, mul(c, pow(inner, s.k))), k: s.k + 1 }),
        { acc: Rational.of(0), k: 0 },
      ).acc;
      this.coeffList = polyCoeffsIn(expandMul(outer), root.root);
    } else {
      this.root = sympify(root);
      this.coeffList = cs;
    }
  }

  /** c[0]*theta**(n-1) + ... + c[n-1] with theta kept symbolic. */
  private asPolyExpr(): Expr {
    const n = this.coeffList.length;
    return add(...this.coeffList.map((c, i) => mul(c, pow(this.root, n - 1 - i))));
  }

  /** The value as an expression (SymPy as_expr). */
  asExpr(): Expr {
    return expandMul(this.asPolyExpr());
  }

  /** The value as an explicit root expression (SymPy to_root). */
  toRoot(): Expr {
    return this.asExpr();
  }

  /** The primitive element theta. */
  primitiveElement(): Expr {
    return this.root;
  }

  /** Coefficients in the primitive element, highest power first. */
  coeffs(): Expr[] {
    return [...this.coeffList];
  }

  evalf(n = 15): Expr {
    return this.asExpr().evalf(n);
  }
}

/** Coefficients of a polynomial expression in theta (theta treated as an atom). */
function polyCoeffsIn(e: Expr, theta: Expr): Expr[] {
  // write e as a polynomial in a fresh symbol t = theta when possible
  const terms = e.kind === 'Add' ? e.args : [e];
  const byPow = new Map<number, Expr[]>();
  for (const t of terms) {
    const fs = t.kind === 'Mul' ? t.args : [t];
    let k = 0;
    const rest: Expr[] = [];
    for (const f of fs) {
      if (f.key === theta.key) k += 1;
      else if (f.kind === 'Pow' && f.args[0]?.key === theta.key && f.args[1] instanceof Rational && f.args[1].isInteger) k += Number(f.args[1].p);
      else rest.push(f);
    }
    const list = byPow.get(k) ?? [];
    list.push(mul(...rest));
    byPow.set(k, list);
  }
  const deg = Math.max(0, ...byPow.keys());
  return Array.from({ length: deg + 1 }, (_, i) => add(...(byPow.get(deg - i) ?? [Rational.of(0)])));
}
