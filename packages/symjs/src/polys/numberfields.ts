// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Algebraic numbers given as polynomials in a primitive element
 * (a minimal port of SymPy AlgebraicNumber).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, S } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { expandMul } from '../simplify/expand';
import { Poly, minimalPolynomial } from './sympoly';

/** The minimal polynomial of theta in t, when symjs can compute it. */
function minpolyIn(theta: Expr, t: Dummy): Poly | undefined {
  try {
    return Poly.from(minimalPolynomial(theta, t), [t]);
  } catch {
    // SymPy computes minimal polynomials of all algebraic numbers (e.g. cos(pi/7))
    return undefined;
  }
}

/** c[0]*t**(n-1) + ... + c[n-1] (Horner). */
const horner = (cs: readonly Expr[], t: Expr): Expr => cs.reduce<Expr>((acc, c) => add(mul(acc, t), c), S.Zero);

/**
 * An element of Q(theta) written as c[0]*theta**(n-1) + ... + c[n-1] for a
 * primitive element theta (SymPy AlgebraicNumber(theta, coeffs)). The
 * polynomial is reduced modulo the minimal polynomial of theta.
 */
export class AlgebraicNumber {
  readonly root: Expr;
  readonly coeffList: readonly Expr[];
  constructor(root: ExprLike | AlgebraicNumber, coeffs: readonly ExprLike[] = [1, 0]) {
    const t = new Dummy('t');
    const cs = coeffs.map((c) => sympify(c));
    // an element of an element: the polynomials composed in the inner primitive element
    const inner = root instanceof AlgebraicNumber ? horner(root.coeffList, t) : t;
    this.root = root instanceof AlgebraicNumber ? root.root : sympify(root);
    const p = Poly.from(expandMul(horner(cs, inner)), [t]);
    const m = minpolyIn(this.root, t);
    this.coeffList = (m ? p.rem(m) : p).allCoeffs();
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
