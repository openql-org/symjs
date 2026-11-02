// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Indexed roots of polynomials (SymPy ComplexRootOf / CRootOf).
 */

import { Expr, ExprLike, ExtensionExpr, Float, Rational, Sym } from '../core/nodes';
import { sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { nroots } from './nroots';
import { Poly } from './sympoly';

/**
 * The index-th root of a polynomial with rational coefficients (SymPy
 * CRootOf): real roots come first in increasing order, then the complex
 * roots by increasing real part, the one with negative imaginary part first.
 */
export class CRootOf extends ExtensionExpr {
  readonly index: number;
  constructor(poly: Expr, index: number | Rational) {
    const i = typeof index === 'number' ? index : Number(index.p);
    super('CRootOf', [poly, Rational.of(i)]);
    this.index = i;
  }
  get poly(): Expr {
    return this.args[0]!;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CRootOf(args[0]!, args[1] as Rational);
  }
  override printStr(print: (e: Expr) => string): string {
    return `CRootOf(${print(this.poly)}, ${this.index})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{CRootOf} {\\left(${print(this.poly)}, ${this.index}\\right)}`;
  }
  /** The generator of the polynomial. */
  get gen(): Sym {
    return [...freeSymbols(this.poly)][0] as Sym;
  }
  override numericValue(dps: number): Expr | undefined {
    const rs = nroots(Poly.from(this.poly, [this.gen]), dps);
    return rs[this.index];
  }
  /** Is this root real? */
  get isRealRoot(): boolean {
    const v = this.numericValue(15);
    return v instanceof Float || v instanceof Rational;
  }
}

/** CRootOf(f, index) for a polynomial expression f in a single generator. */
export function rootOf(f: ExprLike | Poly, index: number): Expr {
  const p = f instanceof Poly ? f : Poly.from(sympify(f));
  const deg = p.degree();
  if (index < -deg || index >= deg) throw new RangeError(`rootof: index ${index} out of range`);
  return new CRootOf(p.asExpr(), index < 0 ? deg + index : index);
}
