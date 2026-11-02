// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Indexed roots of polynomials (SymPy ComplexRootOf / CRootOf).
 */

import { InvariantError } from '../core/errors';
import { at, first, pair } from '../core/guard';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { ExtensionExpr, Float, Rational } from '../core/nodes';
import { sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { nroots } from './nroots';
import { Poly, rootHooks } from './sympoly';

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
    return at(this.args, 0);
  }
  withArgs(args: readonly Expr[]): Expr {
    const [poly, index] = pair(args);
    if (!(index instanceof Rational)) throw new InvariantError('CRootOf index is not a Rational');
    return new CRootOf(poly, index);
  }
  override printStr(print: (e: Expr) => string): string {
    return `CRootOf(${print(this.poly)}, ${this.index})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{CRootOf} {\\left(${print(this.poly)}, ${this.index}\\right)}`;
  }
  /** The generator of the polynomial. */
  get gen(): Sym {
    return first([...freeSymbols(this.poly)]);
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

rootHooks.crootof = (e, i) => new CRootOf(e, i);
