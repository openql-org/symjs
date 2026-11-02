// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The unevaluated Sum / Product node.
 */

import { Expr, ExprLike, Sym } from './nodes';
import { sympify } from './ops';

/**
 * Sum or Product: args [f, k1, a1, b1, k2, a2, b2, ...]. @internal ctor
 *
 * @experimental May change in a minor release.
 */
export class Concrete extends Expr {
  readonly kind = 'Concrete' as const;
  constructor(readonly kind2: 'Sum' | 'Product', readonly args: readonly Expr[]) {
    super();
  }
  get function(): Expr {
    return this.args[0]!;
  }
  get limits(): [Expr, Expr, Expr][] {
    const out: [Expr, Expr, Expr][] = [];
    for (let i = 1; i < this.args.length; i += 3) out.push([this.args[i]!, this.args[i + 1]!, this.args[i + 2]!]);
    return out;
  }
  protected computeKey(): string {
    return `${this.kind2}(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Unevaluated Sum(f, (k, a, b), ...). */
export function Sum(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Sum', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}

/** Unevaluated Product(f, (k, a, b), ...). */
export function Product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Product', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}
