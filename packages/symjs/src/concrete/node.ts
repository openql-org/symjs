// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The unevaluated Sum / Product node.
 */

import { Expr } from '../core/nodes';

/** Sum or Product: args [f, k1, a1, b1, k2, a2, b2, ...]. @internal ctor */
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
