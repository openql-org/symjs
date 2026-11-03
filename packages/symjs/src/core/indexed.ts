// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy IndexedBase and Indexed: indexed objects such as A[i] or f[n],
 * usable as unknowns and inside sums.
 */

import type { Expr, ExprLike } from './nodes';
import { ExtensionExpr, S, Sym } from './nodes';
import { sympify } from './ops';
import { at } from './guard';

/** SymPy Indexed(base, *indices): args are [base symbol, ...indices]; printed base[i, j]. */
export class Indexed extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Indexed', args);
  }
  get base(): Expr {
    return at(this.args, 0);
  }
  get indices(): Expr[] {
    return this.args.slice(1);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Indexed(args);
  }
  override printStr(print: (e: Expr) => string): string {
    return `${print(this.base)}[${this.indices.map(print).join(', ')}]`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `{${print(this.base)}}_{${this.indices.map(print).join(',')}}`;
  }
  /**
   * The derivative with respect to a symbol inside A[i] (diff handles indexed variables):
   * nan for an index (SymPy: d A[i]/d i is not defined), 0 for the label.
   */
  override diffSelf(x: Expr): Expr {
    return this.indices.some((i) => i.has(x)) ? S.NaN : S.Zero;
  }
}

/** SymPy IndexedBase(name): base.at(i, ...) builds A[i, ...]. */
export class IndexedBase {
  readonly label: Sym;
  constructor(name: string | Sym) {
    this.label = typeof name === 'string' ? new Sym(name) : name;
  }
  /** A[i, j] */
  at(...indices: ExprLike[]): Indexed {
    return new Indexed([this.label, ...indices.map(sympify)]);
  }
  toString(): string {
    return this.label.name;
  }
}
