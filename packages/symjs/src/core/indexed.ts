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
import { cast } from './guard';
import { TupleNode } from './containers';
import { NoMatch, isNoMatch } from './truth';
import type { NoMatchResult } from './truth';

/** SymPy Indexed(base, *indices): args are [base symbol, ...indices]; printed base[i, j]. */
export class Indexed extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Indexed', args);
  }
  get rank(): number { return this.args.length - 1; }
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
export class IndexedBase extends ExtensionExpr {
  readonly label: Sym;
  constructor(name: string | Sym, options: { readonly shape?: readonly ExprLike[] } = {}) {
    const label = typeof name === 'string' ? new Sym(name) : name;
    super('IndexedBase', [label, ...(options.shape === undefined ? [] : [new TupleNode(options.shape.map(sympify))])]);
    this.label = label;
  }
  get shape(): readonly Expr[] | NoMatchResult {
    return this.args.length === 1 ? NoMatch : cast(at(this.args, 1), TupleNode).args;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new IndexedBase(cast(at(args, 0), Sym), args.length === 1 ? {} : { shape: cast(at(args, 1), TupleNode).args });
  }
  equals(other: unknown): boolean {
    return other instanceof IndexedBase && this.key === other.key;
  }
  /** The real assumption inherited from the base label. */
  get isReal(): boolean | 'unknown' {
    return this.label.assumptions.real ?? 'unknown';
  }
  /** A[i, j] */
  at(...indices: ExprLike[]): Indexed {
    const shape = this.shape;
    if (!isNoMatch(shape) && shape.length !== indices.length) throw new RangeError('Rank mismatch.');
    return new Indexed([isNoMatch(shape) ? this.label : this, ...indices.map(sympify)]);
  }
  override printStr(print: (e: Expr) => string): string {
    return print(this.label);
  }
  override printLatex(print: (e: Expr) => string): string {
    return print(this.label);
  }
}
