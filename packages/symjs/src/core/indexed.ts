// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy IndexedBase and Indexed: indexed objects such as A[i] or f[n],
 * usable as unknowns and inside sums.
 */

import type { Assumptions, Expr, ExprLike, Head } from './nodes';
import { ExtensionExpr, Rational, S, Sym } from './nodes';
import { sympify } from './ops';
import { at } from './guard';
import { cast } from './guard';
import { TupleNode } from './containers';
import { NoMatch, isNoMatch } from './truth';
import type { NoMatchResult } from './truth';

/** SymPy Indexed(base, *indices): args are [base symbol, ...indices]; printed base[i, j]. */
export class Indexed extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    if (args.length < 2) throw new RangeError('Indexed needs at least one index.');
    const base = at(args, 0);
    if (base instanceof Indexed) throw new TypeError('Indexed requires an unindexed base.');
    super('Indexed', [base instanceof Sym ? new IndexedBase(base) : base, ...args.slice(1)]);
  }
  get rank(): number { return this.args.length - 1; }
  get base(): Expr {
    return at(this.args, 0);
  }
  get indices(): Expr[] {
    return this.args.slice(1);
  }
  get assumptions0(): Map<string, boolean> {
    return this.base instanceof IndexedBase ? this.base.assumptions0 : new Map();
  }
  override isRealSelf(): boolean | undefined {
    return this.assumptions0.get('real');
  }
  withArgs(args: readonly Expr[]): Expr {
    const base = at(args, 0), index = at(args, 1);
    if (base instanceof TupleNode && args.length === 2 && index instanceof Rational && index.isInteger) {
      const n = Number(index.p);
      const value = base.args[n < 0 ? base.args.length + n : n];
      if (value === undefined) throw new RangeError('Indexed sequence index out of range.');
      return value;
    }
    return new Indexed(args);
  }
  override subsSelf(old: Expr, nw: Expr): Expr | undefined {
    if (this.base instanceof IndexedBase && this.base.label.key === old.key) return this.withArgs([nw, ...this.indices]);
    return undefined;
  }
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    // An indexed entry is an independent scalar as well as containing the
    // symbols in its label and indices (SymPy Indexed.free_symbols).
    return new Set([this, ...this.args.flatMap((a) => [...a.freeSymbols()])]);
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
  override get func(): Head {
    return indexedBaseFromArgs;
  }
  readonly label: Sym;
  readonly #assumptionSymbol: Sym;
  constructor(name: string | Sym, options: Assumptions & { readonly shape?: readonly ExprLike[] } = {}) {
    const { shape, ...assumptions } = options;
    const label = typeof name === 'string' ? new Sym(name, assumptions) : name;
    super('IndexedBase', [label, ...(shape === undefined ? [] : [new TupleNode(shape.map(sympify))])]);
    this.label = label;
    this.#assumptionSymbol = new Sym(label.name, { ...label.assumptions, ...assumptions });
  }
  get assumptions0(): Map<string, boolean> {
    return this.#assumptionSymbol.assumptions0;
  }
  protected override computeKey(): string {
    return `${super.computeKey()}:${this.#assumptionSymbol.key}`;
  }
  protected override computeCommutative(): boolean {
    return this.#assumptionSymbol.isCommutative;
  }
  override isRealSelf(): boolean | undefined {
    return this.assumptions0.get('real');
  }
  get shape(): readonly Expr[] | NoMatchResult {
    return this.args.length === 1 ? NoMatch : cast(at(this.args, 1), TupleNode).args;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new IndexedBase(cast(at(args, 0), Sym), { ...this.#assumptionSymbol.assumptions, ...(args.length === 1 ? {} : { shape: cast(at(args, 1), TupleNode).args }) });
  }
  equals(other: unknown): boolean {
    return other instanceof IndexedBase && this.key === other.key;
  }
  /** The real assumption inherited from the base label. */
  get isReal(): boolean | 'unknown' {
    return this.assumptions0.get('real') ?? 'unknown';
  }
  /** A[i, j] */
  at(...indices: ExprLike[]): Indexed {
    const shape = this.shape;
    if (!isNoMatch(shape) && shape.length !== indices.length) throw new RangeError('Rank mismatch.');
    return new Indexed([this, ...indices.map(sympify)]);
  }
  override printStr(print: (e: Expr) => string): string {
    return print(this.label);
  }
  override printLatex(print: (e: Expr) => string): string {
    return print(this.label);
  }
}

const indexedBaseFromArgs = (...args: ExprLike[]): IndexedBase => new IndexedBase(cast(sympify(at(args, 0)), Sym), args[1] === undefined ? {} : { shape: cast(sympify(args[1]), TupleNode).args });
