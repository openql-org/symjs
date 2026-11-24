// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/series/series_class.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/** @file Common expression, term and indexing protocol for series. */

import { ExtensionExpr, Rational, S } from '../core/nodes';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { Lt } from '../core/logic';
import { add, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import type { SetExpr } from '../sets/sets';

/** Python's truth test of a strict comparison, including undecidable bounds. */
function less(a: ExprLike, b: ExprLike): boolean {
  const result = Lt(a, b);
  if (result === S.true) return true;
  if (result === S.false) return false;
  throw new TypeError(`Cannot determine truth value of ${result.toString()}`);
}

function index(value: number): number {
  if (!Number.isSafeInteger(value)) throw new TypeError('series index must be a safe integer');
  return value;
}

/**
 * Base class for indexed series with inclusive bounds and cached terms.
 *
 * @see SymPy `sympy.series.series_class.SeriesBase`
 */
export class SeriesBase extends ExtensionExpr {
  private readonly termCache = new Map<string, Expr>();

  /**
   * Constructs a new `SeriesBase`.
   *
   * @param args - The defining expressions in structural order.
   */
  constructor(...args: ExprLike[]) {
    super('SeriesBase', args.map(sympify));
  }

  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new SeriesBase(...args);
  }

  /**
   * Specifies both inclusive endpoints of the series indices.
   *
   * @returns The index interval.
   * @throws NotImplementedError when the concrete series does not implement this operation.
   * @see SymPy `sympy.series.series_class.SeriesBase.interval`
   */
  get interval(): SetExpr { throw new NotImplementedError(`${this.name}.interval`); }
  /**
   * Identifies the first index at which a term is defined.
   *
   * @returns The starting index.
   * @throws NotImplementedError when the concrete series does not implement this operation.
   * @see SymPy `sympy.series.series_class.SeriesBase.start`
   */
  get start(): Expr { throw new NotImplementedError(`${this.name}.start`); }
  /**
   * Identifies the final index in the series or sequence.
   *
   * @returns The ending index.
   * @throws NotImplementedError when the concrete series does not implement this operation.
   * @see SymPy `sympy.series.series_class.SeriesBase.stop`
   */
  get stop(): Expr { throw new NotImplementedError(`${this.name}.stop`); }
  /**
   * Counts the terms in the index interval, allowing an infinite range.
   *
   * @returns The term count or infinity.
   * @throws NotImplementedError when the concrete series does not implement this operation.
   * @see SymPy `sympy.series.series_class.SeriesBase.length`
   */
  get length(): Expr { throw new NotImplementedError(`${this.name}.length`); }

  /**
   * Lists the variables whose scope is the series.
   *
   * @returns The bound symbols.
   * @see SymPy `sympy.series.series_class.SeriesBase.variables`
   */
  get variables(): Sym[] { return []; }

  /**
   * Collects symbols occurring freely after accounting for the series bindings.
   *
   * @returns The free symbols.
   * @see SymPy `sympy.series.series_class.SeriesBase.free_symbols`
   */
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    const symbols = new Map<string, Expr>();
    for (const arg of this.args) for (const symbol of freeSymbols(arg)) symbols.set(symbol.key, symbol);
    for (const variable of this.variables) symbols.delete(variable.key);
    return new Set(symbols.values());
  }

  /**
   * Retrieves the term after checking that its index lies within the inclusive bounds.
   *
   * @param pt - Index of the requested term.
   * @returns The term at the specified index.
   * @throws RangeError when the index lies outside the inclusive bounds.
   * @see SymPy `sympy.series.series_class.SeriesBase.term`
   */
  term(pt: ExprLike): Expr {
    const point = sympify(pt);
    const cached = this.termCache.get(point.key);
    if (cached !== undefined) return cached;
    if (less(point, this.start) || less(this.stop, point)) {
      throw new RangeError(`Index ${point.toString()} out of bounds ${this.interval.toString()}`);
    }
    const result = this.evalTerm(point);
    this.termCache.set(point.key, result);
    return result;
  }

  protected evalTerm(_pt: Expr): Expr {
    throw new NotImplementedError(`${this.name}.evalTerm must implement series term evaluation`);
  }

  /** Offset from start, or backwards from stop when start is negative infinity. */
  protected ithPoint(i: number): Expr {
    return this.start === S.NegativeInfinity ? add(this.stop, -i) : add(this.start, i);
  }

  /**
   * Selects a term by offset from the initial endpoint, extending backwards for negative offsets.
   *
   * @param i - Integer term offset.
   * @returns The term at the requested offset.
   * @see SymPy `sympy.series.series_class.SeriesBase.__getitem__`
   */
  getItem(i: number): Expr {
    return this.term(this.ithPoint(index(i)));
  }

  /**
   * Collects terms at successive offsets up to the exclusive stopping index.
   *
   * @param start - First offset to include.
   * @param stop - Exclusive ending offset.
   * @param step - Stride between offsets.
   * @returns The selected terms in order.
   * @throws TypeError when an infinite series is sliced without a finite stop, or an offset is not a safe integer.
   * @see SymPy `sympy.series.series_class.SeriesBase.__getitem__`
   */
  slice(start = 0, stop?: number, step = 1): Expr[] {
    index(start);
    let end = stop;
    if (end === undefined) {
      const length = this.length;
      if (!(length instanceof Rational) || !length.isInteger) throw new TypeError('series slice requires a finite integer stop');
      end = Number(length.p);
    }
    index(end);
    // SeriesBase.__getitem__ uses index.step or 1, including a zero step.
    const stride = index(step) || 1;
    const terms: Expr[] = [];
    for (let i = start; stride > 0 ? i < end : i > end; i += stride) terms.push(this.getItem(i));
    return terms;
  }

  /**
   * Iterates over the terms in index order. An infinite series keeps yielding terms.
   *
   * @returns A generator over successive terms.
   * @see SymPy `sympy.series.series_class.SeriesBase.__iter__`
   */
  *[Symbol.iterator](): Generator<Expr, void, undefined> {
    for (let i = 0; less(i, this.length); i++) yield this.getItem(i);
  }
}
