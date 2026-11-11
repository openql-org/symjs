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

/** SymPy SeriesBase: subclasses supply bounds and evalTerm. */
export class SeriesBase extends ExtensionExpr {
  private readonly termCache = new Map<string, Expr>();

  constructor(...args: ExprLike[]) {
    super('SeriesBase', args.map(sympify));
  }

  override withArgs(args: readonly Expr[]): Expr {
    return new SeriesBase(...args);
  }

  /** The interval of term indices, with both endpoints included. */
  get interval(): SetExpr { throw new NotImplementedError(`${this.name}.interval`); }
  get start(): Expr { throw new NotImplementedError(`${this.name}.start`); }
  get stop(): Expr { throw new NotImplementedError(`${this.name}.stop`); }
  get length(): Expr { throw new NotImplementedError(`${this.name}.length`); }

  /** Variables bound by the series. */
  get variables(): Sym[] { return []; }

  override freeSymbolsSelf(): ReadonlySet<Expr> {
    const symbols = new Map<string, Expr>();
    for (const arg of this.args) for (const symbol of freeSymbols(arg)) symbols.set(symbol.key, symbol);
    for (const variable of this.variables) symbols.delete(variable.key);
    return new Set(symbols.values());
  }

  /** The cached term at a point, checked against the inclusive bounds. */
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

  /** SymPy series[i]; negative indices are offsets, not offsets from the end. */
  getItem(i: number): Expr {
    return this.term(this.ithPoint(index(i)));
  }

  /** SymPy series[start:stop:step], without clipping to the series bounds. */
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

  *[Symbol.iterator](): Generator<Expr, void, undefined> {
    for (let i = 0; less(i, this.length); i++) yield this.getItem(i);
  }
}
