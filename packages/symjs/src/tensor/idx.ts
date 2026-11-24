// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy Idx (sympy.tensor.indexed.Idx): an integer index with an
 * optional range, used with IndexedBase and as a summation index.
 */

import { at } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Rational, Special, Sym } from '../core/nodes';
import { add, sympify } from '../core/ops';
import { isIntegerQ } from '../core/assumptions';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import type { Indexed } from '../core/indexed';
import { isNoMatch } from '../core/truth';
import { latex } from '../printing/latex';
import { str } from '../printing/str';
import { TupleNode } from '../core/containers';

const isInfinite = (e: Expr): boolean => e instanceof Special && (e.name === 'oo' || e.name === '-oo');

/** The range argument of Idx: a dimension n (bounds 0 and n - 1) or a pair [lower, upper]. */
export type IdxRange = ExprLike | readonly ExprLike[];

/**
 * Finds the inclusive index bounds of an indexed expression.
 *
 * @param e - Expression to inspect.
 * @returns One pair of inclusive bounds per index, or `NoMatch` where bounds are unavailable.
 * @see SymPy `sympy.tensor.indexed.Indexed.ranges`
 */
export function ranges(e: Indexed): (readonly [Expr, Expr] | NoMatchResult)[] {
  return e.indices.map((i) => i instanceof IdxNode && !isNoMatch(i.lower) && !isNoMatch(i.upper) ? [i.lower, i.upper] : NoMatch);
}

/**
 * An integer index. The label is an integer symbol (a string gives an integer Symbol) or an
 * integer expression; the range is a dimension n (bounds 0 and n - 1) or a pair [lower, upper].
 *
 * Idx is a symbol (it prints as its label, is integer and real, is its own free symbol and can be
 * differentiated by); its structural key includes the bounds, so `Idx('i', 3)` differs from
 * `Idx('i')` and from the symbol `i`. `Idx(n)` with an integer n gives n itself.
 *
 * @see SymPy `sympy.tensor.indexed.Idx`
 */
export class IdxNode extends Sym {
  /**
   * The index label followed by the bounds tuple when a range is supplied.
   *
   * @see SymPy `sympy.tensor.indexed.Idx.args`
   */
  override readonly args: readonly Expr[];
  /**
   * The top-level function in an expression.
   *
   * @returns The top-level function in an expression.
   * @see SymPy `sympy.tensor.indexed.Idx.func`
   */
  override get func(): typeof makeIdx {
    return makeIdx;
  }
  /**
   * Whether the index behaves as an atomic expression.
   *
   * @returns Whether the index behaves as an atomic expression.
   */
  override get isAtom(): boolean {
    return true;
  }
  /**
   * The label (an integer symbol or integer expression).
   *
   * @see SymPy `sympy.tensor.indexed.Idx.label`
   */
  readonly label: Expr;
  readonly #bounds: readonly [Expr, Expr] | undefined;

  /**
   * Constructs an instance of `IdxNode`.
   *
   * @param label - Symbolic label used to identify this object.
   * @param range - Dimension or pair of inclusive index bounds.
   * @throws TypeError when the label is not integer-valued or the node constructor receives a literal integer label.
   */
  constructor(label: string | Expr, range?: IdxRange) {
    const lab = typeof label === 'string' ? new Sym(label, { integer: true }) : label;
    if (lab instanceof Rational) throw new TypeError('Idx: an integer label gives the integer itself; call Idx(n)');
    if (isIntegerQ(lab) !== true) throw new TypeError('Idx object requires an integer label.');
    super(lab instanceof Sym ? lab.name : str(lab), { integer: true });
    this.label = lab;
    this.#bounds = parseRange(range);
    this.args = [lab, ...(this.#bounds ? [new TupleNode(this.#bounds)] : [])];
  }

  /**
   * The lower bound, or NoMatch when the index has no range.
   *
   * @returns The inclusive lower bound, or `NoMatch` for an unbounded index.
   * @see SymPy `sympy.tensor.indexed.Idx.lower`
   */
  get lower(): Expr | NoMatchResult {
    return this.#bounds ? this.#bounds[0] : NoMatch;
  }
  /**
   * The upper bound, or NoMatch when the index has no range.
   *
   * @returns The inclusive upper bound, or `NoMatch` for an unbounded index.
   * @see SymPy `sympy.tensor.indexed.Idx.upper`
   */
  get upper(): Expr | NoMatchResult {
    return this.#bounds ? this.#bounds[1] : NoMatch;
  }

  /**
   * Applies a substitution to the label and bounds of the index.
   *
   * @param f - Substitution function applied to the label and bounds.
   * @returns The transformed tensor expression.
   */
  override substituteInner(f: (e: Expr) => Expr): Expr {
    return makeIdx(f(this.label), this.#bounds?.map(f));
  }

  /**
   * LaTeX form like SymPy: the label with the range as a subscript (`{i}_{0\mathrel{..}\nobreak
   * 3}`), or the label alone.
   *
   * @returns The formatted text.
   */
  override toLatex(): string {
    const lab = latex(this.label);
    if (!this.#bounds) return lab;
    return `{${lab}}_{${latex(this.#bounds[0])}\\mathrel{..}\\nobreak ${latex(this.#bounds[1])}}`;
  }

  protected override computeKey(): string {
    const b = this.#bounds;
    return `Idx(${this.label.key}${b ? `;${b[0].key};${b[1].key}` : ''})`;
  }
}

const isRangeList = (r: IdxRange): r is readonly ExprLike[] => Array.isArray(r);

function parseRange(range: IdxRange | undefined): readonly [Expr, Expr] | undefined {
  if (range === undefined) return undefined;
  if (range instanceof TupleNode) return parseRange(range.args);
  if (isRangeList(range)) {
    const r = range;
    if (r.length !== 2) throw new RangeError(`Idx range tuple must have length 2, but got ${r.length}`);
    const bounds = r.map((b) => sympify(b));
    for (const b of bounds) if (isIntegerQ(b) === false && !isInfinite(b)) throw new TypeError('Idx object requires integer bounds.');
    return [at(bounds, 0), at(bounds, 1)];
  }
  const n = sympify(range);
  if (n instanceof Special && n.name === 'oo') return [Rational.of(0), n];
  if (isIntegerQ(n) === false) throw new TypeError('Idx object requires an integer dimension.');
  return [Rational.of(0), add(n, -1)];
}

/**
 * SymPy Idx(label, range) as a function: an integer label gives the
 * integer itself, any other label an Idx.
 */
export function makeIdx(label: string | ExprLike, range?: IdxRange): Expr {
  const lab = typeof label === 'string' ? label : sympify(label);
  if (lab instanceof Rational) {
    if (lab.q !== 1n) throw new TypeError('Idx object requires an integer label.');
    return lab;
  }
  return new IdxNode(lab, range);
}
