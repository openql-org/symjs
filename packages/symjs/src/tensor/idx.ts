// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy Idx (sympy.tensor.indexed.Idx): an integer index with an
 * optional range, used with IndexedBase and as a summation index.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Rational, Special, Sym } from '../core/nodes';
import { add, sympify } from '../core/ops';
import { isIntegerQ } from '../core/assumptions';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { latex } from '../printing/latex';
import { str } from '../printing/str';

const isInfinite = (e: Expr): boolean => e instanceof Special && (e.name === 'oo' || e.name === '-oo');

/** The range argument of Idx: a dimension n (bounds 0 and n - 1) or a pair [lower, upper]. */
export type IdxRange = ExprLike | readonly ExprLike[];

/**
 * SymPy Idx(label, range): an integer index. The label is an integer
 * symbol (a string gives an integer Symbol) or an integer expression; the
 * range is a dimension n (bounds 0 and n - 1) or a pair [lower, upper].
 *
 * Idx is a symbol (it prints as its label, is integer and real, is its own
 * free symbol and can be differentiated by); its structural key includes
 * the bounds, so `Idx('i', 3)` differs from `Idx('i')` and from the symbol
 * `i`. `Idx(n)` with an integer n gives n itself.
 */
export class IdxNode extends Sym {
  /** The label (an integer symbol or integer expression). */
  readonly label: Expr;
  readonly #bounds: readonly [Expr, Expr] | undefined;

  constructor(label: string | Expr, range?: IdxRange) {
    const lab = typeof label === 'string' ? new Sym(label, { integer: true }) : label;
    if (lab instanceof Rational) throw new TypeError('Idx: an integer label gives the integer itself; call Idx(n)');
    if (isIntegerQ(lab) !== true) throw new TypeError('Idx object requires an integer label.');
    super(lab instanceof Sym ? lab.name : str(lab), { integer: true });
    this.label = lab;
    this.#bounds = parseRange(range);
  }

  /** The lower bound (SymPy Idx.lower), or NoMatch when the index has no range (SymPy None). */
  get lower(): Expr | NoMatchResult {
    return this.#bounds ? this.#bounds[0] : NoMatch;
  }
  /** The upper bound (SymPy Idx.upper), or NoMatch when the index has no range (SymPy None). */
  get upper(): Expr | NoMatchResult {
    return this.#bounds ? this.#bounds[1] : NoMatch;
  }

  /**
   * LaTeX form like SymPy: the label with the range as a subscript
   * (`{i}_{0\mathrel{..}\nobreak 3}`), or the label alone.
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

function parseRange(range: IdxRange | undefined): readonly [Expr, Expr] | undefined {
  if (range === undefined) return undefined;
  if (Array.isArray(range)) {
    const r = range as readonly ExprLike[];
    if (r.length !== 2) throw new RangeError(`Idx range tuple must have length 2, but got ${r.length}`);
    const bounds = r.map((b) => sympify(b));
    for (const b of bounds) if (isIntegerQ(b) === false && !isInfinite(b)) throw new TypeError('Idx object requires integer bounds.');
    return [bounds[0]!, bounds[1]!];
  }
  const n = sympify(range as ExprLike);
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
