// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/series/sequences.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Sequences (SymPy sympy.series.sequences): formula sequences
 * (SeqFormula), periodic sequences (SeqPer), recursive sequences
 * (RecursiveSeq), their term-wise sums and products (SeqAdd, SeqMul), the
 * empty sequence, and find_linear_recurrence.
 */

import type { ExprLike } from '../core/nodes';
import { Dummy, type Expr, Rational, S, Special, Sym, UndefFn, registerArithmetic } from '../core/nodes';
import { at, cast } from '../core/guard';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { freeSymbols, subs, xreplace } from '../core/traverse';
import { type NoMatchResult, NoMatch } from '../core/truth';
import { Matrix } from '../matrices/matrix';
import { matrixSolve } from '../matrices/linalg';
import { factor } from '../polys/sympoly';
import { EmptySet, type SetExpr, inf, intersection, interval, sup } from '../sets/sets';
import { expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';
import { Tuple } from '../core/containers';
import { Eq } from '../core/logic';
import { NotImplementedError } from '../core/errors';
import { SeriesBase } from './series_class';

const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isInf = (e: Expr, name: 'oo' | '-oo'): boolean => e instanceof Special && e.name === name;

/** a < b for numbers (false when the order is unknown). */
function less(a: Expr, b: Expr): boolean {
  if (isInf(a, '-oo') || isInf(b, 'oo')) return !(a.key === b.key);
  if (isInf(a, 'oo') || isInf(b, '-oo')) return false;
  if (a instanceof Rational && b instanceof Rational) return a.p * b.q < b.p * a.q;
  return false;
}

/** An integer point of a sequence as a JavaScript number. */
function asIndex(pt: Expr): number {
  const r = pt;
  if (!(r instanceof Rational) || !r.isInteger) throw new TypeError(`sequence index must be an integer: ${r.toString()}`);
  return Number(r.p);
}

/**
 * The base class of sequences.
 *
 * @see SymPy `sympy.series.sequences.SeqBase`
 */
export abstract class SeqBase extends SeriesBase {
  /** The expression class name used when printing the series. */
  override readonly name: string;
  /**
   * Constructs a new `SeqBase`.
   *
   * @param name - Expression class name used for the node.
   * @param args - The defining expressions in structural order.
   */
  constructor(name: string, args: readonly Expr[]) {
    super(...args);
    this.name = name;
  }
  protected override evalTerm(pt: Expr): Expr {
    return this.coeff(pt);
  }
  /**
   * The interval on which the sequence is defined.
   *
   * @returns The interval on which the sequence is defined.
   * @see SymPy `sympy.series.sequences.SeqBase.interval`
   */
  abstract override get interval(): SetExpr;
  /**
   * The first point.
   *
   * @returns The first point.
   * @see SymPy `sympy.series.sequences.SeqBase.start`
   */
  override get start(): Expr {
    return inf(this.interval);
  }
  /**
   * The last point.
   *
   * @returns The last point.
   * @see SymPy `sympy.series.sequences.SeqBase.stop`
   */
  override get stop(): Expr {
    return sup(this.interval);
  }
  /**
   * The number of terms (stop - start + 1, oo for an infinite sequence).
   *
   * @returns The number of terms (stop - start + 1, oo for an infinite sequence).
   * @see SymPy `sympy.series.sequences.SeqBase.length`
   */
  override get length(): Expr {
    return add(sub(this.stop, this.start), 1);
  }
  /**
   * The term at the point pt.
   *
   * @param pt - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.SeqBase.coeff`
   */
  abstract coeff(pt: ExprLike): Expr;
  /** The point pt, checked to lie within the interval of the sequence. */
  protected point(pt: ExprLike): Expr {
    const p = sympify(pt);
    if (less(p, this.start) || less(this.stop, p)) throw new RangeError(`Index ${p.toString()} out of bounds ${this.interval.toString()}`);
    return p;
  }
  /**
   * Every term multiplied by coeff. The operation is not
   * defined for sequences in general: only SeqFormula, SeqPer and
   * EmptySequence have it, and SymPy raises for the others (SeqAdd, SeqMul,
   * RecursiveSeq), as for their negation.
   *
   * @param coeff - Scalar multiplier of each term.
   * @returns The sequence of scaled terms.
   * @throws TypeError when this sequence has no rule for scalar multiplication.
   * @see SymPy `sympy.series.sequences.SeqBase.coeff_mul`
   */
  coeffMul(coeff: ExprLike): SeqBase {
    throw new TypeError(`cannot multiply ${this.name} and ${String(coeff)}`);
  }
  /**
   * The term-wise sum (SymPy +).
   *
   * @param other - Other operand.
   * @returns The term-wise sum.
   * @throws TypeError when the other operand is not a sequence.
   */
  override add(other: ExprLike): SeqBase {
    if (!(other instanceof SeqBase)) throw new TypeError(`cannot add sequence and ${String(other)}`);
    return SeqAdd(this, other);
  }
  /**
   * The term-wise difference (SymPy -).
   *
   * @param other - Other operand.
   * @returns The term-wise difference.
   * @throws TypeError when the other operand is not a sequence.
   */
  override sub(other: ExprLike): SeqBase {
    if (!(other instanceof SeqBase)) throw new TypeError(`cannot subtract sequence and ${String(other)}`);
    return SeqAdd(this, other.neg());
  }
  /**
   * The sequence with every term negated.
   *
   * @returns The sequence with every term negated.
   */
  override neg(): SeqBase {
    return this.coeffMul(-1);
  }
  /**
   * The term-wise product (SymPy *).
   *
   * @param other - Other operand.
   * @returns The term-wise product.
   * @throws TypeError when the other operand is not a sequence.
   */
  override mul(other: ExprLike): SeqBase {
    if (!(other instanceof SeqBase)) throw new TypeError(`cannot multiply sequence and ${String(other)}`);
    return SeqMul(this, other);
  }
  /**
   * The coefficients [c1, ..., ck]
   * of the shortest linear recurrence a(m) = c1*a(m-1) + ... + ck*a(m-k) of
   * order at most d satisfied by the first n terms ([] when there is none);
   * with gfvar also the generating function in gfvar (NoMatch when there is
   * no recurrence).
   *
   * @param n - Number of terms to use.
   * @param d - Maximum order to try.
   * @param gfvar - Variable of the generating function.
   * @returns The recurrence coefficients, paired with the generating function (or `NoMatch`) when `gfvar` is supplied.
   * @see SymPy `sympy.series.sequences.SeqBase.find_linear_recurrence`
   * @example
   * ```ts
   * import { ex, sequence, symbols } from '@symjs/symjs';
   *
   * const [n] = symbols('n');
   * const s = sequence(ex`n**2`, [n, 0, 10]);
   * s.findLinearRecurrence(6); // => [3, -3, 1]
   * ```
   */
  findLinearRecurrence(n: number, d?: number): Expr[];
  findLinearRecurrence(n: number, d: number | undefined, gfvar: Sym): [Expr[], Expr | NoMatchResult];
  findLinearRecurrence(n: number, d?: number, gfvar?: Sym): Expr[] | [Expr[], Expr | NoMatchResult] {
    const x = this.slice(0, n).map((t) => simplify(expand(t)));
    const lx = x.length;
    const r = d === undefined ? Math.floor(lx / 2) : Math.min(d, Math.floor(lx / 2));
    let coeffs: Expr[] = [];
    for (let l = 1; l <= r; l++) {
      const l2 = 2 * l;
      const m = Matrix.of(Array.from({ length: l }, (_, k) => x.slice(k, k + l)));
      if (isZero(simplify(m.det()))) continue;
      const y = matrixSolve(m, Matrix.of(x.slice(l, l2).map((t) => [t]))).map((t) => simplify(t));
      if (lx === l2) {
        coeffs = [...y.data].reverse();
        break;
      }
      const rest = Matrix.of(Array.from({ length: lx - 2 * l }, (_, k) => x.slice(l + k, l + k + l)));
      const prod = rest.mul(y);
      if (x.slice(l2).every((t, i) => isZero(simplify(sub(at(prod.data, i), t))))) {
        coeffs = [...y.data].reverse();
        break;
      }
    }
    if (gfvar === undefined) return coeffs;
    const l = coeffs.length;
    if (l === 0) return [[], NoMatch];
    let num: Expr = mul(at(x, l - 1), pow(gfvar, l - 1));
    let den: Expr = sub(1, mul(at(coeffs, l - 1), pow(gfvar, l)));
    for (let i = 0; i < l - 1; i++) {
      num = add(num, mul(at(x, i), pow(gfvar, i)));
      for (let j = 0; j < l - i - 1; j++) num = sub(num, mul(at(coeffs, i), at(x, j), pow(gfvar, i + j + 1)));
      den = sub(den, mul(at(coeffs, i), pow(gfvar, i + 1)));
    }
    return [coeffs, simplify(mul(factor(num), pow(factor(den), -1)))];
  }
}

/**
 * The sequence with no terms.
 *
 * @see SymPy `sympy.series.sequences.EmptySequence`
 * @example
 * ```ts
 * import { EmptySequenceNode } from '@symjs/symjs';
 *
 * new EmptySequenceNode().length; // => 0
 * ```
 */
export class EmptySequenceNode extends SeqBase {
  /** Constructs a new `EmptySequenceNode`. */
  constructor() {
    super('EmptySequence', []);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @returns The rebuilt expression.
   */
  override withArgs(): Expr {
    return EmptySequence;
  }
  /**
   * The inclusive interval of term indices.
   *
   * @returns The inclusive interval of term indices.
   * @see SymPy `sympy.series.sequences.EmptySequence.interval`
   */
  override get interval(): SetExpr {
    return EmptySet;
  }
  /**
   * The number of terms, possibly infinite.
   *
   * @returns The number of terms, possibly infinite.
   * @see SymPy `sympy.series.sequences.EmptySequence.length`
   */
  override get length(): Expr {
    return S.Zero;
  }
  /**
   * The first index of the series or sequence.
   *
   * @returns The first index of the series or sequence.
   * @see SymPy `sympy.series.sequences.EmptySequence.start`
   */
  override get start(): Expr {
    return S.Infinity;
  }
  /**
   * The last index of the series or sequence.
   *
   * @returns The last index of the series or sequence.
   * @see SymPy `sympy.series.sequences.EmptySequence.stop`
   */
  override get stop(): Expr {
    return S.NegativeInfinity;
  }
  /**
   * EmptySequence has no terms: every index is out of bounds.
   *
   * @param pt - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.EmptySequence.coeff`
   */
  coeff(pt: ExprLike): Expr {
    return this.point(pt);
  }
  /**
   * Scales every term of the sequence by a scalar.
   *
   * @returns The sequence of scaled terms.
   * @see SymPy `sympy.series.sequences.EmptySequence.coeff_mul`
   */
  override coeffMul(): SeqBase {
    return this;
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @returns A plain-text representation.
   */
  override printStr(): string {
    return 'EmptySequence';
  }
}

/**
 * The sequence with no terms.
 *
 * @see SymPy `sympy.series.sequences.EmptySequence`
 * @example
 * ```ts
 * import { EmptySequence, SeqMul, SeqPer } from '@symjs/symjs';
 *
 * SeqMul(SeqPer([1, 2]), EmptySequence); // => EmptySequence
 * ```
 */
export const EmptySequence: SeqBase = new EmptySequenceNode();

/** A sequence given by an expression of its variable on an interval (SymPy SeqExpr). */
abstract class SeqExprBase extends SeqBase {
  /** The expression generating this sequence. */
  get gen(): Expr { return at(this.args, 3); }
  /** The bound variable. */
  get variable(): Sym {
    return cast(at(this.args, 0), Sym, 'sequence variable');
  }
  override get interval(): SetExpr {
    return interval(at(this.args, 1), at(this.args, 2));
  }
  override get start(): Expr {
    return at(this.args, 1);
  }
  override get stop(): Expr {
    return at(this.args, 2);
  }
  override get variables(): Sym[] {
    return [this.variable];
  }
  protected limitsStr(print: (e: Expr) => string): string {
    return `(${print(this.variable)}, ${print(this.start)}, ${print(this.stop)})`;
  }
}

/**
 * A symbolic sequence expression, without a rule for evaluating its terms.
 *
 * @see SymPy `sympy.series.sequences.SeqExpr`
 * @example
 * ```ts
 * import { SeqExprNode, Tuple, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * new SeqExprNode(Tuple(1, 2, 3), x, ex`0`, ex`10`).length; // => 11
 * ```
 */
export class SeqExprNode extends SeqExprBase {
  /**
   * Constructs a new `SeqExprNode`.
   *
   * @param gen - Generating expression.
   * @param variable - Independent variable.
   * @param start - First index.
   * @param stop - Final index.
   */
  constructor(gen: Expr, variable: Sym, start: Expr, stop: Expr) {
    super('SeqExpr', [variable, start, stop, gen]);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new SeqExprNode(at(args, 3), cast(at(args, 0), Sym), at(args, 1), at(args, 2));
  }
  /**
   * The term at the given index.
   *
   * @returns The term at the specified index.
   * @throws NotImplementedError when the base sequence has no term evaluation rule.
   * @see SymPy `sympy.series.sequences.SeqExpr.coeff`
   */
  coeff(): Expr { throw new NotImplementedError('SeqExpr: no term evaluation rule'); }
}

/**
 * Constructs an indexed sequence from its generator and inclusive bounds.
 *
 * @param gen - Generating expression.
 * @param limits - Index variable and inclusive endpoints, or just the endpoints.
 * @returns The resulting sequence.
 * @see SymPy `sympy.series.sequences.SeqExpr`
 * @example
 * ```ts
 * import { SeqExpr, Tuple, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * SeqExpr(Tuple(1, 2, 3), [x, 0, 10]).length; // => 11
 * ```
 */
export function SeqExpr(gen: ExprLike, limits: readonly [Sym, ExprLike, ExprLike]): SeqExprNode {
  return new SeqExprNode(sympify(gen), limits[0], sympify(limits[1]), sympify(limits[2]));
}

/** Limits (x, start, stop) or (start, stop) of a sequence. */
export type SeqLimits = readonly [Sym, ExprLike, ExprLike] | readonly [ExprLike, ExprLike];

/** The variable, start and stop of a sequence (the variable found from the expression when omitted). */
function parseLimits(limits: SeqLimits | undefined, find: () => Sym): [Sym, Expr, Expr] {
  let x: Sym;
  let start: Expr;
  let stop: Expr;
  if (limits === undefined) [x, start, stop] = [find(), S.Zero, S.Infinity];
  else if (limits.length === 3) {
    const v = limits[0];
    if (!(v instanceof Sym)) throw new RangeError(`Invalid limits given: ${String(limits)}`);
    [x, start, stop] = [v, sympify(limits[1]), sympify(limits[2])];
  } else [x, start, stop] = [find(), sympify(limits[0]), sympify(limits[1])];
  if (isInf(start, '-oo') && isInf(stop, 'oo')) throw new RangeError('Both the start and end value cannot be unbounded');
  return [x, start, stop];
}

/**
 * The sequence of the values of a formula.
 *
 * @see SymPy `sympy.series.sequences.SeqFormula`
 * @example
 * ```ts
 * import { SeqFormulaNode, ex, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * new SeqFormulaNode(ex`n**2`, n, ex`0`, ex`5`).coeff(3); // => 9
 * ```
 */
export class SeqFormulaNode extends SeqExprBase {
  /**
   * Constructs a new `SeqFormulaNode`.
   *
   * @param formula - Expression for the term at the running index.
   * @param x - Variable of the expansion.
   * @param start - First index.
   * @param stop - Final index.
   */
  constructor(formula: Expr, x: Sym, start: Expr, stop: Expr) {
    super('SeqFormula', [x, start, stop, formula]);
  }
  /**
   * The formula of the terms.
   *
   * @returns The formula of the terms.
   * @see SymPy `sympy.series.sequences.SeqFormula.formula`
   */
  get formula(): Expr {
    return at(this.args, 3);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return SeqFormula(at(args, 3), [cast(at(args, 0), Sym, 'sequence variable'), at(args, 1), at(args, 2)]);
  }
  /**
   * The argument positions of bound variables and their scopes.
   *
   * @returns The argument positions of bound variables and their scopes.
   */
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [0], scope: [3] };
  }
  /**
   * Evaluates the defining formula at the supplied index.
   *
   * @param pt0 - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.SeqFormula.coeff`
   */
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    return subs(this.formula, [[this.variable, pt]]);
  }
  /**
   * Scales every term of the sequence by a scalar.
   *
   * @param coeff - Scalar multiplier of each term.
   * @returns The sequence of scaled terms.
   * @see SymPy `sympy.series.sequences.SeqFormula.coeff_mul`
   */
  override coeffMul(coeff: ExprLike): SeqBase {
    return SeqFormula(mul(this.formula, sympify(coeff)), [this.variable, this.start, this.stop]);
  }
  /**
   * The sequence of the expanded formula.
   *
   * @returns The sequence of the expanded formula.
   * @see SymPy `sympy.series.sequences.SeqFormula.expand`
   */
  expand(): SeqBase {
    return SeqFormula(expand(this.formula), [this.variable, this.start, this.stop]);
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @param print - Printer used for the component expressions.
   * @returns A plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    return `SeqFormula(${print(this.formula)}, ${this.limitsStr(print)})`;
  }
}

/**
 * Defines a sequence by evaluating a formula at successive indices. With no explicit limits, the indices start at zero.
 *
 * @param formulaIn - Expression for the term at the running index.
 * @param limits - Index variable and inclusive endpoints, or just the endpoints.
 * @returns The formula sequence, or `EmptySequence` for an empty interval.
 * @throws RangeError when the index is ambiguous or invalid, or both endpoints are unbounded.
 * @see SymPy `sympy.series.sequences.SeqFormula`
 * @example
 * ```ts
 * import { SeqFormula, ex, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * SeqFormula(ex`n**2`, [n, 0, 5]).coeff(3); // => 9
 * ```
 */
export function SeqFormula(formulaIn: ExprLike, limits?: SeqLimits): SeqBase {
  const formula = sympify(formulaIn);
  const [x, start, stop] = parseLimits(limits, () => {
    const free = [...freeSymbols(formula)].filter((s) => s instanceof Sym);
    if (free.length === 1) return at(free, 0);
    if (free.length === 0) return new Dummy('k');
    throw new RangeError(
      ` specify dummy variables for ${formula.toString()}. If the formula contains more than one free symbol, a dummy variable should be supplied explicitly e.g., SeqFormula(m*n**2, (n, 0, 5))`,
    );
  });
  if (interval(start, stop) === EmptySet) return EmptySequence;
  return new SeqFormulaNode(formula, x, start, stop);
}

/**
 * A periodic sequence.
 *
 * @see SymPy `sympy.series.sequences.SeqPer`
 * @example
 * ```ts
 * import { SeqPerNode, ex, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * new SeqPerNode([ex`1`, ex`2`, ex`3`], n, ex`0`, ex`5`).period; // => 3
 * ```
 */
export class SeqPerNode extends SeqExprBase {
  /**
   * Constructs a new `SeqPerNode`.
   *
   * @param periodical - Terms repeated in each period.
   * @param x - Variable of the expansion.
   * @param start - First index.
   * @param stop - Final index.
   */
  constructor(periodical: readonly Expr[], x: Sym, start: Expr, stop: Expr) {
    super('SeqPer', [x, start, stop, ...periodical]);
  }
  /**
   * The terms of one period.
   *
   * @returns The terms of one period.
   * @see SymPy `sympy.series.sequences.SeqPer.periodical`
   */
  get periodical(): Expr[] {
    return this.args.slice(3);
  }
  /**
   * The expression generating the terms of the sequence.
   *
   * @returns The expression generating the terms of the sequence.
   * @see SymPy `sympy.series.sequences.SeqPer.gen`
   */
  override get gen(): Expr { return Tuple(...this.periodical); }
  /**
   * The length of the period.
   *
   * @returns The length of the period.
   * @see SymPy `sympy.series.sequences.SeqPer.period`
   */
  get period(): number {
    return this.args.length - 3;
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return SeqPer(args.slice(3), [cast(at(args, 0), Sym, 'sequence variable'), at(args, 1), at(args, 2)]);
  }
  /**
   * The argument positions of bound variables and their scopes.
   *
   * @returns The argument positions of bound variables and their scopes.
   */
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [0], scope: this.periodical.map((_, i) => 3 + i) };
  }
  /**
   * Selects a term by reducing its index modulo the period.
   *
   * @param pt0 - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.SeqPer.coeff`
   */
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    const k = isInf(this.start, '-oo') ? asIndex(sub(this.stop, pt)) : asIndex(sub(pt, this.start));
    const idx = ((k % this.period) + this.period) % this.period;
    return subs(at(this.periodical, idx), [[this.variable, pt]]);
  }
  /**
   * Scales every term of the sequence by a scalar.
   *
   * @param coeff - Scalar multiplier of each term.
   * @returns The sequence of scaled terms.
   * @see SymPy `sympy.series.sequences.SeqPer.coeff_mul`
   */
  override coeffMul(coeff: ExprLike): SeqBase {
    const c = sympify(coeff);
    return SeqPer(this.periodical.map((t) => mul(t, c)), [this.variable, this.start, this.stop]);
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @param print - Printer used for the component expressions.
   * @returns A plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    const per = this.periodical;
    const tuple = per.length === 1 ? `(${print(at(per, 0))},)` : `(${per.map(print).join(', ')})`;
    return `SeqPer(${tuple}, ${this.limitsStr(print)})`;
  }
}

/**
 * Repeats the supplied terms over an inclusive range of indices.
 *
 * @param periodical - Terms repeated in each period.
 * @param limits - Index variable and inclusive endpoints, or just the endpoints.
 * @returns The periodic sequence, or `EmptySequence` for an empty interval.
 * @throws RangeError when the index is invalid or both endpoints are unbounded.
 * @see SymPy `sympy.series.sequences.SeqPer`
 * @example
 * ```ts
 * import { SeqPer } from '@symjs/symjs';
 *
 * SeqPer([1, 2, 3], [0, 5]).coeff(3); // => 1
 * ```
 */
export function SeqPer(periodical: readonly ExprLike[], limits?: SeqLimits): SeqBase {
  const per = periodical.map(sympify);
  const [x, start, stop] = parseLimits(limits, () => {
    const free = new Map<string, Sym>();
    for (const t of per) for (const s of [...freeSymbols(t)].filter((s) => s instanceof Sym)) free.set(s.key, s);
    return free.size === 1 ? at([...free.values()], 0) : new Dummy('k');
  });
  if (interval(start, stop) === EmptySet) return EmptySequence;
  return new SeqPerNode(per, x, start, stop);
}

/**
 * Creates a periodic sequence from an array or a formula sequence from an expression.
 *
 * @param seq - Formula or array of repeating terms.
 * @param limits - Index variable and inclusive endpoints, or just the endpoints.
 * @returns The sequence on the requested interval.
 * @throws RangeError when the index is invalid or both endpoints are unbounded.
 * @see SymPy `sympy.series.sequences.sequence`
 * @example
 * ```ts
 * import { ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * sequence(ex`n**2`, [n, 0, 5]).coeff(3); // => 9
 * ```
 */
export function sequence(seq: ExprLike | readonly ExprLike[], limits?: SeqLimits): SeqBase {
  const isList = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);
  return isList(seq) ? SeqPer(seq, limits) : SeqFormula(seq, limits);
}

/** The applications y(...) of the undefined function y in e. */
function applications(e: Expr, y: string, out: Expr[] = []): Expr[] {
  if (e instanceof UndefFn && e.name === y) out.push(e);
  for (const a of e.args) applications(a, y, out);
  return out;
}

/**
 * A sequence defined by a recurrence relation and initial terms.
 *
 * @see SymPy `sympy.series.sequences.RecursiveSeq`
 * @example
 * ```ts
 * import { UndefFn, RecursiveSeqNode, SymFunction, ex, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const y = SymFunction('y');
 * const recurrence = y(n.sub(1)).add(y(n.sub(2)));
 * new RecursiveSeqNode(recurrence, y(n) as UndefFn, n, [ex`0`, ex`1`], ex`0`, 2).coeff(3); // => 2
 * ```
 */
export class RecursiveSeqNode extends SeqBase {
  /** The terms computed so far, from the start on. */
  private readonly terms: Expr[];
  /** The order of the recurrence. */
  readonly degree: number;
  /**
   * Constructs a new `RecursiveSeqNode`.
   *
   * @param recurrence - Expression for a term in terms of earlier values.
   * @param yn - Sequence function evaluated at its index.
   * @param n - Index variable of the sequence.
   * @param initial - Consecutive initial terms.
   * @param start - First index.
   * @param degree - Order of the recurrence.
   */
  constructor(recurrence: Expr, yn: UndefFn, n: Sym, initial: readonly Expr[], start: Expr, degree: number) {
    super('RecursiveSeq', [recurrence, yn, n, start, ...initial]);
    this.degree = degree;
    this.terms = [...initial];
  }
  /**
   * The equation y(n) = recurrence.
   *
   * @returns The equation y(n) = recurrence.
   * @see SymPy `sympy.series.sequences.RecursiveSeq.recurrence`
   */
  get recurrence(): Expr {
    return Eq(this.yn, at(this.args, 0));
  }
  /**
   * The term y(n).
   *
   * @returns The term y(n).
   * @see SymPy `sympy.series.sequences.RecursiveSeq.yn`
   */
  get yn(): UndefFn {
    return cast(at(this.args, 1), UndefFn, 'recurrence function');
  }
  /**
   * The recurrence variable.
   *
   * @returns The recurrence variable.
   */
  get variable(): Sym {
    return cast(at(this.args, 2), Sym, 'recurrence variable');
  }
  /**
   * The initial terms.
   *
   * @returns The initial terms.
   * @see SymPy `sympy.series.sequences.RecursiveSeq.initial`
   */
  get initial(): Expr[] {
    return this.args.slice(4);
  }
  /**
   * The first index of the series or sequence.
   *
   * @returns The first index of the series or sequence.
   * @see SymPy `sympy.series.sequences.RecursiveSeq.start`
   */
  override get start(): Expr {
    return at(this.args, 3);
  }
  /**
   * The last index of the series or sequence.
   *
   * @returns The last index of the series or sequence.
   * @see SymPy `sympy.series.sequences.RecursiveSeq.stop`
   */
  override get stop(): Expr {
    return S.Infinity;
  }
  /**
   * The inclusive interval of term indices.
   *
   * @returns The inclusive interval of term indices.
   * @see SymPy `sympy.series.sequences.RecursiveSeq.interval`
   */
  override get interval(): SetExpr {
    return interval(this.start, S.Infinity);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return RecursiveSeq(at(args, 0), at(args, 1), at(args, 2), args.slice(4), at(args, 3));
  }
  /**
   * The term at the given index.
   *
   * @param pt - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.RecursiveSeq.coeff`
   */
  coeff(pt: ExprLike): Expr {
    const index = this.point(pt);
    const i = asIndex(sub(index, this.start));
    for (let current = this.terms.length; current <= i; current++) {
      const rec = xreplace(at(this.args, 0), [[this.variable, add(this.start, current)]]);
      // the earlier terms y(start + k) by their values
      const known = this.terms.map((t, k): [Expr, Expr] => [new UndefFn(this.yn.name, [add(this.start, k)]), t]);
      this.terms.push(xreplace(rec, known));
    }
    return at(this.terms, i);
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @param print - Printer used for the component expressions.
   * @returns A plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    const init = this.initial;
    return `RecursiveSeq(${print(at(this.args, 0))}, ${print(this.yn)}, ${print(this.variable)}, (${init.map(print).join(', ')}${init.length === 1 ? ',' : ''}), ${print(this.start)})`;
  }
}

/**
 * The sequence y(n)
 * with y(n) = recurrence for n >= start + degree and the initial terms
 * (Dummy symbols c_k when omitted) before.
 *
 * @param recurrenceIn - Expression for a term in terms of earlier values.
 * @param yn - Sequence function evaluated at its index.
 * @param n - Index variable of the sequence.
 * @param initial - Consecutive initial terms.
 * @param startIn - First index.
 * @returns The sequence y(n) with y(n) = recurrence for n >= start + degree and the initial terms (Dummy symbols c_k when omitted) before.
 * @throws TypeError when the recurrence has invalid shifts or does not define a recurrence for the given indexed function.
 * @throws RangeError when the number of initial values differs from the recurrence order.
 * @see SymPy `sympy.series.sequences.RecursiveSeq`
 * @example
 * ```ts
 * import { RecursiveSeq, SymFunction, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const y = SymFunction('y');
 * const recurrence = y(n.sub(1)).add(y(n.sub(2)));
 * RecursiveSeq(recurrence, y(n), n, [0, 1]).coeff(3); // => 2
 * ```
 */
export function RecursiveSeq(recurrenceIn: ExprLike, yn: Expr, n: Expr, initial: readonly ExprLike[] = [], startIn: ExprLike = 0): SeqBase {
  if (!(yn instanceof UndefFn)) throw new TypeError(`recurrence sequence must be an applied undefined function, found \`${yn.toString()}\``);
  if (!(n instanceof Sym)) throw new TypeError(`recurrence variable must be a symbol, found \`${n.toString()}\``);
  if (yn.args.length !== 1 || at(yn.args, 0).key !== n.key) throw new TypeError('recurrence sequence does not match symbol');
  const recurrence = sympify(recurrenceIn);
  let degree = 0;
  for (const prev of applications(recurrence, yn.name)) {
    if (prev.args.length !== 1) throw new TypeError('Recurrence should be in a single variable');
    const shift = sub(at(prev.args, 0), n);
    if (!(shift instanceof Rational && shift.isInteger && shift.isNegative)) throw new TypeError(`Recurrence should have constant, negative, integer shifts (found ${prev.toString()})`);
    degree = Math.max(degree, -Number(shift.p));
  }
  const init = initial.length ? initial.map(sympify) : Array.from({ length: degree }, (_, k) => new Dummy(`c_${k}`));
  if (init.length !== degree) throw new RangeError('Number of initial terms must equal degree');
  return new RecursiveSeqNode(recurrence, yn, n, init, sympify(startIn), degree);
}

/** The bounds of the interval common to two sequences. */
function commonBounds(a: SeqBase, b: SeqBase): [Expr, Expr] {
  const iv = intersection(a.interval, b.interval);
  return [inf(iv), sup(iv)];
}

/** Two periodic sequences combined term-wise over the least common period. */
function combinePeriodic(a: SeqPerNode, b: SeqPerNode, op: (u: Expr, v: Expr) => Expr): SeqBase {
  const [p1, p2] = [a.periodical, b.periodical];
  const g = (u: number, v: number): number => (v === 0 ? u : g(v, u % v));
  const len = (p1.length / g(p1.length, p2.length)) * p2.length;
  const per = Array.from({ length: len }, (_, i) => op(at(p1, i % p1.length), at(p2, i % p2.length)));
  const [start, stop] = commonBounds(a, b);
  return SeqPer(per, [a.variable, start, stop]);
}

/**
 * The term-wise sum or product of two sequences when a rule applies (SymPy
 * SeqFormula._add and _mul, SeqPer._add and _mul), else undefined.
 */
function combineRule(s: SeqBase, t: SeqBase, op: (u: Expr, v: Expr) => Expr): SeqBase | undefined {
  if (s instanceof SeqFormulaNode && t instanceof SeqFormulaNode) {
    const [start, stop] = commonBounds(s, t);
    return SeqFormula(op(s.formula, subs(t.formula, [[t.variable, s.variable]])), [s.variable, start, stop]);
  }
  if (s instanceof SeqPerNode && t instanceof SeqPerNode) return combinePeriodic(s, t, op);
  return undefined;
}

/** The number of nodes of an expression tree (SymPy _nodes). */
const nodeCount = (e: Expr): number => 1 + e.args.reduce((t, a) => t + nodeCount(a), 0);

/** The number of nodes of a sequence as SymPy counts them (the limits are a Tuple, the period of SeqPer too). */
function seqNodes(s: SeqBase): number {
  if (s instanceof SeqFormulaNode) return 5 + nodeCount(s.formula);
  if (s instanceof SeqPerNode) return 6 + s.periodical.reduce((t, a) => t + nodeCount(a), 0);
  return 1 + s.args.reduce((t, a) => t + (a instanceof SeqBase ? seqNodes(a) : nodeCount(a)), 0);
}

/**
 * The arguments of SeqAdd and SeqMul in SymPy's order (ordered with the key
 * _start_key): by start, then by the number of nodes, then by class name and
 * printed form.
 */
function ordered(args: readonly SeqBase[]): SeqBase[] {
  return [...args].sort((a, b) => {
    const [sa, sb] = [a.start, b.start];
    if (less(sa, sb)) return -1;
    if (less(sb, sa)) return 1;
    const d = seqNodes(a) - seqNodes(b);
    if (d !== 0) return d;
    if (a.name !== b.name) return a.name < b.name ? -1 : 1;
    return a.key < b.key ? -1 : a.key > b.key ? 1 : 0;
  });
}

/** The sequences of nested arguments, with nested operations of the same class flattened. */
function flattenSeqs(args: readonly (SeqBase | readonly SeqBase[])[], cls: typeof SeqAddNode | typeof SeqMulNode): SeqBase[] {
  const out: SeqBase[] = [];
  const go = (a: SeqBase | readonly SeqBase[]): void => {
    if (a instanceof cls) a.seqs.forEach(go);
    else if (a instanceof SeqBase) out.push(a);
    else a.forEach(go);
  };
  args.forEach(go);
  return out;
}

/** The interval common to the sequences. */
const commonInterval = (args: readonly SeqBase[]): SetExpr => intersection(...args.map((a) => a.interval));

/** Combine pairs of the sequences by the rule until none applies (SymPy SeqAdd.reduce and SeqMul.reduce). */
function reduce(args0: readonly SeqBase[], rule: (s: SeqBase, t: SeqBase) => SeqBase | undefined): SeqBase[] {
  let args = [...args0];
  for (let changed = true; changed; ) {
    changed = false;
    outer: for (let i = 0; i < args.length; i++) {
      for (let j = 0; j < args.length; j++) {
        if (i === j) continue;
        const s = at(args, i);
        const t = at(args, j);
        const r = rule(s, t);
        if (r !== undefined) {
          args = [...args.filter((a) => a !== s && a !== t), r];
          changed = true;
          break outer;
        }
      }
    }
  }
  return args;
}

/** Term-wise operation of sequences (SymPy SeqExprOp). */
abstract class SeqExprOpBase extends SeqBase {
  /** The generators of all operands, preserving their order. */
  get gen(): Expr {
    return Tuple(...this.seqs.map((s) => {
      if (s instanceof SeqExprBase || s instanceof SeqExprOpBase) return s.gen;
      throw new TypeError('SeqExprOp: operand has no expression generator');
    }));
  }
  /** The operand sequences. */
  get seqs(): SeqBase[] {
    return this.args.map((a) => cast(a, SeqBase, 'sequence'));
  }
  override get interval(): SetExpr {
    return commonInterval(this.seqs);
  }
  override get variables(): Sym[] {
    return this.seqs.flatMap((s) => s.variables);
  }
}

/**
 * An unevaluated operation on sequences, with their common interval.
 *
 * @see SymPy `sympy.series.sequences.SeqExprOp`
 * @example
 * ```ts
 * import { SeqExprOpNode, ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const a = sequence(ex`n**2`, [n, 0, 10]);
 * const b = sequence([1, 2, 3], [n, 5, 10]);
 * new SeqExprOpNode([a, b]).length; // => 6
 * ```
 */
export class SeqExprOpNode extends SeqExprOpBase {
  /**
   * Constructs a new `SeqExprOpNode`.
   *
   * @param seqs - Operand sequences.
   */
  constructor(seqs: readonly SeqBase[]) { super('SeqExprOp', seqs); }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr { return new SeqExprOpNode(args.map((a) => cast(a, SeqBase))); }
  /**
   * The term at the given index.
   *
   * @returns The term at the specified index.
   * @throws NotImplementedError when the operation has no term evaluation rule.
   * @see SymPy `sympy.series.sequences.SeqExprOp.coeff`
   */
  coeff(): Expr { throw new NotImplementedError('SeqExprOp: no term evaluation rule'); }
}

/**
 * Represents an unevaluated operation on sequences over their common interval.
 *
 * @param seqs - Operand sequences.
 * @returns The resulting sequence.
 * @see SymPy `sympy.series.sequences.SeqExprOp`
 * @example
 * ```ts
 * import { SeqExprOp, ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const a = sequence(ex`n**2`, [n, 0, 10]);
 * const b = sequence([1, 2, 3], [n, 5, 10]);
 * SeqExprOp(a, b).length; // => 6
 * ```
 */
export function SeqExprOp(...seqs: SeqBase[]): SeqExprOpNode { return new SeqExprOpNode(seqs); }

/**
 * The term-wise sum of sequences (unevaluated).
 *
 * @see SymPy `sympy.series.sequences.SeqAdd`
 * @example
 * ```ts
 * import { SeqAddNode, ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const a = sequence(ex`n**2`, [n, 0, 10]);
 * const b = sequence([1, 2, 3], [n, 5, 10]);
 * new SeqAddNode([a, b]).coeff(5); // => 26
 * ```
 */
export class SeqAddNode extends SeqExprOpBase {
  /**
   * Constructs a new `SeqAddNode`.
   *
   * @param args - The operand sequences.
   */
  constructor(args: readonly SeqBase[]) {
    super('SeqAdd', ordered(flattenSeqs(args, SeqAddNode)));
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return SeqAdd(...args.map((a) => cast(a, SeqBase, 'sequence')));
  }
  /**
   * The term at the given index.
   *
   * @param pt0 - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.SeqAdd.coeff`
   */
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    return add(...this.seqs.map((a) => a.coeff(pt)));
  }
}

/**
 * The term-wise product of sequences (unevaluated).
 *
 * @see SymPy `sympy.series.sequences.SeqMul`
 * @example
 * ```ts
 * import { SeqMulNode, ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const a = sequence(ex`n**2`, [n, 0, 10]);
 * const b = sequence([1, 2, 3], [n, 5, 10]);
 * new SeqMulNode([a, b]).coeff(5); // => 25
 * ```
 */
export class SeqMulNode extends SeqExprOpBase {
  /**
   * Constructs a new `SeqMulNode`.
   *
   * @param args - The operand sequences.
   */
  constructor(args: readonly SeqBase[]) {
    super('SeqMul', ordered(flattenSeqs(args, SeqMulNode)));
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return SeqMul(...args.map((a) => cast(a, SeqBase, 'sequence')));
  }
  /**
   * The term at the given index.
   *
   * @param pt0 - Index of the requested term.
   * @returns The term at the specified index.
   * @see SymPy `sympy.series.sequences.SeqMul.coeff`
   */
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    return mul(...this.seqs.map((a) => a.coeff(pt)));
  }
}

/**
 * Adds sequences term by term on the intersection of their index intervals.
 *
 * @param seqs - Operand sequences.
 * @returns The sum on the common interval, or `EmptySequence` if it is empty.
 * @see SymPy `sympy.series.sequences.SeqAdd`
 * @example
 * ```ts
 * import { SeqAdd, ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const a = sequence(ex`n**2`, [n, 0, 10]);
 * const b = sequence([1, 2, 3], [n, 5, 10]);
 * SeqAdd(a, b).coeff(5); // => 26
 * ```
 */
export function SeqAdd(...seqs: (SeqBase | readonly SeqBase[])[]): SeqBase {
  const args = flattenSeqs(seqs, SeqAddNode).filter((a) => a !== EmptySequence);
  if (!args.length || commonInterval(args) === EmptySet) return EmptySequence;
  const r = reduce(args, (s, t) => combineRule(s, t, add));
  return r.length === 1 ? at(r, 0) : new SeqAddNode(r);
}

/**
 * Multiplies sequences term by term on the intersection of their index intervals.
 *
 * @param seqs - Operand sequences.
 * @returns The product on the common interval, or `EmptySequence` if it is empty.
 * @see SymPy `sympy.series.sequences.SeqMul`
 * @example
 * ```ts
 * import { SeqMul, ex, sequence, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * const a = sequence(ex`n**2`, [n, 0, 10]);
 * const b = sequence([1, 2, 3], [n, 5, 10]);
 * SeqMul(a, b).coeff(5); // => 25
 * ```
 */
export function SeqMul(...seqs: (SeqBase | readonly SeqBase[])[]): SeqBase {
  const args = flattenSeqs(seqs, SeqMulNode);
  if (!args.length || commonInterval(args) === EmptySet) return EmptySequence;
  const r = reduce(args, (s, t) => combineRule(s, t, mul));
  return r.length === 1 ? at(r, 0) : new SeqMulNode(r);
}

// Reflected arithmetic on a scalar and a sequence follows the sequence protocol.
registerArithmetic((op, args) => {
  const [left, right] = args;
  if (args.length !== 2 || !(right instanceof SeqBase) || left instanceof SeqBase) return undefined;
  if (op === 'add') return right.add(at(args, 0));
  if (op === 'mul') return right.mul(at(args, 0));
  return undefined;
});
