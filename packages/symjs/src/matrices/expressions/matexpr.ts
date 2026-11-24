// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Kernel of SymPy's matrix expressions (sympy.matrices.expressions):
 * the base class MatrixExpr and the classes that refer to each other
 * (MatrixSymbol, explicit matrices, MatAdd, MatMul, MatPow, Inverse,
 * Transpose, Adjoint, Identity, ZeroMatrix, OneMatrix, MatrixElement,
 * MatrixSlice, Trace, Determinant, Permanent, ElementwiseApplyFunction)
 * with their canonicalization rules and printers. They live in one module
 * so that the classes can build each other without import cycles; the
 * other modules of the directory extend MatrixExpr.
 */

import { asInt, isSquare as integerIsSquare } from '../../ntheory/intutil';
import { MatrixKind, type MatrixKindNode } from '../kind';
import { callableClass } from '../../core/callable';
import { Concrete, Sum } from '../../core/concrete';
import { MatrixError, NonInvertibleMatrixError, NonSquareMatrixError, NotImplementedError, ShapeError } from '../../core/errors';
export { ShapeError } from '../../core/errors';
import { at, cast, last } from '../../core/guard';
import { LambdaNode } from '../../core/lambda';
import type { ExprLike , Expr} from '../../core/nodes';
import { Add, Dummy, ExtensionExpr, Float, Mul, Pow, Rational, S, Sym, impl, registerArithmetic, registerFromiter, registerHead } from '../../core/nodes';
import { isIntegerQ, isNegative, isPositive, isZero } from '../../core/assumptions';
import { and } from '../../core/boolalg';
import { Eq } from '../../core/logic';
import { add, mul, pow, sympify } from '../../core/ops';
import { freeSymbols, rebuild } from '../../core/traverse';
import type { Truth } from '../../core/truth';
import { doitConcrete } from '../../concrete/summations';
import { adjoint as adjointFn, conjugate as conjugateFn, transpose as transposeFn } from '../../functions/elementary/elementary';
import { KroneckerDelta } from '../../functions/special/hyper';
import { floor } from '../../functions/special/special';
import { latex, latexMatrixSymbol, latexSettings } from '../../printing/latex';
import type { Key } from '../../printing/sortkey';
import { compareKeys, sortKey } from '../../printing/sortkey';
import { str } from '../../printing/str';
import { simplify as simplifyScalar } from '../../simplify/simplify';
import { matrixExp, permanent as explicitPermanent } from '../linalg';
import { Matrix } from '../matrix';
import { PRECEDENCE, isInt, isNumber, relTruth, same, sameList, scalarPrecTraditional, toInt } from './util';
import { precedence as scalarPrecedence } from '../../printing/str';

/** Anything accepted where SymPy sympifies a matrix argument: expressions and explicit matrices. */
export type MatArg = ExprLike | Matrix;

/** Hints of doit. */
export interface DoitHints {
  /** Evaluate the arguments first (default true). */
  readonly deep?: boolean;
  /** False keeps Inverse unevaluated. */
  readonly invExpand?: boolean;
}

/** A slice of a matrix dimension: SymPy `a:b:c` as `[a, b, c]` (null for an omitted bound), or one index. */
export type SliceSpec = ExprLike | readonly [(ExprLike | null)?, (ExprLike | null)?, (ExprLike | null)?];


// ---------------------------------------------------------------------------
// sympify for matrices
// ---------------------------------------------------------------------------

/**
 * Converts an explicit matrix to an immutable matrix expression and sympifies scalar inputs.
 * @param x - The expression or entry to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.immutable.sympify_matrix`
 */
export function toExpr(x: MatArg): Expr {
  if (x instanceof Matrix) return new ImmutableMatrixNode(x);
  return sympify(x);
}

/**
 * Tests whether a value is a matrix expression.
 * @param e - The expression to examine.
 * @returns Whether the value is an instance of `MatrixExpr`.
 */
export const isMatrix = (e: unknown): e is MatrixExpr => e instanceof MatrixExpr;

/** A matrix expression from an argument, or a TypeError. */
export function toMatrix(x: MatArg, message?: string): MatrixExpr {
  const e = toExpr(x);
  if (!(e instanceof MatrixExpr)) throw new TypeError(message ?? `${str(e)} is not a matrix`);
  return e;
}

/** SymPy MatrixExpr._check_dim: a dimension must be a nonnegative integer when that is known. */
export function checkDim(d: Expr): Expr {
  let bad = d instanceof Float;
  if (d instanceof Rational) bad = !d.isInteger || d.isNegative;
  else if (!bad) bad = isIntegerQ(d) === false || isNegative(d) === true;
  if (bad) throw new RangeError(`The dimension specification ${str(d)} should be a nonnegative integer.`);
  return d;
}

const dim = (x: ExprLike): Expr => checkDim(sympify(x));

// ---------------------------------------------------------------------------
// Printing helpers
// ---------------------------------------------------------------------------

/** SymPy precedence() of an expression that may be a matrix expression. */
export function strPrecedence(e: Expr): number {
  if (e instanceof MatrixExpr || e instanceof MatScalar) return e.strPrecedence();
  return scalarPrecedence(e);
}

/** SymPy precedence_traditional() of an expression that may be a matrix expression. */
export function latexPrecedence(e: Expr): number {
  if (e instanceof MatrixExpr || e instanceof MatScalar) return e.latexPrecedence();
  return scalarPrecTraditional(e);
}

/** StrPrinter.parenthesize. */
export function parenStr(e: Expr, level: number, strict = false): string {
  const p = strPrecedence(e);
  const s = str(e);
  return p < level || (!strict && p <= level) ? `(${s})` : s;
}

/** LatexPrinter.parenthesize. */
export function parenLatex(e: Expr, level: number, strict = false): string {
  const p = latexPrecedence(e);
  const s = latex(e);
  return p < level || (!strict && p <= level) ? `\\left(${s}\\right)` : s;
}

/** SymPy could_extract_minus_sign of a matrix product: a negative number in front. */
function mulCouldExtractMinus(e: Expr): boolean {
  if (!(e instanceof MatMulNode)) return false;
  const c = e.args[0];
  return c !== undefined && isNumber(c) && c.isNegative;
}

// ---------------------------------------------------------------------------
// Sort keys (SymPy default_sort_key and as_ordered_terms for matrix terms)
// ---------------------------------------------------------------------------

const ONE_KEY: Key = [[1, 0, 'Number'], [0, []], [], 1];

/** SymPy default_sort_key of an expression that may contain matrix expressions. */
export function matSortKey(e: Expr): Key {
  if (e instanceof Str) return [[2, 0, 'Str'], [1, [e.value]], ONE_KEY, 1];
  if (e instanceof MatMulNode) {
    // MatMul.as_coeff_Mul() is (1, self): the numeric factor is sorted with the other commutative factors
    const cpart = e.args.filter((a) => !(a instanceof MatrixExpr) && a.isCommutative);
    const ncpart = e.args.filter((a) => a instanceof MatrixExpr || !a.isCommutative);
    const ordered = [...cpart.map((a) => ({ a, k: matSortKey(a) })).sort((x, y) => compareKeys(x.k, y.k)).map((x) => x.k), ...ncpart.map(matSortKey)];
    return [[3, 0, 'MatMul'], [ordered.length, ordered], ONE_KEY, 1];
  }
  if (e instanceof MatAddNode) {
    const ks = orderedTerms(e.args).map(matSortKey);
    return [[3, 1, 'MatAdd'], [ks.length, ks], ONE_KEY, 1];
  }
  if (e instanceof ImmutableMatrixNode) {
    const entries = e.matrix.data.map(matSortKey);
    return [[5, 0, 'ImmutableDenseMatrix'], [3, [sortKey(Rational.of(e.matrix.rows)), sortKey(Rational.of(e.matrix.cols)), [[5, 0, 'Tuple'], [entries.length, entries], ONE_KEY, 1]]], ONE_KEY, 1];
  }
  if (e instanceof MatrixExpr || e instanceof MatScalar) {
    const ks = e.sortArgs().map(matSortKey);
    return [[5, 0, e.name], [ks.length, ks], ONE_KEY, 1];
  }
  return sortKey(e);
}

/** SymPy Expr.as_ordered_terms() of the terms of a MatAdd (lex order of SymPy's printers). */
export function orderedTerms(terms: readonly Expr[]): Expr[] {
  const gens = new Map<string, Expr>();
  const parsed = terms.map((term) => {
    let re = 1;
    let im = 0;
    let factors: Expr[];
    if (term instanceof MatMulNode) {
      factors = [...term.args];
    } else factors = [term];
    const cpart = new Map<string, number>();
    const ncpart: Expr[] = [];
    for (const f of factors) {
      if (!(f instanceof MatrixExpr) && f.isCommutative && freeSymbols(f).size === 0 && !hasMatrix(f)) {
        try {
          const v = f.toComplex();
          [re, im] = [re * v.re - im * v.im, re * v.im + im * v.re];
          continue;
        } catch {
          // a generator
        }
      }
      if (!(f instanceof MatrixExpr) && f.isCommutative) {
        let base: Expr = f;
        let ex = 1;
        if (f instanceof Pow && isInt(f.exp)) {
          base = f.base;
          ex = toInt(f.exp);
        }
        cpart.set(base.key, (cpart.get(base.key) ?? 0) + ex);
        gens.set(base.key, base);
      } else ncpart.push(f);
    }
    return { term, re, im, cpart, ncpart };
  });
  const genList = [...gens.values()].map((g) => ({ g, k: matSortKey(g) })).sort((a, b) => compareKeys(a.k, b.k));
  const keyed = parsed.map(({ term, re, im, cpart, ncpart }) => {
    const monom: Key[] = genList.map(({ g }) => -(cpart.get(g.key) ?? 0));
    const ck: Key = [
      [im !== 0 ? 1 : 0, im],
      [re, im],
    ];
    return { term, k: [monom, ncpart.map(matSortKey), ck] as Key };
  });
  return keyed.sort((a, b) => compareKeys(a.k, b.k)).map((x) => x.term);
}

/** True when the expression contains a matrix expression. */
export function hasMatrix(e: Expr): boolean {
  return e instanceof MatrixExpr || e.args.some(hasMatrix);
}

/** True when the expression contains a node satisfying the predicate (SymPy has(cls)). */
export function hasNode(e: Expr, pred: (x: Expr) => boolean): boolean {
  return pred(e) || e.args.some((a) => hasNode(a, pred));
}

// ---------------------------------------------------------------------------
// doit
// ---------------------------------------------------------------------------

const doitable = (e: Expr): boolean => e instanceof MatrixExpr || e instanceof MatScalar || e instanceof Concrete || e.args.some(doitable);

/** SymPy doit of an argument: matrix nodes evaluate themselves, sums are carried out. */
export function doitArg(a: Expr, hints: DoitHints = {}): Expr {
  if (a instanceof MatrixExpr || a instanceof MatScalar) return a.doit(hints);
  if (!doitable(a)) return a;
  // a doitable node that is not a matrix node has arguments (a Concrete always has)
  const r = rebuild(a, a.args.map((x) => doitArg(x, hints)));
  return r instanceof Concrete ? doitConcrete(r) : r;
}

// ---------------------------------------------------------------------------
// Str: a name as an argument (SymPy Str)
// ---------------------------------------------------------------------------

/**
 * A string as an expression argument (the name of a MatrixSymbol).
 * @see SymPy `sympy.core.symbol.Str`
 */
export class Str extends ExtensionExpr {
  /**
   * Constructs a `Str`.
   * @param value - The value represented by this object.
   */
  constructor(
    /** The literal string value. */
    readonly value: string
  ) {
    super('Str', []);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @returns The expression with the given operands.
   */
  withArgs(): Expr {
    return this;
  }
  /**
   * Gets the ordering class for a literal string atom.
   * @returns The ordering class for a literal string atom.
   */
  override get atomClass(): boolean {
    return true;
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return this.value;
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return this.value;
  }
  protected override computeKey(): string {
    return `Str(${this.value})`;
  }
}

// ---------------------------------------------------------------------------
// The base classes
// ---------------------------------------------------------------------------

/** Context of entry(): the generator of summation dummies shared by nested products. */
export interface EntryContext {
  /** Supplies a fresh dummy index for an entry formula. */
  readonly dummy: () => Dummy;
}

/**
 * The base class of matrix expressions. Matrix expressions
 * do not commute; `A.mul(B)`, `A.add(B)` and `A.pow(n)` build and evaluate
 * MatMul, MatAdd and MatPow like SymPy's operators.
 * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr`
 * @example
 * ```ts
 * import { MatrixExpr, MatrixSymbol } from '@symjs/symjs';
 * MatrixSymbol('A', 3, 3) instanceof MatrixExpr; // => True
 * ```
 */
export abstract class MatrixExpr extends ExtensionExpr {
  /**
   * The mathematical kind of the matrix expression.
   * @returns The resulting matrix expression.
   */
  override kindSelf(): MatrixKindNode { return MatrixKind(); }
  /**
   * The shape (rows, cols).
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.shape`
   */
  abstract get shape(): [Expr, Expr];
  /**
   * The number of rows.
   * @returns The row count.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.rows`
   */
  get rows(): Expr {
    return this.shape[0];
  }
  /**
   * The number of columns.
   * @returns The column count.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.cols`
   */
  get cols(): Expr {
    return this.shape[1];
  }
  /**
   * Indicates whether the expression represents a scalar.
   * @returns Whether the matrix is scalar.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.is_scalar`
   */
  override get isScalar(): boolean {
    return false;
  }
  protected override computeCommutative(): boolean {
    return false;
  }
  /**
   * False for explicit matrices.
   * @returns Whether the matrix is matrix expr.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.is_MatrixExpr`
   */
  get isMatrixExpr(): boolean {
    return true;
  }
  /**
   * Tests whether the row and column counts agree.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.is_square`
   */
  get isSquare(): Truth {
    const [r, c] = this.shape;
    if (isInt(r) && isInt(c)) return r.p === c.p;
    if (same(r, c)) return true;
    return 'unknown';
  }
  /**
   * Tests whether the matrix is the identity.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.is_Identity`
   */
  get isIdentity(): Truth {
    return 'unknown';
  }
  /**
   * Tests whether the expression represents a zero matrix.
   * @returns Whether the matrix is zero matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.is_ZeroMatrix`
   */
  get isZeroMatrix(): boolean {
    return false;
  }

  // ---- arithmetic (SymPy operators) ----

  /**
   * Adds a matrix expression to the other operand.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.__add__`
   */
  override add(o: MatArg): Expr {
    return MatAddNode.create([this, toExpr(o)]).doit();
  }
  /**
   * Subtracts the other operand from this matrix.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.__sub__`
   */
  override sub(o: MatArg): Expr {
    return MatAddNode.create([this, negate(toExpr(o))]).doit();
  }
  /**
   * Adds this matrix on the right of the other operand.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   */
  radd(o: MatArg): Expr {
    return this.add(o);
  }
  /**
   * Subtracts this matrix from the other operand.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   */
  rsub(o: MatArg): Expr {
    return MatAddNode.create([toExpr(o), negate(this)]).doit();
  }
  /**
   * Multiplies this matrix by the right operand.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.__mul__`
   */
  override mul(o: MatArg): Expr {
    return matMul(this, toExpr(o));
  }
  /**
   * Multiplies the left operand by this matrix.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   */
  rmul(o: MatArg): Expr {
    return matMul(toExpr(o), this);
  }
  /**
   * Multiplies by the inverse of the other operand.
   * @param o - The other operand.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.__truediv__`
   */
  override div(o: MatArg): Expr {
    const e = toExpr(o);
    return this.mul(e instanceof MatrixExpr ? e.pow(-1) : pow(e, -1));
  }
  /**
   * Handles division with this matrix as the divisor.
   * @param _o - The other operand.
   * @returns This operation always throws.
   * @throws NotImplementedError when the divisor is a matrix.
   */
  rdiv(_o: MatArg): Expr {
    throw new NotImplementedError('Division by a matrix is not defined');
  }
  /**
   * Handles exponentiation with this matrix as the exponent.
   * @param _o - The exponent.
   * @returns This operation always throws.
   * @throws NotImplementedError when the exponent is a matrix.
   */
  rpow(_o: ExprLike): Expr {
    throw new NotImplementedError('Matrix Power not defined');
  }
  /**
   * Raises this matrix to the specified exponent.
   * @param o - The exponent.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr._pow`
   */
  override pow(o: ExprLike): Expr {
    return MatPowNode.create(this, sympify(o)).doit();
  }
  /**
   * Negates all entries of the matrix expression.
   * @returns The resulting symbolic expression.
   */
  override neg(): Expr {
    return negate(this);
  }

  // ---- transposition, inversion ----

  /**
   * The transpose.
   * @returns The transposed matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.T`
   */
  get T(): Expr {
    return this.transpose();
  }
  /**
   * Exchanges the row and column axes.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.transpose`
   */
  transpose(): Expr {
    return this.evalTranspose();
  }
  /**
   * Computes the conjugate transpose.
   * @returns The conjugate transpose.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.adjoint`
   */
  adjoint(): Expr {
    return this.evalAdjoint();
  }
  /**
   * The Hermitian adjoint (adjoint()).
   * @returns The conjugate transpose.
   */
  get H(): Expr {
    return this.adjoint();
  }
  /**
   * Conjugates the matrix entries.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.conjugate`
   */
  override conjugate(): Expr {
    return this.evalConjugate();
  }
  /**
   * Forms the inverse of this square matrix.
   * @returns The inverse of this square matrix.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.inverse`
   */
  inverse(): Expr {
    if (this.isSquare === false) throw new NonSquareMatrixError('Inverse of non-square matrix');
    return this.evalInverse();
  }
  /**
   * Forms the inverse of this square matrix.
   * @returns The inverse of this square matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.inv`
   */
  inv(): Expr {
    return this.inverse();
  }
  /**
   * The inverse.
   * @returns The inverse matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.I`
   */
  get I(): Expr {
    return this.inverse();
  }
  /**
   * The determinant.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.det`
   */
  det(): Expr {
    return det(this);
  }

  // ---- protocol (SymPy _eval_*); the defaults give the unevaluated forms ----

  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @internal
   */
  evalTranspose(): Expr {
    return new TransposeNode(this);
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @internal
   */
  evalAdjoint(): Expr {
    return new AdjointNode(this);
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @internal
   */
  evalConjugate(): Expr {
    return new AdjointNode(new TransposeNode(this));
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @internal
   */
  evalInverse(): Expr {
    return new InverseNode(this);
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @internal
   */
  evalDeterminant(): Expr {
    return new DeterminantNode(this);
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @internal
   */
  evalTrace(): Expr {
    return new TraceNode(this);
  }
  /**
   * Evaluates a power of this matrix when its structure determines the result.
   * @param exp - The exponent to apply.
   * @returns The resulting symbolic expression.
   * @internal
   */
  evalPower(exp: Expr): Expr {
    return new MatPowNode(this, exp);
  }
  /**
   * The entry without index validation.
   * @param _i - The zero-based row index.
   * @param _j - The zero-based column index.
   * @param _ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @throws NotImplementedError when the matrix expression has no entry formula.
   * @internal
   */
  entry(_i: Expr, _j: Expr, _ctx?: EntryContext): Expr {
    throw new NotImplementedError(`Indexing not implemented for ${this.name}`);
  }
  /**
   * Separates the real and imaginary parts of the matrix.
   * @returns The real-part matrix followed by the imaginary-part matrix.
   */
  override asRealImagSelf(): [Expr, Expr] {
    const c = this.evalConjugate();
    return [mul(S.Half, add(this, c)), mul(add(this, mul(-1, c)), pow(mul(2, S.I), -1))];
  }
  /**
   * Separates the scalar coefficient from the matrix product.
   * @returns The scalar coefficient followed by the matrix product.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.as_coeff_mmul`
   */
  asCoeffMmul(): [Expr, MatMulNode] {
    return [S.One, new MatMulNode([this])];
  }
  /**
   * Arguments used by the sort key.
   * @returns The expression operands used for canonical ordering.
   * @internal
   */
  sortArgs(): readonly Expr[] {
    return this.args;
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   * @internal
   */
  strPrecedence(): number {
    return PRECEDENCE.Atom;
  }
  /**
   * Returns the binding precedence used to parenthesize LaTeX output.
   * @returns The binding precedence used to parenthesize LaTeX output.
   * @internal
   */
  latexPrecedence(): number {
    return this.strPrecedence();
  }

  // ---- indexing ----

  /**
   * Tests whether the indices can select an entry of this matrix.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns Whether the indices can select an entry of this matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.valid_index`
   */
  validIndex(i: Expr, j: Expr): boolean {
    const ok = (idx: Expr, d: Expr): boolean => relTruth('Ge', idx, mul(-1, d)) !== false && relTruth('Lt', idx, d) !== false;
    return ok(i, this.rows) && ok(j, this.cols);
  }
  /**
   * Selects an entry, row, column or slice by index.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The resulting symbolic expression.
   * @throws RangeError when a single index is not an integer or a linear index is used with a symbolic column count or an index is out of bounds.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.__getitem__`
   */
  at(i: ExprLike, j?: ExprLike): Expr {
    if (j === undefined) {
      const k = sympify(i);
      const cols = this.cols;
      if (!isInt(k)) throw new RangeError('Only integers may be used when addressing the matrix with a single index.');
      if (!isInt(cols)) throw new RangeError('Single indexing is only supported when the number of columns is known.');
      const c = cols.p;
      let q = k.p / c;
      if (k.p % c !== 0n && k.p < 0n) q -= 1n;
      const r = Rational.of(q);
      const s = Rational.of(k.p - q * c);
      if (this.validIndex(r, s)) return this.entry(r, s);
      throw new RangeError(`Invalid index ${str(k)}`);
    }
    const a = sympify(i);
    const b = sympify(j);
    if (this.validIndex(a, b)) return this.entry(a, b);
    throw new RangeError(`Invalid indices (${str(a)}, ${str(b)})`);
  }
  /**
   * A MatrixSlice. A single index selects one row (or column).
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @returns A MatrixSlice.
   */
  slice(rows: SliceSpec, cols: SliceSpec = [null, null, null]): Expr {
    return MatrixSliceNode.create(this, rows, cols);
  }

  // ---- explicit forms ----

  /**
   * An explicit Matrix.
   * @returns The resulting matrix.
   * @throws RangeError when the dimensions are symbolic.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.as_explicit`
   */
  asExplicit(): Matrix {
    const [r, c] = this.shape;
    if (!isInt(r) || !isInt(c)) throw new RangeError('Matrix with symbolic shape cannot be represented explicitly.');
    return Matrix.fromFunction(toInt(r), toInt(c), (i, j) => this.at(i, j));
  }
  /**
   * An explicit matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.as_mutable`
   */
  asMutable(): Matrix {
    return this.asExplicit();
  }
  /**
   * Compares entries when both matrices have explicit dimensions.
   * @param other - The other matrix operand.
   * @returns Whether entrywise equality can be established.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.equals`
   */
  equalsExplicit(other: ExprLike | Matrix): boolean {
    const o = toExpr(other);
    if (same(this, o)) return true;
    if (!(o instanceof MatrixExpr)) return false;
    let a: Matrix;
    let b: Matrix;
    try {
      a = this.asExplicit();
      b = o.asExplicit();
    } catch {
      return false;
    }
    if (a.rows !== b.rows || a.cols !== b.cols) return false;
    return a.data.every((x, k) => {
      const y = at(b.data, k);
      if (same(x, y)) return true;
      const d = simplifyScalar(add(x, mul(-1, y)));
      return isZero(d) === true;
    });
  }

  // ---- evaluation ----

  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.doit`
   */
  doit(hints: DoitHints = {}): Expr {
    if (hints.deep === false) return this;
    const args = this.args.map((a) => doitArg(a, hints));
    return sameList(args, this.args) ? this : this.withArgs(args);
  }
  /**
   * Evaluates the operation represented by this node.
   * @returns The resulting symbolic expression.
   */
  override doitSelf(): Expr {
    return this.doit({ deep: false });
  }
  /**
   * Evaluates the matrix expression in canonical form.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.canonicalize`
   */
  canonicalize(): Expr {
    return this;
  }
  /**
   * The function applied to every entry (ElementwiseApplyFunction).
   * @param f - The function to apply to the entries.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.applyfunc`
   */
  applyfunc(f: LambdaNode | ((x: Expr) => Expr)): Expr {
    return ElementwiseApplyFunctionNode.create(f, this);
  }
  /**
   * The arguments simplified.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.simplify`
   */
  override simplify(): Expr {
    if (!this.args.length || this instanceof MatrixSymbolNode) return this;
    return this.withArgs(this.args.map(simplifyArg));
  }
  /**
   * Products distributed over sums.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixExpr.expand`
   */
  override expand(): Expr {
    return this.withArgs(this.args.map(expandArg));
  }
  /**
   * Transposes the expression.
   * @returns The resulting symbolic expression.
   */
  override transposeSelf(): Expr {
    return this.evalTranspose();
  }
  /**
   * Forms the conjugate transpose.
   * @returns The conjugate transpose.
   */
  override adjointSelf(): Expr {
    return this.evalAdjoint();
  }
  /**
   * Conjugates the expression.
   * @returns The resulting symbolic expression.
   */
  override conjugateSelf(): Expr {
    return this.evalConjugate();
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    void x;
    void d;
    return undefined;
  }
}

/**
 * Scalars built from matrices (Trace, Determinant, Permanent, MatrixElement,
 * DotProduct): commutative expressions with SymPy's doit.
 */
export abstract class MatScalar extends ExtensionExpr {
  protected override computeCommutative(): boolean {
    return true;
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   */
  doit(hints: DoitHints = {}): Expr {
    if (hints.deep === false) return this;
    const args = this.args.map((a) => doitArg(a, hints));
    return sameList(args, this.args) ? this : this.withArgs(args);
  }
  /**
   * Evaluates the operation represented by this node.
   * @returns The resulting symbolic expression.
   */
  override doitSelf(): Expr {
    return this.doit({ deep: false });
  }
  /**
   * Arguments used by the sort key.
   * @returns The expression operands used for canonical ordering.
   * @internal
   */
  sortArgs(): readonly Expr[] {
    return this.args;
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   * @internal
   */
  strPrecedence(): number {
    return PRECEDENCE.Atom;
  }
  /**
   * Returns the binding precedence used to parenthesize LaTeX output.
   * @returns The binding precedence used to parenthesize LaTeX output.
   * @internal
   */
  latexPrecedence(): number {
    return this.strPrecedence();
  }
  /**
   * Doit, then the scalar simplification.
   * @returns The resulting symbolic expression.
   */
  override simplify(): Expr {
    const r = this.doit();
    if (r instanceof MatScalar) return r.withArgs(r.args.map(simplifyArg));
    return simplifyArg(r);
  }
  /**
   * Expands the scalar matrix expression according to the requested hints.
   * @returns The resulting symbolic expression.
   */
  override expand(): Expr {
    return this.withArgs(this.args.map(expandArg));
  }
}

function simplifyArg(a: Expr): Expr {
  if (a instanceof MatrixExpr || a instanceof MatScalar) return a.simplify();
  if (hasMatrix(a) || a instanceof ExtensionExpr) return a;
  return simplifyScalar(a);
}

function expandArg(a: Expr): Expr {
  if (a instanceof MatrixExpr || a instanceof MatScalar) return a.expand();
  if (hasMatrix(a)) return a;
  return a.expand();
}

/** -M (SymPy MatMul(-1, M).doit()); scalars are negated. */
export function negate(e: Expr): Expr {
  if (e instanceof MatrixExpr) return matMul(S.NegOne, e);
  return mul(-1, e);
}

/** A scalar or matrix derivative helper: zero matrices for matrix arguments free of x. */
function mdiff(e: Expr, x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
  if (e instanceof MatrixExpr && !e.has(x)) return new ZeroMatrixNode(e.rows, e.cols);
  return d(e, x);
}

// ---------------------------------------------------------------------------
// MatrixSymbol
// ---------------------------------------------------------------------------

/**
 * A symbolic n x m matrix.
 * @see SymPy `sympy.matrices.expressions.matexpr.MatrixSymbol`
 */
export class MatrixSymbolNode extends MatrixExpr {
  /**
   * Constructs a `MatrixSymbol`.
   * @param symbolName - The name of the matrix symbol.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @param extra - Additional operands of the matrix symbol.
   */
  constructor(symbolName: string, rows: ExprLike, cols: ExprLike, extra: readonly Expr[] = []) {
    super('MatrixSymbol', [new Str(symbolName), dim(rows), dim(cols), ...extra]);
  }
  /**
   * Collects this matrix symbol as a free variable.
   * @returns A singleton set containing this matrix symbol.
   */
  override freeSymbolsSelf(): ReadonlySet<Expr> { return new Set([this]); }
  /**
   * Gets the name of the matrix.
   * @returns The name of the matrix.
   */
  get symbolName(): string {
    return cast(this.args[0], Str).value;
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixSymbol.shape`
   */
  get shape(): [Expr, Expr] {
    return [at(this.args, 1), at(this.args, 2)];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSymbolNode(cast(args[0], Str).value, at(args, 1), at(args, 2));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixSymbol._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    return new MatrixElementNode(this, i, j);
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return this.symbolName;
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return latexMatrixSymbol(this.symbolName);
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(): Expr {
    return new ZeroMatrixNode(this.rows, this.cols);
  }
  /**
   * The symbol itself (its dimensions stay integers).
   * @returns The resulting symbolic expression.
   */
  override evalfSelf(): Expr {
    return this;
  }
}

// ---------------------------------------------------------------------------
// Explicit matrices
// ---------------------------------------------------------------------------

/** Printed form of an explicit matrix (SymPy str: Matrix([[...], ...]) on one line). */
export function explicitStr(m: Matrix, print: (e: Expr) => string = str): string {
  if (m.rows === 0 || m.cols === 0) return `Matrix(${m.rows}, ${m.cols}, [])`;
  return `Matrix([${m
    .toArray()
    .map((r) => `[${r.map(print).join(', ')}]`)
    .join(', ')}])`;
}

/** The contents of an explicit matrix in LaTeX (SymPy _print_matrix_contents). */
export function explicitLatexContents(m: Matrix, print: (e: Expr) => string = latex): string {
  const lines = m.toArray().map((r) => r.map(print).join(' & '));
  const env = m.cols <= 10 ? 'matrix' : 'array';
  const spec = env === 'array' ? `{${'c'.repeat(m.cols)}}` : '';
  return `\\begin{${env}}${spec}${lines.join('\\\\')}\\end{${env}}`;
}

/**
 * An explicit matrix inside matrix expressions.
 * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix`
 */
export class ImmutableMatrixNode extends MatrixExpr {
  /**
   * Gets the priority for choosing the result class in mixed matrix operations.
   * @returns The priority for choosing the result class in mixed matrix operations.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._class_priority`
   */
  get classPriority(): number { return 8; }
  /**
   * Constructs an `ImmutableMatrix`.
   * @param matrix - The matrix whose entries are used.
   */
  constructor(
    /** The explicit matrix. */
    readonly matrix: Matrix) {
    super('ImmutableDenseMatrix', matrix.data);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    return [Rational.of(this.matrix.rows), Rational.of(this.matrix.cols)];
  }
  /**
   * Indicates whether the object represents a matrix expression.
   * @returns Whether the matrix is matrix expr.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.is_MatrixExpr`
   */
  override get isMatrixExpr(): boolean {
    return false;
  }
  /**
   * Tests whether the matrix is the identity.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.is_Identity`
   */
  override get isIdentity(): Truth {
    const m = this.matrix;
    if (m.rows !== m.cols) return false;
    for (let i = 0; i < m.rows; i++) for (let j = 0; j < m.cols; j++) if (!same(m.get(i, j), i === j ? S.One : S.Zero)) return false;
    return true;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    const { rows, cols } = this.matrix;
    return new ImmutableMatrixNode(Matrix.fromFunction(rows, cols, (i, j) => at(args, i * cols + j)));
  }
  protected override computeKey(): string {
    return `ImmutableDenseMatrix(${this.matrix.rows},${this.matrix.cols};${this.args.map((a) => a.key).join(',')})`;
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    if (isInt(i) && isInt(j)) {
      const r = toInt(i) < 0 ? toInt(i) + this.matrix.rows : toInt(i);
      const c = toInt(j) < 0 ? toInt(j) + this.matrix.cols : toInt(j);
      return this.matrix.get(r, c);
    }
    return new MatrixElementNode(this, i, j);
  }
  /**
   * Evaluates the entries to construct an explicit matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.as_explicit`
   */
  override asExplicit(): Matrix {
    return this.matrix;
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new ImmutableMatrixNode(this.matrix.transpose());
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return new ImmutableMatrixNode(this.matrix.transpose().map((e) => conjugateFn(e)));
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => conjugateFn(e)));
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @throws NonInvertibleMatrixError when the matrix is singular.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_inverse`
   */
  override evalInverse(): Expr {
    try {
      return new ImmutableMatrixNode(this.matrix.inv());
    } catch {
      // the matrix is square here (inverse() checks): Matrix.inv only fails for a singular one
      throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
    }
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_determinant`
   */
  override evalDeterminant(): Expr {
    return this.matrix.det();
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_trace`
   */
  override evalTrace(): Expr {
    return this.matrix.trace();
  }
  /**
   * Evaluates a power of this matrix when its structure determines the result.
   * @param exp - The exponent to apply.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix._eval_power`
   */
  override evalPower(exp: Expr): Expr {
    if (isInt(exp)) {
      const n = toInt(exp);
      return new ImmutableMatrixNode(n >= 0 ? this.matrix.pow(n) : this.matrix.inv().pow(-n));
    }
    const p = explicitPower(this.matrix, exp);
    return p === undefined ? new MatPowNode(this, exp) : new ImmutableMatrixNode(p);
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    if (hints.deep === false) return this;
    return new ImmutableMatrixNode(this.matrix.map((e) => doitArg(e, hints)));
  }
  /**
   * Apply simplify to each element of the matrix.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.simplify`
   */
  override simplify(): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => simplifyArg(e)));
  }
  /**
   * Apply core.function.expand to each entry of the matrix.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix.expand`
   */
  override expand(): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => expandArg(e)));
  }
  /**
   * Formats the expression as plain text.
   * @param print - Formats a child expression.
   * @returns The plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    return explicitStr(this.matrix, print);
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\left[${explicitLatexContents(this.matrix, print)}\\right]`;
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => d(e, x)));
  }
}

/** Explicit matrix product, sum or scaling used by the merge rules. */
function explicitOf(e: Expr): Matrix {
  return cast(e, ImmutableMatrixNode).matrix;
}

// ---------------------------------------------------------------------------
// MatrixElement
// ---------------------------------------------------------------------------

/**
 * The entry M[i, j] of a matrix expression.
 * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement`
 */
export class MatrixElementNode extends MatScalar {
  /**
   * Constructs a `MatrixElement`.
   * @param parent - The object containing the selected element.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   */
  constructor(parent: Expr, i: Expr, j: Expr) {
    super('MatrixElement', [parent, i, j]);
  }
  /**
   * Gets the matrix.
   * @returns The matrix.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement.parent`
   */
  get parent(): Expr {
    return at(this.args, 0);
  }
  /**
   * Gets the matrix owning this entry.
   * @returns The matrix owning this entry.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement.symbol`
   */
  get symbol(): Expr {
    return this.parent;
  }
  /**
   * Gets the row index.
   * @returns The row index.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement.i`
   */
  get i(): Expr {
    return at(this.args, 1);
  }
  /**
   * Gets the column index.
   * @returns The column index.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement.j`
   */
  get j(): Expr {
    return at(this.args, 2);
  }
  /**
   * Identifies the position of this matrix entry.
   * @returns The row and column indices.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement.indices`
   */
  get indices(): [Expr, Expr] {
    return [this.i, this.j];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return matrixElement(at(args, 0), at(args, 1), at(args, 2));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const evaluate = (a: Expr): Expr => (hints.deep === false ? a : doitArg(a, hints));
    const parent = at(this.args, 0);
    const p = parent instanceof MatrixExpr ? evaluate(parent) : explicitMatrixValue(parent, evaluate);
    if (p instanceof MatrixExpr) return p.at(evaluate(at(this.args, 1)), evaluate(at(this.args, 2)));
    return this;
  }
  /**
   * Evalf: the entry of the evaluated matrix ((M**5)[1, 2] of an explicit M is a number); undefined when it stays an element.
   * @returns The evaluated scalar entry when the indices and matrix are explicit.
   */
  override numericValue(): Expr | undefined {
    const v = this.doit();
    return v instanceof MatrixElementNode ? undefined : v;
  }
  /**
   * Formats the expression as plain text.
   * @param print - Formats a child expression.
   * @returns The plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    return `${parenStr(this.parent, PRECEDENCE.Atom, true)}[${print(this.i)}, ${print(this.j)}]`;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `{${parenLatex(this.parent, PRECEDENCE.Atom, true)}}_{${print(this.i)},${print(this.j)}}`;
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param v - The variable of differentiation.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(v: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if (v instanceof MatrixElementNode) {
      if (same(v.parent, this.parent)) {
        const matrix = this.parent;
        const delta = (a: Expr, b: Expr, axis: 0 | 1): Expr => KroneckerDelta(a, b,
          matrix instanceof MatrixExpr ? [S.Zero, add(matrix.shape[axis], -1)] : undefined);
        return mul(delta(this.i, v.i, 0), delta(this.j, v.j, 1));
      }
      if (!this.parent.has(v.parent)) return S.Zero;
      return undefined;
    }
    const p = this.parent;
    if (p instanceof MatrixExpr) {
      const dp = mdiff(p, v, d);
      if (dp instanceof MatrixExpr) return dp.at(this.i, this.j);
    }
    return undefined;
  }
}

/**
 * An explicit parent with integer indices gives the entry.
 * @param parentIn - The object containing the selected element.
 * @param iIn - The zero-based row index.
 * @param jIn - The zero-based column index.
 * @returns The resulting symbolic expression.
 * @throws TypeError when a matrix operand is required.
 * @throws RangeError when an index is out of bounds.
 * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement`
 */
export function matrixElement(parentIn: MatArg, iIn: ExprLike, jIn: ExprLike): Expr {
  const parent = toExpr(parentIn);
  const i = sympify(iIn);
  const j = sympify(jIn);
  if (parent instanceof ImmutableMatrixNode && isInt(i) && isInt(j)) return parent.entry(i, j);
  // a scalar product or function of a matrix has matrix kind in SymPy (sqrt(2)*exp(M) for a 1x1 M)
  if (!(parent instanceof MatrixExpr) && hasMatrixKind(parent)) return new MatrixElementNode(parent, i, j);
  if (!(parent instanceof MatrixExpr)) throw new TypeError('First argument of MatrixElement should be a matrix');
  if (!parent.validIndex(i, j)) throw new RangeError('indices out of range');
  return new MatrixElementNode(parent, i, j);
}

/** A core product or power with a matrix among its arguments (SymPy MatrixKind of such a node). */
function hasMatrixKind(e: Expr): boolean {
  return (e instanceof Mul || e instanceof Pow) && e.args.some((a) => a instanceof MatrixExpr || hasMatrixKind(a));
}

/**
 * The explicit matrix of a core product of scalars with one explicit matrix, with exp of an explicit matrix as
 * its matrix exponential (SymPy exp.eval and Mul of a Matrix); other expressions are returned unchanged.
 */
function explicitMatrixValue(e: Expr, evaluate: (a: Expr) => Expr): Expr {
  if (e instanceof MatrixExpr) return evaluate(e);
  if (e instanceof Pow && same(e.base, S.E)) {
    const argument = explicitMatrixValue(e.exp, evaluate);
    return argument instanceof ImmutableMatrixNode ? new ImmutableMatrixNode(matrixExp(argument.matrix)) : e;
  }
  if (!(e instanceof Mul)) return e;
  const factors = e.args.map((f) => (hasMatrixKind(f) || f instanceof MatrixExpr ? explicitMatrixValue(f, evaluate) : evaluate(f)));
  const matrices = factors.filter((f): f is ImmutableMatrixNode => f instanceof ImmutableMatrixNode);
  if (matrices.length !== 1 || factors.some((f) => (f instanceof MatrixExpr || hasMatrixKind(f)) && !(f instanceof ImmutableMatrixNode))) return e;
  return new ImmutableMatrixNode(at(matrices, 0).matrix.scale(mul(...factors.filter((f) => !(f instanceof ImmutableMatrixNode)))));
}

// ---------------------------------------------------------------------------
// Special matrices
// ---------------------------------------------------------------------------

/**
 * The n x n identity matrix, printed I.
 * @see SymPy `sympy.matrices.expressions.special.Identity`
 */
export class IdentityNode extends MatrixExpr {
  /**
   * Constructs an `Identity`.
   * @param n - The order of the identity matrix.
   */
  constructor(n: ExprLike) {
    super('Identity', [dim(n)]);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.special.Identity.shape`
   */
  get shape(): [Expr, Expr] {
    return [at(this.args, 0), at(this.args, 0)];
  }
  /**
   * Tests whether the row and column counts agree.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.expressions.special.Identity.is_square`
   */
  override get isSquare(): Truth {
    return true;
  }
  /**
   * Tests whether the matrix is the identity.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.expressions.special.Identity.is_Identity`
   */
  override get isIdentity(): Truth {
    return true;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new IdentityNode(at(args, 0));
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_transpose`
   */
  override evalTranspose(): Expr {
    return this;
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_trace`
   */
  override evalTrace(): Expr {
    return this.rows;
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_inverse`
   */
  override evalInverse(): Expr {
    return this;
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return this;
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return this;
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_determinant`
   */
  override evalDeterminant(): Expr {
    return S.One;
  }
  /**
   * Evaluates a power of this matrix when its structure determines the result.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.special.Identity._eval_power`
   */
  override evalPower(): Expr {
    return this;
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.special.Identity._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    const t = relTruth('Eq', i, j);
    if (t === true) return S.One;
    if (t === false) return S.Zero;
    return KroneckerDelta(i, j);
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return 'I';
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return latexSettings().bold ? '\\mathbf{I}' : '\\mathbb{I}';
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(): Expr {
    return new ZeroMatrixNode(this.rows, this.cols);
  }
}

/**
 * The identity of unspecified size (the empty MatMul).
 * @see SymPy `sympy.matrices.expressions.special.GenericIdentity`
 */
export class GenericIdentityNode extends IdentityNode {
  /** Constructs a `GenericIdentity`. */
  constructor() {
    super(0);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @throws TypeError when the shape of a dimensionless matrix is requested.
   * @see SymPy `sympy.matrices.expressions.special.GenericIdentity.shape`
   */
  override get shape(): [Expr, Expr] {
    throw new TypeError('GenericIdentity does not have a specified shape');
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @returns The expression with the given operands.
   */
  override withArgs(): Expr {
    return this;
  }
  protected override computeKey(): string {
    return 'GenericIdentity()';
  }
}

/**
 * The zero matrix, printed 0.
 * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix`
 */
export class ZeroMatrixNode extends MatrixExpr {
  /**
   * Constructs a `ZeroMatrix`.
   * @param m - The number of rows.
   * @param n - The order of the identity matrix.
   */
  constructor(m: ExprLike, n: ExprLike) {
    super('ZeroMatrix', [dim(m), dim(n)]);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    return [at(this.args, 0), at(this.args, 1)];
  }
  /**
   * Tests whether all matrix entries are zero.
   * @returns Whether the matrix is zero matrix.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix.is_ZeroMatrix`
   */
  override get isZeroMatrix(): boolean {
    return true;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new ZeroMatrixNode(at(args, 0), at(args, 1));
  }
  /**
   * Evaluates a power of this matrix when its structure determines the result.
   * @param exp - The exponent to apply.
   * @returns The resulting symbolic expression.
   * @throws NonInvertibleMatrixError when the matrix is singular.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_power`
   */
  override evalPower(exp: Expr): Expr {
    if (relTruth('Lt', exp, S.Zero) === true) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible');
    return this;
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new ZeroMatrixNode(this.cols, this.rows);
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return new ZeroMatrixNode(this.cols, this.rows);
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_trace`
   */
  override evalTrace(): Expr {
    return S.Zero;
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_determinant`
   */
  override evalDeterminant(): Expr {
    return S.Zero;
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @throws NonInvertibleMatrixError when the matrix is singular.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_inverse`
   */
  override evalInverse(): Expr {
    throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return this;
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix._entry`
   */
  override entry(): Expr {
    return S.Zero;
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return '0';
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return latexSettings().bold ? '\\mathbf{0}' : '0';
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(): Expr {
    return this;
  }
}

/**
 * The zero matrix of unspecified size (the empty MatAdd).
 * @see SymPy `sympy.matrices.expressions.special.GenericZeroMatrix`
 */
export class GenericZeroMatrixNode extends ZeroMatrixNode {
  /** Constructs a `GenericZeroMatrix`. */
  constructor() {
    super(0, 0);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @throws TypeError when the shape of a dimensionless matrix is requested.
   * @see SymPy `sympy.matrices.expressions.special.GenericZeroMatrix.shape`
   */
  override get shape(): [Expr, Expr] {
    throw new TypeError('GenericZeroMatrix does not have a specified shape');
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @returns The expression with the given operands.
   */
  override withArgs(): Expr {
    return this;
  }
  protected override computeKey(): string {
    return 'GenericZeroMatrix()';
  }
}

/**
 * The matrix of ones, printed 1.
 * @see SymPy `sympy.matrices.expressions.special.OneMatrix`
 */
export class OneMatrixNode extends MatrixExpr {
  /**
   * Constructs an `OneMatrix`.
   * @param m - The number of rows.
   * @param n - The order of the identity matrix.
   */
  constructor(m: ExprLike, n: ExprLike) {
    super('OneMatrix', [dim(m), dim(n)]);
  }
  /**
   * Constructs the one matrix expression from its operands.
   * @param m - The number of rows.
   * @param n - The order of the identity matrix.
   * @param evaluate - Whether to evaluate the expression immediately.
   * @returns The one matrix expression from its operands.
   */
  static create(m: ExprLike, n: ExprLike, evaluate = false): MatrixExpr {
    const o = new OneMatrixNode(m, n);
    if (evaluate && o.is1x1() === true) return new IdentityNode(1);
    return o;
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    return [at(this.args, 0), at(this.args, 1)];
  }
  /**
   * True when the matrix is known to be 1 x 1.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._is_1x1`
   */
  is1x1(): Truth {
    const a = relTruth('Eq', at(this.args, 0), S.One);
    const b = relTruth('Eq', at(this.args, 1), S.One);
    if (a === false || b === false) return false;
    return a === true && b === true ? true : 'unknown';
  }
  /**
   * Tests whether the matrix is the identity.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix.is_Identity`
   */
  override get isIdentity(): Truth {
    return this.is1x1() === true;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new OneMatrixNode(at(args, 0), at(args, 1));
  }
  /**
   * Evaluates the entries to construct an explicit matrix.
   * @returns The resulting matrix.
   * @throws RangeError when the dimensions are symbolic.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix.as_explicit`
   */
  override asExplicit(): Matrix {
    const [r, c] = this.shape;
    if (!isInt(r) || !isInt(c)) throw new RangeError('Matrix with symbolic shape cannot be represented explicitly.');
    return Matrix.fromFunction(toInt(r), toInt(c), () => 1);
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return OneMatrixNode.create(at(args, 0), at(args, 1), true);
  }
  /**
   * Evaluates a power of this matrix when its structure determines the result.
   * @param exp - The exponent to apply.
   * @returns The resulting symbolic expression.
   * @throws NonInvertibleMatrixError when the matrix is singular.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_power`
   */
  override evalPower(exp: Expr): Expr {
    if (this.is1x1() === true) return new IdentityNode(1);
    if (relTruth('Lt', exp, S.Zero) === true) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible');
    if (isIntegerQ(exp) === true) return matMul(pow(this.rows, add(exp, -1)), new OneMatrixNode(this.rows, this.cols));
    return new MatPowNode(this, exp);
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new OneMatrixNode(this.cols, this.rows);
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return new OneMatrixNode(this.cols, this.rows);
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_trace`
   */
  override evalTrace(): Expr {
    return this.rows;
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_determinant`
   */
  override evalDeterminant(): Expr {
    const c = this.is1x1();
    if (c === true) return S.One;
    if (c === false) return S.Zero;
    return new DeterminantNode(this);
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @throws NonInvertibleMatrixError when the matrix is singular.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_inverse`
   */
  override evalInverse(): Expr {
    const c = this.is1x1();
    if (c === true) return new IdentityNode(1);
    if (c === false) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
    return new InverseNode(this);
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return this;
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.special.OneMatrix._entry`
   */
  override entry(): Expr {
    return S.One;
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return '1';
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return latexSettings().bold ? '\\mathbf{1}' : '1';
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(): Expr {
    return new ZeroMatrixNode(this.rows, this.cols);
  }
}

// ---------------------------------------------------------------------------
// Shape validation (sympy.matrices.expressions._shape)
// ---------------------------------------------------------------------------

/**
 * Integer dimensions of a sum must agree.
 * @param args - The ordered operands of the matrix expression.
 * @throws ShapeError when the matrix shapes differ.
 * @see SymPy `sympy.matrices.expressions._shape.validate_matadd_integer`
 */
export function validateMatAdd(args: readonly MatrixExpr[]): void {
  const rows = args.map((a) => a.rows);
  const cols = args.map((a) => a.cols);
  // a mismatch needs at least two dimensions, so the tuple never has one element
  const fmt = (xs: Expr[]) => `(${xs.map(str).join(', ')})`;
  if (new Set(rows.filter(isInt).map((r) => r.key)).size > 1) throw new ShapeError(`Matrices have mismatching shape: ${fmt(rows)}`);
  if (new Set(cols.filter(isInt).map((r) => r.key)).size > 1) throw new ShapeError(`Matrices have mismatching shape: ${fmt(cols)}`);
}

/**
 * Integer inner dimensions of a product must agree.
 * @param args - The ordered operands of the matrix expression.
 * @throws ShapeError when the inner dimensions do not agree.
 * @see SymPy `sympy.matrices.expressions._shape.validate_matmul_integer`
 */
export function validateMatMul(args: readonly MatrixExpr[]): void {
  for (let k = 0; k + 1 < args.length; k++) {
    const i = at(args, k).cols;
    const j = at(args, k + 1).rows;
    if (isInt(i) && isInt(j) && i.p !== j.p) throw new ShapeError(`Matrices are not aligned: ${str(i)}, ${str(j)}`);
  }
}

/**
 * The condition for the matrices to be added.
 * @param args - The ordered operands of the matrix expression.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions._shape.is_matadd_valid`
 * @example
 * ```ts
 * import { MatrixSymbol, isMataddValid, symbols } from '@symjs/symjs';
 *
 * const [m, n, p, q] = symbols('m n p q');
 * isMataddValid(MatrixSymbol('A', m, n), MatrixSymbol('B', p, q)); // => Eq(m, p) & Eq(n, q)
 * ```
 */
export function isMataddValid(...args: MatArg[]): Expr {
  const ms = args.map((a) => toMatrix(a));
  const conds: Expr[] = [];
  for (let k = 0; k + 1 < ms.length; k++) conds.push(Eq(at(ms, k).rows, at(ms, k + 1).rows));
  for (let k = 0; k + 1 < ms.length; k++) conds.push(Eq(at(ms, k).cols, at(ms, k + 1).cols));
  return and(...conds);
}

/**
 * The condition for the matrices to be multiplied.
 * @param args - The ordered operands of the matrix expression.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions._shape.is_matmul_valid`
 * @example
 * ```ts
 * import { MatrixSymbol, isMatmulValid, symbols } from '@symjs/symjs';
 *
 * const [m, n, p, q] = symbols('m n p q');
 * isMatmulValid(MatrixSymbol('A', m, n), MatrixSymbol('B', p, q)); // => Eq(n, p)
 * ```
 */
export function isMatmulValid(...args: MatArg[]): Expr {
  const ms = args.map(toExpr).filter((a): a is MatrixExpr => a instanceof MatrixExpr);
  const conds: Expr[] = [];
  for (let k = 0; k + 1 < ms.length; k++) conds.push(Eq(at(ms, k).cols, at(ms, k + 1).rows));
  return and(...conds);
}

/**
 * Tests whether the row and column counts agree.
 * @param arg - The expression to operate on.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions._shape.is_square`
 * @example
 * ```ts
 * import { MatrixSymbol, isSquare, symbols } from '@symjs/symjs';
 *
 * const [m, n] = symbols('m n');
 * isSquare(MatrixSymbol('A', m, n)); // => Eq(m, n)
 * ```
 */
export function isSquare(arg: MatArg): Expr {
  if (typeof arg === 'number' || typeof arg === 'bigint' || arg instanceof Rational) return integerIsSquare(asInt(arg)) ? S.true : S.false;
  const m = toMatrix(arg);
  return Eq(m.rows, m.cols);
}

// ---------------------------------------------------------------------------
// MatAdd
// ---------------------------------------------------------------------------

/**
 * A sum of matrix expressions.
 * @see SymPy `sympy.matrices.expressions.matadd.MatAdd`
 */
export class MatAddNode extends MatrixExpr {
  /**
   * Constructs a `MatAdd`.
   * @param args - The ordered operands of the matrix expression.
   */
  constructor(args: readonly Expr[]) {
    super('MatAdd', args);
  }
  /**
   * Gets the associative operation joining the operands.
   * @returns The associative operation joining the operands.
   */
  override get assocOp(): 'Add' {
    return 'Add';
  }
  /**
   * Constructs the mat add expression from its operands.
   * @param argsIn - The ordered operands of the matrix expression.
   * @returns The mat add expression from its operands.
   * @throws TypeError when the sum mixes matrix and scalar terms.
   */
  static create(argsIn: readonly MatArg[]): MatrixExpr {
    const args = argsIn.map(toExpr).filter((a) => !(a instanceof GenericZeroMatrixNode));
    if (!args.length) return new GenericZeroMatrixNode();
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    validateMatAdd(args);
    return new MatAddNode(args);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd.shape`
   */
  get shape(): [Expr, Expr] {
    return cast(this.args[0], MatrixExpr).shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatAddNode(args);
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return add(...this.args.map((a) => cast(a, MatrixExpr).entry(i, j, ctx)));
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd._eval_transpose`
   */
  override evalTranspose(): Expr {
    return MatAddNode.create(this.args.map(transposeOf)).doit();
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return MatAddNode.create(this.args.map((a) => adjointFn(a))).doit();
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd._eval_trace`
   */
  override evalTrace(): Expr {
    return add(...this.args.map((a) => trace(a)));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return canonicalizeMatAdd(MatAddNode.create(args));
  }
  /**
   * Expand an expression using hints.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matadd.MatAdd.expand`
   */
  override expand(): Expr {
    return canonicalizeMatAdd(MatAddNode.create(this.args.map(expandArg)));
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   */
  override strPrecedence(): number {
    return PRECEDENCE.Add;
  }
  /**
   * Formats the expression as plain text.
   * @param print - Formats a child expression.
   * @returns The plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    const parts: string[] = [];
    for (const term of orderedTerms(this.args)) {
      let t = print(term);
      let sign = '+';
      if (t.startsWith('-') && !(term instanceof MatAddNode)) {
        sign = '-';
        t = t.slice(1);
      }
      parts.push(sign, strPrecedence(term) < PRECEDENCE.Add || term instanceof MatAddNode ? `(${t})` : t);
    }
    const first = parts.shift();
    return (first === '-' ? '-' : '') + parts.join(' ');
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    let tex = '';
    orderedTerms(this.args).forEach((t0, k) => {
      let term = t0;
      if (k > 0) {
        if (mulCouldExtractMinus(term)) {
          tex += ' - ';
          term = negate(term);
        } else tex += ' + ';
      }
      const s = print(term);
      tex += term instanceof MatAddNode ? `\\left(${s}\\right)` : s;
    });
    return tex;
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return MatAddNode.create(this.args.map((a) => mdiff(a, x, d))).doit();
  }
}

/** SymPy transpose() of a matrix expression or a scalar. */
export function transposeOf(e: Expr): Expr {
  return e instanceof MatrixExpr ? e.transpose() : transposeFn(e);
}

/**
 * An unevaluated sum of matrices.
 * @param args - The ordered operands of the matrix expression.
 * @returns The resulting matrix expression.
 * @throws TypeError when the sum mixes matrix and scalar terms.
 * @see SymPy `sympy.matrices.expressions.matadd.MatAdd`
 * @example
 * ```ts
 * import { MatAdd, MatrixSymbol } from '@symjs/symjs';
 * MatAdd(MatrixSymbol('A', 5, 5), MatrixSymbol('B', 5, 5), MatrixSymbol('C', 5, 5)); // => A + B + C
 * ```
 */
export const MatAdd = /* @__PURE__ */ callableClass(MatAddNode, (...args: MatArg[]): MatrixExpr => MatAddNode.create(args));
export type MatAdd = MatAddNode;

// ---- MatAdd rules (sympy.matrices.expressions.matadd.canonicalize) ----

type Rule = (e: Expr) => Expr;

function exhaustWhile(pred: (e: Expr) => boolean, rules: readonly Rule[]): Rule {
  return (e0) => {
    let e = e0;
    for (;;) {
      if (!pred(e)) return e;
      let next = e;
      for (const rule of rules) {
        const r = rule(e);
        if (!same(r, e)) {
          next = r;
          break;
        }
      }
      if (same(next, e)) return e;
      e = next;
    }
  };
}

/** sympy.strategies rm_id over the arguments of a node, rebuilt raw. */
function rmId(e: Expr, isId: (a: Expr) => boolean, raw: (args: readonly Expr[]) => Expr): Expr {
  const ids = e.args.map(isId);
  const n = ids.filter(Boolean).length;
  if (n === 0) return e;
  if (n !== ids.length) return raw(e.args.filter((_, k) => !ids[k]));
  return raw([at(e.args, 0)]);
}

const unpackRule = (e: Expr): Expr => (e.args.length === 1 && (e instanceof MatAddNode || e instanceof MatMulNode) ? at(e.args, 0) : e);

/** SymPy unpack of a single-argument MatMul. */
export const unpackMat = (e: Expr): Expr => (e instanceof MatMulNode && e.args.length === 1 ? at(e.args, 0) : e);

const flattenAdd = (e: Expr): Expr => new MatAddNode(e.args.flatMap((a) => (a instanceof MatAddNode ? a.args : [a])));

function glomAdd(e: Expr): Expr {
  const groups = new Map<string, { mat: Expr; cnt: Expr }>();
  for (const arg of e.args) {
    const [c, mm] = cast(arg, MatrixExpr).asCoeffMmul();
    const mat = unpackMat(mm);
    const g = groups.get(mat.key);
    if (g) g.cnt = add(g.cnt, c);
    else groups.set(mat.key, { mat, cnt: c });
  }
  const newargs = [...groups.values()].map(({ mat, cnt }) => (same(cnt, S.One) ? mat : matMul(cnt, mat)));
  const a = new Set(newargs.map((x) => x.key));
  const b = new Set(e.args.map((x) => x.key));
  if (a.size === b.size && [...a].every((k) => b.has(k))) return e;
  return new MatAddNode(newargs);
}

function mergeExplicitAdd(e: Expr): Expr {
  const explicit = e.args.filter((a) => a instanceof ImmutableMatrixNode);
  if (explicit.length <= 1) return e;
  const rest = e.args.filter((a) => !(a instanceof ImmutableMatrixNode));
  const total = explicit.map(explicitOf).reduce((x, y) => x.add(y));
  return MatAddNode.create([...rest, new ImmutableMatrixNode(total)]);
}

const sortAdd = (e: Expr): Expr =>
  new MatAddNode(
    e.args
      .map((a) => ({ a, k: matSortKey(a) }))
      .sort((x, y) => compareKeys(x.k, y.k))
      .map((x) => x.a),
  );

/** SymPy matadd.canonicalize. */
export const canonicalizeMatAdd: Rule = exhaustWhile(
  (e) => e instanceof MatAddNode,
  [(e) => rmId(e, (a) => same(a, S.Zero) || (a instanceof MatrixExpr && a.isZeroMatrix), (args) => new MatAddNode(args)), unpackRule, flattenAdd, glomAdd, mergeExplicitAdd, sortAdd],
);

/**
 * Explicit matrices of a sum added together.
 * @param e - The expression to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.matadd.merge_explicit`
 * @example
 * ```ts
 * import { MatAdd, Matrix, MatrixSymbol, mergeExplicitMatAdd } from '@symjs/symjs';
 *
 * const A = MatrixSymbol('A', 2, 2);
 * mergeExplicitMatAdd(MatAdd(A, Matrix.eye(2), Matrix.eye(2))).args.length; // => 2
 * ```
 */
export function mergeExplicitMatAdd(e: Expr): Expr {
  return e instanceof MatAddNode ? mergeExplicitAdd(e) : e;
}

// ---------------------------------------------------------------------------
// MatMul
// ---------------------------------------------------------------------------

/**
 * A product of scalars and matrix expressions.
 * @see SymPy `sympy.matrices.expressions.matmul.MatMul`
 */
export class MatMulNode extends MatrixExpr {
  /**
   * Constructs a `MatMul`.
   * @param args - The ordered operands of the matrix expression.
   */
  constructor(args: readonly Expr[]) {
    super('MatMul', args);
  }
  /**
   * Gets the associative operation joining the operands.
   * @returns The associative operation joining the operands.
   */
  override get assocOp(): 'Mul' {
    return 'Mul';
  }
  /**
   * Constructs the mat mul expression from its operands.
   * @param argsIn - The ordered operands of the matrix expression.
   * @returns The mat mul expression from its operands.
   */
  static create(argsIn: readonly MatArg[]): Expr {
    const args = argsIn.map(toExpr).filter((a) => !(a instanceof GenericIdentityNode));
    if (!args.length) return new GenericIdentityNode();
    const obj = new MatMulNode(args);
    const [factor, matrices] = obj.asCoeffMatrices();
    validateMatMul(matrices);
    if (!matrices.length) return factor;
    return obj;
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul.shape`
   */
  get shape(): [Expr, Expr] {
    const ms = this.args.filter((a): a is MatrixExpr => a instanceof MatrixExpr);
    return [at(ms, 0).rows, last(ms).cols];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatMulNode(args);
  }
  /**
   * Simplifies the expression and its operands.
   * @param simplify - The simplifier to apply to subexpressions.
   * @returns The resulting symbolic expression.
   */
  override simplifySelf(simplify: (e: Expr) => Expr): Expr {
    return this.withArgs(this.args.map((a) => a instanceof MatrixExpr ? a.simplify() : simplify(a)));
  }
  /**
   * Returns the scalar factor and the matrices.
   * @returns The scalar factor and the matrices.
   * @throws NotImplementedError when a scalar factor is noncommutative.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul.as_coeff_matrices`
   */
  asCoeffMatrices(): [Expr, MatrixExpr[]] {
    const scalars = this.args.filter((a) => !(a instanceof MatrixExpr));
    const matrices = this.args.filter((a): a is MatrixExpr => a instanceof MatrixExpr);
    const coeff = mul(...scalars);
    if (!coeff.isCommutative) throw new NotImplementedError('noncommutative scalars in MatMul are not supported.');
    return [coeff, matrices];
  }
  /**
   * Separates the scalar coefficient from the matrix product.
   * @returns The scalar coefficient followed by the matrix product.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul.as_coeff_mmul`
   */
  override asCoeffMmul(): [Expr, MatMulNode] {
    const [c, ms] = this.asCoeffMatrices();
    return [c, new MatMulNode(ms)];
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const [coeff, matrices] = this.asCoeffMatrices();
    if (matrices.length === 1) return mul(coeff, at(matrices, 0).at(i, j));
    let counter = 0;
    const gen: EntryContext = ctx ?? { dummy: () => new Dummy(`i_${++counter}`) };
    const dummies: Dummy[] = [];
    for (let k = 1; k < matrices.length; k++) dummies.push(gen.dummy());
    const indices: Expr[] = [i, ...dummies, j];
    const ranges = matrices.slice(0, -1).map((m) => add(m.cols, -1));
    const entries = matrices.map((m, k) => m.entry(at(indices, k), at(indices, k + 1), gen));
    const summand = mul(...entries);
    const limits = dummies.map((d, k): [Sym, Expr, Expr] => [d, S.Zero, at(ranges, k)]);
    const result = mul(coeff, Sum(summand, ...limits));
    const expand = ranges.some(isInt);
    return expand ? doitArg(result) : result;
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul._eval_transpose`
   */
  override evalTranspose(): Expr {
    const [coeff, matrices] = this.asCoeffMatrices();
    return matMul(coeff, ...[...matrices].reverse().map((m) => m.transpose()));
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return matMul(...[...this.args].reverse().map((a) => adjointFn(a)));
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul._eval_trace`
   */
  override evalTrace(): Expr {
    const [factor, mmul] = this.asCoeffMmul();
    if (!same(factor, S.One)) return mul(factor, trace(mmul.doit()));
    return super.evalTrace();
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul._eval_determinant`
   */
  override evalDeterminant(): Expr {
    const [factor, matrices] = this.asCoeffMatrices();
    const squares = onlySquares(matrices);
    return mul(pow(factor, this.rows), ...squares.map((m) => new DeterminantNode(m)));
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul._eval_inverse`
   */
  override evalInverse(): Expr {
    if (this.args.every((a) => !(a instanceof MatrixExpr) || a.isSquare === true)) {
      return matMul(...[...this.args].reverse().map((a) => (a instanceof MatrixExpr ? a.inverse() : pow(a, -1))));
    }
    return new InverseNode(this);
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return canonicalizeMatMul(MatMulNode.create(args));
  }
  /**
   * Expand an expression using hints.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matmul.MatMul.expand`
   */
  override expand(): Expr {
    const factors = this.args.map(expandArg);
    let products: Expr[][] = [[]];
    for (const f of factors) {
      const terms = f instanceof MatAddNode ? f.args : [f];
      products = products.flatMap((p) => terms.map((t) => [...p, t]));
    }
    if (products.length === 1) return mul(...at(products, 0));
    return MatAddNode.create(products.map((p) => mul(...p))).doit();
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   */
  override strPrecedence(): number {
    return mulCouldExtractMinus(this) ? PRECEDENCE.Add : PRECEDENCE.Mul;
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    const [c, matrices] = this.asCoeffMatrices();
    let args: readonly Expr[] = this.args;
    let sign = '';
    let level = this.strPrecedence();
    if (freeSymbols(c).size === 0 && !hasMatrix(c)) {
      let v: { re: number; im: number } | undefined;
      try {
        v = c.toComplex();
      } catch {
        v = undefined;
      }
      if (v && ((v.im === 0 && v.re < 0) || (v.re === 0 && v.im < 0))) {
        sign = '-';
        const nc = mul(-1, c);
        args = same(nc, S.One) ? matrices : [nc, ...matrices];
        level = PRECEDENCE.Mul;
      }
    }
    return sign + args.map((a) => parenStr(a, level)).join('*');
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    const level = this.latexPrecedence();
    const parens = (x: Expr): string => (x instanceof Mul ? latex(x) : parenLatex(x, level));
    let args = [...this.args];
    if (mulCouldExtractMinus(this)) {
      if (same(at(args, 0), S.NegOne)) args = args.slice(1);
      else args[0] = mul(-1, at(args, 0));
      return `- ${args.map(parens).join(' ')}`;
    }
    return args.map(parens).join(' ');
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const terms: Expr[] = [];
    this.args.forEach((a, k) => {
      if (!a.has(x)) return;
      terms.push(matMul(...this.args.map((b, l) => (l === k ? mdiff(b, x, d) : b))));
    });
    if (!terms.length) return new ZeroMatrixNode(this.rows, this.cols);
    return MatAddNode.create(terms).doit();
  }
}

/** SymPy MatMul(*args).doit(): the evaluated product (a scalar when there is no matrix). */
function matMul(...args: MatArg[]): Expr {
  // every caller passes at least one matrix, so the product is a matrix
  return asMat(MatMulNode.create(args)).doit();
}

// Matrix equality first compares shapes. Matrices with undecidable entries
// retain an unevaluated relation, just as scalar expressions do.
const previousRelation = impl.relational?.bind(impl);
impl.relational = (op, a, b) => {
  if ((op === 'Eq' || op === 'Ne') && a instanceof MatrixExpr && b instanceof MatrixExpr
      && !(a instanceof GenericIdentityNode || b instanceof GenericIdentityNode || a instanceof GenericZeroMatrixNode || b instanceof GenericZeroMatrixNode)) {
    const dims = [Eq(a.rows, b.rows), Eq(a.cols, b.cols)];
    if (dims.includes(S.false)) return op === 'Eq' ? S.false : S.true;
    if (dims.every((d) => d === S.true) && a.isIdentity === true && b.isIdentity === true) return op === 'Eq' ? S.true : S.false;
  }
  return previousRelation?.(op, a, b);
};

// SymPy constructor postprocessors route matrix arithmetic to the matrix expression classes.
registerArithmetic((op, args) => {
  if (!args.some((a) => a instanceof MatrixExpr)) return undefined;
  switch (op) {
    case 'add':
      if (args.every((a) => a instanceof MatrixExpr)) return MatAddNode.create(args).doit();
      {
        const scalar = add(...args.filter((a) => !(a instanceof MatrixExpr)));
        const matrix = MatAddNode.create(args.filter((a) => a instanceof MatrixExpr)).doit();
        return same(scalar, S.Zero) ? matrix : new Add([scalar, matrix]);
      }
    case 'sub': {
      const [a, b] = [at(args, 0), at(args, 1)];
      return a instanceof MatrixExpr && b instanceof MatrixExpr ? a.sub(b) : undefined;
    }
    case 'mul': {
      // Mul's constructor postprocessor multiplies scalars into an explicit
      // matrix. MatMul's own merge rule only absorbs adjacent numbers.
      const factors = args.flatMap((a) => a instanceof MatMulNode ? a.args : [a]);
      const firstExplicit = factors.findIndex((a) => a instanceof ImmutableMatrixNode);
      if (firstExplicit < 0) return matMul(...args);
      const coefficient = mul(...factors.filter((a) => !(a instanceof MatrixExpr)));
      if (coefficient !== S.One) factors[firstExplicit] = mulExplicit(coefficient, at(factors, firstExplicit));
      return matMul(...factors.filter((a) => a instanceof MatrixExpr));
    }
    case 'pow': {
      const b = at(args, 0);
      return b instanceof MatrixExpr ? b.pow(at(args, 1)) : undefined;
    }
  }
});

// SymPy MatAdd.fromiter(args) and MatMul.fromiter(args): the unevaluated constructors
registerFromiter(MatAddNode, (args) => MatAddNode.create(args));
registerFromiter(MatMulNode, (args) => MatMulNode.create(args));

/**
 * An unevaluated product of scalars and matrices.
 * @param args - The ordered operands of the matrix expression.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.matmul.MatMul`
 * @example
 * ```ts
 * import { Identity, MatMul, MatrixSymbol } from '@symjs/symjs';
 * MatMul(2, MatrixSymbol('A', 3, 4), MatrixSymbol('B', 4, 3)).add(Identity(3)); // => I + 2*A*B
 * ```
 */
export const MatMul = /* @__PURE__ */ callableClass(MatMulNode, (...args: MatArg[]): Expr => MatMulNode.create(args));
export type MatMul = MatMulNode;

/**
 * Consecutive matrices grouped into square products.
 * @param matrices - The matrix operands in order.
 * @returns The resulting expressions in order.
 * @throws MatrixError when the inner dimensions do not agree.
 * @see SymPy `sympy.matrices.expressions.matmul.only_squares`
 */
export function onlySquares(matrices: readonly MatrixExpr[]): Expr[] {
  if (!same(at(matrices, 0).rows, last(matrices).cols)) throw new MatrixError('Invalid matrices being multiplied');
  const out: Expr[] = [];
  let start = 0;
  matrices.forEach((m, i) => {
    if (same(m.cols, at(matrices, start).rows)) {
      out.push(matMul(...matrices.slice(start, i + 1)));
      start = i + 1;
    }
  });
  return out;
}

// ---- MatMul rules (sympy.matrices.expressions.matmul.canonicalize) ----

function newmul(args: readonly Expr[]): Expr {
  return new MatMulNode(args.length && same(at(args, 0), S.One) ? args.slice(1) : args);
}

function distributeMonom(e: Expr): Expr {
  const [a, b] = e.args;
  if (e.args.length === 2 && a && b) {
    const rat = (x: Expr) => x instanceof Rational;
    if (a instanceof MatAddNode && rat(b)) return MatAddNode.create(a.args.map((m) => matMul(m, b)));
    if (b instanceof MatAddNode && rat(a)) return MatAddNode.create(b.args.map((m) => matMul(a, m)));
  }
  return e;
}

/**
 * A zero matrix absorbs the product.
 * @param e - The expression to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.matmul.any_zeros`
 */
export function anyZeros(e: Expr): Expr {
  if (e.args.some((a) => (a instanceof MatrixExpr ? a.isZeroMatrix : isZero(a) === true))) {
    const ms = e.args.filter((a): a is MatrixExpr => a instanceof MatrixExpr);
    return new ZeroMatrixNode(at(ms, 0).rows, last(ms).cols);
  }
  return e;
}

/**
 * Remove identity factors in one rewrite step.
 * @param e - The expression to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.matmul.remove_ids`
 */
export function removeIds(e: Expr): Expr {
  const [factor, mmul] = cast(e, MatMulNode).asCoeffMmul();
  const result = rmId(mmul, (a) => a instanceof MatrixExpr && a.isIdentity === true, (args) => new MatMulNode(args));
  if (!same(result, mmul)) return newmul([factor, ...result.args]);
  return e;
}

function combineOneMatrices(e: Expr): Expr {
  const [f0, args] = cast(e, MatMulNode).asCoeffMatrices();
  let factor = f0;
  const newArgs: Expr[] = [at(args, 0)];
  for (const B of args.slice(1)) {
    const A = last(newArgs);
    if (!(A instanceof OneMatrixNode) || !(B instanceof OneMatrixNode)) {
      newArgs.push(B);
      continue;
    }
    newArgs.pop();
    newArgs.push(new OneMatrixNode(A.rows, B.cols));
    factor = mul(factor, A.cols);
  }
  return newmul([factor, ...newArgs]);
}

/**
 * Combine adjacent powers and inverse products.
 * @param e - The expression to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.matmul.combine_powers`
 */
export function combinePowers(e: Expr): Expr {
  const [factor, args0] = cast(e, MatMulNode).asCoeffMatrices();
  const args: MatrixExpr[] = [...args0];
  let newArgs: MatrixExpr[] = [at(args, 0)];
  for (let i = 1; i < args.length; i++) {
    const A = last(newArgs);
    const B = at(args, i);
    if (B instanceof InverseNode && B.arg instanceof MatMulNode) {
      const bargs = B.arg.args;
      const l = bargs.length;
      if (l <= newArgs.length && sameList(bargs, newArgs.slice(-l))) {
        newArgs = [...newArgs.slice(0, newArgs.length - l), new IdentityNode(B.rows)];
        continue;
      }
    }
    if (A instanceof InverseNode && A.arg instanceof MatMulNode) {
      const aargs = A.arg.args;
      const l = aargs.length;
      if (sameList(aargs, args.slice(i, i + l))) {
        const identity = new IdentityNode(A.rows);
        newArgs[newArgs.length - 1] = identity;
        for (let j = i; j < i + l; j++) args[j] = identity;
        continue;
      }
    }
    if (A.isSquare === false || B.isSquare === false) {
      newArgs.push(B);
      continue;
    }
    const [aBase, aExp] = A instanceof MatPowNode ? [A.base, A.exp] : [A, S.One];
    const [bBase, bExp] = B instanceof MatPowNode ? [B.base, B.exp] : [B, S.One];
    if (same(aBase, bBase)) {
      newArgs[newArgs.length - 1] = asMat(MatPowNode.create(aBase, add(aExp, bExp)).doit({ deep: false }));
      continue;
    } else if (!(bBase instanceof ImmutableMatrixNode) && bBase instanceof MatrixExpr) {
      let inv: Expr | undefined;
      try {
        inv = bBase.inverse();
      } catch (err) {
        // the base is square (or of unknown shape), so only a singular matrix has no inverse
        cast(err, NonInvertibleMatrixError, 'error of inverse()');
        inv = undefined;
      }
      if (inv !== undefined && same(aBase, inv)) {
        newArgs[newArgs.length - 1] = asMat(MatPowNode.create(aBase, add(aExp, mul(-1, bExp))).doit({ deep: false }));
        continue;
      }
    }
    newArgs.push(B);
  }
  return newmul([factor, ...newArgs]);
}

const asMat = (e: Expr): MatrixExpr => cast(e, MatrixExpr);

function mulExplicit(a: Expr, b: Expr): Expr {
  if (a instanceof ImmutableMatrixNode && b instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(a.matrix.mul(b.matrix));
  if (a instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(a.matrix.scale(b));
  if (b instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(b.matrix.scale(a));
  return mul(a, b);
}

function mergeExplicitMul(e: Expr): Expr {
  if (!e.args.some((a) => a instanceof ImmutableMatrixNode)) return e;
  const ok = (x: Expr) => x instanceof ImmutableMatrixNode || isNumber(x);
  const newArgs: Expr[] = [];
  let cur = at(e.args, 0);
  for (const arg of e.args.slice(1)) {
    if (ok(arg) && ok(cur)) cur = mulExplicit(cur, arg);
    else {
      newArgs.push(cur);
      cur = arg;
    }
  }
  newArgs.push(cur);
  return MatMulNode.create(newArgs);
}

/**
 * Collect commutative factors before the matrices.
 * @param e - The expression to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.matmul.factor_in_front`
 */
export function factorInFront(e: Expr): Expr {
  const [factor, matrices] = cast(e, MatMulNode).asCoeffMatrices();
  if (!same(factor, S.One)) return newmul([factor, ...matrices]);
  return e;
}

const flattenMul = (e: Expr): Expr => new MatMulNode(e.args.flatMap((a) => (a instanceof MatMulNode ? a.args : [a])));

/** A matrix that composes with its right neighbour in a product (PermutationMatrix). */
interface Composable {
  composeWith(other: MatrixExpr): Expr;
}
const isComposable = (e: Expr): e is MatrixExpr & Composable => e instanceof MatrixExpr && e.name === 'PermutationMatrix';

function combinePermutations(e: Expr): Expr {
  const args = e.args;
  const result: Expr[] = [at(args, 0)];
  for (const B of args.slice(1)) {
    const A = last(result);
    if (isComposable(A) && isComposable(B)) result[result.length - 1] = A.composeWith(B);
    else result.push(B);
  }
  return MatMulNode.create(result);
}

/** SymPy matmul.canonicalize. */
export const canonicalizeMatMul: Rule = exhaustWhile(
  (e) => e instanceof MatMulNode,
  // SymPy's rm_id(lambda x: x == 1) is omitted: combineOneMatrices already drops the unit factor
  [distributeMonom, anyZeros, removeIds, combineOneMatrices, combinePowers, unpackRule, mergeExplicitMul, factorInFront, flattenMul, combinePermutations],
);

/**
 * Adjacent explicit matrices (and numbers) of a product multiplied.
 * @param e - The expression to examine.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.matmul.merge_explicit`
 * @example
 * ```ts
 * import { MatMul, Matrix, MatrixSymbol, mergeExplicitMatMul } from '@symjs/symjs';
 *
 * const A = MatrixSymbol('A', 2, 2);
 * mergeExplicitMatMul(MatMul(A, Matrix.eye(2), Matrix.eye(2))).args.length; // => 2
 * ```
 */
export function mergeExplicitMatMul(e: Expr): Expr {
  return e instanceof MatMulNode ? mergeExplicitMul(e) : e;
}

// ---------------------------------------------------------------------------
// MatPow and Inverse
// ---------------------------------------------------------------------------

/** SymPy MatPow(base, exp): a power of a square matrix. */
/** SymPy Matrix.pow of an explicit matrix to a non-integer power: entrywise for a diagonal matrix, else undefined (a MatPow). */
function explicitPower(m: Matrix, exp: Expr): Matrix | undefined {
  return m.isDiagonal() ? m.pow(exp) : undefined;
}

/**
 * Represents a symbolic power of a square matrix.
 * @see SymPy `sympy.matrices.expressions.matpow.MatPow`
 */
export class MatPowNode extends MatrixExpr {
  /**
   * Constructs a `MatPow`.
   * @param base - The base of the power.
   * @param exp - The exponent to apply.
   * @param name - The name used to identify the object.
   */
  constructor(base: Expr, exp: Expr, name = 'MatPow') {
    super(name, [base, exp]);
  }
  /**
   * Constructs the mat pow expression from its operands.
   * @param baseIn - The base of the power.
   * @param expIn - The exponent to apply.
   * @returns The mat pow expression from its operands.
   * @throws TypeError when a matrix operand is required.
   * @throws NonSquareMatrixError when the matrix is not square.
   */
  static create(baseIn: MatArg, expIn: ExprLike): MatPowNode {
    const base = toExpr(baseIn);
    if (!(base instanceof MatrixExpr)) throw new TypeError('MatPow base should be a matrix');
    if (base.isSquare === false) throw new NonSquareMatrixError(`Power of non-square matrix ${str(base)}`);
    return new MatPowNode(base, sympify(expIn));
  }
  /**
   * The base.
   * @returns The operand being raised to a power.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow.base`
   */
  get base(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * The exponent.
   * @returns The power applied to the base.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow.exp`
   */
  get exp(): Expr {
    return at(this.args, 1);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow.shape`
   */
  get shape(): [Expr, Expr] {
    return this.base.shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatPowNode(at(args, 0), at(args, 1));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    let A = this.doit();
    if (A instanceof MatPowNode) {
      const e = A.exp;
      if (isInt(e) && e.p > 0n) {
        const base = A.base;
        A = new MatMulNode(Array.from({ length: toInt(e) }, () => base));
      } else if (isInt(this.rows) && isInt(this.cols)) {
        // a positive exponent was expanded above and doit turns the exponent 0 into Identity
        const p = isInt(e) ? A.base.asExplicit().inv().pow(-toInt(e)) : A.explicitNonIntegerPower();
        return p ? new ImmutableMatrixNode(p).at(i, j) : new MatrixElementNode(this, i, j);
      } else return new MatrixElementNode(this, i, j);
    }
    return cast(A, MatrixExpr).at(i, j);
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    let base: Expr = at(this.args, 0);
    let exp: Expr = at(this.args, 1);
    if (hints.deep !== false) {
      base = doitArg(base, hints);
      exp = doitArg(exp, hints);
    }
    while (base instanceof MatPowNode) {
      exp = mul(exp, at(base.args, 1));
      base = at(base.args, 0);
    }
    const b = cast(base, MatrixExpr);
    if (b instanceof ImmutableMatrixNode) return b.evalPower(exp);
    if (same(exp, S.One)) return b;
    if (same(exp, S.Zero)) return new IdentityNode(b.rows);
    if (same(exp, S.NegOne)) return InverseNode.create(b).doit(hints);
    return b.evalPower(exp);
  }
  private explicitNonIntegerPower(): Matrix | undefined {
    const m = this.base.asExplicit();
    if (this.base instanceof MatMulNode && isPositive(this.exp) === true) {
      // A rank-one outer product satisfies M**2 = trace(M)*M.
      const [, factors] = this.base.asCoeffMatrices();
      if (factors.slice(0, -1).some((f) => same(f.cols, S.One)) && !same(m.trace(), S.Zero)) {
        return m.scale(pow(m.trace(), add(this.exp, -1)));
      }
    }
    return m.rows === 2 ? m.pow(this.exp) : explicitPower(m, this.exp);
  }
  /**
   * The power of the explicit base.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow.as_explicit`
   */
  override asExplicit(): Matrix {
    return (isInt(this.exp) ? undefined : this.explicitNonIntegerPower()) ?? super.asExplicit();
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new MatPowNode(this.base.transpose(), this.exp);
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return new MatPowNode(this.base.adjoint(), this.exp);
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return new MatPowNode(this.base.conjugate(), this.exp);
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.matpow.MatPow._eval_inverse`
   */
  override evalInverse(): Expr {
    return new MatPowNode(this.base, mul(-1, this.exp));
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   */
  override strPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return `${parenStr(this.base, PRECEDENCE.Pow)}**${parenStr(this.exp, PRECEDENCE.Pow)}`;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    const base = this.base;
    const e = print(this.exp);
    if (!(base instanceof MatrixSymbolNode) && base.isMatrixExpr) return `\\left(${print(base)}\\right)^{${e}}`;
    const b = print(base);
    return b.includes('^') ? `\\left(${b}\\right)^{${e}}` : `${b}^{${e}}`;
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    const e = this.exp;
    if (e.has(x)) return undefined;
    if (isInt(e) && e.p > 0n) return new MatMulNode(Array.from({ length: toInt(e) }, () => this.base)).diffSelf(x, d);
    if (isInt(e) && e.p < 0n) return new MatMulNode(Array.from({ length: -toInt(e) }, () => new InverseNode(this.base))).diffSelf(x, d);
    return undefined;
  }
}

/**
 * An unevaluated power.
 * @param base - The base of the power.
 * @param exp - The exponent to apply.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @see SymPy `sympy.matrices.expressions.matpow.MatPow`
 * @example
 * ```ts
 * import { Identity, MatPow } from '@symjs/symjs';
 * MatPow(Identity(3), 2).doit(); // => I
 * ```
 */
export const MatPow = /* @__PURE__ */ callableClass(MatPowNode, (base: MatArg, exp: ExprLike): MatPowNode => MatPowNode.create(base, exp));
export type MatPow = MatPowNode;

/**
 * The inverse of a square matrix, printed A**(-1).
 * @see SymPy `sympy.matrices.expressions.inverse.Inverse`
 */
export class InverseNode extends MatPowNode {
  /**
   * Constructs an `Inverse`.
   * @param mat - The matrix operand.
   */
  constructor(mat: Expr) {
    super(mat, S.NegOne, 'Inverse');
  }
  /**
   * Constructs the inverse expression from its operands.
   * @param matIn - The matrix operand.
   * @returns The inverse expression from its operands.
   * @throws TypeError when a matrix operand is required.
   * @throws NonSquareMatrixError when the matrix is not square.
   */
  static override create(matIn: MatArg): InverseNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError('mat should be a matrix');
    if (mat.isSquare === false) throw new NonSquareMatrixError(`Inverse of non-square matrix ${str(mat)}`);
    return new InverseNode(mat);
  }
  /**
   * The inverted matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse.arg`
   */
  get arg(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new InverseNode(at(args, 0));
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse._eval_inverse`
   */
  override evalInverse(): Expr {
    return this.arg;
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new InverseNode(asMat(this.arg.transpose()));
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return new InverseNode(asMat(this.arg.adjoint()));
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return new InverseNode(asMat(this.arg.conjugate()));
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse._eval_determinant`
   */
  override evalDeterminant(): Expr {
    return pow(det(this.arg), -1);
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.inverse.Inverse.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    if (hints.invExpand === false) return this;
    const arg = hints.deep === false ? this.arg : doitArg(this.arg, hints);
    return asMat(arg).inverse();
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return `${parenStr(this.arg, PRECEDENCE.Pow)}**(-1)`;
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return matMul(-1, this, mdiff(this.arg, x, d), this);
  }
}

/**
 * An unevaluated inverse.
 * @param mat - The matrix operand.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @see SymPy `sympy.matrices.expressions.inverse.Inverse`
 * @example
 * ```ts
 * import { Inverse, MatrixSymbol } from '@symjs/symjs';
 * Inverse(MatrixSymbol('A', 3, 3)); // => A**(-1)
 * ```
 */
export const Inverse = /* @__PURE__ */ callableClass(InverseNode, (mat: MatArg): InverseNode => InverseNode.create(mat));
export type Inverse = InverseNode;

// ---------------------------------------------------------------------------
// Transpose and Adjoint
// ---------------------------------------------------------------------------

/**
 * The transpose, printed A.T.
 * @see SymPy `sympy.matrices.expressions.transpose.Transpose`
 * @example
 * ```ts
 * import { MatrixSymbol, MatrixTranspose } from '@symjs/symjs';
 * new MatrixTranspose(MatrixSymbol('A', 3, 5)).shape; // => [5, 3]
 * ```
 */
export class TransposeNode extends MatrixExpr {
  /**
   * Constructs a `Transpose`.
   * @param arg - The expression to operate on.
   */
  constructor(arg: Expr) {
    super('Transpose', [arg]);
  }
  /**
   * The transposed matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose.arg`
   */
  get arg(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose.shape`
   */
  get shape(): [Expr, Expr] {
    const [r, c] = this.arg.shape;
    return [c, r];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TransposeNode(at(args, 0));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const arg = hints.deep === false ? at(this.args, 0) : doitArg(at(this.args, 0), hints);
    return arg instanceof MatrixExpr ? arg.evalTranspose() : transposeFn(arg);
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return this.arg.entry(j, i, ctx);
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return this.arg.conjugate();
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return this.arg.adjoint();
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose._eval_transpose`
   */
  override evalTranspose(): Expr {
    return this.arg;
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose._eval_trace`
   */
  override evalTrace(): Expr {
    return new TraceNode(this.arg);
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.transpose.Transpose._eval_determinant`
   */
  override evalDeterminant(): Expr {
    return det(this.arg);
  }
  /**
   * Returns the binding precedence used to parenthesize LaTeX output.
   * @returns The binding precedence used to parenthesize LaTeX output.
   */
  override latexPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return `${parenStr(this.arg, PRECEDENCE.Pow)}.T`;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return postfixLatex(this.arg, 'T', print);
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return transposeOf(mdiff(this.arg, x, d));
  }
}

/** LaTeX of A^{T} and A^{\dagger} (SymPy _print_Transpose and _print_Adjoint). */
function postfixLatex(mat: MatrixExpr, sup: string, print: (e: Expr) => string): string {
  if (!(mat instanceof MatrixSymbolNode) && mat.name !== 'BlockMatrix' && mat.name !== 'BlockDiagMatrix' && mat.isMatrixExpr) return `\\left(${print(mat)}\\right)^{${sup}}`;
  const s = parenLatex(mat, PRECEDENCE.Pow, true);
  return s.includes('^') ? `\\left(${s}\\right)^{${sup}}` : `${s}^{${sup}}`;
}

/**
 * An unevaluated transpose (of a scalar too, which doit returns unchanged).
 * @param arg - The expression to operate on.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.transpose.Transpose`
 * @example
 * ```ts
 * import { MatrixSymbol, Transpose } from '@symjs/symjs';
 * Transpose(MatrixSymbol('A', 3, 5)); // => A.T
 * ```
 */
export const Transpose = /* @__PURE__ */ callableClass(TransposeNode, (arg: MatArg): TransposeNode => new TransposeNode(toExpr(arg)));
export type Transpose = TransposeNode;

/**
 * The conjugate transpose.
 * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint`
 * @example
 * ```ts
 * import { MatrixAdjoint, MatrixSymbol } from '@symjs/symjs';
 * new MatrixAdjoint(MatrixSymbol('A', 3, 5)).shape; // => [5, 3]
 * ```
 */
export class AdjointNode extends MatrixExpr {
  /**
   * Constructs an `Adjoint`.
   * @param arg - The expression to operate on.
   */
  constructor(arg: Expr) {
    super('Adjoint', [arg]);
  }
  /**
   * The matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint.arg`
   */
  get arg(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint.shape`
   */
  get shape(): [Expr, Expr] {
    const [r, c] = this.arg.shape;
    return [c, r];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new AdjointNode(at(args, 0));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const arg = hints.deep === false ? at(this.args, 0) : doitArg(at(this.args, 0), hints);
    return adjointFn(arg);
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return conjugateFn(this.arg.entry(j, i, ctx));
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return this.arg;
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint._eval_transpose`
   */
  override evalTranspose(): Expr {
    return this.arg.conjugate();
  }
  /**
   * Conjugates the entries of this expression.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint._eval_conjugate`
   */
  override evalConjugate(): Expr {
    return this.arg.transpose();
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint._eval_trace`
   */
  override evalTrace(): Expr {
    return conjugateFn(new TraceNode(this.arg));
  }
  /**
   * Returns the binding precedence used to parenthesize LaTeX output.
   * @returns The binding precedence used to parenthesize LaTeX output.
   */
  override latexPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return postfixLatex(this.arg, latexSettings().adjoint, print);
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return adjointFn(mdiff(this.arg, x, d));
  }
}

/**
 * An unevaluated adjoint (of a scalar too, which doit conjugates).
 * @param arg - The expression to operate on.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint`
 * @example
 * ```ts
 * import { Adjoint, MatMul, MatrixSymbol } from '@symjs/symjs';
 * Adjoint(MatMul(MatrixSymbol('A', 3, 5), MatrixSymbol('B', 5, 3))); // => Adjoint(A*B)
 * ```
 */
export const Adjoint = /* @__PURE__ */ callableClass(AdjointNode, (arg: MatArg): AdjointNode => new AdjointNode(toExpr(arg)));
export type Adjoint = AdjointNode;

// ---------------------------------------------------------------------------
// MatrixSlice
// ---------------------------------------------------------------------------

type Triple = [Expr, Expr, Expr];

const isSliceTuple = (s: SliceSpec): s is readonly [(ExprLike | null)?, (ExprLike | null)?, (ExprLike | null)?] => Array.isArray(s);

/** SymPy slice.normalize. */
function normalizeSlice(spec: SliceSpec, size: Expr): Triple {
  let parts: (Expr | null)[];
  if (isSliceTuple(spec)) parts = spec.map((x) => (x === null || x === undefined ? null : sympify(x)));
  else {
    let i = sympify(spec);
    if (relTruth('Lt', i, S.Zero) === true) i = add(i, size);
    parts = [i, add(i, 1), S.One];
  }
  while (parts.length < 3) parts.push(null);
  let start = parts[0] ?? S.Zero;
  let stop = parts[1] ?? size;
  if (relTruth('Lt', start, S.Zero) === true) start = add(start, size);
  if (relTruth('Lt', stop, S.Zero) === true) stop = add(stop, size);
  const p2 = at(parts, 2);
  const step = p2 === null || same(p2, S.Zero) ? S.One : p2;
  if (relTruth('Lt', mul(add(stop, mul(-1, start)), step), S.One) === true) throw new RangeError('Invalid slice');
  return [start, stop, step];
}

function sliceOfSlice(s: Triple, t: Triple): Triple {
  const [start1, , step1] = s;
  const [start2, stop2, step2] = t;
  const start = add(start1, mul(start2, step1));
  const step = mul(step1, step2);
  const stop = add(start1, mul(step1, stop2));
  return [start, stop, step];
}

/**
 * A slice of a matrix expression.
 * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice`
 */
export class MatrixSliceNode extends MatrixExpr {
  /**
   * Constructs a `MatrixSlice`.
   * @param parent - The object containing the selected element.
   * @param rowslice - The row index or slice.
   * @param colslice - The column index or slice.
   */
  constructor(parent: Expr, rowslice: Triple, colslice: Triple) {
    super('MatrixSlice', [parent, ...rowslice, ...colslice]);
  }
  /**
   * Constructs the matrix slice expression from its operands.
   * @param parentIn - The object containing the selected element.
   * @param rowSpec - The rows to select.
   * @param colSpec - The columns to select.
   * @returns The matrix slice expression from its operands.
   * @throws RangeError when the slice bounds or step are invalid.
   */
  static create(parentIn: MatArg, rowSpec: SliceSpec, colSpec: SliceSpec): Expr {
    const parent = toMatrix(parentIn);
    const rs = normalizeSlice(rowSpec, parent.rows);
    const cs = normalizeSlice(colSpec, parent.cols);
    if (relTruth('Gt', S.Zero, rs[0]) === true || relTruth('Lt', parent.rows, rs[1]) === true || relTruth('Gt', S.Zero, cs[0]) === true || relTruth('Lt', parent.cols, cs[1]) === true) {
      throw new RangeError('Invalid slice');
    }
    if (parent instanceof MatrixSliceNode) return new MatrixSliceNode(parent.parent, sliceOfSlice(parent.rowslice, rs), sliceOfSlice(parent.colslice, cs));
    return new MatrixSliceNode(parent, rs, cs);
  }
  /**
   * Gets the sliced matrix.
   * @returns The sliced matrix.
   * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice.parent`
   */
  get parent(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * Describes the selected sequence of rows.
   * @returns The starting row, exclusive stop and step.
   * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice.rowslice`
   */
  get rowslice(): Triple {
    return [at(this.args, 1), at(this.args, 2), at(this.args, 3)];
  }
  /**
   * Describes the selected sequence of columns.
   * @returns The starting column, exclusive stop and step.
   * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice.colslice`
   */
  get colslice(): Triple {
    return [at(this.args, 4), at(this.args, 5), at(this.args, 6)];
  }
  /**
   * Gets the row and column slices agree.
   * @returns The row and column slices agree.
   * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice.on_diag`
   */
  get onDiag(): boolean {
    return sameList(this.rowslice, this.colslice);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice.shape`
   */
  get shape(): [Expr, Expr] {
    const len = ([a, b, s]: Triple): Expr => {
      const n = add(b, mul(-1, a));
      return same(s, S.One) ? n : floor(mul(n, pow(s, -1)));
    };
    return [len(this.rowslice), len(this.colslice)];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSliceNode(at(args, 0), [at(args, 1), at(args, 2), at(args, 3)], [at(args, 4), at(args, 5), at(args, 6)]);
  }
  /**
   * Orders the operands for canonical comparison.
   * @returns The expression operands used for canonical ordering.
   */
  override sortArgs(): readonly Expr[] {
    return [this.parent, new TupleNode(this.rowslice), new TupleNode(this.colslice)];
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const [r0, , rs] = this.rowslice;
    const [c0, , cs] = this.colslice;
    return this.parent.entry(add(mul(i, rs), r0), add(mul(j, cs), c0), ctx);
  }
  /**
   * Formats the expression as plain text.
   * @param print - Formats a child expression.
   * @returns The plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    const sl = (x: Triple, d: Expr): string => {
      const parts: string[] = [same(x[0], S.Zero) ? '' : print(x[0]), same(x[1], d) ? '' : print(x[1])];
      if (!same(x[2], S.One)) parts.push(print(x[2]));
      return parts.join(':');
    };
    return `${parenStr(this.parent, PRECEDENCE.Atom, true)}[${sl(this.rowslice, this.parent.rows)}, ${sl(this.colslice, this.parent.cols)}]`;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    const sl = (x: Triple, d: Expr): string => {
      const parts: string[] = [same(x[0], S.Zero) ? '' : print(x[0]), same(x[1], d) ? '' : print(x[1])];
      if (!same(x[2], S.One)) parts.push(print(x[2]));
      return parts.join(':');
    };
    return `${parenLatex(this.parent, PRECEDENCE.Atom, true)}\\left[${sl(this.rowslice, this.parent.rows)}, ${sl(this.colslice, this.parent.cols)}\\right]`;
  }
}

/** A tuple used only in sort keys (SymPy Tuple). */
class TupleNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Tuple', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new TupleNode(args);
  }
}

/**
 * Selects a rectangular slice of a matrix expression.
 * @param parent - The object containing the selected element.
 * @param rowslice - The row index or slice.
 * @param colslice - The column index or slice.
 * @returns The resulting matrix expression.
 * @throws RangeError when the slice bounds or step are invalid.
 * @see SymPy `sympy.matrices.expressions.slice.MatrixSlice`
 * @example
 * ```ts
 * import { MatrixSlice, MatrixSymbol, sympify } from '@symjs/symjs';
 * MatrixSlice(MatrixSlice(MatrixSymbol('X', 10, 10), [1, 9, 2], [2, 6, 1]), [1, 3], sympify(2)); // => X[3:7:2, 4:5]
 * ```
 */
export const MatrixSlice = /* @__PURE__ */ callableClass(MatrixSliceNode, (parent: MatArg, rowslice: SliceSpec, colslice: SliceSpec): Expr => MatrixSliceNode.create(parent, rowslice, colslice));
export type MatrixSlice = MatrixSliceNode;

// ---------------------------------------------------------------------------
// Trace, Determinant, Permanent
// ---------------------------------------------------------------------------

/**
 * The unevaluated trace of a square matrix.
 * @see SymPy `sympy.matrices.expressions.trace.Trace`
 */
export class TraceNode extends MatScalar {
  /**
   * Constructs a `Trace`.
   * @param mat - The matrix operand.
   */
  constructor(mat: Expr) {
    super('Trace', [mat]);
  }
  /**
   * Constructs the trace expression from its operands.
   * @param matIn - The matrix operand.
   * @returns The trace expression from its operands.
   * @throws TypeError when a matrix operand is required.
   * @throws NonSquareMatrixError when the matrix is not square.
   */
  static create(matIn: MatArg): TraceNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError(`input to Trace, ${str(mat)}, is not a matrix`);
    if (mat.isSquare === false) throw new NonSquareMatrixError('Trace of a non-square matrix');
    return new TraceNode(mat);
  }
  /**
   * The matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.trace.Trace.arg`
   */
  get arg(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TraceNode(at(args, 0));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.trace.Trace.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    if (hints.deep !== false) {
      // the doit of a matrix expression is a matrix expression
      return asMat(doitArg(this.arg, hints)).evalTrace();
    }
    return this.arg instanceof ImmutableMatrixNode ? trace(this.arg) : this;
  }
  /**
   * The generic doit: the argument is evaluated already, the trace is taken (Trace(c*A) = c*Trace(A)).
   * @returns The generic doit.
   */
  override doitSelf(): Expr {
    return this.arg.evalTrace();
  }
  /**
   * The trace of the explicit matrix.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.trace.Trace.as_explicit`
   */
  asExplicit(): Expr {
    return new TraceNode(new ImmutableMatrixNode(this.arg.asExplicit())).doit();
  }
  /**
   * The sum of the diagonal entries.
   * @returns The resulting symbolic expression.
   */
  rewriteAsSum(): Expr {
    const i = new Sym(uniqueName('i', this));
    return doitArg(Sum(this.arg.at(i, i), [i, S.Zero, add(this.arg.rows, -1)]));
  }
  /**
   * Rewrites the expression in terms of the requested operation.
   * @param target - The target form of the rewrite.
   * @returns The equivalent expression when the target representation is supported.
   */
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'Sum' ? this.rewriteAsSum() : undefined;
  }
  /**
   * Transposes the expression.
   * @returns The resulting symbolic expression.
   */
  override transposeSelf(): Expr {
    return this;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{tr}\\left(${print(this.arg)} \\right)`;
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if (x instanceof MatrixElementNode) return d(this.rewriteAsSum(), x);
    // the derivative of a matrix expression is a matrix expression (or diff throws)
    return trace(asMat(mdiff(this.arg, x, d)));
  }
}

/** A symbol name not used in the expression (SymPy uniquely_named_symbol). */
function uniqueName(base: string, e: Expr): string {
  const used = new Set([...freeSymbols(e), ...matrixSymbols(e).flatMap((m) => m.shape.flatMap((dim) => [...freeSymbols(dim)]))].filter((s) => s instanceof Sym).map((s) => s.name));
  if (!used.has(base)) return base;
  for (let k = 0; ; k++) if (!used.has(`${base}${k}`)) return `${base}${k}`;
}

/**
 * An unevaluated trace.
 * @param mat - The matrix operand.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @see SymPy `sympy.matrices.expressions.trace.Trace`
 * @example
 * ```ts
 * import { MatrixSymbol, Trace } from '@symjs/symjs';
 * Trace(MatrixSymbol('A', 3, 3)); // => Trace(A)
 * ```
 */
export const Trace = /* @__PURE__ */ callableClass(TraceNode, (mat: MatArg): TraceNode => TraceNode.create(mat));
export type Trace = TraceNode;

/**
 * The trace, evaluated where possible (trace(eye(3)) = 3, trace(2*X) = 2*Trace(X)).
 * @param expr - The expression to transform.
 * @returns The sum of the diagonal entries, left symbolic when necessary.
 * @see SymPy `sympy.matrices.expressions.trace.trace`
 * @example
 * ```ts
 * import { Matrix, trace } from '@symjs/symjs';
 * trace(Matrix.of([[1, 0, 0], [0, 1, 0], [0, 0, 1]])); // => 3
 * ```
 */
export function trace(expr: MatArg): Expr {
  if (expr instanceof Matrix) return expr.trace();
  return TraceNode.create(expr).doit();
}

/**
 * The unevaluated determinant of a square matrix.
 * @see SymPy `sympy.matrices.expressions.determinant.Determinant`
 */
export class DeterminantNode extends MatScalar {
  /**
   * Constructs a `Determinant`.
   * @param mat - The matrix operand.
   */
  constructor(mat: Expr) {
    super('Determinant', [mat]);
  }
  /**
   * Constructs the determinant expression from its operands.
   * @param matIn - The matrix operand.
   * @returns The determinant expression from its operands.
   * @throws TypeError when a matrix operand is required.
   * @throws NonSquareMatrixError when the matrix is not square.
   */
  static create(matIn: MatArg): DeterminantNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError(`Input to Determinant, ${str(mat)}, not a matrix`);
    if (mat.isSquare === false) throw new NonSquareMatrixError('Det of a non-square matrix');
    return new DeterminantNode(mat);
  }
  /**
   * The matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.determinant.Determinant.arg`
   */
  get arg(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DeterminantNode(at(args, 0));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.determinant.Determinant.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    // the doit of a matrix expression is a matrix expression
    return (hints.deep === false ? this.arg : asMat(doitArg(this.arg, hints))).evalDeterminant();
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    const m = this.arg;
    if (m instanceof ImmutableMatrixNode) return `\\left|{${explicitLatexContents(m.matrix, print)}}\\right|`;
    if ((m.name === 'BlockMatrix' || m.name === 'BlockDiagMatrix') && 'blocks' in m && m.blocks instanceof Matrix) {
      const blocks = m.blocks;
      return `\\left|{${explicitLatexContents(blocks, print)}}\\right|`;
    }
    return `\\left|{${print(m)}}\\right|`;
  }
}

/**
 * An unevaluated determinant.
 * @param mat - The matrix operand.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @see SymPy `sympy.matrices.expressions.determinant.Determinant`
 * @example
 * ```ts
 * import { Determinant, MatrixSymbol } from '@symjs/symjs';
 * Determinant(MatrixSymbol('A', 3, 3)); // => Determinant(A)
 * ```
 */
export const Determinant = /* @__PURE__ */ callableClass(DeterminantNode, (mat: MatArg): DeterminantNode => DeterminantNode.create(mat));
export type Determinant = DeterminantNode;

/**
 * The determinant, evaluated where possible (det(A) = Determinant(A), det(eye(3)) = 1).
 * @param matexpr - The matrix expression to evaluate.
 * @returns The determinant, left symbolic when necessary.
 * @see SymPy `sympy.matrices.expressions.determinant.det`
 * @example
 * ```ts
 * import { MatrixSymbol, det } from '@symjs/symjs';
 * det(MatrixSymbol('A', 3, 3)); // => Determinant(A)
 * ```
 */
export function det(matexpr: MatArg): Expr {
  if (matexpr instanceof Matrix) return matexpr.det();
  return DeterminantNode.create(matexpr).doit();
}

/**
 * The unevaluated permanent of a matrix.
 * @see SymPy `sympy.matrices.expressions.determinant.Permanent`
 */
export class PermanentNode extends MatScalar {
  /**
   * Constructs a `Permanent`.
   * @param mat - The matrix operand.
   */
  constructor(mat: Expr) {
    super('Permanent', [mat]);
  }
  /**
   * Constructs the permanent expression from its operands.
   * @param matIn - The matrix operand.
   * @returns The permanent expression from its operands.
   * @throws TypeError when a matrix operand is required.
   */
  static create(matIn: MatArg): PermanentNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError(`Input to Permanent, ${str(mat)}, not a matrix`);
    return new PermanentNode(mat);
  }
  /**
   * The matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.determinant.Permanent.arg`
   */
  get arg(): MatrixExpr {
    return cast(this.args[0], MatrixExpr);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new PermanentNode(at(args, 0));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.determinant.Permanent.doit`
   */
  override doit(): Expr {
    if (this.arg instanceof ImmutableMatrixNode) return explicitPermanent(this.arg.matrix);
    return this;
  }
}

/**
 * An unevaluated permanent.
 * @param mat - The matrix operand.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required.
 * @see SymPy `sympy.matrices.expressions.determinant.Permanent`
 * @example
 * ```ts
 * import { MatrixSymbol, Permanent } from '@symjs/symjs';
 * Permanent(MatrixSymbol('A', 3, 3)); // => Permanent(A)
 * ```
 */
export const Permanent = /* @__PURE__ */ callableClass(PermanentNode, (mat: MatArg): PermanentNode => PermanentNode.create(mat));
export type Permanent = PermanentNode;

/**
 * The permanent, evaluated for explicit matrices (per(ones(5, 5)) = 120).
 * @param matexpr - The matrix expression to evaluate.
 * @returns The permanent, left symbolic when necessary.
 * @see SymPy `sympy.matrices.expressions.determinant.per`
 * @example
 * ```ts
 * import { Matrix, per } from '@symjs/symjs';
 * per(Matrix.of([[1], [2], [5]])); // => 8
 * ```
 */
export function per(matexpr: MatArg): Expr {
  return PermanentNode.create(matexpr).doit();
}

// ---------------------------------------------------------------------------
// ElementwiseApplyFunction
// ---------------------------------------------------------------------------

/** A function given to applyfunc: a Lambda or a JavaScript function of one expression. */
export type ElementFunction = LambdaNode | ((x: Expr) => Expr);

const toLambda = (f: ElementFunction): LambdaNode => {
  if (f instanceof LambdaNode) return f;
  const d = new Dummy('d');
  return new LambdaNode([d, f(d)]);
};

/**
 * A function applied to every entry, printed f.(X).
 * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction`
 */
export class ElementwiseApplyFunctionNode extends MatrixExpr {
  /**
   * Constructs an `ElementwiseApplyFunction`.
   * @param fn - The function to apply to each entry.
   * @param expr - The expression to transform.
   */
  constructor(fn: LambdaNode, expr: Expr) {
    super('ElementwiseApplyFunction', [fn, expr]);
  }
  /**
   * Constructs the elementwise apply function expression from its operands.
   * @param f - The scalar function to evaluate or differentiate.
   * @param exprIn - The expression to transform.
   * @returns The elementwise apply function expression from its operands.
   * @throws TypeError when a matrix operand is required or the function does not accept one argument.
   */
  static create(f: ElementFunction, exprIn: MatArg): Expr {
    const expr = toExpr(exprIn);
    if (!(expr instanceof MatrixExpr)) throw new TypeError(`${str(expr)} must be a matrix instance.`);
    if (same(expr.rows, S.One) && same(expr.cols, S.One)) {
      const ret = f instanceof LambdaNode ? f.call(expr) : f(expr);
      if (ret instanceof MatrixExpr) return ret;
    }
    const lam = toLambda(f);
    if (lam.variables.length !== 1) throw new TypeError(`${str(lam)} should be able to accept 1 arguments.`);
    return new ElementwiseApplyFunctionNode(lam, expr);
  }
  /**
   * Gets the function (a Lambda).
   * @returns The function (a Lambda).
   * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction.function`
   */
  get function(): LambdaNode {
    return cast(this.args[0], LambdaNode);
  }
  /**
   * Gets the matrix.
   * @returns The matrix.
   * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction.expr`
   */
  get expr(): MatrixExpr {
    return cast(this.args[1], MatrixExpr);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction.shape`
   */
  get shape(): [Expr, Expr] {
    return this.expr.shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The ordered operands of the matrix expression.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new ElementwiseApplyFunctionNode(cast(args[0], LambdaNode), at(args, 1));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const expr = hints.deep === false ? this.expr : doitArg(this.expr, hints);
    const f = this.function;
    if (f.variables.length === 1 && same(at(f.variables, 0), f.expr)) return expr;
    if (expr instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(expr.matrix.map((e) => f.call(e)));
    if (expr instanceof ElementwiseApplyFunctionNode) {
      const g = expr.function;
      return asMat(ElementwiseApplyFunctionNode.create((x: Expr) => f.call(g.call(x)), expr.expr)).doit(hints);
    }
    return expr === this.expr ? this : new ElementwiseApplyFunctionNode(f, expr);
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return this.function.call(this.expr.entry(i, j, ctx));
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new ElementwiseApplyFunctionNode(this.function, this.expr.transpose());
  }
  /**
   * The arguments simplified, the application kept.
   * @param simplify - The simplifier to apply to subexpressions.
   * @returns The resulting symbolic expression.
   */
  override simplifySelf(simplify: (e: Expr) => Expr): Expr {
    return ElementwiseApplyFunctionNode.create(cast(simplify(this.function), LambdaNode), simplify(this.expr));
  }
  /**
   * Formats the expression as plain text.
   * @param print - Formats a child expression.
   * @returns The plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    return `${print(this.function)}.(${print(this.expr)})`;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `{${print(this.function)}}_{\\circ}\\left({${print(this.expr)}}\\right)`;
  }
}

/**
 * Applies a scalar function to each entry of a matrix expression.
 * @param f - The scalar function to evaluate or differentiate.
 * @param expr - The expression to transform.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required or the function does not accept one argument.
 * @see SymPy `sympy.matrices.expressions.applyfunc.ElementwiseApplyFunction`
 * @example
 * ```ts
 * import { Dummy, ElementwiseApplyFunction, Lambda, MatrixSymbol, fn, symbols } from '@symjs/symjs';
 *
 * const [k, i] = symbols('k i');
 * ElementwiseApplyFunction(Lambda([new Dummy('d', {}, 1000000)], fn('sin', [new Dummy('d', {}, 1000000)], { evaluate: false })), MatrixSymbol('x', k, 1)).diff(i); // => 0
 * ```
 */
export const ElementwiseApplyFunction = /* @__PURE__ */ callableClass(ElementwiseApplyFunctionNode, (f: ElementFunction, expr: MatArg): Expr => ElementwiseApplyFunctionNode.create(f, expr));
export type ElementwiseApplyFunction = ElementwiseApplyFunctionNode;
registerHead(ElementwiseApplyFunctionNode, ElementwiseApplyFunction);

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

/**
 * A symbolic n x m matrix (also usable with new).
 * @param name - The name used to identify the object.
 * @param n - The number of rows.
 * @param m - The number of columns.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.matexpr.MatrixSymbol`
 * @example
 * ```ts
 * import { MatrixSymbol } from '@symjs/symjs';
 * MatrixSymbol('X', 2, 2).T; // => X.T
 * ```
 */
export const MatrixSymbol = /* @__PURE__ */ callableClass(MatrixSymbolNode, (name: string, n: ExprLike, m: ExprLike): MatrixSymbolNode => new MatrixSymbolNode(name, n, m));
export type MatrixSymbol = MatrixSymbolNode;

/**
 * Creates an identity matrix of the given order.
 * @param n - The order of the identity matrix.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.special.Identity`
 * @example
 * ```ts
 * import { Identity } from '@symjs/symjs';
 * Identity(3); // => I
 * ```
 */
export const Identity = /* @__PURE__ */ callableClass(IdentityNode, (n: ExprLike): IdentityNode => new IdentityNode(n));
export type Identity = IdentityNode;

/**
 * Creates a rectangular zero matrix.
 * @param m - The number of rows.
 * @param n - The number of columns.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.special.ZeroMatrix`
 * @example
 * ```ts
 * import { MatrixSymbol, Transpose, ZeroMatrix } from '@symjs/symjs';
 * ZeroMatrix(3, 5).mul(Transpose(MatrixSymbol('A', 3, 5))); // => 0
 * ```
 */
export const ZeroMatrix = /* @__PURE__ */ callableClass(ZeroMatrixNode, (m: ExprLike, n: ExprLike): ZeroMatrixNode => new ZeroMatrixNode(m, n));
export type ZeroMatrix = ZeroMatrixNode;

/**
 * Creates a rectangular matrix of ones.
 * @param m - The number of rows.
 * @param n - The number of columns.
 * @param evaluate - Whether to evaluate the expression immediately.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.special.OneMatrix`
 * @example
 * ```ts
 * import { OneMatrix } from '@symjs/symjs';
 * OneMatrix(1, 1).I; // => I
 * ```
 */
export const OneMatrix = /* @__PURE__ */ callableClass(OneMatrixNode, (m: ExprLike, n: ExprLike, evaluate = false): MatrixExpr => OneMatrixNode.create(m, n, evaluate));
export type OneMatrix = OneMatrixNode;

/**
 * Represents a multiplicative identity with unspecified dimensions.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.special.GenericIdentity`
 * @example
 * ```ts
 * import { GenericIdentity } from '@symjs/symjs';
 * GenericIdentity(); // => I
 * ```
 */
export const GenericIdentity = /* @__PURE__ */ callableClass(GenericIdentityNode, (): GenericIdentityNode => new GenericIdentityNode());
export type GenericIdentity = GenericIdentityNode;

/**
 * Represents an additive identity with unspecified dimensions.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.special.GenericZeroMatrix`
 * @example
 * ```ts
 * import { GenericZeroMatrix } from '@symjs/symjs';
 * GenericZeroMatrix(); // => 0
 * ```
 */
export const GenericZeroMatrix = /* @__PURE__ */ callableClass(GenericZeroMatrixNode, (): GenericZeroMatrixNode => new GenericZeroMatrixNode());
export type GenericZeroMatrix = GenericZeroMatrixNode;

/**
 * The entry M[i, j] of a matrix expression.
 * @see SymPy `sympy.matrices.expressions.matexpr.MatrixElement`
 * @example
 * ```ts
 * import { MatrixElement, MatrixSymbol, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * MatrixElement(MatrixSymbol('A', 1, 1), 0, 0).mul(x); // => x*A[0, 0]
 * ```
 */
export const MatrixElement = /* @__PURE__ */ callableClass(MatrixElementNode, matrixElement);
export type MatrixElement = MatrixElementNode;

/**
 * An explicit matrix as a matrix expression, from a
 * Matrix, nested rows, or (rows, cols, entries).
 * @param a - The source matrix, row arrays, or number of rows.
 * @param cols - The number of columns.
 * @param entries - The matrix entries in row-major order.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.immutable.ImmutableDenseMatrix`
 * @example
 * ```ts
 * import { ImmutableDenseMatrix, Matrix } from '@symjs/symjs';
 * ImmutableDenseMatrix(Matrix.of([[1, 0, 0], [0, 1, 0], [0, 0, 1]])); // => Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
 * ```
 */
export const ImmutableMatrix = /* @__PURE__ */ callableClass(
  ImmutableMatrixNode,
  (a: Matrix | MatrixExpr | readonly (readonly ExprLike[])[] | number, cols?: number, entries?: readonly ExprLike[] | ((i: number, j: number) => ExprLike)): ImmutableMatrixNode => {
    if (a instanceof Matrix) return new ImmutableMatrixNode(a);
    // the explicit matrix of a matrix expression of known shape
    if (a instanceof MatrixExpr) return new ImmutableMatrixNode(a.asExplicit());
    if (typeof a === 'number') {
      const c = cols ?? 0;
      const f = typeof entries === 'function' ? entries : (i: number, j: number): ExprLike => entries?.[i * c + j] ?? 0;
      return new ImmutableMatrixNode(Matrix.fromFunction(a, c, f));
    }
    return new ImmutableMatrixNode(Matrix.of(a));
  },
);
export type ImmutableMatrix = ImmutableMatrixNode;

/**
 * Returns the MatrixSymbols of an expression.
 * @param expr - The expression to transform.
 * @returns The MatrixSymbols of an expression.
 * @see SymPy `sympy.matrices.expressions.matexpr.matrix_symbols`
 */
export function matrixSymbols(expr: MatArg): MatrixSymbolNode[] {
  const out = new Map<string, MatrixSymbolNode>();
  const go = (e: Expr): void => {
    if (e instanceof MatrixSymbolNode) out.set(e.key, e);
    else e.args.forEach(go);
  };
  go(toExpr(expr));
  return [...out.values()];
}
