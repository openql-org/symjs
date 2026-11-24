// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy FunctionMatrix (sympy.matrices.expressions.funcmatrix): a
 * matrix whose entries are given by a function of the indices, and the
 * discrete Fourier transform matrices DFT and IDFT (fourier).
 */

import { callableClass } from '../../core/callable';
import { LambdaNode } from '../../core/lambda';
import type { ExprLike , Expr} from '../../core/nodes';
import { Dummy, Rational, S, Sym } from '../../core/nodes';
import { exp, mul, pow, sqrt } from '../../core/ops';
import { parse } from '../../parsing/parser';
import { latex } from '../../printing/latex';
import { MatrixExpr, TraceNode, checkDim } from './matexpr';
import { isInt } from './util';
import { isIntegerQ } from '../../core/assumptions';
import { sympify } from '../../core/ops';
import { at, cast, defined, first, pair } from '../../core/guard';

/** A function of the row and column indices: a Lambda, a JavaScript function or SymPy's 'lambda i, j: ...' string. */
export type IndexFunction = LambdaNode | ((i: Expr, j: Expr) => Expr) | string;

function toLambda2(f: IndexFunction): LambdaNode {
  if (f instanceof LambdaNode) {
    if (f.variables.length !== 2) throw new RangeError(`${String(f)} should be able to accept 2 arguments.`);
    return f;
  }
  if (typeof f === 'string') {
    const m = /^\s*lambda\s+(\w+)\s*,\s*(\w+)\s*:(.*)$/s.exec(f);
    if (!m) throw new RangeError(`${f} should be compatible with SymPy function classes.`);
    const iName = defined(m[1], 'row index name');
    const jName = defined(m[2], 'column index name');
    const body = defined(m[3], 'lambda body');
    const i = new Sym(iName);
    const j = new Sym(jName);
    return new LambdaNode([i, j, parse(body.trim(), { symbols: { [iName]: i, [jName]: j } })]);
  }
  const i = new Dummy('i');
  const j = new Dummy('j');
  return new LambdaNode([i, j, f(i, j)]);
}

/**
 * The matrix with entries lamda(i, j).
 * @see SymPy `sympy.matrices.expressions.funcmatrix.FunctionMatrix`
 */
export class FunctionMatrixNode extends MatrixExpr {
  /**
   * Constructs a `FunctionMatrix`.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @param lamda - The function of row and column indices.
   */
  constructor(rows: Expr, cols: Expr, lamda: LambdaNode) {
    super('FunctionMatrix', [rows, cols, lamda]);
  }
  /**
   * Constructs the function matrix expression from its operands.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @param lamda - The function of row and column indices.
   * @returns The function matrix expression from its operands.
   */
  static create(rows: ExprLike, cols: ExprLike, lamda: IndexFunction): FunctionMatrixNode {
    return new FunctionMatrixNode(checkDim(sympify(rows)), checkDim(sympify(cols)), toLambda2(lamda));
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.funcmatrix.FunctionMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    return pair(this.args);
  }
  /**
   * Gets the function of the indices.
   * @returns The function of the indices.
   * @see SymPy `sympy.matrices.expressions.funcmatrix.FunctionMatrix.lamda`
   */
  get lamda(): LambdaNode {
    return cast(at(this.args, 2), LambdaNode);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new FunctionMatrixNode(at(args, 0), at(args, 1), cast(at(args, 2), LambdaNode));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.funcmatrix.FunctionMatrix._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    return this.lamda.call(i, j);
  }
  /**
   * Computes the trace using the structure of this matrix.
   * @returns The trace using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.funcmatrix.FunctionMatrix._eval_trace`
   */
  override evalTrace(): Expr {
    return new TraceNode(this).rewriteAsSum();
  }
}

/**
 * Defines a matrix by a function of its row and column indices.
 * @param rows - The number of rows.
 * @param cols - The number of columns.
 * @param lamda - The function of row and column indices.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.funcmatrix.FunctionMatrix`
 * @example
 * ```ts
 * import { FunctionMatrix, symbols } from '@symjs/symjs';
 *
 * const [n, m] = symbols('n m');
 * FunctionMatrix(n, m, 'lambda i, j: i + j'); // => FunctionMatrix(n, m, Lambda((i, j), i + j))
 * ```
 */
export const FunctionMatrix = /* @__PURE__ */ callableClass(FunctionMatrixNode, (rows: ExprLike, cols: ExprLike, lamda: IndexFunction): FunctionMatrixNode => FunctionMatrixNode.create(rows, cols, lamda));
export type FunctionMatrix = FunctionMatrixNode;

/**
 * w**k/sqrt(n) with w = exp(-2*pi*I/n). For integer k and n the exponent
 * is reduced to the principal argument, as SymPy's exp does
 * (exp(-4*I*pi/3) = exp(2*I*pi/3)).
 */
function dftEntry(n: Expr, k: Expr): Expr {
  const scale = pow(sqrt(n), -1);
  if (isInt(n) && isInt(k) && n.p > 0n) {
    const N = n.p;
    let r = ((k.p % N) + N) % N;
    if (2n * r >= N) r -= N;
    // angle -2*pi*r/n in (-pi, pi]
    return mul(exp(mul(Rational.of(-2n * r, N), S.Pi, S.I)), scale);
  }
  // exp(z)**k = exp(z*k) for an integer k, as SymPy's power of exp evaluates
  if (isIntegerQ(k) === true) return mul(exp(mul(-2, S.Pi, S.I, k, pow(n, -1))), scale);
  const w = exp(mul(-2, S.Pi, S.I, pow(n, -1)));
  return mul(pow(w, k), scale);
}

/**
 * The unitary discrete Fourier transform matrix, entries w**(i*j)/sqrt(n) with w = exp(-2*pi*I/n).
 * @see SymPy `sympy.matrices.expressions.fourier.DFT`
 */
export class DFTNode extends MatrixExpr {
  /**
   * Constructs a `DFT`.
   * @param n - The order of the Fourier transform matrix.
   * @param name - The name used to identify the object.
   */
  constructor(n: ExprLike, name = 'DFT') {
    super(name, [checkDim(sympify(n))]);
  }
  /**
   * The size.
   * @returns The size of the object.
   */
  get size(): Expr {
    return first(this.args);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.fourier.DFT.shape`
   */
  get shape(): [Expr, Expr] {
    return [this.size, this.size];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DFTNode(first(args));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.fourier.DFT._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    return dftEntry(this.size, mul(i, j));
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.fourier.DFT._eval_inverse`
   */
  override evalInverse(): Expr {
    return new IDFTNode(this.size);
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return `\\text{${this.name}}_{${latex(this.size)}}`;
  }
}

/**
 * The inverse discrete Fourier transform matrix.
 * @see SymPy `sympy.matrices.expressions.fourier.IDFT`
 */
export class IDFTNode extends DFTNode {
  /**
   * Constructs an `IDFT`.
   * @param n - The order of the Fourier transform matrix.
   */
  constructor(n: ExprLike) {
    super(n, 'IDFT');
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new IDFTNode(first(args));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.fourier.IDFT._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    return dftEntry(this.size, mul(-1, i, j));
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.fourier.IDFT._eval_inverse`
   */
  override evalInverse(): Expr {
    return new DFTNode(this.size);
  }
}

/**
 * The unitary discrete Fourier transform matrix, entries w**(i*j)/sqrt(n) with w = exp(-2*pi*I/n).
 * @param n - The order of the Fourier transform matrix.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.fourier.DFT`
 * @example
 * ```ts
 * import { DFT } from '@symjs/symjs';
 * DFT(3); // => DFT(3)
 * ```
 */
export const DFT = /* @__PURE__ */ callableClass(DFTNode, (n: ExprLike): DFTNode => new DFTNode(n));
export type DFT = DFTNode;

/**
 * The inverse discrete Fourier transform matrix.
 * @param n - The order of the Fourier transform matrix.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.fourier.IDFT`
 * @example
 * ```ts
 * import { IDFT } from '@symjs/symjs';
 * IDFT(3); // => IDFT(3)
 * ```
 */
export const IDFT = /* @__PURE__ */ callableClass(IDFTNode, (n: ExprLike): IDFTNode => new IDFTNode(n));
export type IDFT = IDFTNode;
