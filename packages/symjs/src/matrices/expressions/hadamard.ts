// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy HadamardProduct and HadamardPower (sympy.matrices.expressions.
 * hadamard): the elementwise product and power of matrices.
 */

import { callableClass } from '../../core/callable';
import type { ExprLike } from '../../core/nodes';
import type { Expr } from '../../core/nodes';
import { mul, pow, sympify } from '../../core/ops';
import { Matrix } from '../matrix';
import type { DoitHints, EntryContext, MatArg } from './matexpr';
import {
  ImmutableMatrixNode,
  MatrixExpr,
  MatAddNode,
  OneMatrixNode,
  ZeroMatrixNode,
  doitArg,
  matSortKey,
  parenLatex,
  toExpr,
  transposeOf,
  validateMatAdd,
} from './matexpr';
import { compareKeys } from '../../printing/sortkey';
import { PRECEDENCE, same } from './util';
import { latexPrecedence } from './matexpr';
import { at, cast, first, pair } from '../../core/guard';
import type { CanonComponent, PermLike } from '../../tensor/tensorcan';
import { canonicalizeTensor } from '../../tensor/tensorcan';

/**
 * The elementwise product of matrices of the same shape.
 * @see SymPy `sympy.matrices.expressions.hadamard.HadamardProduct`
 */
export class HadamardProductNode extends MatrixExpr {
  /**
   * Constructs a `HadamardProduct`.
   * @param args - The operands in their defining order.
   */
  constructor(args: readonly Expr[]) {
    super('HadamardProduct', args);
  }
  /**
   * Constructs the hadamard product expression from its operands.
   * @param argsIn - The operands in their defining order.
   * @param evaluate - Whether to evaluate the expression immediately.
   * @returns The hadamard product expression from its operands.
   * @throws RangeError when no factors are supplied.
   * @throws TypeError when the sum mixes matrix and scalar terms.
   */
  static create(argsIn: readonly MatArg[], evaluate = false): Expr {
    const args = argsIn.map(toExpr);
    if (!args.length) throw new RangeError('HadamardProduct needs at least one argument');
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    validateMatAdd(args);
    const obj = new HadamardProductNode(args);
    return evaluate ? obj.doit({ deep: false }) : obj;
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardProduct.shape`
   */
  get shape(): [Expr, Expr] {
    return cast(first(this.args), MatrixExpr).shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new HadamardProductNode(args);
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardProduct._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return mul(...this.args.map((a) => cast(a, MatrixExpr).entry(i, j, ctx)));
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardProduct._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new HadamardProductNode(this.args.map(transposeOf));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardProduct.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    // SymPy evaluates the arguments also for deep=False (self.func(*(i.doit(**hints) for i in self.args)))
    const args = this.args.map((a) => doitArg(a, hints));
    let expr: Expr = new HadamardProductNode(args);
    const explicit = args.filter((a): a is ImmutableMatrixNode => a instanceof ImmutableMatrixNode);
    if (explicit.length) {
      const remainder = args.filter((a) => !(a instanceof ImmutableMatrixNode));
      const m0 = first(explicit).matrix;
      const m = Matrix.fromFunction(m0.rows, m0.cols, (i, j) => mul(...explicit.map((x) => x.matrix.get(i, j))));
      expr = new HadamardProductNode([new ImmutableMatrixNode(m), ...remainder]);
    }
    return canonicalize(expr);
  }
  /**
   * Differentiates the expression with respect to the given variable.
   * @param x - The differentiation variable.
   * @param d - Differentiates a subexpression.
   * @returns The derivative when this matrix expression supplies a differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const terms = this.args.flatMap((a, i) => a.has(x) ? [hadamardProduct(...this.args.map((b, j) => i === j ? d(b, x) : b))] : []);
    return terms.length ? MatAddNode.create(terms).doit() : new ZeroMatrixNode(...this.shape);
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   */
  override strPrecedence(): number {
    return PRECEDENCE.Mul;
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return this.args.map((a) => parenLatex(a, PRECEDENCE.Pow, true)).join(' \\circ ');
  }
}

/**
 * An unevaluated elementwise product.
 * @param args - The operands in matrix expression order.
 * @returns The resulting matrix expression.
 * @throws RangeError when no factors are supplied.
 * @throws TypeError when the sum mixes matrix and scalar terms.
 * @see SymPy `sympy.matrices.expressions.hadamard.HadamardProduct`
 * @example
 * ```ts
 * import { HadamardProduct, MatrixSymbol, OneMatrix } from '@symjs/symjs';
 * HadamardProduct(MatrixSymbol('A', 2, 2), OneMatrix(2, 2)); // => HadamardProduct(A, 1)
 * ```
 */
export const HadamardProduct = /* @__PURE__ */ callableClass(HadamardProductNode, (...args: MatArg[]): Expr => HadamardProductNode.create(args));
export type HadamardProduct = HadamardProductNode;

/**
 * The evaluated elementwise product.
 * @param matrices - The matrix operands in order.
 * @returns The resulting symbolic expression.
 * @throws TypeError when no factors are supplied.
 * @see SymPy `sympy.matrices.expressions.hadamard.hadamard_product`
 * @example
 * ```ts
 * import { MatrixSymbol, hadamardProduct } from '@symjs/symjs';
 * hadamardProduct(MatrixSymbol('A', 2, 3)); // => A
 * ```
 */
export function hadamardProduct(...matrices: MatArg[]): Expr {
  if (!matrices.length) throw new TypeError('Empty Hadamard product is undefined');
  if (matrices.length === 1) return toExpr(first(matrices));
  return cast(HadamardProductNode.create(matrices), MatrixExpr).doit();
}

/**
 * Canonicalizes an elementwise matrix product, or a tensor index permutation with its slot and dummy-index symmetries.
 * @param x0 - The Hadamard expression or permutation to canonicalize.
 * @param g - The permutation encoding tensor slots.
 * @param dummies - The dummy-index pairs grouped by type.
 * @param msym - The metric symmetries for the dummy-index types.
 * @param v - The component tensors and their slot symmetries.
 * @returns The canonical matrix expression, tensor permutation array, or zero for a vanishing tensor.
 * @throws TypeError when tensor canonicalization lacks dummy indices or metric symmetries.
 * @see SymPy `sympy.combinatorics.tensor_can.canonicalize`
 * @see SymPy `sympy.matrices.expressions.hadamard.canonicalize`
 * @example
 * ```ts
 * import { HadamardProduct, MatrixSymbol, OneMatrix, canonicalize } from '@symjs/symjs';
 * canonicalize(HadamardProduct(MatrixSymbol('A', 2, 2), OneMatrix(2, 2))); // => A
 * ```
 */
export function canonicalize(x0: Expr): Expr;
export function canonicalize(g: PermLike, dummies: readonly number[] | readonly (readonly number[])[], msym: 0 | 1 | null | readonly (0 | 1 | null)[], ...v: CanonComponent[]): number[] | 0;
export function canonicalize(
  x0: Expr | PermLike,
  ...rest: [] | TensorCanonArgs
): Expr | number[] | 0 {
  if (isTensorArgs(rest)) return canonicalizeTensor(x0, ...rest);
  if (isArrayForm(x0)) throw new TypeError('canonicalize of a tensor needs dummies and msym');
  return canonicalizeHadamard(x0);
}

const isArrayForm = (x: Expr | PermLike): x is readonly number[] => Array.isArray(x);
type TensorCanonArgs = [readonly number[] | readonly (readonly number[])[], 0 | 1 | null | readonly (0 | 1 | null)[], ...CanonComponent[]];
const isTensorArgs = (r: [] | TensorCanonArgs): r is TensorCanonArgs => r.length > 0;

function canonicalizeHadamard(x0: Expr): Expr {
  let x = x0;
  // associativity
  for (;;) {
    if (!(x instanceof HadamardProductNode)) break;
    const flat = x.args.flatMap((a) => (a instanceof HadamardProductNode ? a.args : [a]));
    if (flat.length === x.args.length) break;
    x = new HadamardProductNode(flat);
  }
  if (x instanceof HadamardProductNode) {
    // identity
    const ids = x.args.map((a) => a instanceof OneMatrixNode);
    const n = ids.filter(Boolean).length;
    if (n && n !== ids.length) x = new HadamardProductNode(x.args.filter((_, k) => !ids[k]));
    else if (n) x = new HadamardProductNode([first(x.args)]);
  }
  // absorbing by the zero matrix
  if (x instanceof HadamardProductNode && x.args.some((a) => a instanceof ZeroMatrixNode)) {
    const [r, c] = x.shape;
    x = new ZeroMatrixNode(r, c);
  }
  // repeated factors as HadamardPower
  if (x instanceof HadamardProductNode) {
    const tally = new Map<string, { base: Expr; n: number }>();
    for (const a of x.args) {
      const t = tally.get(a.key);
      if (t) t.n++;
      else tally.set(a.key, { base: a, n: 1 });
    }
    x = new HadamardProductNode([...tally.values()].map(({ base, n }) => (n === 1 ? base : new HadamardPowerNode(base, sympify(n)))));
  }
  // commutativity
  if (x instanceof HadamardProductNode) {
    x = new HadamardProductNode(
      x.args
        .map((a) => ({ a, k: matSortKey(a) }))
        .sort((p, q) => compareKeys(p.k, q.k))
        .map((p) => p.a),
    );
  }
  // unpacking
  if (x instanceof HadamardProductNode && x.args.length === 1) return first(x.args);
  return x;
}

/**
 * The elementwise power.
 * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower`
 */
export class HadamardPowerNode extends MatrixExpr {
  /**
   * Constructs a `HadamardPower`.
   * @param base - The base of the power.
   * @param exp - The exponent to apply.
   */
  constructor(base: Expr, exp: Expr) {
    super('HadamardPower', [base, exp]);
  }
  /**
   * Constructs the hadamard power expression from its operands.
   * @param baseIn - The base of the power.
   * @param expIn - The exponent to apply.
   * @returns The hadamard power expression from its operands.
   */
  static create(baseIn: MatArg, expIn: MatArg): Expr {
    const base = toExpr(baseIn);
    const exp = toExpr(expIn);
    if (!(base instanceof MatrixExpr) && !(exp instanceof MatrixExpr)) return pow(base, exp);
    if (base instanceof MatrixExpr && exp instanceof MatrixExpr) validateMatAdd([base, exp]);
    return new HadamardPowerNode(base, exp);
  }
  /**
   * The base.
   * @returns The operand being raised to a power.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower.base`
   */
  get base(): Expr {
    return at(this.args, 0);
  }
  /**
   * The exponent.
   * @returns The power applied to the base.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower.exp`
   */
  get exp(): Expr {
    return at(this.args, 1);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower.shape`
   */
  get shape(): [Expr, Expr] {
    return this.base instanceof MatrixExpr ? this.base.shape : cast(this.exp, MatrixExpr).shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new HadamardPowerNode(...pair(args));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const a = this.base instanceof MatrixExpr ? this.base.entry(i, j, ctx) : this.base;
    const b = this.exp instanceof MatrixExpr ? this.exp.entry(i, j, ctx) : this.exp;
    return pow(a, b);
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower._eval_transpose`
   */
  override evalTranspose(): Expr {
    return new HadamardPowerNode(transposeOf(this.base), this.exp);
  }
  /**
   * Returns the binding precedence used to parenthesize expressions in plain text.
   * @returns The binding precedence used to parenthesize expressions in plain text.
   */
  override strPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    const e = print(this.exp);
    const base = parenLatex(this.base, PRECEDENCE.Pow);
    return latexPrecedence(this.exp) < PRECEDENCE.Mul ? `${base}^{\\circ \\left({${e}}\\right)}` : `${base}^{\\circ {${e}}}`;
  }
}

/**
 * The elementwise power.
 * @param base - The base of the power.
 * @param exp - The exponent to apply.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.hadamard.HadamardPower`
 * @example
 * ```ts
 * import { HadamardPower, symbols } from '@symjs/symjs';
 *
 * const [a, b] = symbols('a b');
 * HadamardPower(a, b); // => a**b
 * ```
 */
export const HadamardPower = /* @__PURE__ */ callableClass(HadamardPowerNode, (base: MatArg, exp: MatArg): Expr => HadamardPowerNode.create(base, exp));
export type HadamardPower = HadamardPowerNode;

/**
 * The elementwise power (base for exp = 1, base**exp for scalars).
 * @param baseIn - The base of the power.
 * @param expIn - The exponent to apply.
 * @returns The resulting symbolic expression.
 * @throws RangeError when the exponent is a matrix.
 * @see SymPy `sympy.matrices.expressions.hadamard.hadamard_power`
 * @example
 * ```ts
 * import { hadamardPower, symbols } from '@symjs/symjs';
 *
 * const [m] = symbols('m', { integer: true });
 * const [n] = symbols('n', { integer: true });
 * hadamardPower(m, n); // => m**n
 * ```
 */
export function hadamardPower(baseIn: MatArg, expIn: ExprLike): Expr {
  const base = toExpr(baseIn);
  const exp = sympify(expIn);
  if (same(exp, sympify(1))) return base;
  if (!(base instanceof MatrixExpr)) return pow(base, exp);
  if (exp instanceof MatrixExpr) throw new RangeError('cannot raise expression to a matrix');
  return new HadamardPowerNode(base, exp);
}
