// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy PermutationMatrix and MatrixPermute (sympy.matrices.
 * expressions.permutation), with the permutations they need as
 * expressions (printed in SymPy's cyclic notation).
 */

import { callableClass } from '../../core/callable';
import type { ExprLike , Expr} from '../../core/nodes';
import { ExtensionExpr, Rational, S } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { KroneckerDelta } from '../../functions/special/hyper';
import type { DoitHints, MatArg } from './matexpr';
import { IdentityNode, MatMulNode, MatrixElementNode, MatrixExpr, OneMatrixNode, ZeroMatrixNode, doitArg, toMatrix } from './matexpr';
import { BlockDiagMatrixNode } from './blockmatrix';
import { isInt, toInt } from './util';
import { at, cast, defined, first } from '../../core/guard';

/** A permutation given by its array form (images of 0..n-1) or an object with one. */
export type PermutationLike = readonly number[] | { readonly arrayForm: readonly number[] };

/**
 * Represents the permutation acting on the axes of a matrix expression.
 * @see SymPy `sympy.combinatorics.permutations.Permutation`
 * @example
 * ```ts
 * import { Perm, PermutationMatrix } from '@symjs/symjs';
 *
 * const p = PermutationMatrix(new Perm([2, 0, 1])).perm;
 * p.apply(0); // => 2
 * p.inverse().arrayForm; // => [1, 2, 0]
 * ```
 * @experimental May change in a minor release.
 */
export class PermutationNode extends ExtensionExpr {
  /**
   * Constructs a `Permutation`.
   * @param arrayForm - The image of each point in order.
   * @throws RangeError when the images do not contain each point exactly once.
   */
  constructor(arrayForm: readonly number[]) {
    const seen = new Set(arrayForm);
    if (seen.size !== arrayForm.length || arrayForm.some((x) => !Number.isInteger(x) || x < 0 || x >= arrayForm.length)) {
      throw new RangeError('Integers 0 through n - 1 must be present.');
    }
    super('Permutation', arrayForm.map((x) => Rational.of(x)));
  }
  /**
   * Constructs a permutation from its images or an object containing them.
   * @param p - The permutation to examine.
   * @returns The permutation of the specified points.
   */
  static from(p: PermutationLike): PermutationNode {
    if (p instanceof PermutationNode) return p;
    return new PermutationNode('arrayForm' in p ? p.arrayForm : p);
  }
  /**
   * Builds a permutation by composing cycles in the order given.
   * @param cycles - The cycles in product order.
   * @param size - The number of positions.
   * @returns The permutation of the specified points.
   */
  static fromCycles(cycles: readonly (readonly number[])[], size?: number): PermutationNode {
    const n = Math.max(size ?? 0, ...cycles.flat().map((x) => x + 1), 0);
    let a = Array.from({ length: n }, (_, i) => i);
    for (const c of cycles) {
      const img = Array.from({ length: n }, (_, i) => i);
      c.forEach((x, k) => (img[x] = at(c, (k + 1) % c.length)));
      a = a.map((x) => at(img, x));
    }
    return new PermutationNode(a);
  }
  /**
   * Gets the images of 0..n-1.
   * @returns The images of 0..n-1.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.array_form`
   */
  get arrayForm(): number[] {
    return this.args.map(toInt);
  }
  /**
   * The number of elements.
   * @returns The size of the object.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.size`
   */
  get size(): number {
    return this.args.length;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new PermutationNode(args.map(toInt));
  }
  /**
   * Applies the permutation to a point.
   * @param i - The zero-based point label.
   * @returns The point to which `i` maps.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__call__`
   */
  apply(i: number): number {
    return defined(this.arrayForm[i], `the image of ${i}`);
  }
  /**
   * Tests whether every point is fixed.
   * @returns Whether the permutation is the identity.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_Identity`
   */
  get isIdentity(): boolean {
    return this.arrayForm.every((x, i) => x === i);
  }
  /**
   * Composes this permutation with a second one.
   * @param q - The other permutation in the composition.
   * @returns The permutation of the specified points.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__mul__`
   */
  compose(q: PermutationNode): PermutationNode {
    const a = this.arrayForm;
    const b = q.arrayForm;
    const n = Math.max(a.length, b.length);
    const image = (arr: number[], i: number): number => arr[i] ?? i;
    return new PermutationNode(Array.from({ length: n }, (_, i) => image(b, image(a, i))));
  }
  /**
   * Reverses the mapping from each point to its image.
   * @returns The inverse permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__invert__`
   */
  inverse(): PermutationNode {
    const a = this.arrayForm;
    const inv = new Array<number>(a.length);
    a.forEach((x, i) => (inv[x] = i));
    return new PermutationNode(inv);
  }
  /**
   * Raises the permutation to an integer power.
   * @param k - The integer exponent, negative for powers of the inverse.
   * @returns The permutation of the specified points.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__pow__`
   */
  power(k: number): PermutationNode {
    let base: PermutationNode = k < 0 ? this.inverse() : this;
    let r = new PermutationNode(Array.from({ length: this.size }, (_, i) => i));
    for (let e = Math.abs(k); e > 0; e >>= 1) {
      if (e & 1) r = r.compose(base);
      base = base.compose(base);
    }
    return r;
  }
  /**
   * Gets the cycles of length > 1, each starting with its least element.
   * @returns The cycles of length > 1, each starting with its least element.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.cyclic_form`
   */
  get cyclicForm(): number[][] {
    const a = this.arrayForm;
    const seen = new Set<number>();
    const out: number[][] = [];
    for (const [i, ai] of a.entries()) {
      if (seen.has(i)) continue;
      const c = [i];
      seen.add(i);
      for (let j = ai; j !== i; j = at(a, j)) {
        c.push(j);
        seen.add(j);
      }
      if (c.length > 1) out.push(c);
    }
    return out;
  }
  /**
   * Decomposes the permutation into disjoint cycles, including singleton cycles.
   * @returns The cycles covering all points of the permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.full_cyclic_form`
   */
  get fullCyclicForm(): number[][] {
    const cyc = this.cyclicForm;
    const used = new Set(cyc.flat());
    const all = [...cyc, ...Array.from({ length: this.size }, (_, i) => i).filter((i) => !used.has(i)).map((i) => [i])];
    return all.sort((x, y) => first(x) - first(y));
  }
  /**
   * Computes the sign of the permutation.
   * @returns Positive one for even parity and negative one for odd parity.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.signature`
   */
  signature(): 1 | -1 {
    const parity = this.cyclicForm.reduce((s, c) => s + c.length - 1, 0) % 2;
    return parity === 0 ? 1 : -1;
  }
  /**
   * Extends or truncates the fixed points at the end of the permutation.
   * @param n - The new permutation size.
   * @returns The permutation of the specified points.
   * @throws RangeError when truncation would split a nontrivial cycle.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.resize`
   */
  resize(n: number): PermutationNode {
    const a = this.arrayForm;
    if (n >= a.length) return new PermutationNode([...a, ...Array.from({ length: n - a.length }, (_, k) => a.length + k)]);
    const broken = this.cyclicForm.find((c) => c.some((x) => x >= n));
    if (broken) throw new RangeError(`The permutation cannot be resized to ${n} because the cycle (${broken.join(', ')}) may break.`);
    return new PermutationNode(a.slice(0, n));
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    if (!this.size) return '()';
    const cycles = this.cyclicForm;
    let s = cycles.map((c) => `(${c.join(', ')})`).join('');
    const big = this.size - 1;
    if (!cycles.some((c) => c.includes(big))) s += `(${big})`;
    const last = s.lastIndexOf('(');
    if (last !== 0 && !s.slice(last).includes(',')) s = s.slice(last) + s.slice(0, last);
    return s.replaceAll(',', '');
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    if (!this.size) return '\\left( \\right)';
    const cycles = this.cyclicForm;
    if (this.arrayForm[this.size - 1] === this.size - 1) cycles.push([this.size - 1]);
    return cycles.map((c) => `\\left( ${c.join('\\; ')}\\right)`).join('');
  }
}

/**
 * The matrix with entries KroneckerDelta(perm(i), j).
 * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix`
 */
export class PermutationMatrixNode extends MatrixExpr {
  /**
   * Constructs a `PermutationMatrix`.
   * @param perm - The permutation to apply.
   */
  constructor(perm: PermutationNode) {
    super('PermutationMatrix', [perm]);
  }
  /**
   * Gets the permutation.
   * @returns The permutation.
   */
  get perm(): PermutationNode {
    return cast(first(this.args), PermutationNode);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    const n = Rational.of(this.perm.size);
    return [n, n];
  }
  /**
   * Tests whether the matrix is the identity.
   * @returns Whether the matrix is identity.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix.is_Identity`
   */
  override get isIdentity(): boolean {
    return this.perm.isIdentity;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new PermutationMatrixNode(cast(first(args), PermutationNode));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix.doit`
   */
  override doit(): Expr {
    return this.isIdentity ? new IdentityNode(this.rows) : this;
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    if (isInt(i)) return KroneckerDelta(this.perm.apply(toInt(i)), j);
    // P[i, j] = delta(perm(i), j) = delta(i, perm^-1(j))
    if (isInt(j)) return KroneckerDelta(i, this.perm.inverse().apply(toInt(j)));
    return new MatrixElementNode(this, i, j);
  }
  /**
   * Evaluates a power of this matrix when its structure determines the result.
   * @param exp - The exponent to apply.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix._eval_power`
   */
  override evalPower(exp: Expr): Expr {
    if (!isInt(exp)) return super.evalPower(exp);
    return new PermutationMatrixNode(this.perm.power(toInt(exp))).doit();
  }
  /**
   * Computes the inverse using the structure of this matrix.
   * @returns The inverse using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix._eval_inverse`
   */
  override evalInverse(): Expr {
    return new PermutationMatrixNode(this.perm.inverse());
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix._eval_transpose`
   */
  override evalTranspose(): Expr {
    return this.evalInverse();
  }
  /**
   * Computes the conjugate transpose of this expression.
   * @returns The conjugate transpose of this expression.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix._eval_adjoint`
   */
  override evalAdjoint(): Expr {
    return this.evalInverse();
  }
  /**
   * Computes the determinant using the structure of this matrix.
   * @returns The determinant using the structure of this matrix.
   * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix._eval_determinant`
   */
  override evalDeterminant(): Expr {
    return this.perm.signature() === 1 ? S.One : S.NegOne;
  }
  /**
   * The product with a permutation matrix on the right.
   * @param other - The other matrix operand.
   * @returns The resulting symbolic expression.
   */
  composeWith(other: MatrixExpr): Expr {
    return new PermutationMatrixNode(this.perm.compose(cast(other, PermutationMatrixNode).perm));
  }
  /**
   * The block diagonal form of the permutation matrix.
   * @returns The resulting symbolic expression.
   */
  rewriteAsBlockDiagMatrix(): Expr {
    const full = this.perm.fullCyclicForm;
    const picks: number[][][] = [];
    let a = 0;
    let b = 0;
    let c = 0;
    let flag = false;
    let temp: number[][] = [];
    for (const cycle of full) {
      const l = cycle.length;
      const m = Math.max(...cycle);
      if (!flag) {
        if (m + 1 > a + l) {
          flag = true;
          temp = [cycle];
          b = m;
          c = l;
        } else {
          picks.push([cycle]);
          a += l;
        }
      } else if (m > b) {
        if (m + 1 === a + c + l) {
          temp.push(cycle);
          picks.push(temp);
          flag = false;
          a = m + 1;
        } else {
          b = m;
          temp.push(cycle);
          c += l;
        }
      } else if (b + 1 === a + c + l) {
        temp.push(cycle);
        picks.push(temp);
        flag = false;
        a = b + 1;
      } else {
        temp.push(cycle);
        c += l;
      }
    }
    let p = 0;
    const mats = picks.map((pick) => {
      const size = pick.reduce((s, cy) => s + cy.length, 0);
      const perm = PermutationNode.fromCycles(
        pick.map((cy) => cy.map((x) => x - p)),
        size,
      );
      p += size;
      return new PermutationMatrixNode(perm);
    });
    return BlockDiagMatrixNode.create(mats);
  }
  /**
   * Rewrites the expression in terms of the requested operation.
   * @param target - The target form of the rewrite.
   * @returns The equivalent expression when the target representation is supported.
   */
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'BlockDiagMatrix' ? this.rewriteAsBlockDiagMatrix() : undefined;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `P_{${print(this.perm)}}`;
  }
}

/**
 * Perm is a permutation object; an array is a RangeError,
 * as it could be read in array form or as a cycle.
 * @param perm - The permutation to apply.
 * @returns The resulting matrix expression.
 * @throws RangeError when the argument is not a permutation.
 * @see SymPy `sympy.matrices.expressions.permutation.PermutationMatrix`
 * @remarks SymPy prints this result as `Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])`.
 * @example
 * ```ts
 * import { Perm, PermutationMatrix } from '@symjs/symjs';
 * PermutationMatrix(new Perm([1, 2, 0])).asExplicit(); // => Matrix([
 * //   [0, 1, 0],
 * //   [0, 0, 1],
 * //   [1, 0, 0]])
 * ```
 */
export const PermutationMatrix = /* @__PURE__ */ callableClass(PermutationMatrixNode, (perm: PermutationNode | { readonly arrayForm: readonly number[] }): PermutationMatrixNode => {
  if (Array.isArray(perm)) throw new RangeError(`${String(perm)} must be a SymPy Permutation instance.`);
  return new PermutationMatrixNode(PermutationNode.from(perm));
});
export type PermutationMatrix = PermutationMatrixNode;

/**
 * The rows (axis 0) or columns (axis 1) of a matrix permuted.
 * @see SymPy `sympy.matrices.expressions.permutation.MatrixPermute`
 */
export class MatrixPermuteNode extends MatrixExpr {
  /**
   * Constructs a `MatrixPermute`.
   * @param mat - The matrix operand.
   * @param perm - The permutation to apply.
   * @param axis - The axis along which to permute the matrix.
   */
  constructor(mat: Expr, perm: PermutationNode, axis: Expr) {
    super('MatrixPermute', [mat, perm, axis]);
  }
  /**
   * Constructs the matrix permute expression from its operands.
   * @param matIn - The matrix operand.
   * @param permIn - The permutation to apply.
   * @param axisIn - The axis along which to permute the matrix.
   * @returns The matrix permute expression from its operands.
   * @throws RangeError when the axis is neither zero nor one.
   */
  static create(matIn: MatArg, permIn: PermutationLike | PermutationMatrixNode, axisIn: ExprLike = 0): MatrixPermuteNode {
    const mat = toMatrix(matIn, `${String(matIn)} must be a SymPy matrix instance.`);
    let perm = permIn instanceof PermutationMatrixNode ? permIn.perm : PermutationNode.from(permIn);
    const axis = sympify(axisIn);
    if (!isInt(axis) || (axis.p !== 0n && axis.p !== 1n)) throw new RangeError('The axis must be 0 or 1.');
    const size = at(mat.shape, toInt(axis));
    if (isInt(size) && toInt(size) !== perm.size) perm = perm.resize(toInt(size));
    return new MatrixPermuteNode(mat, perm, axis);
  }
  /**
   * Gets the permuted matrix.
   * @returns The permuted matrix.
   */
  get mat(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  /**
   * Gets the permutation.
   * @returns The permutation.
   */
  get perm(): PermutationNode {
    return cast(at(this.args, 1), PermutationNode);
  }
  /**
   * Identifies the matrix axis to permute.
   * @returns Zero for rows or one for columns.
   */
  get axis(): number {
    return toInt(at(this.args, 2));
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.permutation.MatrixPermute.shape`
   */
  get shape(): [Expr, Expr] {
    return this.mat.shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixPermuteNode(at(args, 0), cast(at(args, 1), PermutationNode), at(args, 2));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.permutation.MatrixPermute.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const mat = hints.deep === false ? this.mat : cast(doitArg(this.mat, hints), MatrixExpr);
    const perm = this.perm;
    if (perm.isIdentity) return mat;
    if (mat.isIdentity === true) return new PermutationMatrixNode(this.axis === 0 ? perm : perm.inverse());
    if (mat instanceof ZeroMatrixNode || mat instanceof OneMatrixNode) return mat;
    if (mat instanceof MatrixPermuteNode && mat.axis === this.axis) return new MatrixPermuteNode(mat.mat, perm.compose(mat.perm), at(this.args, 2));
    return mat === this.mat ? this : new MatrixPermuteNode(mat, perm, at(this.args, 2));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.permutation.MatrixPermute._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    if (this.axis === 0) return isInt(i) ? this.mat.at(this.perm.apply(toInt(i)), j) : new MatrixElementNode(this, i, j);
    return isInt(j) ? this.mat.at(i, this.perm.apply(toInt(j))) : new MatrixElementNode(this, i, j);
  }
  /**
   * The permutation as a product with a permutation matrix.
   * @returns The resulting symbolic expression.
   */
  rewriteAsMatMul(): Expr {
    if (this.axis === 0) return MatMulNode.create([new PermutationMatrixNode(this.perm), this.mat]);
    return MatMulNode.create([this.mat, new PermutationMatrixNode(this.perm.inverse())]);
  }
  /**
   * Rewrites the expression in terms of the requested operation.
   * @param target - The target form of the rewrite.
   * @returns The equivalent expression when the target representation is supported.
   */
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'MatMul' ? this.rewriteAsMatMul() : undefined;
  }
}

/**
 * The rows (axis 0) or columns (axis 1) of a matrix permuted.
 * @param mat - The matrix operand.
 * @param perm - The permutation to apply.
 * @param axis - The axis along which to permute the matrix.
 * @returns The resulting matrix expression.
 * @throws RangeError when the axis is neither zero nor one.
 * @see SymPy `sympy.matrices.expressions.permutation.MatrixPermute`
 * @example
 * ```ts
 * import { MatrixPermute, OneMatrix, Perm } from '@symjs/symjs';
 * MatrixPermute(OneMatrix(3, 3), new Perm([1, 2, 0]), 0).doit(); // => 1
 * ```
 */
export const MatrixPermute = /* @__PURE__ */ callableClass(MatrixPermuteNode, (mat: MatArg, perm: PermutationLike | PermutationMatrixNode, axis: ExprLike = 0): MatrixPermuteNode => MatrixPermuteNode.create(mat, perm, axis));
export type MatrixPermute = MatrixPermuteNode;
