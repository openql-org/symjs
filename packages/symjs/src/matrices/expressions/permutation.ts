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
 * A permutation of 0..n-1 as an expression argument (SymPy Permutation),
 * printed in cyclic form like SymPy: (0 1 2).
 *
 * @experimental May change in a minor release.
 */
export class PermutationNode extends ExtensionExpr {
  constructor(arrayForm: readonly number[]) {
    const seen = new Set(arrayForm);
    if (seen.size !== arrayForm.length || arrayForm.some((x) => !Number.isInteger(x) || x < 0 || x >= arrayForm.length)) {
      throw new RangeError('Integers 0 through n - 1 must be present.');
    }
    super('Permutation', arrayForm.map((x) => Rational.of(x)));
  }
  /** A permutation from its array form or a permutation-like object. */
  static from(p: PermutationLike): PermutationNode {
    if (p instanceof PermutationNode) return p;
    return new PermutationNode('arrayForm' in p ? p.arrayForm : p);
  }
  /** SymPy Permutation from cycles: Permutation(1, 2, 0) is the cycle (1 2 0); size defaults to the largest element + 1. */
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
  /** The images of 0..n-1 (SymPy array_form). */
  get arrayForm(): number[] {
    return this.args.map(toInt);
  }
  /** The number of elements. */
  get size(): number {
    return this.args.length;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new PermutationNode(args.map(toInt));
  }
  /** The image of i (SymPy apply). */
  apply(i: number): number {
    return defined(this.arrayForm[i], `the image of ${i}`);
  }
  /** True for the identity permutation. */
  get isIdentity(): boolean {
    return this.arrayForm.every((x, i) => x === i);
  }
  /** SymPy p*q: first p, then q. */
  compose(q: PermutationNode): PermutationNode {
    const a = this.arrayForm;
    const b = q.arrayForm;
    const n = Math.max(a.length, b.length);
    const image = (arr: number[], i: number): number => arr[i] ?? i;
    return new PermutationNode(Array.from({ length: n }, (_, i) => image(b, image(a, i))));
  }
  /** The inverse permutation. */
  inverse(): PermutationNode {
    const a = this.arrayForm;
    const inv = new Array<number>(a.length);
    a.forEach((x, i) => (inv[x] = i));
    return new PermutationNode(inv);
  }
  /** SymPy p**k. */
  power(k: number): PermutationNode {
    let base: PermutationNode = k < 0 ? this.inverse() : this;
    let r = new PermutationNode(Array.from({ length: this.size }, (_, i) => i));
    for (let e = Math.abs(k); e > 0; e >>= 1) {
      if (e & 1) r = r.compose(base);
      base = base.compose(base);
    }
    return r;
  }
  /** The cycles of length > 1, each starting with its least element (SymPy cyclic_form). */
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
  /** All cycles including the fixed points (SymPy full_cyclic_form). */
  get fullCyclicForm(): number[][] {
    const cyc = this.cyclicForm;
    const used = new Set(cyc.flat());
    const all = [...cyc, ...Array.from({ length: this.size }, (_, i) => i).filter((i) => !used.has(i)).map((i) => [i])];
    return all.sort((x, y) => first(x) - first(y));
  }
  /** SymPy signature: +1 for even, -1 for odd permutations. */
  signature(): 1 | -1 {
    const parity = this.cyclicForm.reduce((s, c) => s + c.length - 1, 0) % 2;
    return parity === 0 ? 1 : -1;
  }
  /** SymPy resize(n): fixed points added or removed. */
  resize(n: number): PermutationNode {
    const a = this.arrayForm;
    if (n >= a.length) return new PermutationNode([...a, ...Array.from({ length: n - a.length }, (_, k) => a.length + k)]);
    const broken = this.cyclicForm.find((c) => c.some((x) => x >= n));
    if (broken) throw new RangeError(`The permutation cannot be resized to ${n} because the cycle (${broken.join(', ')}) may break.`);
    return new PermutationNode(a.slice(0, n));
  }
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
  override printLatex(): string {
    if (!this.size) return '\\left( \\right)';
    const cycles = this.cyclicForm;
    if (this.arrayForm[this.size - 1] === this.size - 1) cycles.push([this.size - 1]);
    return cycles.map((c) => `\\left( ${c.join('\\; ')}\\right)`).join('');
  }
}

/** SymPy PermutationMatrix(perm): the matrix with entries KroneckerDelta(perm(i), j). */
export class PermutationMatrixNode extends MatrixExpr {
  constructor(perm: PermutationNode) {
    super('PermutationMatrix', [perm]);
  }
  /** The permutation. */
  get perm(): PermutationNode {
    return cast(first(this.args), PermutationNode);
  }
  get shape(): [Expr, Expr] {
    const n = Rational.of(this.perm.size);
    return [n, n];
  }
  override get isIdentity(): boolean {
    return this.perm.isIdentity;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new PermutationMatrixNode(cast(first(args), PermutationNode));
  }
  override doit(): Expr {
    return this.isIdentity ? new IdentityNode(this.rows) : this;
  }
  override entry(i: Expr, j: Expr): Expr {
    if (!isInt(i)) return new MatrixElementNode(this, i, j);
    return KroneckerDelta(this.perm.apply(toInt(i)), j);
  }
  override evalPower(exp: Expr): Expr {
    if (!isInt(exp)) return super.evalPower(exp);
    return new PermutationMatrixNode(this.perm.power(toInt(exp))).doit();
  }
  override evalInverse(): Expr {
    return new PermutationMatrixNode(this.perm.inverse());
  }
  override evalTranspose(): Expr {
    return this.evalInverse();
  }
  override evalAdjoint(): Expr {
    return this.evalInverse();
  }
  override evalDeterminant(): Expr {
    return this.perm.signature() === 1 ? S.One : S.NegOne;
  }
  /** The product with a permutation matrix on the right (SymPy combine_permutations). */
  composeWith(other: MatrixExpr): Expr {
    return new PermutationMatrixNode(this.perm.compose(cast(other, PermutationMatrixNode).perm));
  }
  /** SymPy rewrite(BlockDiagMatrix): the block diagonal form of the permutation matrix. */
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
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'BlockDiagMatrix' ? this.rewriteAsBlockDiagMatrix() : undefined;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `P_{${print(this.perm)}}`;
  }
}

/** SymPy PermutationMatrix(perm). */
export const PermutationMatrix = /* @__PURE__ */ callableClass(PermutationMatrixNode, (perm: PermutationLike): PermutationMatrixNode => new PermutationMatrixNode(PermutationNode.from(perm)));
export type PermutationMatrix = PermutationMatrixNode;

/** SymPy MatrixPermute(mat, perm, axis): the rows (axis 0) or columns (axis 1) of a matrix permuted. */
export class MatrixPermuteNode extends MatrixExpr {
  constructor(mat: Expr, perm: PermutationNode, axis: Expr) {
    super('MatrixPermute', [mat, perm, axis]);
  }
  /** SymPy MatrixPermute(mat, perm, axis=0). */
  static create(matIn: MatArg, permIn: PermutationLike | PermutationMatrixNode, axisIn: ExprLike = 0): MatrixPermuteNode {
    const mat = toMatrix(matIn, `${String(matIn)} must be a SymPy matrix instance.`);
    let perm = permIn instanceof PermutationMatrixNode ? permIn.perm : PermutationNode.from(permIn);
    const axis = sympify(axisIn);
    if (!isInt(axis) || (axis.p !== 0n && axis.p !== 1n)) throw new RangeError('The axis must be 0 or 1.');
    const size = at(mat.shape, toInt(axis));
    if (isInt(size) && toInt(size) !== perm.size) perm = perm.resize(toInt(size));
    return new MatrixPermuteNode(mat, perm, axis);
  }
  /** The permuted matrix. */
  get mat(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  /** The permutation. */
  get perm(): PermutationNode {
    return cast(at(this.args, 1), PermutationNode);
  }
  /** 0 for rows, 1 for columns. */
  get axis(): number {
    return toInt(at(this.args, 2));
  }
  get shape(): [Expr, Expr] {
    return this.mat.shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixPermuteNode(at(args, 0), cast(at(args, 1), PermutationNode), at(args, 2));
  }
  override doit(hints: DoitHints = {}): Expr {
    const mat = hints.deep === false ? this.mat : cast(doitArg(this.mat, hints), MatrixExpr);
    const perm = this.perm;
    if (perm.isIdentity) return mat;
    if (mat.isIdentity === true) return new PermutationMatrixNode(this.axis === 0 ? perm : perm.inverse());
    if (mat instanceof ZeroMatrixNode || mat instanceof OneMatrixNode) return mat;
    if (mat instanceof MatrixPermuteNode && mat.axis === this.axis) return new MatrixPermuteNode(mat.mat, perm.compose(mat.perm), at(this.args, 2));
    return mat === this.mat ? this : new MatrixPermuteNode(mat, perm, at(this.args, 2));
  }
  override entry(i: Expr, j: Expr): Expr {
    if (this.axis === 0) return isInt(i) ? this.mat.at(this.perm.apply(toInt(i)), j) : new MatrixElementNode(this, i, j);
    return isInt(j) ? this.mat.at(i, this.perm.apply(toInt(j))) : new MatrixElementNode(this, i, j);
  }
  /** SymPy rewrite(MatMul): the permutation as a product with a permutation matrix. */
  rewriteAsMatMul(): Expr {
    if (this.axis === 0) return MatMulNode.create([new PermutationMatrixNode(this.perm), this.mat]);
    return MatMulNode.create([this.mat, new PermutationMatrixNode(this.perm.inverse())]);
  }
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'MatMul' ? this.rewriteAsMatMul() : undefined;
  }
}

/** SymPy MatrixPermute(mat, perm, axis=0). */
export const MatrixPermute = /* @__PURE__ */ callableClass(MatrixPermuteNode, (mat: MatArg, perm: PermutationLike | PermutationMatrixNode, axis: ExprLike = 0): MatrixPermuteNode => MatrixPermuteNode.create(mat, perm, axis));
export type MatrixPermute = MatrixPermuteNode;
