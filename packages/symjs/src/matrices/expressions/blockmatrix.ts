// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy BlockMatrix and BlockDiagMatrix (sympy.matrices.expressions.
 * blockmatrix): matrices made of matrix-expression blocks, with block
 * multiplication, block inversion, Schur complements, block
 * decompositions and block_collapse.
 */

import { callableClass } from '../../core/callable';
import { NonInvertibleMatrixError } from '../../core/errors';
import { at, cast } from '../../core/guard';
import type { ExprLike , Expr} from '../../core/nodes';
import { ExtensionExpr, S } from '../../core/nodes';
import { add, mul, sympify } from '../../core/ops';
import { rebuild } from '../../core/traverse';
import type { Truth } from '../../core/truth';
import { adjoint as adjointFn } from '../../functions/elementary';
import { Matrix } from '../matrix';
import type { MatArg } from './matexpr';
import {
  DeterminantNode,
  IdentityNode,
  InverseNode,
  MatAddNode,
  MatMulNode,
  MatPowNode,
  MatrixElementNode,
  MatrixExpr,
  MatrixSliceNode,
  ShapeError,
  ZeroMatrixNode,
  det,
  doitArg,
  explicitLatexContents,
  explicitStr,
  hasNode,
  toExpr,
  trace,
  transposeOf,
  unpackMat,
} from './matexpr';
import { askInvertible } from './predicates';
import { isInt, relTruth, same, sameList } from './util';

const asMat = (e: Expr): MatrixExpr => cast(e, MatrixExpr);

/** M1 * M2 with SymPy's operator (MatMul(...).doit()). */
function times(...xs: Expr[]): Expr {
  // every caller passes at least one matrix, so the product is a matrix expression
  return asMat(MatMulNode.create(xs)).doit();
}

/** M1 + M2 with SymPy's operator (MatAdd(...).doit()). */
function plus(...xs: Expr[]): Expr {
  return MatAddNode.create(xs).doit();
}

/** M1 - M2. */
function minus(a: Expr, b: Expr): Expr {
  return plus(a, times(S.NegOne, b));
}

/** The sum of the dimensions (SymPy sum()). */
const total = (xs: readonly Expr[]): Expr => add(...xs);

const keysEqual = (a: readonly Expr[], b: readonly Expr[]): boolean => sameList(a, b);

/** SymPy BlockMatrix: a matrix of matrix-expression blocks. */
export class BlockMatrixNode extends MatrixExpr {
  /** Number of block rows and block columns of the stored arguments. */
  protected readonly bshape: [number, number];
  constructor(blocks: readonly Expr[], blockshape: [number, number], name = 'BlockMatrix') {
    super(name, blocks);
    this.bshape = blockshape;
  }
  /**
   * SymPy BlockMatrix(rows): validated. Each row holds blocks of the same
   * number of rows and each column blocks of the same number of columns.
   */
  static create(rowsIn: Matrix | readonly MatArg[] | readonly (readonly MatArg[])[]): BlockMatrixNode {
    if (rowsIn instanceof Matrix) return new BlockMatrixNode(rowsIn.data, [rowsIn.rows, rowsIn.cols]);
    const isRow = (r: unknown): r is readonly MatArg[] => Array.isArray(r);
    const isRowList = (x: readonly MatArg[] | readonly (readonly MatArg[])[]): x is readonly (readonly MatArg[])[] => !x.length || isRow(x[0]);
    let rows: Expr[][];
    if (isRowList(rowsIn)) rows = rowsIn.map((r) => r.map(toExpr));
    else rows = [rowsIn.map(toExpr)];
    if (!rows.length || !rows.every((r) => r.every((b) => b instanceof MatrixExpr))) {
      throw new RangeError('expecting a sequence of 1 or more rows containing Matrices.');
    }
    const ms = rows;
    const distinct = (xs: Expr[]) => new Set(xs.map((x) => x.key)).size;
    let blocky = new Set(ms.map((r) => r.length)).size === 1;
    let ok = blocky;
    if (ok) {
      for (const r of ms) {
        ok = distinct(r.map((b) => b.rows)) === 1;
        if (!ok) break;
      }
      blocky = ok;
      if (ok) {
        for (let c = 0; c < at(ms, 0).length; c++) {
          ok = distinct(ms.map((r) => at(r, c).cols)) === 1;
          if (!ok) break;
        }
      }
    }
    if (!ok) {
      ok = distinct(ms.map((r) => total(r.map((b) => b.cols)))) === 1;
      if (blocky && ok) {
        throw new RangeError(
          'Although this matrix is comprised of blocks, the blocks do not fill the matrix in a size-symmetric fashion. To create a full matrix from these arguments, pass them directly to Matrix.',
        );
      }
      throw new RangeError(
        "When there are not the same number of rows in each row's matrices or there are not the same number of total columns in each row, the matrix is not a block matrix. If this matrix is known to consist of blocks fully filling a 2-D space then see Matrix.irregular.",
      );
    }
    return new BlockMatrixNode(ms.flat(), [ms.length, at(ms, 0).length]);
  }
  /** The blocks as an explicit matrix of matrix expressions. */
  get blocks(): Matrix {
    const [r, c] = this.bshape;
    return Matrix.fromFunction(r, c, (i, j) => at(this.args, i * c + j));
  }
  /** The block at block position (i, j). */
  block(i: number, j: number): MatrixExpr {
    return asMat(this.blocks.get(i, j));
  }
  /** The number of block rows and columns (SymPy blockshape). */
  get blockshape(): [number, number] {
    return [...this.bshape];
  }
  get shape(): [Expr, Expr] {
    const [r, c] = this.blockshape;
    return [total(Array.from({ length: r }, (_, i) => this.block(i, 0).rows)), total(Array.from({ length: c }, (_, j) => this.block(0, j).cols))];
  }
  /** The numbers of rows of the block rows. */
  get rowblocksizes(): Expr[] {
    return Array.from({ length: this.blockshape[0] }, (_, i) => this.block(i, 0).rows);
  }
  /** The numbers of columns of the block columns. */
  get colblocksizes(): Expr[] {
    return Array.from({ length: this.blockshape[1] }, (_, j) => this.block(0, j).cols);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new BlockMatrixNode(args, this.bshape);
  }
  protected override computeKey(): string {
    return `${this.name}[${this.bshape.join('x')}](${this.args.map((a) => a.key).join(',')})`;
  }
  override sortArgs(): readonly Expr[] {
    return [new BlockTuple(this.args)];
  }
  /** SymPy structurally_equal: the same block structure. */
  structurallyEqual(other: Expr): boolean {
    return (
      other instanceof BlockMatrixNode &&
      keysEqual(this.shape, other.shape) &&
      this.blockshape[0] === other.blockshape[0] &&
      this.blockshape[1] === other.blockshape[1] &&
      keysEqual(this.rowblocksizes, other.rowblocksizes) &&
      keysEqual(this.colblocksizes, other.colblocksizes)
    );
  }
  /** SymPy _blockmul: the block product when the block sizes match, else the product. */
  blockmul(other: Expr): Expr {
    if (other instanceof BlockMatrixNode && keysEqual(this.colblocksizes, other.rowblocksizes)) {
      const a = this.blocks;
      const b = other.blocks;
      const out = Matrix.fromFunction(a.rows, b.cols, (i, j) => {
        const vec = Array.from({ length: a.cols }, (_, k) => times(a.get(i, k), b.get(k, j)));
        return vec.length === 1 ? at(vec, 0) : MatAddNode.create(vec).doit({ deep: false });
      });
      return BlockMatrixNode.create(out);
    }
    return times(this, other);
  }
  /** SymPy _blockadd: the block sum of structurally equal block matrices, else the sum. */
  blockadd(other: Expr): Expr {
    if (other instanceof BlockMatrixNode && this.structurallyEqual(other)) {
      const a = this.blocks;
      const b = other.blocks;
      return BlockMatrixNode.create(Matrix.fromFunction(a.rows, a.cols, (i, j) => plus(a.get(i, j), b.get(i, j))));
    }
    return plus(this, other);
  }
  override evalTranspose(): Expr {
    const b = this.blocks;
    return BlockMatrixNode.create(Matrix.fromFunction(b.cols, b.rows, (i, j) => transposeOf(b.get(j, i))));
  }
  override transpose(): Expr {
    return this.evalTranspose();
  }
  override evalAdjoint(): Expr {
    const b = this.blocks;
    return BlockMatrixNode.create(Matrix.fromFunction(b.cols, b.rows, (i, j) => adjointFn(b.get(j, i))));
  }
  override evalTrace(): Expr {
    if (keysEqual(this.rowblocksizes, this.colblocksizes)) {
      return add(...Array.from({ length: this.blockshape[0] }, (_, i) => trace(this.block(i, i))));
    }
    return super.evalTrace();
  }
  override evalDeterminant(): Expr {
    const [r, c] = this.blockshape;
    if (r === 1 && c === 1) return det(this.block(0, 0));
    if (r === 2 && c === 2) {
      const [A, B, C, D] = [this.block(0, 0), this.block(0, 1), this.block(1, 0), this.block(1, 1)];
      if (askInvertible(A) === true) return mul(det(A), det(minus(D, times(C, A.I, B))));
      if (askInvertible(D) === true) return mul(det(D), det(minus(A, times(B, D.I, C))));
    }
    return new DeterminantNode(this);
  }
  /**
   * SymPy schur(mat, generalized): the Schur complement with respect to the
   * block 'A', 'B', 'C' or 'D' of a 2 x 2 block matrix; the generalized
   * complement uses the Moore-Penrose inverse (X.T*X)**-1*X.T.
   */
  schur(mat: 'A' | 'B' | 'C' | 'D' = 'A', generalized = false): Expr {
    const [r, c] = this.blockshape;
    if (r !== 2 || c !== 2) throw new ShapeError('Schur Complement can only be calculated for 2x2 block matrices');
    const [A, B, C, D] = [this.block(0, 0), this.block(0, 1), this.block(1, 0), this.block(1, 1)];
    const d = { A, B, C, D }[mat];
    let inv: Expr;
    try {
      inv = generalized ? times(asMat(times(d.T, d)).inv(), d.T) : d.inv();
    } catch (e) {
      if (e instanceof NonInvertibleMatrixError) {
        throw new NonInvertibleMatrixError(
          'The given matrix is not invertible. Please set generalized=True to compute the generalized Schur Complement which uses Moore-Penrose Inverse',
        );
      }
      throw e;
    }
    switch (mat) {
      case 'A':
        return minus(D, times(C, inv, B));
      case 'B':
        return minus(C, times(D, inv, A));
      case 'C':
        return minus(B, times(A, inv, D));
      case 'D':
        return minus(A, times(B, inv, C));
    }
  }
  /** SymPy LDUdecomposition: [L, D, U] with X = L*D*U for a 2 x 2 block matrix. */
  LDUdecomposition(): [Expr, Expr, Expr] {
    const [A, B, C] = this.blocks22('LDU');
    let AI: Expr;
    try {
      AI = A.I;
    } catch (e) {
      if (e instanceof NonInvertibleMatrixError) throw new NonInvertibleMatrixError('Block LDU decomposition cannot be calculated when "A" is singular');
      throw e;
    }
    const Ip = new IdentityNode(B.rows);
    const Iq = new IdentityNode(B.cols);
    const Z = new ZeroMatrixNode(B.rows, B.cols);
    const L = BlockMatrixNode.create([
      [Ip, Z],
      [times(C, AI), Iq],
    ]);
    const Dm = BlockDiagMatrixNode.create([A, this.schur()]);
    const U = BlockMatrixNode.create([
      [Ip, times(AI, B)],
      [Z.T, Iq],
    ]);
    return [L, Dm, U];
  }
  /** SymPy UDLdecomposition: [U, D, L] with X = U*D*L for a 2 x 2 block matrix. */
  UDLdecomposition(): [Expr, Expr, Expr] {
    const [A, B, C, D] = this.blocks22('UDL');
    let DI: Expr;
    try {
      DI = D.I;
    } catch (e) {
      if (e instanceof NonInvertibleMatrixError) throw new NonInvertibleMatrixError('Block UDL decomposition cannot be calculated when "D" is singular');
      throw e;
    }
    const Ip = new IdentityNode(A.rows);
    const Iq = new IdentityNode(B.cols);
    const Z = new ZeroMatrixNode(B.rows, B.cols);
    const U = BlockMatrixNode.create([
      [Ip, times(B, DI)],
      [Z.T, Iq],
    ]);
    const Dm = BlockDiagMatrixNode.create([this.schur('D'), D]);
    const L = BlockMatrixNode.create([
      [Ip, Z],
      [times(DI, C), Iq],
    ]);
    return [U, Dm, L];
  }
  /** SymPy LUdecomposition: [L, U] with X = L*U for a 2 x 2 block matrix. */
  LUdecomposition(): [Expr, Expr] {
    const [A0, B, C] = this.blocks22('LU');
    let A: MatrixExpr;
    let AI: Expr;
    try {
      A = asMat(A0.pow(S.Half));
      AI = A.I;
    } catch (e) {
      if (e instanceof NonInvertibleMatrixError) throw new NonInvertibleMatrixError('Block LU decomposition cannot be calculated when "A" is singular');
      throw e;
    }
    const Z = new ZeroMatrixNode(B.rows, B.cols);
    const Q = asMat(this.schur()).pow(S.Half);
    const L = BlockMatrixNode.create([
      [A, Z],
      [times(C, AI), Q],
    ]);
    const U = BlockMatrixNode.create([
      [A, times(AI, B)],
      [Z.T, Q],
    ]);
    return [L, U];
  }
  private blocks22(kind: string): [MatrixExpr, MatrixExpr, MatrixExpr, MatrixExpr] {
    const [r, c] = this.blockshape;
    if (r !== 2 || c !== 2) throw new ShapeError(`Block ${kind} decomposition is supported only for 2x2 block matrices`);
    return [this.block(0, 0), this.block(0, 1), this.block(1, 0), this.block(1, 1)];
  }
  override entry(iIn: Expr, jIn: Expr): Expr {
    let i = iIn;
    let j = jIn;
    const [br, bc] = this.blockshape;
    const rs = this.rowblocksizes;
    let rowBlock = 0;
    for (; rowBlock < rs.length; rowBlock++) {
      const cmp = relTruth('Lt', i, at(rs, rowBlock));
      if (cmp === true) break;
      if (cmp === false) i = add(i, mul(-1, at(rs, rowBlock)));
      else if (rowBlock < br - 1) return new MatrixElementNode(this, iIn, jIn);
      else break;
    }
    rowBlock = Math.min(rowBlock, br - 1);
    const cs = this.colblocksizes;
    let colBlock = 0;
    for (; colBlock < cs.length; colBlock++) {
      const cmp = relTruth('Lt', j, at(cs, colBlock));
      if (cmp === true) break;
      if (cmp === false) j = add(j, mul(-1, at(cs, colBlock)));
      else if (colBlock < bc - 1) return new MatrixElementNode(this, iIn, jIn);
      else break;
    }
    colBlock = Math.min(colBlock, bc - 1);
    return this.block(rowBlock, colBlock).at(i, j);
  }
  override get isIdentity(): Truth {
    const [r, c] = this.blockshape;
    if (r !== c) return false;
    for (let i = 0; i < r; i++) {
      for (let j = 0; j < c; j++) {
        const b = this.block(i, j);
        if (i === j && b.isIdentity !== true) return false;
        if (i !== j && !b.isZeroMatrix) return false;
      }
    }
    return true;
  }
  /** SymPy is_structurally_symmetric: the row and column block sizes agree. */
  get isStructurallySymmetric(): boolean {
    return keysEqual(this.rowblocksizes, this.colblocksizes);
  }
  override equalsExplicit(other: ExprLike | Matrix): boolean {
    const o = toExpr(other);
    if (same(this, o)) return true;
    if (o instanceof BlockMatrixNode && sameList(this.blocks.data, o.blocks.data) && this.blocks.rows === o.blocks.rows) return true;
    return super.equalsExplicit(other);
  }
  override printStr(print: (e: Expr) => string): string {
    return explicitStr(this.blocks, print);
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\left[${explicitLatexContents(this.blocks, print)}\\right]`;
  }
}

/** A tuple of blocks used in sort keys. */
class BlockTuple extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('ImmutableDenseMatrix', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new BlockTuple(args);
  }
}

/** SymPy BlockMatrix(rows): a block matrix from rows of blocks (or an explicit matrix of blocks). */
export const BlockMatrix = /* @__PURE__ */ callableClass(BlockMatrixNode, (rows: Matrix | readonly MatArg[] | readonly (readonly MatArg[])[]): BlockMatrixNode => BlockMatrixNode.create(rows));
export type BlockMatrix = BlockMatrixNode;

/** SymPy BlockDiagMatrix(*mats): a block diagonal matrix. */
export class BlockDiagMatrixNode extends BlockMatrixNode {
  constructor(mats: readonly Expr[]) {
    super(mats, [mats.length, mats.length], 'BlockDiagMatrix');
  }
  /** SymPy BlockDiagMatrix(*mats). */
  static override create(mats: readonly MatArg[]): BlockDiagMatrixNode {
    return new BlockDiagMatrixNode(mats.map((m) => toExpr(m)));
  }
  /** The diagonal blocks (SymPy diag). */
  get diag(): MatrixExpr[] {
    return this.args.map(asMat);
  }
  override get blocks(): Matrix {
    const ms = this.diag;
    return Matrix.fromFunction(ms.length, ms.length, (i, j) => (i === j ? at(ms, i) : new ZeroMatrixNode(at(ms, i).rows, at(ms, j).cols)));
  }
  override get shape(): [Expr, Expr] {
    return [total(this.diag.map((b) => b.rows)), total(this.diag.map((b) => b.cols))];
  }
  override get rowblocksizes(): Expr[] {
    return this.diag.map((b) => b.rows);
  }
  override get colblocksizes(): Expr[] {
    return this.diag.map((b) => b.cols);
  }
  override withArgs(args: readonly Expr[]): Expr {
    return new BlockDiagMatrixNode(args);
  }
  override sortArgs(): readonly Expr[] {
    return this.args;
  }
  /** SymPy _all_square_blocks. */
  allSquareBlocks(): boolean {
    return this.diag.every((m) => m.isSquare === true);
  }
  override evalDeterminant(): Expr {
    if (this.allSquareBlocks()) return mul(...this.diag.map((m) => det(m)));
    return S.Zero;
  }
  override evalInverse(): Expr {
    if (this.allSquareBlocks()) return BlockDiagMatrixNode.create(this.diag.map((m) => m.inverse()));
    throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  }
  override evalTranspose(): Expr {
    return BlockDiagMatrixNode.create(this.diag.map((m) => m.transpose()));
  }
  override blockmul(other: Expr): Expr {
    if (other instanceof BlockDiagMatrixNode && keysEqual(this.colblocksizes, other.rowblocksizes)) {
      return BlockDiagMatrixNode.create(this.diag.map((a, k) => times(a, at(other.diag, k))));
    }
    return super.blockmul(other);
  }
  override blockadd(other: Expr): Expr {
    if (
      other instanceof BlockDiagMatrixNode &&
      this.blockshape[0] === other.blockshape[0] &&
      keysEqual(this.rowblocksizes, other.rowblocksizes) &&
      keysEqual(this.colblocksizes, other.colblocksizes)
    ) {
      return BlockDiagMatrixNode.create(this.diag.map((a, k) => plus(a, at(other.diag, k))));
    }
    return super.blockadd(other);
  }
  /** SymPy get_diag_blocks: the diagonal blocks. */
  getDiagBlocks(): MatrixExpr[] {
    return this.diag;
  }
}

/** SymPy BlockDiagMatrix(*mats). */
export const BlockDiagMatrix = /* @__PURE__ */ callableClass(BlockDiagMatrixNode, (...mats: MatArg[]): BlockDiagMatrixNode => BlockDiagMatrixNode.create(mats));
export type BlockDiagMatrix = BlockDiagMatrixNode;

// ---------------------------------------------------------------------------
// block_collapse
// ---------------------------------------------------------------------------

type Rule = (e: Expr) => Expr;

const isBlock = (e: Expr): e is BlockMatrixNode => e instanceof BlockMatrixNode;

const exhaust =
  (rule: Rule): Rule =>
  (e0) => {
    let e = e0;
    for (;;) {
      const r = rule(e);
      if (same(r, e)) return e;
      e = r;
    }
  };

const doOne =
  (...rules: Rule[]): Rule =>
  (e) => {
    for (const rule of rules) {
      const r = rule(e);
      if (!same(r, e)) return r;
    }
    return e;
  };

function bottomUp(rule: Rule, e: Expr): Expr {
  if (!e.args.length) return rule(e);
  const args = e.args.map((a) => bottomUp(rule, a));
  const r = sameList(args, e.args) ? e : e instanceof ExtensionExpr ? e.withArgs(args) : rebuild(e, args);
  return rule(r);
}

function bcUnpack(e: Expr): Expr {
  const b = cast(e, BlockMatrixNode);
  const [r, c] = b.blockshape;
  return r === 1 && c === 1 ? b.block(0, 0) : e;
}

function bcMatAdd(e: Expr): Expr {
  const blocks = e.args.filter(isBlock);
  if (!blocks.length) return e;
  const nonblocks = e.args.filter((a) => !isBlock(a));
  let block: Expr = at(blocks, 0);
  for (const b of blocks.slice(1)) block = cast(block, BlockMatrixNode).blockadd(b);
  if (nonblocks.length) return plus(MatAddNode.create(nonblocks), block);
  return block;
}

function bcBlockPlusIdent(e: Expr): Expr {
  const idents = e.args.filter((a) => a instanceof MatrixExpr && a.isIdentity === true);
  if (!idents.length) return e;
  const blocks = e.args.filter(isBlock);
  if (blocks.length && blocks.every((b) => b.structurallyEqual(at(blocks, 0))) && at(blocks, 0).isStructurallySymmetric) {
    const blockId = BlockDiagMatrixNode.create(at(blocks, 0).rowblocksizes.map((k) => new IdentityNode(k)));
    const rest = e.args.filter((a) => !(a instanceof MatrixExpr && a.isIdentity === true) && !isBlock(a));
    return MatAddNode.create([times(blockId, sympify(idents.length)), ...blocks, ...rest]).doit();
  }
  return e;
}

function bcDist(e: Expr): Expr {
  const [factor, mat] = cast(e, MatrixExpr).asCoeffMmul();
  if (same(factor, S.One)) return e;
  const unpacked = unpackMat(mat);
  if (unpacked instanceof BlockDiagMatrixNode) return BlockDiagMatrixNode.create(unpacked.diag.map((m) => times(factor, m)));
  if (unpacked instanceof BlockMatrixNode) return BlockMatrixNode.create(unpacked.blocks.map((b) => times(factor, b)));
  return e;
}

function bcMatMul(e: Expr): Expr {
  let factor: Expr;
  let matrices: Expr[];
  if (e instanceof MatPowNode) {
    const k = e.exp;
    if (isInt(k) && k.p > 0n) {
      factor = S.One;
      matrices = Array.from({ length: Number(k.p) }, () => e.base);
    } else return e;
  } else {
    const [f, ms] = cast(e, MatMulNode).asCoeffMatrices();
    factor = f;
    matrices = ms;
  }
  let i = 0;
  while (i + 1 < matrices.length) {
    const A = at(matrices, i);
    const B = at(matrices, i + 1);
    if (isBlock(A) && isBlock(B)) {
      matrices[i] = A.blockmul(B);
      matrices.splice(i + 1, 1);
    } else if (isBlock(A)) {
      matrices[i] = A.blockmul(BlockMatrixNode.create([[B]]));
      matrices.splice(i + 1, 1);
    } else if (isBlock(B)) {
      matrices[i] = BlockMatrixNode.create([[A]]).blockmul(B);
      matrices.splice(i + 1, 1);
    } else i++;
  }
  return times(factor, ...matrices);
}

function bcTranspose(e: Expr): Expr {
  return asMat(blockCollapse(at(e.args, 0))).evalTranspose();
}

function bcInverse(e: Expr): Expr {
  const inv = cast(e, InverseNode);
  if (inv.arg instanceof BlockDiagMatrixNode) return inv.arg.inverse();
  // SymPy's blockinverse_1x1 never applies: bottom_up unpacks a 1 x 1 block matrix before its inverse is visited
  return blockinverse2x2(new InverseNode(reblock2x2(inv.arg)));
}

function blockinverse2x2(e: InverseNode): Expr {
  const a = e.arg;
  if (!(a instanceof BlockMatrixNode) || a.blockshape[0] !== 2 || a.blockshape[1] !== 2) return e;
  const [A, B, C, D] = [a.block(0, 0), a.block(0, 1), a.block(1, 0), a.block(1, 1)];
  const formula = choose2x2InversionFormula(A, B, C, D);
  if (formula === undefined) return e;
  const MI = asMat(a.schur(formula)).I;
  const neg = (x: Expr) => times(S.NegOne, x);
  switch (formula) {
    case 'A': {
      const AI = A.I;
      return BlockMatrixNode.create([
        [plus(AI, times(AI, B, MI, C, AI)), neg(times(AI, B, MI))],
        [neg(times(MI, C, AI)), MI],
      ]);
    }
    case 'B': {
      const BI = B.I;
      return BlockMatrixNode.create([
        [neg(times(MI, D, BI)), MI],
        [plus(BI, times(BI, A, MI, D, BI)), neg(times(BI, A, MI))],
      ]);
    }
    case 'C': {
      const CI = C.I;
      return BlockMatrixNode.create([
        [neg(times(CI, D, MI)), plus(CI, times(CI, D, MI, A, CI))],
        [MI, neg(times(MI, A, CI))],
      ]);
    }
    case 'D': {
      const DI = D.I;
      return BlockMatrixNode.create([
        [MI, neg(times(MI, B, DI))],
        [neg(times(DI, C, MI)), plus(DI, times(DI, C, MI, B, DI))],
      ]);
    }
  }
}

/** SymPy _choose_2x2_inversion_formula: the block whose inverse the block inversion uses. */
function choose2x2InversionFormula(A: MatrixExpr, B: MatrixExpr, C: MatrixExpr, D: MatrixExpr): 'A' | 'B' | 'C' | 'D' | undefined {
  const inv = [askInvertible(A), askInvertible(B), askInvertible(C), askInvertible(D)];
  const names = ['A', 'B', 'C', 'D'] as const;
  for (let k = 0; k < 4; k++) if (inv[k] === true) return names[k];
  for (let k = 0; k < 4; k++) if (inv[k] !== false) return names[k];
  return undefined;
}

/** SymPy deblock: a BlockMatrix of BlockMatrices flattened. */
export function deblock(B: Expr): Expr {
  if (!(B instanceof BlockMatrixNode) || !B.blocks.data.some((b) => hasNode(b, isBlock))) return B;
  const bb = B.blocks.map((x) => (isBlock(x) ? x : BlockMatrixNode.create([[x]])));
  const inner = (i: number, j: number): Matrix => cast(bb.get(i, j), BlockMatrixNode).blocks;
  const rows: Expr[][] = [];
  for (let r = 0; r < bb.rows; r++) {
    const h = inner(r, 0).rows;
    for (let c = 0; c < bb.cols; c++) if (inner(r, c).rows !== h) return B;
    for (let k = 0; k < h; k++) rows.push(Array.from({ length: bb.cols }, (_, c) => at(inner(r, c).toArray(), k)).flat());
  }
  if (new Set(rows.map((r) => r.length)).size > 1) return B;
  return BlockMatrixNode.create(Matrix.of(rows));
}

/** SymPy reblock_2x2: a block matrix regrouped into 2 x 2 blocks of block matrices. */
export function reblock2x2(expr: Expr): Expr {
  if (!(expr instanceof BlockMatrixNode) || !expr.blockshape.every((d) => d > 2)) return expr;
  const [rowblocks, colblocks] = expr.blockshape;
  const blocks = expr.blocks;
  const sub = (r0: number, r1: number, c0: number, c1: number): Expr =>
    bcUnpack(BlockMatrixNode.create(Matrix.fromFunction(r1 - r0, c1 - c0, (i, j) => blocks.get(r0 + i, c0 + j))));
  for (let i = 1; i < rowblocks; i++) {
    for (let j = 1; j < colblocks; j++) {
      const A = sub(0, i, 0, j);
      const B = sub(0, i, j, colblocks);
      const C = sub(i, rowblocks, 0, j);
      const D = sub(i, rowblocks, j, colblocks);
      if (choose2x2InversionFormula(asMat(A), asMat(B), asMat(C), asMat(D)) !== undefined) {
        return BlockMatrixNode.create([
          [A, B],
          [C, D],
        ]);
      }
    }
  }
  return BlockMatrixNode.create([
    [blocks.get(0, 0), BlockMatrixNode.create(Matrix.fromFunction(1, colblocks - 1, (_, j) => blocks.get(0, j + 1)))],
    [BlockMatrixNode.create(Matrix.fromFunction(rowblocks - 1, 1, (i) => blocks.get(i + 1, 0))), BlockMatrixNode.create(Matrix.fromFunction(rowblocks - 1, colblocks - 1, (i, j) => blocks.get(i + 1, j + 1)))],
  ]);
}

const conditionedRule: Rule = (e) => {
  if (!(e instanceof MatrixExpr) || !hasNode(e, isBlock)) return e;
  switch (e.name) {
    case 'MatAdd':
      return doOne(bcMatAdd, bcBlockPlusIdent)(e);
    case 'MatMul':
      return doOne(bcMatMul, bcDist)(e);
    case 'MatPow':
      return bcMatMul(e);
    case 'Transpose':
      return bcTranspose(e);
    case 'Inverse':
      return bcInverse(e);
    case 'BlockMatrix':
      return doOne(bcUnpack, deblock)(e);
    default:
      return e;
  }
};

/**
 * SymPy block_collapse(expr): a matrix expression with block matrices
 * evaluated blockwise (block products, sums, transposes and inverses).
 */
export function blockCollapse(expr: MatArg): Expr {
  const rule = exhaust((e) => bottomUp(exhaust(conditionedRule), e));
  return doitArg(rule(toExpr(expr)));
}

/** SymPy bounds(sizes): consecutive [low, high) pairs. */
export function bounds(sizes: readonly number[]): [number, number][] {
  let low = 0;
  return sizes.map((s) => {
    const r: [number, number] = [low, low + s];
    low += s;
    return r;
  });
}

/** SymPy blockcut(expr, rowsizes, colsizes): a matrix cut into blocks of slices. */
export function blockcut(expr: MatArg, rowsizes: readonly number[], colsizes: readonly number[]): BlockMatrixNode {
  const rb = bounds(rowsizes);
  const cb = bounds(colsizes);
  return BlockMatrixNode.create(rb.map((r) => cb.map((c) => MatrixSliceNode.create(expr, r, c))));
}
