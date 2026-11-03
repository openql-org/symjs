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

/** SymPy FunctionMatrix(rows, cols, lamda): the matrix with entries lamda(i, j). */
export class FunctionMatrixNode extends MatrixExpr {
  constructor(rows: Expr, cols: Expr, lamda: LambdaNode) {
    super('FunctionMatrix', [rows, cols, lamda]);
  }
  /** SymPy FunctionMatrix(rows, cols, lamda). */
  static create(rows: ExprLike, cols: ExprLike, lamda: IndexFunction): FunctionMatrixNode {
    return new FunctionMatrixNode(checkDim(sympify(rows)), checkDim(sympify(cols)), toLambda2(lamda));
  }
  get shape(): [Expr, Expr] {
    return pair(this.args);
  }
  /** The function of the indices. */
  get lamda(): LambdaNode {
    return cast(at(this.args, 2), LambdaNode);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new FunctionMatrixNode(at(args, 0), at(args, 1), cast(at(args, 2), LambdaNode));
  }
  override entry(i: Expr, j: Expr): Expr {
    return this.lamda.call(i, j);
  }
  override evalTrace(): Expr {
    return new TraceNode(this).rewriteAsSum();
  }
}

/** SymPy FunctionMatrix(rows, cols, lamda). */
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

/** SymPy DFT(n): the unitary discrete Fourier transform matrix, entries w**(i*j)/sqrt(n) with w = exp(-2*pi*I/n). */
export class DFTNode extends MatrixExpr {
  constructor(n: ExprLike, name = 'DFT') {
    super(name, [checkDim(sympify(n))]);
  }
  /** The size (SymPy DFT.n; n is evalf in symjs). */
  get size(): Expr {
    return first(this.args);
  }
  get shape(): [Expr, Expr] {
    return [this.size, this.size];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DFTNode(first(args));
  }
  override entry(i: Expr, j: Expr): Expr {
    return dftEntry(this.size, mul(i, j));
  }
  override evalInverse(): Expr {
    return new IDFTNode(this.size);
  }
  override printLatex(): string {
    return `\\text{${this.name}}_{${latex(this.size)}}`;
  }
}

/** SymPy IDFT(n): the inverse discrete Fourier transform matrix. */
export class IDFTNode extends DFTNode {
  constructor(n: ExprLike) {
    super(n, 'IDFT');
  }
  override withArgs(args: readonly Expr[]): Expr {
    return new IDFTNode(first(args));
  }
  override entry(i: Expr, j: Expr): Expr {
    return dftEntry(this.size, mul(-1, i, j));
  }
  override evalInverse(): Expr {
    return new DFTNode(this.size);
  }
}

/** SymPy DFT(n). */
export const DFT = /* @__PURE__ */ callableClass(DFTNode, (n: ExprLike): DFTNode => new DFTNode(n));
export type DFT = DFTNode;

/** SymPy IDFT(n). */
export const IDFT = /* @__PURE__ */ callableClass(IDFTNode, (n: ExprLike): IDFTNode => new IDFTNode(n));
export type IDFT = IDFTNode;
