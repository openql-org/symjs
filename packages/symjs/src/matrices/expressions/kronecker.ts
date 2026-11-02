// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy KroneckerProduct (sympy.matrices.expressions.kronecker): the
 * tensor product of matrices, kronecker_product and combine_kronecker.
 */

import { callableClass } from '../../core/callable';
import type { Expr } from '../../core/nodes';
import { ExtensionExpr, S } from '../../core/nodes';
import { mul, pow } from '../../core/ops';
import { rebuild } from '../../core/traverse';
import { adjoint as adjointFn } from '../../functions/elementary';
import { Matrix } from '../matrix';
import type { DoitHints, MatArg } from './matexpr';
import {
  DeterminantNode,
  IdentityNode,
  ImmutableMatrixNode,
  InverseNode,
  MatAddNode,
  MatMulNode,
  MatPowNode,
  MatrixElementNode,
  MatrixExpr,
  ShapeError,
  det,
  doitArg,
  hasNode,
  parenLatex,
  toExpr,
  trace,
  transposeOf,
} from './matexpr';
import { PRECEDENCE, isInt, same, sameList, toInt } from './util';

const isKron = (e: Expr): e is KroneckerProductNode => e instanceof KroneckerProductNode;

/** SymPy KroneckerProduct(*args): the Kronecker (tensor) product of matrices. */
export class KroneckerProductNode extends MatrixExpr {
  constructor(args: readonly Expr[]) {
    super('KroneckerProduct', args);
  }
  /** SymPy KroneckerProduct(*args): identities give an identity; validated, unevaluated. */
  static create(argsIn: readonly MatArg[], check = true): Expr {
    const args = argsIn.map(toExpr);
    if (args.length && args.every((a) => a instanceof MatrixExpr && a.isIdentity === true)) {
      const ret = new IdentityNode(mul(...args.map((a) => (a as MatrixExpr).rows)));
      if (args.every((a) => a instanceof ImmutableMatrixNode)) return new ImmutableMatrixNode(ret.asExplicit());
      return ret;
    }
    if (check && !args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    return new KroneckerProductNode(args);
  }
  get shape(): [Expr, Expr] {
    const ms = this.args as MatrixExpr[];
    return [mul(...ms.map((m) => m.rows)), mul(...ms.map((m) => m.cols))];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new KroneckerProductNode(args);
  }
  override entry(i0: Expr, j0: Expr): Expr {
    const ms = this.args as MatrixExpr[];
    if (!isInt(i0) || !isInt(j0) || !ms.every((m) => isInt(m.rows) && isInt(m.cols))) return new MatrixElementNode(this, i0, j0);
    let i = toInt(i0);
    let j = toInt(j0);
    let result: Expr = S.One;
    for (const m of [...ms].reverse()) {
      const r = toInt(m.rows);
      const c = toInt(m.cols);
      const a = i % r;
      const b = j % c;
      i = Math.floor(i / r);
      j = Math.floor(j / c);
      result = mul(result, m.at(a, b));
    }
    return result;
  }
  override evalAdjoint(): Expr {
    return doitKron(this.args.map((a) => adjointFn(a)));
  }
  override evalConjugate(): Expr {
    return doitKron(this.args.map((a) => (a as MatrixExpr).conjugate()));
  }
  override evalTranspose(): Expr {
    return doitKron(this.args.map(transposeOf));
  }
  override evalTrace(): Expr {
    return mul(...this.args.map((a) => trace(a)));
  }
  override evalDeterminant(): Expr {
    const ms = this.args as MatrixExpr[];
    if (!ms.every((a) => a.isSquare === true)) return new DeterminantNode(this);
    const m = this.rows;
    return mul(...ms.map((a) => pow(det(a), mul(m, pow(a.rows, -1)))));
  }
  override evalInverse(): Expr {
    try {
      return KroneckerProductNode.create(this.args.map((a) => (a as MatrixExpr).inverse()));
    } catch (e) {
      if (e instanceof ShapeError) return new InverseNode(this);
      throw e;
    }
  }
  /** SymPy structurally_equal: Kronecker products with factors of the same shapes. */
  structurallyEqual(other: Expr): boolean {
    return (
      other instanceof KroneckerProductNode &&
      sameList(this.shape, other.shape) &&
      this.args.length === other.args.length &&
      this.args.every((a, k) => sameList((a as MatrixExpr).shape, (other.args[k] as MatrixExpr).shape))
    );
  }
  /** SymPy has_matching_shape: the factors can be multiplied factorwise. */
  hasMatchingShape(other: Expr): boolean {
    return (
      other instanceof KroneckerProductNode &&
      same(this.cols, other.rows) &&
      this.args.length === other.args.length &&
      this.args.every((a, k) => same((a as MatrixExpr).cols, (other.args[k] as MatrixExpr).rows))
    );
  }
  /** SymPy _eval_expand_kroneckerproduct: distributed over sums of the factors. */
  expandKroneckerProduct(): Expr {
    let products: Expr[][] = [[]];
    for (const f of this.args) {
      const terms = f instanceof MatAddNode ? f.args : [f];
      products = products.flatMap((p) => terms.map((t) => [...p, t]));
    }
    if (products.length === 1) return this;
    return MatAddNode.create(products.map((p) => new KroneckerProductNode(p)));
  }
  override expandSelf(hint: string): Expr | undefined {
    return hint === 'kroneckerproduct' ? this.expandKroneckerProduct() : undefined;
  }
  /** SymPy _kronecker_add. */
  kroneckerAdd(other: Expr): Expr {
    if (this.structurallyEqual(other)) return new KroneckerProductNode(this.args.map((a, k) => MatAddNode.create([a, other.args[k]!]).doit()));
    return MatAddNode.create([this, other]).doit();
  }
  /** SymPy _kronecker_mul. */
  kroneckerMul(other: Expr): Expr {
    if (this.hasMatchingShape(other)) return new KroneckerProductNode(this.args.map((a, k) => times(a, other.args[k]!)));
    return times(this, other);
  }
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return canonicalizeKron(KroneckerProductNode.create(args));
  }
  override strPrecedence(): number {
    return PRECEDENCE.Mul;
  }
  override printLatex(): string {
    return this.args.map((a) => parenLatex(a, PRECEDENCE.Pow, true)).join(' \\otimes ');
  }
}

function times(...xs: Expr[]): Expr {
  const r = MatMulNode.create(xs);
  return r instanceof MatrixExpr ? r.doit() : r;
}

function doitKron(args: readonly Expr[]): Expr {
  const r = KroneckerProductNode.create(args);
  return r instanceof MatrixExpr ? r.doit() : r;
}

/** SymPy KroneckerProduct(*args). */
export const KroneckerProduct = /* @__PURE__ */ callableClass(KroneckerProductNode, (...args: MatArg[]): Expr => KroneckerProductNode.create(args));
export type KroneckerProduct = KroneckerProductNode;

/** SymPy kronecker_product(*matrices): the evaluated Kronecker product (explicit for explicit factors). */
export function kroneckerProduct(...matrices: MatArg[]): Expr {
  if (!matrices.length) throw new TypeError('Empty Kronecker product is undefined');
  if (matrices.length === 1) return toExpr(matrices[0]!);
  return doitKron(matrices.map(toExpr));
}

/** SymPy matrix_kronecker_product(*matrices): the Kronecker product of explicit matrices. */
export function matrixKroneckerProduct(...matrices: Matrix[]): Matrix {
  if (!matrices.length || !matrices.every((m) => m instanceof Matrix)) throw new TypeError('Sequence of Matrices expected');
  return matrices.slice(1).reduce((a, b) => a.kron(b), matrices[0]!);
}

function extractCommutative(kron: KroneckerProductNode): Expr {
  const cPart: Expr[] = [];
  const ncPart: Expr[] = [];
  for (const arg of kron.args) {
    if (arg instanceof MatMulNode) {
      cPart.push(...arg.args.filter((a) => !(a instanceof MatrixExpr) && a.isCommutative));
      const nc = arg.args.filter((a) => a instanceof MatrixExpr || !a.isCommutative);
      ncPart.push(nc.length === 1 ? nc[0]! : new MatMulNode(nc));
    } else ncPart.push(arg);
  }
  const c = mul(...cPart);
  if (!same(c, S.One)) return times(c, new KroneckerProductNode(ncPart));
  return kron;
}

/** SymPy kronecker.canonicalize. */
function canonicalizeKron(e0: Expr): Expr {
  let e = e0;
  for (;;) {
    if (!isKron(e)) return e;
    let next: Expr = e;
    if (e.args.length === 1) next = e.args[0]!;
    else if (e.args.every((a) => a instanceof ImmutableMatrixNode)) next = new ImmutableMatrixNode(matrixKroneckerProduct(...e.args.map((a) => (a).matrix)));
    else if (e.args.some(isKron)) next = new KroneckerProductNode(e.args.flatMap((a) => (isKron(a) ? a.args : [a])));
    else next = extractCommutative(e);
    if (same(next, e)) return e;
    e = next;
  }
}

const dimsKey = (e: Expr): string => (isKron(e) ? e.args.map((a) => (a as MatrixExpr).shape.map((s) => s.key).join('x')).join(';') : '');

function kroneckerMatAdd(e: Expr): Expr {
  const groups = new Map<string, Expr[]>();
  const nonkrons: Expr[] = [];
  for (const a of e.args) {
    const k = dimsKey(a);
    if (!k) nonkrons.push(a);
    else groups.set(k, [...(groups.get(k) ?? []), a]);
  }
  if (!groups.size) return e;
  const krons = [...groups.values()].map((g) => g.slice(1).reduce((x, y) => (isKron(x) ? x.kroneckerAdd(y) : MatAddNode.create([x, y]).doit()), g[0]!));
  if (!nonkrons.length) return MatAddNode.create(krons);
  return MatAddNode.create([...krons, ...nonkrons]).doit();
}

function kroneckerMatMul(e: Expr): Expr {
  const [factor, ms] = (e as MatMulNode).asCoeffMatrices();
  const matrices: Expr[] = [...ms];
  let i = 0;
  while (i < matrices.length - 1) {
    const A = matrices[i]!;
    const B = matrices[i + 1]!;
    if (isKron(A) && isKron(B)) {
      matrices[i] = A.kroneckerMul(B);
      matrices.splice(i + 1, 1);
    } else i++;
  }
  return times(factor, MatMulNode.create(matrices));
}

function kroneckerMatPow(e: Expr): Expr {
  const p = e as MatPowNode;
  if (isKron(p.base) && p.base.args.every((a) => (a as MatrixExpr).isSquare === true)) {
    return new KroneckerProductNode(p.base.args.map((a) => MatPowNode.create(a, p.exp)));
  }
  return e;
}

/**
 * SymPy combine_kronecker(expr): sums, products and powers of Kronecker
 * products with matching factors combined factorwise.
 */
export function combineKronecker(exprIn: MatArg): Expr {
  const haskron = (e: Expr): boolean => e instanceof MatrixExpr && hasNode(e, isKron);
  const rule = (e: Expr): Expr => {
    if (!haskron(e) || !(e instanceof MatrixExpr)) return e;
    switch (e.name) {
      case 'MatAdd':
        return kroneckerMatAdd(e);
      case 'MatMul':
        return kroneckerMatMul(e);
      case 'MatPow':
        return kroneckerMatPow(e);
      default:
        return e;
    }
  };
  const exhaust = (f: (e: Expr) => Expr) => (e0: Expr) => {
    let e = e0;
    for (;;) {
      const r = f(e);
      if (same(r, e)) return e;
      e = r;
    }
  };
  const bottomUp = (f: (e: Expr) => Expr, e: Expr): Expr => {
    if (!e.args.length) return f(e);
    const args = e.args.map((a) => bottomUp(f, a));
    const r = sameList(args, e.args) ? e : e instanceof ExtensionExpr ? e.withArgs(args) : rebuild(e, args);
    return f(r);
  };
  const result = exhaust((e) => bottomUp(exhaust(rule), e))(toExpr(exprIn));
  return doitArg(result);
}
