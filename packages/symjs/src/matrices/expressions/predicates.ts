// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Matrix predicates of SymPy's assumption system (Q.invertible,
 * Q.orthogonal, Q.symmetric, ...), their queries (ask) and the refine
 * handlers of matrix expressions (refine_Transpose, refine_Inverse,
 * refine_MatMul, refine_Determinant).
 */

import type { Expr } from '../../core/nodes';
import { ExtensionExpr, S } from '../../core/nodes';
import { isIntegerQ, isNegative, isZero } from '../../core/assumptions';
import { rebuild } from '../../core/traverse';
import type { Truth } from '../../core/truth';
import { str } from '../../printing/str';
import { simplify } from '../../simplify/simplify';
import type { MatArg } from './matexpr';
import {
  AdjointNode,
  DeterminantNode,
  IdentityNode,
  ImmutableMatrixNode,
  InverseNode,
  MatAddNode,
  MatMulNode,
  MatPowNode,
  MatrixExpr,
  MatrixSliceNode,
  OneMatrixNode,
  TransposeNode,
  ZeroMatrixNode,
  toExpr,
} from './matexpr';
import { isInt, same, sameList } from './util';

/** Names of the matrix predicates (SymPy Q.<name>). */
export type MatrixPredicateName =
  | 'invertible'
  | 'singular'
  | 'orthogonal'
  | 'unitary'
  | 'symmetric'
  | 'diagonal'
  | 'square'
  | 'upper_triangular'
  | 'lower_triangular'
  | 'unit_triangular'
  | 'positive_definite'
  | 'fullrank';

/**
 * A matrix predicate applied to a matrix expression, such as
 * Q.orthogonal(X) (SymPy AppliedPredicate).
 *
 * @experimental May change in a minor release.
 */
export class MatrixPredicate {
  constructor(
    readonly name: MatrixPredicateName,
    readonly arg: Expr,
  ) {}
  toString(): string {
    return `Q.${this.name}(${str(this.arg)})`;
  }
}

/** One matrix predicate or a conjunction (array) of them. */
export type MatrixAssumption = MatrixPredicate | readonly MatrixPredicate[];

const pred =
  (name: MatrixPredicateName) =>
  (x: MatArg): MatrixPredicate =>
    new MatrixPredicate(name, toExpr(x));

/**
 * The matrix predicates of SymPy's Q (Q.orthogonal(X), Q.symmetric(X), ...).
 *
 * @experimental May change in a minor release.
 */
export const MatrixQ = {
  invertible: pred('invertible'),
  singular: pred('singular'),
  orthogonal: pred('orthogonal'),
  unitary: pred('unitary'),
  symmetric: pred('symmetric'),
  diagonal: pred('diagonal'),
  square: pred('square'),
  upper_triangular: pred('upper_triangular'),
  lower_triangular: pred('lower_triangular'),
  unit_triangular: pred('unit_triangular'),
  positive_definite: pred('positive_definite'),
  fullrank: pred('fullrank'),
} as const;

const flatten = (a: MatrixAssumption | undefined): readonly MatrixPredicate[] => (a === undefined ? [] : a instanceof MatrixPredicate ? [a] : a);

/** Predicates implied by an assumed predicate (SymPy's matrix fact rules). */
const IMPLIES: Partial<Record<MatrixPredicateName, MatrixPredicateName[]>> = {
  orthogonal: ['unitary', 'invertible', 'square', 'fullrank'],
  unitary: ['invertible', 'square', 'fullrank'],
  positive_definite: ['invertible', 'square', 'fullrank'],
  invertible: ['square', 'fullrank'],
  symmetric: ['square'],
  diagonal: ['symmetric', 'upper_triangular', 'lower_triangular', 'square'],
  unit_triangular: ['invertible', 'square'],
};

function assumed(name: MatrixPredicateName, m: Expr, assumptions: readonly MatrixPredicate[]): Truth {
  for (const p of assumptions) {
    if (!same(p.arg, m)) continue;
    if (p.name === name || (IMPLIES[p.name] ?? []).includes(name)) return true;
    if ((name === 'singular' && (p.name === 'invertible' || (IMPLIES[p.name] ?? []).includes('invertible'))) || (name === 'invertible' && p.name === 'singular')) return false;
  }
  return 'unknown';
}

const all = (xs: readonly Truth[]): Truth => (xs.every((x) => x === true) ? true : xs.some((x) => x === false) ? false : 'unknown');
const notT = (t: Truth): Truth => (t === 'unknown' ? t : !t);

/**
 * SymPy ask(Q.<name>(M), assumptions) for the matrix predicates: true,
 * false or 'unknown'.
 *
 * @experimental May change in a minor release.
 */
export function askMatrix(p: MatrixPredicate, assumptions?: MatrixAssumption): Truth {
  return askPred(p.name, p.arg, flatten(assumptions));
}

function askPred(name: MatrixPredicateName, m: Expr, as: readonly MatrixPredicate[]): Truth {
  if (!(m instanceof MatrixExpr)) return false;
  const a = assumed(name, m, as);
  if (a !== 'unknown') return a;
  switch (name) {
    case 'square':
      return m.isSquare;
    case 'singular':
      return notT(askPred('invertible', m, as));
    case 'invertible':
      return askInvertible(m, as);
    case 'fullrank':
      return askPred('invertible', m, as) === true ? true : 'unknown';
    case 'orthogonal':
    case 'unitary': {
      if (m instanceof IdentityNode) return true;
      if (m instanceof ZeroMatrixNode) return false;
      if (name === 'unitary' && askPred('orthogonal', m, as) === true) return true;
      if (m instanceof TransposeNode || m instanceof InverseNode || m instanceof AdjointNode) return askPred(name, m.arg, as);
      if (m instanceof MatMulNode) {
        const [c, ms] = m.asCoeffMatrices();
        if (!same(c, S.One)) return 'unknown';
        return all(ms.map((x) => askPred(name, x, as)));
      }
      if (m instanceof MatPowNode && isInt(m.exp)) return askPred(name, m.base, as);
      return 'unknown';
    }
    case 'symmetric': {
      if (m.isSquare === false) return false;
      if (m instanceof IdentityNode || m instanceof ZeroMatrixNode) return true;
      if (askPred('diagonal', m, as) === true) return true;
      if (m instanceof TransposeNode || m instanceof InverseNode) return askPred(name, m.arg, as);
      if (m instanceof MatAddNode) return all(m.args.map((x) => askPred(name, x, as)));
      if (m instanceof MatMulNode) {
        const [, ms] = m.asCoeffMatrices();
        if (ms.length === 2 && same(ms[1]!, ms[0]!.transpose())) return true;
        if (ms.every((x) => askPred(name, x, as) === true) && sameList(ms, [...ms].reverse())) return true;
        return 'unknown';
      }
      if (m instanceof MatPowNode && isInt(m.exp)) return askPred(name, m.base, as);
      return 'unknown';
    }
    case 'diagonal':
      if (m instanceof IdentityNode || m instanceof ZeroMatrixNode) return true;
      if (m instanceof TransposeNode || m instanceof InverseNode) return askPred(name, m.arg, as);
      if (m.name === 'DiagMatrix' || m.name === 'DiagonalMatrix') return true;
      return 'unknown';
    case 'upper_triangular':
    case 'lower_triangular':
      if (m instanceof IdentityNode || m instanceof ZeroMatrixNode) return true;
      if (askPred('diagonal', m, as) === true) return true;
      return 'unknown';
    case 'unit_triangular':
      if (m instanceof IdentityNode) return true;
      return 'unknown';
    case 'positive_definite':
      if (m instanceof IdentityNode) return true;
      return 'unknown';
  }
}

/** SymPy ask(Q.invertible(M), assumptions) with SymPy's handlers. */
export function askInvertible(m: Expr, assumptions: readonly MatrixPredicate[] = []): Truth {
  if (!(m instanceof MatrixExpr)) return 'unknown';
  const a = assumed('invertible', m, assumptions);
  if (m instanceof MatMulNode) {
    const [c, ms] = m.asCoeffMatrices();
    if (isZero(c) === true) return false;
    const r = all(ms.map((x) => askInvertible(x, assumptions)));
    return r === 'unknown' ? a : r;
  }
  if (m instanceof InverseNode || m instanceof IdentityNode) return true;
  if (m instanceof MatPowNode) {
    if (isIntegerQ(m.exp) !== true) return a;
    return isNegative(m.exp) === false ? askInvertible(m.base, assumptions) : a;
  }
  if (m instanceof MatAddNode) return a;
  if (m instanceof ZeroMatrixNode) return false;
  if (m instanceof OneMatrixNode) return same(m.rows, S.One) && same(m.cols, S.One);
  if (m instanceof TransposeNode || m instanceof AdjointNode) return askInvertible(m.arg, assumptions);
  if (m instanceof MatrixSliceNode) return m.onDiag ? askInvertible(m.parent, assumptions) : a;
  // MatrixSymbol, explicit matrices and the other matrix expressions: not known to be square means singular
  if (m.isSquare !== true) return false;
  if (a !== 'unknown') return a;
  if (m instanceof ImmutableMatrixNode) {
    const z = isZero(simplify(m.matrix.det()));
    return z === undefined ? 'unknown' : !z;
  }
  if (m.name === 'BlockDiagMatrix') return all(m.args.map((x) => askInvertible(x, assumptions)));
  return 'unknown';
}

// ---------------------------------------------------------------------------
// refine
// ---------------------------------------------------------------------------

function refineNode(e: Expr, as: readonly MatrixPredicate[]): Expr {
  if (e instanceof TransposeNode) return askPred('symmetric', e, as) === true ? e.arg : e;
  if (e instanceof InverseNode) {
    if (askPred('orthogonal', e, as) === true) return e.arg.transpose();
    // the inverse of a unitary matrix is its conjugate transpose (SymPy returns the conjugate)
    if (askPred('unitary', e, as) === true) return e.arg.adjoint();
    if (askPred('singular', e, as) === true) throw new RangeError(`Inverse of singular matrix ${str(e.arg)}`);
    return e;
  }
  if (e instanceof MatMulNode) {
    const newargs: Expr[] = [];
    const exprargs: MatrixExpr[] = [];
    for (const a of e.args) {
      if (a instanceof MatrixExpr) exprargs.push(a);
      else newargs.push(a);
    }
    let last: MatrixExpr = exprargs[0]!;
    for (const arg of exprargs.slice(1)) {
      if (same(arg, last.T) && askPred('orthogonal', arg, as) === true) last = new IdentityNode(arg.rows);
      // X*Adjoint(X) = I for a unitary X (SymPy compares with the conjugate, which is not the inverse)
      else if (same(arg, last.adjoint()) && askPred('unitary', arg, as) === true) last = new IdentityNode(arg.rows);
      else {
        newargs.push(last);
        last = arg;
      }
    }
    newargs.push(last);
    return MatMulNode.create(newargs);
  }
  if (e instanceof DeterminantNode) {
    if (askPred('orthogonal', e.arg, as) === true) return S.One;
    if (askPred('singular', e.arg, as) === true) return S.Zero;
    if (askPred('unit_triangular', e.arg, as) === true) return S.One;
    return e;
  }
  return e;
}

/**
 * SymPy refine(expr, assumptions) for matrix expressions with the matrix
 * predicates: refine(X.T, Q.symmetric(X)) = X, refine(X.I, Q.orthogonal(X))
 * = X.T, refine(X*X.T, Q.orthogonal(X)) = I, refine(det(X), Q.orthogonal(X)) = 1.
 *
 * @experimental May change in a minor release.
 */
export function refineMatrix(expr: MatArg, assumptions?: MatrixAssumption): Expr {
  const as = flatten(assumptions);
  const go = (e: Expr): Expr => {
    if (!e.args.length) return e;
    const args = e.args.map(go);
    const r = sameList(args, e.args) ? e : e instanceof ExtensionExpr ? e.withArgs(args) : rebuild(e, args);
    return refineNode(r, as);
  };
  return go(toExpr(expr));
}
