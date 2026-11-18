// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The matrix handlers of ask (SymPy sympy.assumptions.handlers.matrices):
 * Q.square, Q.invertible, Q.orthogonal, ... of matrix expressions and the
 * element predicates (Q.integer_elements(X) makes X[i, j] an integer) are
 * answered by the matrix predicates of matrices/expressions/predicates.ts.
 * Loading this module registers the handlers.
 */

import { ExtensionExpr, S, type Expr } from '../../core/nodes';
import { isIntegerQ } from '../../core/assumptions';
import { BoolOp } from '../../core/boolalg';
import { AppliedPredicate, ask, registerHandler } from '../../core/refine';
import type { Truth } from '../../core/truth';
import type { MatrixPredicateName } from '../../matrices/expressions/predicates';
import { MatrixPredicate, askMatrix } from '../../matrices/expressions/predicates';
import { DeterminantNode, IdentityNode, ImmutableMatrixNode, InverseNode, MatAddNode, MatMulNode, MatPowNode, MatrixElementNode, MatrixExpr, MatrixSliceNode, OneMatrixNode, TraceNode, TransposeNode, ZeroMatrixNode } from '../../matrices/expressions/matexpr';
import { BlockMatrixNode } from '../../matrices/expressions/blockmatrix';
import { at } from '../../core/guard';

const MATRIX_PREDICATES: readonly MatrixPredicateName[] = [
  'invertible', 'singular', 'orthogonal', 'unitary', 'symmetric', 'diagonal', 'square', 'upper_triangular', 'lower_triangular', 'unit_triangular', 'positive_definite', 'fullrank',
];
const isMatrixPredicate = (n: string): n is MatrixPredicateName => (MATRIX_PREDICATES as readonly string[]).includes(n);

/** The conjuncts of the assumptions. */
const conjuncts = (a: Expr): readonly Expr[] => (a instanceof BoolOp && a.op === 'And' ? a.args : [a]);

/** The matrix predicates among the assumptions (~Q.invertible(X) is Q.singular(X)). */
function matrixAssumptions(a: Expr): MatrixPredicate[] {
  const out: MatrixPredicate[] = [];
  for (const c of conjuncts(a)) {
    if (c instanceof AppliedPredicate && isMatrixPredicate(c.predicate)) out.push(new MatrixPredicate(c.predicate, c.arg));
    if (c instanceof BoolOp && c.op === 'Not') {
      const p = at(c.args, 0);
      if (p instanceof AppliedPredicate && p.predicate === 'invertible') out.push(new MatrixPredicate('singular', p.arg));
    }
  }
  return out;
}

/** The predicate is assumed of e. */
const holds = (a: Expr, name: string, e: Expr): boolean => conjuncts(a).some((c) => c instanceof AppliedPredicate && c.predicate === name && c.arg.equals(e));

for (const name of MATRIX_PREDICATES) {
  registerHandler(name, (e: Expr, a: Expr): Truth => {
    if (!(e instanceof MatrixExpr)) return 'unknown';
    const rec = (p: MatrixPredicateName, x: Expr): Truth => ask(new AppliedPredicate(p, [x]), a);
    const tiny = e.rows.equals(e.cols) && (e.rows.equals(S.One) || e.rows.equals(S.Zero));
    if (tiny && ['symmetric', 'diagonal', 'upper_triangular', 'lower_triangular'].includes(name)) return true;
    if (e instanceof OneMatrixNode && ['diagonal', 'upper_triangular', 'lower_triangular', 'fullrank', 'positive_definite'].includes(name)) return e.rows.equals(S.One) && e.cols.equals(S.One);
    if (e instanceof OneMatrixNode && name === 'symmetric') return e.isSquare;
    if (e instanceof BlockMatrixNode) {
      if (e.args.length === 1) return rec(name, at(e.args, 0));
      if (name === 'invertible' && e.args.every((block) => block instanceof ImmutableMatrixNode)) return rec(name, new ImmutableMatrixNode(e.asExplicit()));
    }
    if (e instanceof MatrixSliceNode && e.onDiag && ['symmetric', 'diagonal', 'upper_triangular', 'lower_triangular', 'positive_definite'].includes(name)) {
      if (rec(name, e.parent) === true) return true;
    }
    const as = matrixAssumptions(a);
    const r = askMatrix(new MatrixPredicate(name, e), as);
    if (r !== 'unknown') return r;
    // SymPy's handlers that the matrix predicates do not have
    if (e.isSquare === false && (name === 'orthogonal' || name === 'unitary' || name === 'positive_definite')) return false;
    if (name === 'diagonal' && holds(a, 'lower_triangular', e) && holds(a, 'upper_triangular', e)) return true;
    if (e instanceof MatPowNode && isIntegerQ(e.exp) === true && ['diagonal', 'upper_triangular', 'lower_triangular', 'fullrank'].includes(name)) {
      if (rec(name, e.base) === true) return true;
    }
    if (name === 'symmetric' && e instanceof MatMulNode) {
      const [, ms] = e.asCoeffMatrices();
      if (ms.length === 3 && at(ms, 0).equals(at(ms, 2).transpose()) && rec('symmetric', at(ms, 1)) === true) return true;
    }
    if (name === 'upper_triangular' || name === 'lower_triangular' || name === 'diagonal') {
      if (e instanceof TransposeNode) return rec(name === 'diagonal' ? name : name === 'upper_triangular' ? 'lower_triangular' : 'upper_triangular', e.arg);
      if (e instanceof InverseNode) return rec(name, e.arg);
      if (e instanceof MatAddNode || e instanceof MatMulNode) {
        const ms = e instanceof MatMulNode ? e.asCoeffMatrices()[1] : e.args;
        if (ms.every((x) => rec(name, x) === true)) return true;
      }
    }
    if (name === 'positive_definite') {
      if (e instanceof ZeroMatrixNode) return false;
      if (e instanceof TransposeNode || e instanceof InverseNode) return rec(name, e.arg);
    }
    if (name === 'fullrank') {
      if (e instanceof ZeroMatrixNode) return false;
      if (e instanceof TransposeNode || e instanceof InverseNode) return rec('fullrank', e.arg);
      if (e instanceof MatMulNode && e.args.every((x) => !(x instanceof MatrixExpr) || rec('fullrank', x) === true)) return true;
    }
    if (name === 'positive_definite' && e instanceof MatAddNode && e.args.every((x) => rec('positive_definite', x) === true)) return true;
    // a square matrix of full rank is invertible (SymPy's fact rules)
    if (name === 'invertible' || name === 'singular') {
      const sq = askMatrix(new MatrixPredicate('square', e), as);
      if (sq === true && holds(a, 'fullrank', e)) return name === 'invertible';
    }
    return 'unknown';
  });
}

// the entries of a matrix whose elements are integers (reals, complex numbers)
for (const [name, elements] of [['integer', 'integer_elements'], ['real', 'real_elements'], ['complex', 'complex_elements']] as const) {
  registerHandler(name, (e: Expr, a: Expr): Truth => (e instanceof MatrixElementNode && holds(a, elements, e.parent) ? true : 'unknown'));
}

// Entry sets are closed under matrix sums, products and integer powers.
for (const [name, scalar] of [['integer_elements', 'integer'], ['real_elements', 'real'], ['complex_elements', 'complex']] as const) {
  registerHandler(name, (e: Expr, a: Expr): Truth => {
    const rec = (x: Expr): Truth => ask(new AppliedPredicate(name, [x]), a);
    if (e instanceof IdentityNode || e instanceof ZeroMatrixNode || e instanceof OneMatrixNode) return true;
    if (e instanceof MatrixExpr && (e.name === 'DFT' || e.name === 'IDFT') && name === 'complex_elements') return true;
    if (e instanceof MatrixExpr && e.name === 'LofLU' && name !== 'integer_elements') return rec(at(e.args, 0));
    if (e instanceof MatrixSliceNode) return rec(e.parent);
    if (e instanceof TransposeNode || e instanceof DeterminantNode || e instanceof TraceNode) return rec(e.arg);
    if (e instanceof InverseNode && name !== 'integer_elements' && ask(new AppliedPredicate('invertible', [e.arg]), a) === true) return rec(e.arg);
    if (e instanceof MatPowNode && isIntegerQ(e.exp) === true) {
      if (ask(new AppliedPredicate('nonnegative', [e.exp]), a) === true || (name !== 'integer_elements' && ask(new AppliedPredicate('invertible', [e.base]), a) === true)) return rec(e.base);
    }
    if (e instanceof MatAddNode || e instanceof BlockMatrixNode || (e instanceof ExtensionExpr && e.name === 'HadamardProduct')) return e.args.every((x) => rec(x) === true) ? true : 'unknown';
    if (e instanceof MatMulNode) {
      const [c, ms] = e.asCoeffMatrices();
      if (ask(new AppliedPredicate(scalar, [c]), a) === true && ms.every((x) => rec(x) === true)) return true;
    }
    return 'unknown';
  });
}

for (const [name, elements] of [['integer', 'integer_elements'], ['real', 'real_elements'], ['complex', 'complex_elements']] as const) {
  registerHandler(name, (e: Expr, a: Expr): Truth => {
    if (e instanceof TraceNode || e instanceof DeterminantNode) return ask(new AppliedPredicate(elements, [e.arg]), a);
    return 'unknown';
  });
}
registerHandler('positive', (e: Expr, a: Expr): Truth => {
  if (e instanceof TraceNode || e instanceof DeterminantNode) return ask(new AppliedPredicate('positive_definite', [e.arg]), a);
  if (e instanceof MatrixElementNode && e.i.equals(e.j)) return ask(new AppliedPredicate('positive_definite', [e.parent]), a);
  return 'unknown';
});
