// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The matrix handlers of ask (SymPy sympy.assumptions.handlers.matrices):
 * Q.square, Q.invertible, Q.orthogonal, ... of matrix expressions and the
 * element predicates (Q.integer_elements(X) makes X[i, j] an integer) are
 * answered by the matrix predicates of matrices/expressions/predicates.ts.
 * Loading this module registers the handlers.
 */

import type { Expr } from '../../core/nodes';
import { BoolOp } from '../../core/boolalg';
import { AppliedPredicate, ask, registerHandler } from '../../core/refine';
import type { Truth } from '../../core/truth';
import type { MatrixPredicateName } from '../../matrices/expressions/predicates';
import { MatrixPredicate, askMatrix } from '../../matrices/expressions/predicates';
import { InverseNode, MatAddNode, MatMulNode, MatrixElementNode, MatrixExpr, TransposeNode, ZeroMatrixNode } from '../../matrices/expressions/matexpr';
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
    const as = matrixAssumptions(a);
    const r = askMatrix(new MatrixPredicate(name, e), as);
    if (r !== 'unknown') return r;
    const rec = (p: MatrixPredicateName, x: Expr): Truth => ask(new AppliedPredicate(p, [x]), a);
    // SymPy's handlers that the matrix predicates do not have
    if (e.isSquare === false && (name === 'orthogonal' || name === 'unitary' || name === 'positive_definite')) return false;
    if (name === 'diagonal' && holds(a, 'lower_triangular', e) && holds(a, 'upper_triangular', e)) return true;
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
