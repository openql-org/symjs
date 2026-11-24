// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (solvers/ode/systems.py), BSD-3-Clause; see LICENSE.

import { NonSquareMatrixError, NotImplementedError } from '../core/errors';
import { type Expr, Integral, S, Sym } from '../core/nodes';
import { exp, mul } from '../core/ops';
import { subs } from '../core/traverse';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { jordanForm } from '../matrices/linalg';
import { simplify } from '../simplify/simplify';
import { linodesolveType } from './odesystem';

/** Parameters for a first-order linear matrix ODE. */
export interface LinodesolveOptions {
  /** The inhomogeneous forcing vector. */
  b?: Matrix;
  /** An antiderivative of the coefficient matrix. */
  B?: Matrix;
  /** The classification of the linear system. */
  type?: 'auto' | 'type1' | 'type2' | 'type3' | 'type4';
  /** Whether to evaluate integrals in the solution. */
  doit?: boolean;
  /** The independent variable after a change of variables. */
  tau?: Expr;
}

function exponential(A: Matrix, scale: Expr = S.One): Matrix {
  if (A.data.every((e, i) => Math.floor(i / A.cols) === i % A.cols || e.equals(S.Zero))) return Matrix.diag(...Array.from({ length: A.rows }, (_, i) => exp(mul(A.get(i, i), scale))));
  const [P, J] = jordanForm(A);
  const diagonal = Matrix.diag(...Array.from({ length: J.rows }, (_, i) => J.get(i, i)));
  const N = J.sub(diagonal).scale(scale);
  let series = Matrix.eye(J.rows), term = series;
  for (let k = 1; k < J.rows; k++) {
    term = term.mul(N).scale(S.One.div(k));
    series = series.add(term);
  }
  const D = Matrix.diag(...Array.from({ length: J.rows }, (_, i) => exp(mul(J.get(i, i), scale))));
  return P.mul(D).mul(series).mul(P.inv()).map((e) => simplify(e));
}

/**
 * Solves X'(t) = A(t) X(t) + b(t) when A commutes with its antiderivative.
 *
 * @param A - The square coefficient matrix.
 * @param t - The independent variable.
 * @param opts - The linodesolve settings.
 * @returns The solution components in dependent-variable order.
 * @throws TypeError when the coefficient input is not a matrix.
 * @throws NonSquareMatrixError when the coefficient matrix is not square.
 * @throws RangeError when the forcing vector has incompatible dimensions.
 * @throws NotImplementedError when the matrix does not commute with its antiderivative.
 * @see SymPy `sympy.solvers.ode.systems.linodesolve`
 * @example
 * ```ts
 * import { Matrix, linodesolve, symbols } from '@symjs/symjs';
 *
 * const [t] = symbols('t');
 * linodesolve(Matrix.of([[1]]), t); // => [C1*exp(t)]
 * ```
 */
export function linodesolve(A: Matrix, t: Sym, opts: LinodesolveOptions = {}): Expr[] {
  if (!(A instanceof Matrix)) throw new TypeError('linodesolve: coefficients must be a matrix');
  if (A.rows !== A.cols) throw new NonSquareMatrixError('linodesolve: coefficients must be square');
  const { b, B, type = 'auto' } = opts;
  if (b !== undefined && (!(b instanceof Matrix) || b.rows !== A.rows || b.cols !== 1)) throw new RangeError('linodesolve: incompatible forcing vector');
  if (B !== undefined) {
    if (!(B instanceof Matrix)) throw new TypeError('linodesolve: antiderivative must be a matrix');
    if (B.rows !== B.cols) throw new NonSquareMatrixError('linodesolve: antiderivative must be square');
    if (B.rows !== A.rows) throw new RangeError('linodesolve: incompatible antiderivative');
  }
  if (!['auto', 'type1', 'type2', 'type3', 'type4'].includes(type)) throw new RangeError('linodesolve: unsupported system type');
  // Classification also verifies commutativity for variable coefficient matrices.
  const classification = type === 'auto' ? linodesolveType(A, t, b).get('type_of_equation') : type;
  const primitive = classification === 'type1' || classification === 'type2' ? A.scale(t) : B ?? A.map((e) => integrate(e, t));
  if (A.mul(primitive).sub(primitive.mul(A)).data.some((e) => !simplify(e).equals(S.Zero))) throw new NotImplementedError('linodesolve: noncommuting antiderivative');
  const constant = classification === 'type1' || classification === 'type2';
  const fundamental = constant ? exponential(A, t) : exponential(primitive);
  const used = new Set([t, opts.tau ?? t, ...primitive.data, ...(b?.data ?? [])].flatMap((e) => [...e.freeSymbols()].map((s) => s.key)));
  let index = 0;
  const constants = Matrix.col(...Array.from({ length: A.rows }, () => {
    let c: Sym;
    do { c = new Sym(`C${++index}`); } while (used.has(c.key));
    return c;
  }));
  const forcing = b === undefined ? Matrix.zeros(A.rows, 1) : (constant ? exponential(A, mul(-1, t)) : exponential(primitive.scale(-1))).mul(b).map((e) => {
    if (e.equals(S.Zero)) return S.Zero;
    return opts.doit === true ? integrate(e, t) : new Integral([e, t]);
  });
  const solution = fundamental.mul(constants.add(forcing)).data;
  return solution.map((e) => opts.tau === undefined ? e : subs(e, [[t, opts.tau]]));
}
