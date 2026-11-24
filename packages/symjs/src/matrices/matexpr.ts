// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Matrix expressions (SymPy sympy.matrices.expressions): symbolic
 * matrices `MatrixSymbol('A', n, m)` that do not commute, with their
 * transposes (`A.T`) and adjoints (`Adjoint(A)`). The implementation lives
 * in `./expressions`; this module keeps the names of the first version.
 */

export { MatrixSymbol } from './expressions/matexpr';

/**
 * Represents the unevaluated transpose of a matrix expression.
 *
 * @see SymPy `sympy.matrices.expressions.transpose.Transpose`
 */
export { TransposeNode as MatrixTranspose } from './expressions/matexpr';

/**
 * Represents the unevaluated conjugate transpose of a matrix expression.
 *
 * @see SymPy `sympy.matrices.expressions.adjoint.Adjoint`
 */
export { AdjointNode as MatrixAdjoint } from './expressions/matexpr';
