// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Matrix expressions (SymPy sympy.matrices.expressions): symbolic
 * matrices `MatrixSymbol('A', n, m)` that do not commute, with their
 * transposes (`A.T`) and adjoints (`Adjoint(A)`). The implementation lives
 * in `./expressions`; this module keeps the names of the first version.
 */

export { MatrixSymbol } from './expressions/matexpr';

/** SymPy Transpose (the node class of transposes). */
export { TransposeNode as MatrixTranspose } from './expressions/matexpr';

/** SymPy Adjoint (the node class of adjoints). */
export { AdjointNode as MatrixAdjoint } from './expressions/matexpr';
