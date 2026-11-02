// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/matrices`: matrices and linear algebra.
 */

// every entry point brings the core with its registrations
import './core';

export {
  Matrix,
} from './matrices/matrix';
export { MatrixSymbol, MatrixTranspose, MatrixAdjoint } from './matrices/matexpr';
export * as linalg from './matrices/linalg';
export {
  rref,
  echelonForm,
  rank,
  nullspace,
  columnspace,
  rowspace,
  eigenvects,
  isDiagonalizable,
  diagonalize,
  matrixExp,
  matrixLog,
  analyticFunc,
  cholesky,
  ldl as LDLdecomposition,
  luDecomposition as LUdecomposition,
  qrDecomposition as QRdecomposition,
  dot,
  cross,
  singularValues,
  norm,
  pinv,
  jacobian,
  blockDiag,
  rotAxis1,
  rotAxis2,
  rotAxis3,
  rotCcwAxis1,
  rotCcwAxis2,
  rotCcwAxis3,
  rotGivens,
  jordanBlock,
  gaussJordanSolve,
  matrixSolve,
  solveLeastSquares,
  gramSchmidt as GramSchmidt,
  normalized,
  hessian,
  wronskian,
  casoratian,
  pinvSolve,
  multiplyElementwise,
  companion,
  permanent,
  connectedComponents,
  stronglyConnectedComponents,
} from './matrices/linalg';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { ldl as _ldl_ } from './matrices/linalg';
import { luDecomposition as _luDecomposition_ } from './matrices/linalg';
import { qrDecomposition as _qrDecomposition_ } from './matrices/linalg';

/** @deprecated Use `LDLdecomposition`. */
export const ldl = _ldl_;

/** @deprecated Use `LUdecomposition`. */
export const luDecomposition = _luDecomposition_;

/** @deprecated Use `QRdecomposition`. */
export const qrDecomposition = _qrDecomposition_;
