// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/matrices`: matrices and linear algebra.
 */

// every entry point brings the core with its registrations
import './core';

export { Matrix } from './matrices/matrix';
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
  ldl,
  luDecomposition,
  qrDecomposition,
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
  jordanBlock, pinvSolve, multiplyElementwise, companion, permanent, connectedComponents, stronglyConnectedComponents } from './matrices/linalg';
