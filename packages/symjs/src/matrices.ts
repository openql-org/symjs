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
export { MutableDenseMatrix, MutableMatrix } from './matrices/mutable';
export { ImmutableSparseMatrix, MutableSparseMatrix, SparseMatrix } from './matrices/sparse';
export type { MatrixPosition, SparseData, SparseMatrixArgs, SparseValue } from './matrices/sparse';
// SymPy ImmutableDenseMatrix is ImmutableMatrix
export { ImmutableMatrix as ImmutableDenseMatrix } from './matrices/expressions/matexpr';
export { DomainMatrix, toDM } from './matrices/domainmatrix';
export { Matrix as MatrixBase } from './matrices/matrix';
export { MatrixTranspose, MatrixAdjoint } from './matrices/matexpr';
// matrix expressions (SymPy sympy.matrices.expressions)
export * from './matrices/expressions/index';
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
  isPositiveDefinite,
  isPositiveSemidefinite,
  isNegativeDefinite,
  isNegativeSemidefinite,
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
  liupc,
  rowStructureSymbolicCholesky,
  irregular,
  jordanForm,
  rrefRhs,
  rankDecomposition,
  invMod,
  permuteRows,
  permuteCols,
  matrixSolve,
  solveLeastSquares,
  gramSchmidt as GramSchmidt,
  normalized,
  hessian,
  wronskian,
  casoratian,
  pinvSolve,
  multiplyElementwise,
  matrixMultiplyElementwise,
  companion,
  permanent,
  connectedComponents,
  stronglyConnectedComponents,
  diagonalSolve,
  lowerTriangularSolve,
  upperTriangularSolve,
  choleskySolve,
  cramerSolve,
  inverseADJ,
  inverseBLOCK,
  inverseCH,
  inverseGE,
  inverseLDL,
  inverseLU,
  inverseQR,
  conditionNumber,
  leftEigenvects,
} from './matrices/linalg';
export {
  berkowitz,
  berkowitzEigenvals,
  berkowitzMinors,
  bidiagonalize,
  bidiagonalDecomposition,
  upperHessenbergDecomposition,
  singularValueDecomposition,
  luDecompositionSimple as LUdecompositionSimple,
  luDecompositionFF as LUdecompositionFF,
  lll,
  lllTransform,
  elementaryRowOp,
  elementaryColOp,
  permuteFwd,
  permuteBkwd,
  rowDel,
  colDel,
  getDiagBlocks,
  connectedComponentsDecomposition,
  stronglyConnectedComponentsDecomposition,
  jordanCell,
  jordanCells,
  dual,
  iterItems,
  iterValues,
  key2ij,
  key2bounds,
  printNonzero,
  table,
  wilkinson,
  randMatrix,
  symarray,
  matrix2numpy,
  list2numpy,
  type ElementaryOp,
  type IndexSlice,
  type TableOptions,
  type RandMatrixOptions,
} from './matrices/more';

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
