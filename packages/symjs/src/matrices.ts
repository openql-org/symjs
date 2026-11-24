// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/matrices`: matrices and linear algebra.
 */

// every entry point brings the core with its registrations
import './core';
// the methods that simplify (inv, eigenvals, simplify, rref of symbolic entries, ...) call it late-bound
import './simplify/simplify';
// Matrix differentiation uses tensor contractions, including for named subpath imports.
import './tensor/array/arrayderivatives';
// the matrix handlers of ask (Q.invertible, Q.symmetric, ... of matrix expressions) register on load
import './assumptions/handlers/matrices';
import { Matrix as MatrixClass } from './matrices/matrix';
import { registerTableFormMatrix } from './printing/tableform';

// TableForm.asMatrix (printing, a lower layer) builds its matrix with the matrices
registerTableFormMatrix((rows) => MatrixClass.of(rows));

export {
  Matrix, classof,
} from './matrices/matrix';
export { MutableDenseMatrix, MutableMatrix } from './matrices/mutable';
export { ImmutableSparseMatrix, MutableSparseMatrix, SparseMatrix } from './matrices/sparse';
export { banded } from './matrices/sparsetools';
export type { BandedArgs, BandedDiagonals, BandedOptions, BandedValue } from './matrices/sparsetools';
export type { MatrixPosition, SparseData, SparseMatrixArgs, SparseValue } from './matrices/sparse';
// SymPy ImmutableDenseMatrix is ImmutableMatrix
export { ImmutableMatrix as ImmutableDenseMatrix } from './matrices/expressions/matexpr';
export { DomainMatrix, toDM } from './matrices/domainmatrix';
export { smithNormalForm, isSmithNormalForm, smithNormalDecomp, invariantFactors, hermiteNormalForm } from './matrices/normalforms';
export { Matrix as MatrixBase } from './matrices/matrix';
export { MatrixTranspose, MatrixAdjoint } from './matrices/matexpr';
// matrix expressions (SymPy sympy.matrices.expressions)
export * from './matrices/expressions/index';
export * as linalg from './matrices/linalg';
export {
  rref,
  echelonForm,
  isEchelon,
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
  isIndefinite,
  isStronglyDiagonallyDominant,
  isWeaklyDiagonallyDominant,
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
  blockDiagSized,
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

/**
 * Alias for {@link LDLdecomposition}.
 *
 * @deprecated Use {@link LDLdecomposition}.
 * @param m - The matrix to decompose.
 * @param hermitian - Whether to use conjugate transposition during decomposition.
 * @returns The unit lower triangular factor and diagonal factor.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LDLdecomposition`
 * @example
 * ```ts
 * import { Matrix, ldl } from '@symjs/symjs';
 *
 * ldl(Matrix.of([[4, 2], [2, 3]]))[1].get(1, 1); // => 2
 * ```
 */
export const ldl = _ldl_;

/**
 * Alias for {@link LUdecomposition}.
 *
 * @deprecated Use {@link LUdecomposition}.
 * @param m - The matrix to decompose.
 * @returns The lower and upper triangular factors and the row swaps.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LUdecomposition`
 * @example
 * ```ts
 * import { Matrix, luDecomposition } from '@symjs/symjs';
 *
 * luDecomposition(Matrix.of([[1, 2], [3, 4]]))[1].get(1, 1); // => -2
 * ```
 */
export const luDecomposition = _luDecomposition_;

/**
 * Alias for {@link QRdecomposition}.
 *
 * @deprecated Use {@link QRdecomposition}.
 * @param m - The matrix to decompose.
 * @returns The orthogonal and upper triangular factors.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.QRdecomposition`
 * @example
 * ```ts
 * import { Matrix, qrDecomposition } from '@symjs/symjs';
 *
 * qrDecomposition(Matrix.of([[3], [4]]))[1].get(0, 0); // => 5
 * ```
 */
export const qrDecomposition = _qrDecomposition_;
export { MatrixKind, MatrixKindNode } from './matrices/kind';
