// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy's matrix expressions (sympy.matrices.expressions): symbolic
 * matrices and the expressions built from them.
 */

export {
  MatrixExpr,
  MatScalar,
  ShapeError,
  Str,
  MatrixSymbol,
  ImmutableMatrix,
  MatrixElement,
  Identity,
  GenericIdentity,
  ZeroMatrix,
  GenericZeroMatrix,
  OneMatrix,
  MatAdd,
  MatMul,
  MatPow,
  Inverse,
  Transpose,
  Adjoint,
  MatrixSlice,
  Trace,
  Determinant,
  Permanent,
  ElementwiseApplyFunction,
  trace,
  det,
  per,
  matrixSymbols,
  matrixElement,
  isMatrix,
  isMataddValid,
  isMatmulValid,
  isSquare,
  validateMatAdd,
  validateMatMul,
  mergeExplicitMatAdd,
  mergeExplicitMatMul,
  onlySquares,
  toExpr as sympifyMatrix,
} from './matexpr';
export type { MatArg, DoitHints, SliceSpec, ElementFunction, EntryContext } from './matexpr';
export { BlockMatrix, BlockDiagMatrix, blockCollapse, blockcut, bounds, deblock, reblock2x2 } from './blockmatrix';
export { HadamardProduct, HadamardPower, hadamardProduct, hadamardPower, canonicalize } from './hadamard';
export { KroneckerProduct, kroneckerProduct, matrixKroneckerProduct, combineKronecker } from './kronecker';
export { DiagonalMatrix, DiagonalOf, DiagMatrix, diagonalizeVector } from './diagonal';
export { FunctionMatrix, DFT, IDFT } from './funcmatrix';
export type { IndexFunction } from './funcmatrix';
export { PermutationMatrix, MatrixPermute, PermutationNode } from './permutation';
export type { PermutationLike } from './permutation';
export {
  DotProduct,
  CompanionMatrix,
  MatrixSet,
  FactorizationNode as Factorization,
  LofLU,
  UofLU,
  LofCholesky,
  UofCholesky,
  QofQR,
  RofQR,
  EigenVectors,
  EigenValues,
  UofSVD,
  SofSVD,
  VofSVD,
  lu,
  qr,
  eig,
  svd,
} from './misc';
export { MatrixQ, MatrixPredicate, askMatrix, refineMatrix } from './predicates';
export type { MatrixPredicateName, MatrixAssumption } from './predicates';
export { fromIndexSummation } from './indexsum';
