// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (matrices/normalforms.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The Smith and Hermite normal forms of a Matrix (SymPy
 * smith_normal_form, smith_normal_decomp, is_smith_normal_form,
 * invariant_factors, hermite_normal_form), computed on its DomainMatrix.
 */

import type { Expr } from '../core/nodes';
import type { Domain } from '../polys/domains';
import { DomainMatrix } from '../polys/matrices/domainmatrix';
import { hermiteNormalForm as hnf, invariantFactors as invf, isSmithNormalForm as isSnf, smithNormalDecomp as snd, smithNormalForm as snf } from '../polys/matrices/normalforms';
import type { Matrix } from './matrix';
import type { MutableDenseMatrix } from './mutable';

/** The DomainMatrix of a Matrix, converted to the domain if one is given. */
function toDomain(m: Matrix, domain?: Domain): DomainMatrix {
  const dM = DomainMatrix.fromMatrix(m);
  return domain ? dM.convertTo(domain) : dM;
}

/**
 * The Smith normal form of a matrix over a
 * principal ideal domain (of a DomainMatrix, as a DomainMatrix: SymPy
 * sympy.polys.matrices.normalforms.smith_normal_form).
 * @param m - The input matrix.
 * @param domain - The coefficient domain for the calculation.
 * @returns The diagonal Smith form over the chosen domain.
 * @see SymPy `sympy.matrices.normalforms.smith_normal_form`
 * @example
 * ```ts
 * import { Matrix, smithNormalForm } from '@symjs/symjs';
 * smithNormalForm(Matrix.of([[2, 4]])); // => Matrix([[2, 0]])
 * ```
 */
export function smithNormalForm(m: Matrix, domain?: Domain): MutableDenseMatrix;
export function smithNormalForm(m: DomainMatrix): DomainMatrix;
export function smithNormalForm(m: Matrix | DomainMatrix, domain?: Domain): MutableDenseMatrix | DomainMatrix {
  if (m instanceof DomainMatrix) return snf(m);
  return snf(toDomain(m, domain)).toMatrix();
}

/**
 * Tests whether the matrix is diagonal with each invariant factor dividing its successor.
 * @param m - The input matrix.
 * @param domain - The coefficient domain for the calculation.
 * @returns Whether the matrix satisfies the Smith divisibility conditions.
 * @see SymPy `sympy.matrices.normalforms.is_smith_normal_form`
 * @example
 * ```ts
 * import { Matrix, isSmithNormalForm } from '@symjs/symjs';
 * isSmithNormalForm(Matrix.of([[]])); // => True
 * ```
 */
export function isSmithNormalForm(m: Matrix | DomainMatrix, domain?: Domain): boolean {
  return isSnf(m instanceof DomainMatrix ? m : toDomain(m, domain));
}

/**
 * Return the Smith Normal Decomposition of a matrix `m` over the ring
 * `domain`.
 * @param m - The input matrix.
 * @param domain - The coefficient domain for the calculation.
 * @returns The Smith form and the left and right transformations.
 * @see SymPy `sympy.matrices.normalforms.smith_normal_decomp`
 * @example
 * ```ts
 * import { Matrix, ZZ, smithNormalDecomp } from '@symjs/symjs';
 *
 * const M = Matrix.of([[12, 6, 4], [3, 9, 6], [2, 16, 14]]);
 * const [D, S, T] = smithNormalDecomp(M, ZZ);
 * S.mul(M).mul(T).equals(D); // => True
 * ```
 */
export function smithNormalDecomp(m: Matrix, domain?: Domain): [MutableDenseMatrix, MutableDenseMatrix, MutableDenseMatrix];
export function smithNormalDecomp(m: DomainMatrix): [DomainMatrix, DomainMatrix, DomainMatrix];
export function smithNormalDecomp(m: Matrix | DomainMatrix, domain?: Domain): [MutableDenseMatrix, MutableDenseMatrix, MutableDenseMatrix] | [DomainMatrix, DomainMatrix, DomainMatrix] {
  if (m instanceof DomainMatrix) return snd(m);
  const [a, s, t] = snd(toDomain(m, domain));
  return [a.toMatrix(), s.toMatrix(), t.toMatrix()];
}

/**
 * The invariant factors of a matrix over a principal ideal domain (domain elements for a DomainMatrix).
 * @param m - The input matrix.
 * @param domain - The coefficient domain for the calculation.
 * @returns The diagonal invariant factors in divisibility order.
 * @see SymPy `sympy.matrices.normalforms.invariant_factors`
 */
export function invariantFactors(m: Matrix | DomainMatrix, domain?: Domain): Expr[] {
  if (m instanceof DomainMatrix) return invf(m);
  const dM = toDomain(m, domain);
  return invf(dM).map((f) => dM.domain.toSympy(f));
}

/**
 * The Hermite normal form of an integer matrix;
 * with D (a positive multiple of the determinant of a full-rank matrix) the
 * computation is done modulo D.
 * @param A - The input matrix.
 * @param opts - The optional determinant multiple `D` and whether to verify full row rank with `checkRank`.
 * @returns The Hermite normal form over the integers.
 * @see SymPy `sympy.matrices.normalforms.hermite_normal_form`
 * @remarks SymPy prints this result as `Matrix([[1], [0], [0]])`.
 * @example
 * ```ts
 * import { Matrix, hermiteNormalForm } from '@symjs/symjs';
 * hermiteNormalForm(Matrix.of([[2, 7], [0, 0], [0, 0]])); // => Matrix([
 * //   [1],
 * //   [0],
 * //   [0]])
 * ```
 */
export function hermiteNormalForm(A: Matrix, opts?: { D?: bigint | number | Expr; checkRank?: boolean }): MutableDenseMatrix;
export function hermiteNormalForm(A: DomainMatrix, opts?: { D?: bigint | number | Expr; checkRank?: boolean }): DomainMatrix;
export function hermiteNormalForm(A: Matrix | DomainMatrix, opts: { D?: bigint | number | Expr; checkRank?: boolean } = {}): MutableDenseMatrix | DomainMatrix {
  const D = opts.D === undefined ? undefined : typeof opts.D === 'object' ? BigInt(String(opts.D)) : opts.D;
  if (A instanceof DomainMatrix) return hnf(A, { D, checkRank: opts.checkRank });
  return hnf(DomainMatrix.fromMatrix(A), { D, checkRank: opts.checkRank }).toMatrix();
}
