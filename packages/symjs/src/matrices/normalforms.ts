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
 * SymPy smith_normal_form: the Smith normal form of a matrix over a
 * principal ideal domain (of a DomainMatrix, as a DomainMatrix: SymPy
 * sympy.polys.matrices.normalforms.smith_normal_form).
 */
export function smithNormalForm(m: Matrix, domain?: Domain): MutableDenseMatrix;
export function smithNormalForm(m: DomainMatrix): DomainMatrix;
export function smithNormalForm(m: Matrix | DomainMatrix, domain?: Domain): MutableDenseMatrix | DomainMatrix {
  if (m instanceof DomainMatrix) return snf(m);
  return snf(toDomain(m, domain)).toMatrix();
}

/** SymPy is_smith_normal_form. */
export function isSmithNormalForm(m: Matrix | DomainMatrix, domain?: Domain): boolean {
  return isSnf(m instanceof DomainMatrix ? m : toDomain(m, domain));
}

/** SymPy smith_normal_decomp: [smf, s, t] with smf = s*m*t (DomainMatrices for a DomainMatrix). */
export function smithNormalDecomp(m: Matrix, domain?: Domain): [MutableDenseMatrix, MutableDenseMatrix, MutableDenseMatrix];
export function smithNormalDecomp(m: DomainMatrix): [DomainMatrix, DomainMatrix, DomainMatrix];
export function smithNormalDecomp(m: Matrix | DomainMatrix, domain?: Domain): [MutableDenseMatrix, MutableDenseMatrix, MutableDenseMatrix] | [DomainMatrix, DomainMatrix, DomainMatrix] {
  if (m instanceof DomainMatrix) return snd(m);
  const [a, s, t] = snd(toDomain(m, domain));
  return [a.toMatrix(), s.toMatrix(), t.toMatrix()];
}

/** SymPy invariant_factors: the invariant factors of a matrix over a principal ideal domain (domain elements for a DomainMatrix). */
export function invariantFactors(m: Matrix | DomainMatrix, domain?: Domain): Expr[] {
  if (m instanceof DomainMatrix) return invf(m);
  const dM = toDomain(m, domain);
  return invf(dM).map((f) => dM.domain.toSympy(f));
}

/**
 * SymPy hermite_normal_form: the Hermite normal form of an integer matrix;
 * with D (a positive multiple of the determinant of a full-rank matrix) the
 * computation is done modulo D.
 */
export function hermiteNormalForm(A: Matrix, opts?: { D?: bigint | number | Expr; checkRank?: boolean }): MutableDenseMatrix;
export function hermiteNormalForm(A: DomainMatrix, opts?: { D?: bigint | number | Expr; checkRank?: boolean }): DomainMatrix;
export function hermiteNormalForm(A: Matrix | DomainMatrix, opts: { D?: bigint | number | Expr; checkRank?: boolean } = {}): MutableDenseMatrix | DomainMatrix {
  const D = opts.D === undefined ? undefined : typeof opts.D === 'object' ? BigInt(String(opts.D)) : opts.D;
  if (A instanceof DomainMatrix) return hnf(A, { D, checkRank: opts.checkRank });
  return hnf(DomainMatrix.fromMatrix(A), { D, checkRank: opts.checkRank }).toMatrix();
}
