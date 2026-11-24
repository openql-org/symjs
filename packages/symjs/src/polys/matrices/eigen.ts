// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/eigen.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/** @file Exact eigenvectors over coefficient fields and finite extensions. */

import { at, cast } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { Dummy, Sym } from '../../core/nodes';
import { subs } from '../../core/traverse';
import { Matrix } from '../../matrices/matrix';
import { FiniteExtension } from '../agca/extensions';
import type { Domain } from '../domains';
import { rootsDict } from '../poly';
import { CRootOf } from '../rootof';
import { Poly } from '../sympoly';
import { DomainMatrix } from './domainmatrix';

/** Eigenvalue, algebraic multiplicity and row basis over the original domain. */
export type RationalEigenvectors = [Domain, Expr, number, DomainMatrix];
/** Minimal polynomial, algebraic multiplicity and row basis over its finite extension. */
export type AlgebraicEigenvectors = [FiniteExtension, Poly, number, DomainMatrix];

/**
 * Groups eigenspace bases by the irreducible factors of the characteristic polynomial.
 *
 * @param A - Square matrix.
 * @param lambda - Variable of the characteristic polynomial.
 * @returns The eigenspaces over the ground domain and its algebraic extensions.
 * @see SymPy `sympy.polys.matrices.eigen.dom_eigenvects`
 */
export function domEigenvects(A: DomainMatrix, lambda: Sym = new Dummy('lambda')): [RationalEigenvectors[], AlgebraicEigenvectors[]] {
  const polynomial = Poly.fromList(A.charpoly(), [lambda], { domain: A.domain.toString() });
  const [, factors] = polynomial.factorList();
  const rational: RationalEigenvectors[] = [];
  const algebraic: AlgebraicEigenvectors[] = [];
  const [rows, cols] = A.shape;
  for (const [factor, multiplicity] of factors) {
    const minpoly = Poly.from(factor.asExpr(), [lambda], { domain: A.domain.toString() });
    const extension = minpoly.degree() > 1 ? new FiniteExtension(minpoly) : undefined;
    const K = extension === undefined ? A.domain : extension.toDomain();
    const value = extension === undefined ? K.quo(K.neg(minpoly.TC()), minpoly.LC()) : lambda;
    const shifted = new DomainMatrix(A.toList().map((row, i) => row.map((c, j) => i === j ? K.sub(c, value) : K.fromSympy(c))), [rows, cols], K);
    const basis = shifted.nullspace({ divideLast: true });
    if (extension === undefined) rational.push([K, value, multiplicity, basis]);
    else algebraic.push([extension, minpoly, multiplicity, basis]);
  }
  return [rational, algebraic];
}

/**
 * Convert domain eigenvectors to expression eigenvalues and column matrices.
 *
 * @param rational - Eigenspaces over the ground domain.
 * @param algebraic - Eigenspaces over algebraic extensions.
 * @param matrix - Constructor for the returned column matrices.
 * @param options - Additional root-finding options.
 * @returns Eigenvalues with their multiplicities and eigenvector bases.
 * @see SymPy `sympy.polys.matrices.eigen.dom_eigenvects_to_sympy`
 */
export function domEigenvectsToSympy(
  rational: readonly RationalEigenvectors[],
  algebraic: readonly AlgebraicEigenvectors[],
  matrix: typeof Matrix | ((entries: readonly Expr[]) => Matrix) = Matrix,
  options: { cubics?: boolean; quartics?: boolean; quintics?: boolean } = {},
): [Expr, number, Matrix[]][] {
  const makeMatrix = (entries: readonly Expr[]): Matrix => 'col' in matrix ? matrix.col(...entries) : matrix(entries);
  const result: [Expr, number, Matrix[]][] = rational.map(([K, value, multiplicity, basis]) => [K.toSympy(value), multiplicity, basis.toList().map((row) => makeMatrix(row.map((c) => K.toSympy(c))))]);
  for (const [, minpoly, multiplicity, basis] of algebraic) {
    const lambda = cast(at(minpoly.gens, 0), Sym);
    const polynomial = minpoly.asExpr();
    const degree = minpoly.degree();
    const radicals = (degree !== 3 || options.cubics !== false) && (degree !== 4 || options.quartics !== false);
    let values = radicals ? [...rootsDict(polynomial, lambda, { skipQuintic: options.quintics !== true }).keys()] : [];
    if (values.length !== minpoly.degree()) values = Array.from({ length: minpoly.degree() }, (_, i) => CRootOf(minpoly, i));
    for (const value of values) result.push([value, multiplicity, basis.toList().map((row) => makeMatrix(row.map((c) => subs(c, [[lambda, value]]))))]);
  }
  return result;
}
