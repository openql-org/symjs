// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/multivariate_resultants.py, BSD-3-Clause; see LICENSE.

import { at } from '../core/guard';
import { IndexedBase } from '../core/indexed';
import type { Expr, ExprLike } from '../core/nodes';
import { mul, pow, sub, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { isTrue } from '../core/truth';
import { luDecomposition, rref } from '../matrices/linalg';
import { Matrix } from '../matrices/matrix';
import { cancel } from '../simplify/rational';
import { Poly } from './sympoly';

function monomials(degree: number, n: number): number[][] {
  if (n === 1) return [[degree]];
  return Array.from({ length: degree + 1 }, (_, i) => degree - i).flatMap((d) => monomials(degree - d, n - 1).map((tail) => [d, ...tail]));
}
const monomial = (powers: readonly number[], vars: readonly Expr[]): Expr => mul(...vars.map((v, i) => pow(v, at(powers, i))));

/** Dixon's divided-difference polynomial and its coefficient matrix. */
export class DixonResultant {
  readonly polynomials: readonly Expr[];
  readonly dummyVariables: readonly Expr[];
  constructor(polynomials: readonly ExprLike[], readonly variables: readonly Expr[]) {
    if (!variables.length) throw new RangeError('at least one variable is required');
    this.polynomials = polynomials.map(sympify);
    const alpha = new IndexedBase('alpha');
    this.dummyVariables = variables.map((_, i) => alpha.at(i));
  }
  get n(): number { return this.variables.length; }
  get m(): number { return this.polynomials.length; }
  /** The maximal degree of each variable over the input polynomials. */
  get maxDegrees(): number[] {
    const degrees = this.polynomials.map((p) => Poly.from(p, this.variables).degreeList());
    return this.variables.map((_, i) => Math.max(...degrees.map((d) => at(d, i))));
  }
  /** The total degree of the product of the variables raised to their maximal degrees. */
  getUpperDegree(): number { return this.maxDegrees.reduce((a, d) => a + d, 0); }
  getDixonPolynomial(): Poly {
    if (this.m !== this.n + 1) throw new RangeError('Dixon requires n+1 polynomials in n variables');
    const matrix = Matrix.of(Array.from({ length: this.n + 1 }, (_, i) => this.polynomials.map((p) => subs(p, this.variables.slice(0, i).map((v, j) => [v, at(this.dummyVariables, j)])))));
    const denominator = mul(...this.variables.map((v, i) => sub(v, at(this.dummyVariables, i))));
    return Poly.from(cancel(mul(matrix.det(), pow(denominator, -1))), this.dummyVariables);
  }
  getMaxDegrees(polynomial: Poly): number[] {
    const degrees = polynomial.coeffs().map((c) => Poly.from(c, this.variables).degreeList());
    return this.variables.map((_, i) => Math.max(0, ...degrees.map((d) => at(d, i))));
  }
  getDixonMatrix(polynomial: Poly): Matrix {
    const degrees = this.getMaxDegrees(polynomial);
    let powers: number[][] = [[]];
    for (const d of degrees) powers = powers.flatMap((prefix) => Array.from({ length: d + 1 }, (_, i) => [...prefix, d - i]));
    const rows = polynomial.coeffs().map((c) => {
      const p = Poly.from(c, this.variables);
      return powers.map((m) => p.coeffMonomial(m));
    });
    const keep = powers.map((_, i) => i).filter((i) => rows.length === powers.length || rows.some((r) => !at(r, i).equals(0)));
    return Matrix.of(rows.map((r) => keep.map((i) => at(r, i))));
  }
  /**
   * The Kapur-Saxena-Yang precondition: the column of the monomial 1 (the last
   * one) is not a linear combination of the others, so the last nonzero row of
   * the reduced row echelon form is [0, ..., 0, 1].
   */
  KSYPrecondition(matrix: Matrix): boolean {
    if (isTrue(matrix.isZeroMatrix)) return false;
    const reduced = rref(matrix)[0].simplify();
    const rows = reduced.toArray().filter((row) => row.some((e) => !e.equals(0)));
    const last = at(rows, rows.length - 1);
    return last.every((e, j) => j === last.length - 1 ? e.equals(1) : e.equals(0));
  }
  /** The matrix without its zero rows and zero columns. */
  deleteZeroRowsAndColumns(matrix: Matrix): Matrix {
    const rows = Array.from({ length: matrix.rows }, (_, i) => i).filter((i) => !isTrue(matrix.row(i).isZeroMatrix));
    const cols = Array.from({ length: matrix.cols }, (_, j) => j).filter((j) => !isTrue(matrix.col(j).isZeroMatrix));
    return matrix.slice(rows, cols);
  }
  /** The product of the first nonzero entry of every row. */
  productLeadingEntries(matrix: Matrix): Expr {
    return mul(1, ...matrix.toArray().flatMap((row) => row.filter((e) => !e.equals(0)).slice(0, 1)));
  }
  /** The Kapur-Saxena-Yang Dixon resultant: the product of the leading entries of the reduced upper factor. */
  getKSYDixonResultant(matrix: Matrix): Expr {
    const [, U] = luDecomposition(this.deleteZeroRowsAndColumns(matrix));
    return this.productLeadingEntries(this.deleteZeroRowsAndColumns(U.simplify()));
  }
}

/** Macaulay's homogeneous resultant numerator and denominator matrices. */
export class MacaulayResultant {
  readonly polynomials: readonly Expr[];
  readonly degrees: readonly number[];
  readonly degreeM: number;
  readonly monomialSet: readonly Expr[];
  private readonly powers: readonly number[][];
  constructor(polynomials: readonly ExprLike[], readonly variables: readonly Expr[]) {
    if (!variables.length || polynomials.length !== variables.length) throw new RangeError('Macaulay requires n homogeneous polynomials in n variables');
    this.polynomials = polynomials.map(sympify);
    const polys = this.polynomials.map((p) => Poly.from(p, variables));
    if (polys.some((p) => p.totalDegree() < 1)) throw new RangeError('positive-degree polynomials required');
    this.degrees = polys.map((p) => p.totalDegree());
    this.degreeM = 1 + this.degrees.reduce((a, d) => a + d - 1, 0);
    this.powers = monomials(this.degreeM, variables.length);
    this.monomialSet = this.powers.map((m) => monomial(m, variables));
  }
  get n(): number { return this.variables.length; }
  get monomialsSize(): number { return this.powers.length; }
  getSize(): number { return this.monomialsSize; }
  getMonomialsOfCertainDegree(degree: number): Expr[] {
    if (!Number.isInteger(degree) || degree < 0) throw new RangeError('degree must be a nonnegative integer');
    return monomials(degree, this.n).map((m) => monomial(m, this.variables));
  }
  private rowPowers(): number[][][] {
    return this.degrees.map((d, i) => monomials(this.degreeM - d, this.n).filter((m) => m.slice(0, i).every((e, j) => e < at(this.degrees, j))));
  }
  getRowCoefficients(): Expr[][] { return this.rowPowers().map((rows) => rows.map((m) => monomial(m, this.variables))); }
  getMatrix(): Matrix {
    return Matrix.of(this.getRowCoefficients().flatMap((rows, i) => rows.map((m) => {
      const p = Poly.from(mul(at(this.polynomials, i), m), this.variables);
      return this.powers.map((powers) => p.coeffMonomial(powers));
    })));
  }
  getReducedNonreduced(): [number[], number[]] {
    const reduced: number[] = [], nonreduced: number[] = [];
    // A monomial is nonreduced when at least TWO pure powers divide it,
    // independently of n. SymPy 1.14 uses n-1, which fails outside n=3.
    this.powers.forEach((m, i) => (m.filter((e, j) => e >= at(this.degrees, j)).length < 2 ? reduced : nonreduced).push(i));
    return [reduced, nonreduced];
  }
  getSubmatrix(matrix: Matrix): Matrix {
    if (matrix.rows !== this.getSize() || matrix.cols !== this.getSize()) throw new RangeError('incorrect Macaulay matrix shape');
    const [, columns] = this.getReducedNonreduced();
    if (!columns.length) return Matrix.eye(1);
    const nonreduced = new Set(columns.map((i) => at(this.powers, i).join(',')));
    const rowMonomials = this.rowPowers().flatMap((rows, i) => rows.map((m) => m.map((d, j) => d + (i === j ? at(this.degrees, i) : 0))));
    // Select rows by their monomials, so equal numerical coefficients cannot
    // accidentally remove rows as in SymPy's coefficient-membership test.
    const rows = rowMonomials.map((m, i) => [m.join(','), i] as const).filter(([m]) => nonreduced.has(m)).map(([, i]) => i);
    return Matrix.of(rows.map((i) => columns.map((j) => matrix.get(i, j))));
  }
}
