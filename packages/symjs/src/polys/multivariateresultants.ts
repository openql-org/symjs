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

/**
 * Dixon's divided-difference polynomial and its coefficient matrix.
 *
 * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant`
 * @example
 * ```ts
 * import { DixonResultant, ex, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * const dixon = new DixonResultant([ex`x + y`, ex`x**2 + y**3`, ex`x**2 + y`], [x, y]);
 * dixon.getDixonMatrix(dixon.getDixonPolynomial()).det(); // => 0
 * ```
 */
export class DixonResultant {
  /**
   * The polynomials of the system.
   *
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.polynomials`
   */
  readonly polynomials: readonly Expr[];
  /**
   * The auxiliary variables used in the Dixon construction.
   *
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.dummy_variables`
   */
  readonly dummyVariables: readonly Expr[];
  /**
   * Construct the Dixon resultant system.
   *
   * @param polynomials - Polynomials defining the system.
   * @param variables - Ordered variables of the polynomial system.
   * @throws RangeError when the variable list is empty.
   */
  constructor(polynomials: readonly ExprLike[],
    /** The variables of the polynomial system. @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.variables` */
    readonly variables: readonly Expr[]) {
    if (!variables.length) throw new RangeError('at least one variable is required');
    this.polynomials = polynomials.map(sympify);
    const alpha = new IndexedBase('alpha');
    this.dummyVariables = variables.map((_, i) => alpha.at(i));
  }
  /**
   * Counts the variables in the polynomial system.
   *
   * @returns The variable count.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.n`
   */
  get n(): number { return this.variables.length; }
  /**
   * Counts the equations supplied as polynomials.
   *
   * @returns The input polynomial count.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.m`
   */
  get m(): number { return this.polynomials.length; }
  /**
   * Finds the largest degree in each variable across all inputs.
   *
   * @returns The degrees in variable order.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.max_degrees`
   */
  get maxDegrees(): number[] {
    const degrees = this.polynomials.map((p) => Poly.from(p, this.variables).degreeList());
    return this.variables.map((_, i) => Math.max(...degrees.map((d) => at(d, i))));
  }
  /**
   * Sums the maximal degrees across the variables.
   *
   * @returns The upper total degree.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.get_upper_degree`
   */
  getUpperDegree(): number { return this.maxDegrees.reduce((a, d) => a + d, 0); }
  /**
   * Constructs the Dixon polynomial from the divided-difference determinant.
   *
   * @returns The Dixon polynomial.
   * @throws RangeError when the number of polynomials is not one more than the number of variables.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.get_dixon_polynomial`
   */
  getDixonPolynomial(): Poly {
    if (this.m !== this.n + 1) throw new RangeError('Dixon requires n+1 polynomials in n variables');
    const matrix = Matrix.of(Array.from({ length: this.n + 1 }, (_, i) => this.polynomials.map((p) => subs(p, this.variables.slice(0, i).map((v, j) => [v, at(this.dummyVariables, j)])))));
    const denominator = mul(...this.variables.map((v, i) => sub(v, at(this.dummyVariables, i))));
    return Poly.from(cancel(mul(matrix.det(), pow(denominator, -1))), this.dummyVariables);
  }
  /**
   * Finds the largest exponent in each variable among the coefficient polynomials.
   *
   * @param polynomial - Polynomial to operate on.
   * @returns The maximum exponents.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.get_max_degrees`
   */
  getMaxDegrees(polynomial: Poly): number[] {
    const degrees = polynomial.coeffs().map((c) => Poly.from(c, this.variables).degreeList());
    return this.variables.map((_, i) => Math.max(0, ...degrees.map((d) => at(d, i))));
  }
  /**
   * Extracts the Dixon polynomial's coefficients into a matrix.
   *
   * @param polynomial - Polynomial to operate on.
   * @returns The Dixon matrix.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.get_dixon_matrix`
   */
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
   * Tests the Kapur–Saxena–Yang precondition that the constant-monomial column is independent of the
   * other columns.
   *
   * @param matrix - Matrix to operate on.
   * @returns Whether the resultant matrix meets the KSY criterion.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.KSY_precondition`
   */
  KSYPrecondition(matrix: Matrix): boolean {
    if (isTrue(matrix.isZeroMatrix)) return false;
    const reduced = rref(matrix)[0].simplify();
    const rows = reduced.toArray().filter((row) => row.some((e) => !e.equals(0)));
    const last = at(rows, rows.length - 1);
    return last.every((e, j) => j === last.length - 1 ? e.equals(1) : e.equals(0));
  }
  /**
   * Drops rows and columns whose entries are all zero.
   *
   * @param matrix - Matrix to operate on.
   * @returns The reduced matrix.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.delete_zero_rows_and_columns`
   */
  deleteZeroRowsAndColumns(matrix: Matrix): Matrix {
    const rows = Array.from({ length: matrix.rows }, (_, i) => i).filter((i) => !isTrue(matrix.row(i).isZeroMatrix));
    const cols = Array.from({ length: matrix.cols }, (_, j) => j).filter((j) => !isTrue(matrix.col(j).isZeroMatrix));
    return matrix.slice(rows, cols);
  }
  /**
   * Multiplies the leading nonzero entries of the matrix rows.
   *
   * @param matrix - Matrix to operate on.
   * @returns The leading-entry product.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.product_leading_entries`
   */
  productLeadingEntries(matrix: Matrix): Expr {
    return mul(1, ...matrix.toArray().flatMap((row) => row.filter((e) => !e.equals(0)).slice(0, 1)));
  }
  /**
   * Multiplies the leading entries of the reduced upper factor to obtain the Kapur–Saxena–Yang resultant.
   *
   * @param matrix - Matrix to operate on.
   * @returns The Dixon resultant.
   * @see SymPy `sympy.polys.multivariate_resultants.DixonResultant.get_KSY_Dixon_resultant`
   */
  getKSYDixonResultant(matrix: Matrix): Expr {
    const [, U] = luDecomposition(this.deleteZeroRowsAndColumns(matrix));
    return this.productLeadingEntries(this.deleteZeroRowsAndColumns(U.simplify()));
  }
}

/**
 * Macaulay's homogeneous resultant numerator and denominator matrices.
 *
 * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant`
 * @example
 * ```ts
 * import { MacaulayResultant, ex, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * new MacaulayResultant([ex`x**2 + y**2`, ex`x*y`], [x, y]).getSize(); // => 4
 * ```
 */
export class MacaulayResultant {
  /**
   * The polynomials of the system.
   *
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.polynomials`
   */
  readonly polynomials: readonly Expr[];
  /**
   * The total degrees of the input polynomials.
   *
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.degrees`
   */
  readonly degrees: readonly number[];
  /**
   * The degree of the monomials indexing the Macaulay matrix.
   *
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.degree_m`
   */
  readonly degreeM: number;
  /**
   * The monomials indexing the columns of the resultant matrix.
   *
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.monomial_set`
   */
  readonly monomialSet: readonly Expr[];
  private readonly powers: readonly number[][];
  /**
   * Construct the Macaulay resultant system.
   *
   * @param polynomials - Polynomials defining the system.
   * @param variables - Ordered variables of the polynomial system.
   * @throws RangeError when the system does not have one homogeneous polynomial per variable or an input polynomial has nonpositive degree.
   */
  constructor(polynomials: readonly ExprLike[],
    /** The variables of the polynomial system. @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.variables` */
    readonly variables: readonly Expr[]) {
    if (!variables.length || polynomials.length !== variables.length) throw new RangeError('Macaulay requires n homogeneous polynomials in n variables');
    this.polynomials = polynomials.map(sympify);
    const polys = this.polynomials.map((p) => Poly.from(p, variables));
    if (polys.some((p) => p.totalDegree() < 1)) throw new RangeError('positive-degree polynomials required');
    this.degrees = polys.map((p) => p.totalDegree());
    this.degreeM = 1 + this.degrees.reduce((a, d) => a + d - 1, 0);
    this.powers = monomials(this.degreeM, variables.length);
    this.monomialSet = this.powers.map((m) => monomial(m, variables));
  }
  /**
   * Counts the variables in the polynomial system.
   *
   * @returns The variable count.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.n`
   */
  get n(): number { return this.variables.length; }
  /**
   * Counts the indexing monomials of the resultant matrix.
   *
   * @returns The monomial count.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.monomials_size`
   */
  get monomialsSize(): number { return this.powers.length; }
  /**
   * Determines the column count of the Macaulay matrix.
   *
   * @returns The matrix width.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.get_size`
   */
  getSize(): number { return this.monomialsSize; }
  /**
   * Enumerates monomials of the requested total degree.
   *
   * @param degree - Total degree of the monomials.
   * @returns The monomial list.
   * @throws RangeError when the degree is not a nonnegative integer.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.get_monomials_of_certain_degree`
   */
  getMonomialsOfCertainDegree(degree: number): Expr[] {
    if (!Number.isInteger(degree) || degree < 0) throw new RangeError('degree must be a nonnegative integer');
    return monomials(degree, this.n).map((m) => monomial(m, this.variables));
  }
  private rowPowers(): number[][][] {
    return this.degrees.map((d, i) => monomials(this.degreeM - d, this.n).filter((m) => m.slice(0, i).every((e, j) => e < at(this.degrees, j))));
  }
  /**
   * Finds the monomials multiplying each polynomial in the Macaulay matrix.
   *
   * @returns The row multipliers grouped by polynomial.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.get_row_coefficients`
   */
  getRowCoefficients(): Expr[][] { return this.rowPowers().map((rows) => rows.map((m) => monomial(m, this.variables))); }
  /**
   * Builds the matrix whose determinant is the numerator of the Macaulay resultant.
   *
   * @returns The numerator matrix.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.get_matrix`
   */
  getMatrix(): Matrix {
    return Matrix.of(this.getRowCoefficients().flatMap((rows, i) => rows.map((m) => {
      const p = Poly.from(mul(at(this.polynomials, i), m), this.variables);
      return this.powers.map((powers) => p.coeffMonomial(powers));
    })));
  }
  /**
   * Partitions the monomial positions into reduced and nonreduced classes.
   *
   * @returns Two index lists.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.get_reduced_nonreduced`
   */
  getReducedNonreduced(): [number[], number[]] {
    const reduced: number[] = [], nonreduced: number[] = [];
    // A monomial is nonreduced when at least TWO pure powers divide it,
    // independently of n. SymPy 1.14 uses n-1, which fails outside n=3.
    this.powers.forEach((m, i) => (m.filter((e, j) => e >= at(this.degrees, j)).length < 2 ? reduced : nonreduced).push(i));
    return [reduced, nonreduced];
  }
  /**
   * Extracts the submatrix whose determinant is the denominator of the Macaulay resultant.
   *
   * @param matrix - Matrix to operate on.
   * @returns The denominator matrix.
   * @throws RangeError when the matrix does not have the dimensions of the Macaulay matrix.
   * @see SymPy `sympy.polys.multivariate_resultants.MacaulayResultant.get_submatrix`
   */
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
