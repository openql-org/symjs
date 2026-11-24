// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Smaller modules of sympy.matrices.expressions: DotProduct
 * (dotproduct), CompanionMatrix (companion), MatrixSet (sets) and the
 * symbolic factorizations LofLU, QofQR, ... (factorizations).
 */

import { callableClass } from '../../core/callable';
import type { ExprLike , Expr} from '../../core/nodes';
import { Add, Float, S } from '../../core/nodes';
import { isIntegerQ, isNegative } from '../../core/assumptions';
import { pow, sympify } from '../../core/ops';
import type { Truth } from '../../core/truth';
import { Poly } from '../../polys/sympoly';
import { SetExpr, containsQ } from '../../sets/sets';
import { latex } from '../../printing/latex';
import { companion } from '../linalg';
import type { Matrix } from '../matrix';
import type { DoitHints, MatArg } from './matexpr';
import { MatScalar, MatrixExpr, checkDim, doitArg, parenLatex, toExpr, toMatrix, transposeOf } from './matexpr';
import { isInt, same } from './util';
import { at, cast, defined, first, pair } from '../../core/guard';
import { parse } from '../../parsing/parser';

// ---------------------------------------------------------------------------
// DotProduct
// ---------------------------------------------------------------------------

/**
 * The dot product of two vectors of the same length.
 * @see SymPy `sympy.matrices.expressions.dotproduct.DotProduct`
 */
export class DotProductNode extends MatScalar {
  /**
   * Constructs a `DotProduct`.
   * @param a - The first operand.
   * @param b - The second operand.
   */
  constructor(a: Expr, b: Expr) {
    super('DotProduct', [a, b]);
  }
  /**
   * Constructs the dot product expression from its operands.
   * @param a1 - The first vector.
   * @param a2 - The second vector.
   * @returns The dot product expression from its operands.
   * @throws TypeError when a matrix operand is required or a vector argument has more than one row and column or the vector lengths differ.
   */
  static create(a1: MatArg, a2: MatArg): DotProductNode {
    const a = toExpr(a1);
    const b = toExpr(a2);
    if (!(a instanceof MatrixExpr)) throw new TypeError('Argument 1 of DotProduct is not a matrix');
    if (!(b instanceof MatrixExpr)) throw new TypeError('Argument 2 of DotProduct is not a matrix');
    const one = (m: MatrixExpr) => m.shape.some((d) => same(d, S.One));
    if (!one(a)) throw new TypeError('Argument 1 of DotProduct is not a vector');
    if (!one(b)) throw new TypeError('Argument 2 of DotProduct is not a vector');
    const set = (m: MatrixExpr) => new Set(m.shape.map((d) => d.key));
    const sa = set(a);
    const sb = set(b);
    if (sa.size !== sb.size || [...sa].some((k) => !sb.has(k))) throw new TypeError('DotProduct arguments are not the same length');
    return new DotProductNode(a, b);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DotProductNode(...pair(args));
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.dotproduct.DotProduct.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const [a0, b0] = pair(this.args.map((x) => cast(hints.deep === false ? x : doitArg(x, hints), MatrixExpr)));
    const mul = (x: Expr, y: Expr): MatrixExpr => cast(cast(x, MatrixExpr).mul(y), MatrixExpr);
    let m: MatrixExpr;
    if (same(a0.rows, b0.rows) && same(a0.cols, b0.cols)) m = same(a0.rows, S.One) ? mul(a0, transposeOf(b0)) : mul(transposeOf(a0), b0);
    else m = same(a0.rows, S.One) ? mul(a0, b0) : mul(transposeOf(a0), transposeOf(b0));
    return m.at(0);
  }
  /**
   * Returns the binding precedence used to parenthesize LaTeX output.
   * @returns The binding precedence used to parenthesize LaTeX output.
   */
  override latexPrecedence(): number {
    return 49;
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    return `${parenLatex(at(this.args, 0), 49)} \\cdot ${parenLatex(at(this.args, 1), 49)}`;
  }
}

/**
 * The dot product of two vectors of the same length.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The resulting matrix expression.
 * @throws TypeError when a matrix operand is required or a vector argument has more than one row and column or the vector lengths differ.
 * @see SymPy `sympy.matrices.expressions.dotproduct.DotProduct`
 * @example
 * ```ts
 * import { DotProduct, MatrixSymbol } from '@symjs/symjs';
 * DotProduct(MatrixSymbol('A', 1, 3), MatrixSymbol('B', 1, 3)); // => DotProduct(A, B)
 * ```
 */
export const DotProduct = /* @__PURE__ */ callableClass(DotProductNode, (a: MatArg, b: MatArg): DotProductNode => DotProductNode.create(a, b));
export type DotProduct = DotProductNode;

// ---------------------------------------------------------------------------
// CompanionMatrix
// ---------------------------------------------------------------------------

/**
 * The companion matrix of a monic univariate polynomial.
 * @see SymPy `sympy.matrices.expressions.companion.CompanionMatrix`
 */
export class CompanionMatrixNode extends MatrixExpr {
  /** The polynomial. */
  readonly poly: Poly;
  /**
   * Constructs a `CompanionMatrix`.
   * @param poly - The monic polynomial defining the companion matrix.
   */
  constructor(poly: Poly) {
    super('CompanionMatrix', [poly.asExpr(), ...poly.gens]);
    this.poly = poly;
  }
  /**
   * Constructs the companion matrix expression from its operands.
   * @param poly - The monic polynomial defining the companion matrix.
   * @returns The companion matrix expression from its operands.
   * @throws RangeError when the argument is not a polynomial or the polynomial has more than one variable or the polynomial is not monic or the polynomial has degree less than one.
   */
  static create(poly: Poly): CompanionMatrixNode {
    if (!(poly instanceof Poly)) throw new RangeError(`${String(poly)} must be a Poly instance.`);
    if (poly.gens.length !== 1) throw new RangeError(`${String(poly)} must be a univariate polynomial.`);
    if (!same(first(poly.allCoeffs()), S.One)) throw new RangeError(`${String(poly)} must be a monic polynomial.`);
    if (poly.degree() < 1) throw new RangeError(`${String(poly)} must have degree not less than 1.`);
    return new CompanionMatrixNode(poly);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.companion.CompanionMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    const n = sympify(this.poly.degree());
    return [n, n];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new CompanionMatrixNode(Poly.from(first(args), args.slice(1)));
  }
  protected override computeKey(): string {
    return `CompanionMatrix(${String(this.poly)})`;
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @throws TypeError when the indices are not integers.
   * @see SymPy `sympy.matrices.expressions.companion.CompanionMatrix._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    const n = this.poly.degree();
    if (!isInt(i) || !isInt(j)) throw new TypeError('CompanionMatrix entries need integer indices');
    const r = Number(i.p);
    const c = Number(j.p);
    if (c === n - 1) {
      const cs = this.poly.allCoeffs();
      return sympify(defined(cs[cs.length - 1 - r], 'coefficient')).neg();
    }
    return r === c + 1 ? S.One : S.Zero;
  }
  /**
   * Evaluates the entries to construct an explicit matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.expressions.companion.CompanionMatrix.as_explicit`
   */
  override asExplicit(): Matrix {
    return companion(this.poly.allCoeffs());
  }
  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    return `CompanionMatrix(${String(this.poly)})`;
  }
  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    const dom = domainLatex(this.poly.domain);
    const gens = this.poly.gens.map((g) => latex(g)).join(', ');
    return `\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( ${polyLatex(this.poly)}, ${gens}, domain=${dom} \\right)}\\right)`;
  }
}

/** SymPy's LaTeX of a polynomial domain: \\mathbb{Z}, \\mathbb{Q}\\left[k\\right], \\mathbb{Q}\\left(k\\right). */
function domainLatex(dom: string): string {
  const fields: Record<string, string> = { ZZ: '\\mathbb{Z}', QQ: '\\mathbb{Q}', RR: '\\mathbb{R}', CC: '\\mathbb{C}' };
  const m = /^(ZZ|QQ|RR|CC)(?:([[(])(.*)[\])])?$/.exec(dom);
  if (!m) return `\\mathtt{\\text{${dom.replaceAll('_', '\\_')}}}`;
  const base = defined(fields[defined(m[1], 'ground domain')], 'ground domain');
  if (m[2] === undefined) return base;
  const gens = defined(m[3], 'generators')
    .split(',')
    .map((g) => latex(parse(g.trim())));
  return m[2] === '[' ? `${base}\\left[${gens.join(', ')}\\right]` : `${base}\\left(${gens.join(', ')}\\right)`;
}

/** SymPy LatexPrinter._print_Poly terms of a monic univariate polynomial, from the leading term. */
function polyLatex(poly: Poly): string {
  const gen = first(poly.gens);
  const cs = poly.allCoeffs();
  const terms: string[] = [];
  cs.forEach((c, k) => {
    const e = cs.length - 1 - k;
    if (same(c, S.Zero)) return;
    const mon = e === 0 ? '' : latex(e === 1 ? gen : pow(gen, e));
    let sc: string;
    if (c instanceof Add) sc = mon ? `\\left(${latex(c)}\\right)` : latex(c);
    else if (mon && same(c, S.One)) return void terms.push('+', mon);
    else if (mon && same(c, S.NegOne)) return void terms.push('-', mon);
    else sc = latex(c);
    const st = mon ? `${sc} ${mon}` : sc;
    if (st.startsWith('-')) terms.push('-', st.slice(1));
    else terms.push('+', st);
  });
  // the leading coefficient is 1, so the first sign is '+'
  return terms.slice(1).join(' ');
}

/**
 * The companion matrix of a monic univariate polynomial.
 * @param poly - The monic polynomial defining the companion matrix.
 * @returns The resulting matrix expression.
 * @throws RangeError when the argument is not a polynomial or the polynomial has more than one variable or the polynomial is not monic or the polynomial has degree less than one.
 * @see SymPy `sympy.matrices.expressions.companion.CompanionMatrix`
 * @example
 * ```ts
 * import { CompanionMatrix, Poly, ZZ, ex } from '@symjs/symjs';
 *
 * const x = ex`x`;
 * CompanionMatrix(Poly.from(ex`c0 + x`, [x], { domain: 'ZZ[c0]', pure: false })).asExplicit(); // => Matrix([[-c0]])
 * ```
 */
export const CompanionMatrix = /* @__PURE__ */ callableClass(CompanionMatrixNode, (poly: Poly): CompanionMatrixNode => CompanionMatrixNode.create(poly));
export type CompanionMatrix = CompanionMatrixNode;

// ---------------------------------------------------------------------------
// MatrixSet
// ---------------------------------------------------------------------------

/**
 * The set of n x m matrices with entries in a set (a set, as in SymPy).
 * @see SymPy `sympy.matrices.expressions.sets.MatrixSet`
 */
export class MatrixSetNode extends SetExpr {
  /**
   * Returns a tuple of arguments of 'self'.
   * @see SymPy `sympy.matrices.expressions.sets.MatrixSet.args`
   */
  readonly args: readonly Expr[];
  /**
   * Constructs a `MatrixSet`.
   * @param n - The number of rows.
   * @param m - The matrix being factored.
   * @param set - The set of allowed matrix entries.
   */
  constructor(n: Expr, m: Expr, set: SetExpr) {
    super();
    this.args = [n, m, set];
  }
  /**
   * Gets the class name.
   * @returns The class name.
   */
  get className(): string {
    return 'MatrixSet';
  }
  protected computeKey(): string {
    return `MatrixSet(${this.args.map((a) => a.key).join(',')})`;
  }
  /**
   * Constructs the matrix set expression from its operands.
   * @param n - The number of rows.
   * @param m - The matrix being factored.
   * @param set - The set of allowed matrix entries.
   * @returns The matrix set expression from its operands.
   * @throws RangeError when a dimension is negative or nonintegral.
   */
  static create(n: ExprLike, m: ExprLike, set: SetExpr): MatrixSetNode {
    const d = (x: ExprLike): Expr => {
      const e = sympify(x);
      if (e instanceof Float || isIntegerQ(e) === false || isNegative(e) === true) throw new RangeError(`The dimension specification ${String(e)} should be a nonnegative integer.`);
      return checkDim(e);
    };
    return new MatrixSetNode(d(n), d(m), set);
  }
  /**
   * The shape (n, m).
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.sets.MatrixSet.shape`
   */
  get shape(): [Expr, Expr] {
    return pair(this.args);
  }
  /**
   * Gets the set of the entries.
   * @returns The set of the entries.
   * @see SymPy `sympy.matrices.expressions.sets.MatrixSet.set`
   */
  get set(): SetExpr {
    return cast(at(this.args, 2), SetExpr);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new MatrixSetNode(at(args, 0), at(args, 1), cast(at(args, 2), SetExpr));
  }
  /**
   * Tests whether the given expression belongs to this set of matrices.
   * @param x - The expression or entry to examine.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   */
  override elementOf(x: Expr): Truth {
    return this.contains(x);
  }
  /**
   * Tests the dimensions and entry set of a candidate matrix.
   * @param other - The other matrix operand.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @throws TypeError when a matrix operand is required.
   * @see SymPy `sympy.matrices.expressions.sets.MatrixSet.contains`
   */
  contains(other: MatArg): Truth {
    const x = toExpr(other);
    if (!(x instanceof MatrixExpr)) throw new TypeError(`${String(x)} should be an instance of MatrixExpr.`);
    const [r, c] = this.shape;
    if (!same(x.rows, r) || !same(x.cols, c)) {
      if ([...x.shape, r, c].some((d) => !isInt(d))) return 'unknown';
      return false;
    }
    let result: Truth = true;
    for (const e of x.asExplicit().data) {
      const t = containsQ(this.set, e);
      if (t === false) return false;
      if (t !== true) result = 'unknown';
    }
    return result;
  }
  /**
   * Formats the expression as plain text.
   * @param print - Formats a child expression.
   * @returns The plain-text representation.
   */
  printStr(print: (e: Expr) => string): string {
    return `MatrixSet(${this.args.map(print).join(', ')})`;
  }
  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{MatrixSet}\\left(${this.args.map(print).join(', ')}\\right)`;
  }
}

/**
 * The set of n x m matrices with entries in a set (a set, as in SymPy).
 * @param n - The number of rows.
 * @param m - The number of columns.
 * @param set - The set of allowed matrix entries.
 * @returns The resulting matrix expression.
 * @throws RangeError when a dimension is negative or nonintegral.
 * @see SymPy `sympy.matrices.expressions.sets.MatrixSet`
 * @example
 * ```ts
 * import { Matrix, MatrixSet, Reals } from '@symjs/symjs';
 * MatrixSet(2, 2, Reals).contains(Matrix.of([[1, 2], [3, 4]])); // => True
 * ```
 */
export const MatrixSet = /* @__PURE__ */ callableClass(MatrixSetNode, (n: ExprLike, m: ExprLike, set: SetExpr): MatrixSetNode => MatrixSetNode.create(n, m, set));
export type MatrixSet = MatrixSetNode;

// ---------------------------------------------------------------------------
// Factorizations
// ---------------------------------------------------------------------------

/**
 * A factor of a matrix factorization, with the shape of the matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.Factorization`
 * @example
 * ```ts
 * import { Factorization, LofLU, MatrixSymbol } from '@symjs/symjs';
 * LofLU(MatrixSymbol('A', 3, 3)) instanceof Factorization; // => True
 * ```
 */
export class FactorizationNode extends MatrixExpr {
  /**
   * Constructs a `Factorization`.
   * @param name - The name used to identify the object.
   * @param arg - The expression to operate on.
   * @param predicates - The matrix properties satisfied by the factor.
   */
  constructor(
    name: string,
    arg: Expr,
    /** The predicates the factor satisfies (SymPy predicates, e.g. 'lower_triangular'). */
    readonly predicates: readonly string[],
  ) {
    super(name, [arg]);
  }
  /**
   * The factorized matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.factorizations.Factorization.arg`
   */
  get arg(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.factorizations.Factorization.shape`
   */
  get shape(): [Expr, Expr] {
    return this.arg.shape;
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new FactorizationNode(this.name, first(args), this.predicates);
  }
}

const factor = (name: string, preds: readonly string[]) => (m: MatArg) => new FactorizationNode(name, toMatrix(m), preds);

/**
 * Represents the lower triangular factor of an LU decomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.LofLU`
 * @example
 * ```ts
 * import { LofLU, MatrixSymbol } from '@symjs/symjs';
 * LofLU(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const LofLU = factor('LofLU', ['lower_triangular']);
/**
 * Represents the upper triangular factor of an LU decomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.UofLU`
 * @example
 * ```ts
 * import { MatrixSymbol, UofLU } from '@symjs/symjs';
 * UofLU(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const UofLU = factor('UofLU', ['upper_triangular']);
/**
 * Represents the lower triangular Cholesky factor.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.LofCholesky`
 * @example
 * ```ts
 * import { LofCholesky, MatrixSymbol } from '@symjs/symjs';
 * LofCholesky(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const LofCholesky = factor('LofCholesky', ['lower_triangular']);
/**
 * Represents the upper triangular Cholesky factor.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.UofCholesky`
 * @example
 * ```ts
 * import { MatrixSymbol, UofCholesky } from '@symjs/symjs';
 * UofCholesky(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const UofCholesky = factor('UofCholesky', ['upper_triangular']);
/**
 * Represents the orthogonal factor of a QR decomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.QofQR`
 * @example
 * ```ts
 * import { MatrixSymbol, QofQR } from '@symjs/symjs';
 * QofQR(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const QofQR = factor('QofQR', ['orthogonal']);
/**
 * Represents the upper triangular factor of a QR decomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.RofQR`
 * @example
 * ```ts
 * import { MatrixSymbol, RofQR } from '@symjs/symjs';
 * RofQR(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const RofQR = factor('RofQR', ['upper_triangular']);
/**
 * Represents the eigenvector factor of a symbolic eigendecomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.EigenVectors`
 * @example
 * ```ts
 * import { EigenVectors, MatrixSymbol } from '@symjs/symjs';
 * EigenVectors(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const EigenVectors = factor('EigenVectors', ['orthogonal']);
/**
 * Represents the diagonal eigenvalue factor of a symbolic eigendecomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.EigenValues`
 * @example
 * ```ts
 * import { EigenValues, MatrixSymbol } from '@symjs/symjs';
 * EigenValues(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const EigenValues = factor('EigenValues', ['diagonal']);
/**
 * Represents the left singular vectors of a symbolic singular value decomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.UofSVD`
 * @example
 * ```ts
 * import { MatrixSymbol, UofSVD } from '@symjs/symjs';
 * UofSVD(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const UofSVD = factor('UofSVD', ['orthogonal']);
/**
 * Represents the diagonal matrix of singular values.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.SofSVD`
 * @example
 * ```ts
 * import { MatrixSymbol, SofSVD } from '@symjs/symjs';
 * SofSVD(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const SofSVD = factor('SofSVD', ['diagonal']);
/**
 * Represents the right singular vectors of a symbolic singular value decomposition.
 * @param m - The matrix being factored.
 * @returns The symbolic factor of the input matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.VofSVD`
 * @example
 * ```ts
 * import { MatrixSymbol, VofSVD } from '@symjs/symjs';
 * VofSVD(MatrixSymbol('A', 3, 3)).shape; // => [3, 3]
 * ```
 */
export const VofSVD = factor('VofSVD', ['orthogonal']);

/**
 * Forms symbolic lower and upper triangular factors of a matrix.
 * @param expr - The expression to transform.
 * @returns The symbolic factors `[L, U]`.
 * @see SymPy `sympy.matrices.expressions.factorizations.lu`
 */
export function lu(expr: MatArg): [FactorizationNode, FactorizationNode] {
  return [LofLU(expr), UofLU(expr)];
}

/**
 * Forms the symbolic orthogonal and upper triangular factors of a matrix.
 * @param expr - The expression to transform.
 * @returns The symbolic factors `[Q, R]`.
 * @see SymPy `sympy.matrices.expressions.factorizations.qr`
 */
export function qr(expr: MatArg): [FactorizationNode, FactorizationNode] {
  return [QofQR(expr), RofQR(expr)];
}

/**
 * Forms the symbolic eigenvalue and eigenvector matrices.
 * @param expr - The expression to transform.
 * @returns The eigenvalue matrix followed by the eigenvector matrix.
 * @see SymPy `sympy.matrices.expressions.factorizations.eig`
 */
export function eig(expr: MatArg): [FactorizationNode, FactorizationNode] {
  return [EigenValues(expr), EigenVectors(expr)];
}

/**
 * Forms the symbolic factors of a singular value decomposition.
 * @param expr - The expression to transform.
 * @returns The symbolic factors `[U, S, V]`.
 * @see SymPy `sympy.matrices.expressions.factorizations.svd`
 */
export function svd(expr: MatArg): [FactorizationNode, FactorizationNode, FactorizationNode] {
  return [UofSVD(expr), SofSVD(expr), VofSVD(expr)];
}

