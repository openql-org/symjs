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

/** SymPy DotProduct(a, b): the dot product of two vectors of the same length. */
export class DotProductNode extends MatScalar {
  constructor(a: Expr, b: Expr) {
    super('DotProduct', [a, b]);
  }
  /** SymPy DotProduct(arg1, arg2): validated. */
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
  withArgs(args: readonly Expr[]): Expr {
    return new DotProductNode(...pair(args));
  }
  override doit(hints: DoitHints = {}): Expr {
    const [a0, b0] = pair(this.args.map((x) => cast(hints.deep === false ? x : doitArg(x, hints), MatrixExpr)));
    const mul = (x: Expr, y: Expr): MatrixExpr => cast(cast(x, MatrixExpr).mul(y), MatrixExpr);
    let m: MatrixExpr;
    if (same(a0.rows, b0.rows) && same(a0.cols, b0.cols)) m = same(a0.rows, S.One) ? mul(a0, transposeOf(b0)) : mul(transposeOf(a0), b0);
    else m = same(a0.rows, S.One) ? mul(a0, b0) : mul(transposeOf(a0), transposeOf(b0));
    return m.at(0);
  }
  override latexPrecedence(): number {
    return 49;
  }
  override printLatex(): string {
    return `${parenLatex(at(this.args, 0), 49)} \\cdot ${parenLatex(at(this.args, 1), 49)}`;
  }
}

/** SymPy DotProduct(a, b). */
export const DotProduct = /* @__PURE__ */ callableClass(DotProductNode, (a: MatArg, b: MatArg): DotProductNode => DotProductNode.create(a, b));
export type DotProduct = DotProductNode;

// ---------------------------------------------------------------------------
// CompanionMatrix
// ---------------------------------------------------------------------------

/** SymPy CompanionMatrix(poly): the companion matrix of a monic univariate polynomial. */
export class CompanionMatrixNode extends MatrixExpr {
  /** The polynomial. */
  readonly poly: Poly;
  constructor(poly: Poly) {
    super('CompanionMatrix', [poly.asExpr(), ...poly.gens]);
    this.poly = poly;
  }
  /** SymPy CompanionMatrix(poly): the polynomial must be monic, univariate and of degree >= 1. */
  static create(poly: Poly): CompanionMatrixNode {
    if (!(poly instanceof Poly)) throw new RangeError(`${String(poly)} must be a Poly instance.`);
    if (poly.gens.length !== 1) throw new RangeError(`${String(poly)} must be a univariate polynomial.`);
    if (!same(first(poly.allCoeffs()), S.One)) throw new RangeError(`${String(poly)} must be a monic polynomial.`);
    if (poly.degree() < 1) throw new RangeError(`${String(poly)} must have degree not less than 1.`);
    return new CompanionMatrixNode(poly);
  }
  get shape(): [Expr, Expr] {
    const n = sympify(this.poly.degree());
    return [n, n];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CompanionMatrixNode(Poly.from(first(args), args.slice(1)));
  }
  protected override computeKey(): string {
    return `CompanionMatrix(${String(this.poly)})`;
  }
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
  override asExplicit(): Matrix {
    return companion(this.poly.allCoeffs());
  }
  override printStr(): string {
    return `CompanionMatrix(${String(this.poly)})`;
  }
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

/** SymPy CompanionMatrix(poly). */
export const CompanionMatrix = /* @__PURE__ */ callableClass(CompanionMatrixNode, (poly: Poly): CompanionMatrixNode => CompanionMatrixNode.create(poly));
export type CompanionMatrix = CompanionMatrixNode;

// ---------------------------------------------------------------------------
// MatrixSet
// ---------------------------------------------------------------------------

/** SymPy MatrixSet(n, m, set): the set of n x m matrices with entries in a set (a set, as in SymPy). */
export class MatrixSetNode extends SetExpr {
  readonly args: readonly Expr[];
  constructor(n: Expr, m: Expr, set: SetExpr) {
    super();
    this.args = [n, m, set];
  }
  get className(): string {
    return 'MatrixSet';
  }
  protected computeKey(): string {
    return `MatrixSet(${this.args.map((a) => a.key).join(',')})`;
  }
  /** SymPy MatrixSet(n, m, set). */
  static create(n: ExprLike, m: ExprLike, set: SetExpr): MatrixSetNode {
    const d = (x: ExprLike): Expr => {
      const e = sympify(x);
      if (e instanceof Float || isIntegerQ(e) === false || isNegative(e) === true) throw new RangeError(`The dimension specification ${String(e)} should be a nonnegative integer.`);
      return checkDim(e);
    };
    return new MatrixSetNode(d(n), d(m), set);
  }
  /** The shape (n, m). */
  get shape(): [Expr, Expr] {
    return pair(this.args);
  }
  /** The set of the entries. */
  get set(): SetExpr {
    return cast(at(this.args, 2), SetExpr);
  }
  override withArgs(args: readonly Expr[]): Expr {
    return new MatrixSetNode(at(args, 0), at(args, 1), cast(at(args, 2), SetExpr));
  }
  /** SymPy MatrixSet._contains (a TypeError for a value that is not a matrix expression). */
  override elementOf(x: Expr): Truth {
    return this.contains(x);
  }
  /** SymPy X in M: true, false or 'unknown'. */
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
  printStr(print: (e: Expr) => string): string {
    return `MatrixSet(${this.args.map(print).join(', ')})`;
  }
  printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{MatrixSet}\\left(${this.args.map(print).join(', ')}\\right)`;
  }
}

/** SymPy MatrixSet(n, m, set). */
export const MatrixSet = /* @__PURE__ */ callableClass(MatrixSetNode, (n: ExprLike, m: ExprLike, set: SetExpr): MatrixSetNode => MatrixSetNode.create(n, m, set));
export type MatrixSet = MatrixSetNode;

// ---------------------------------------------------------------------------
// Factorizations
// ---------------------------------------------------------------------------

/** SymPy Factorization: a factor of a matrix factorization, with the shape of the matrix. */
export class FactorizationNode extends MatrixExpr {
  constructor(
    name: string,
    arg: Expr,
    /** The predicates the factor satisfies (SymPy predicates, e.g. 'lower_triangular'). */
    readonly predicates: readonly string[],
  ) {
    super(name, [arg]);
  }
  /** The factorized matrix. */
  get arg(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  get shape(): [Expr, Expr] {
    return this.arg.shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new FactorizationNode(this.name, first(args), this.predicates);
  }
}

const factor = (name: string, preds: readonly string[]) => (m: MatArg) => new FactorizationNode(name, toMatrix(m), preds);

/** SymPy LofLU(X). */
export const LofLU = factor('LofLU', ['lower_triangular']);
/** SymPy UofLU(X). */
export const UofLU = factor('UofLU', ['upper_triangular']);
/** SymPy LofCholesky(X). */
export const LofCholesky = factor('LofCholesky', ['lower_triangular']);
/** SymPy UofCholesky(X). */
export const UofCholesky = factor('UofCholesky', ['upper_triangular']);
/** SymPy QofQR(X). */
export const QofQR = factor('QofQR', ['orthogonal']);
/** SymPy RofQR(X). */
export const RofQR = factor('RofQR', ['upper_triangular']);
/** SymPy EigenVectors(X). */
export const EigenVectors = factor('EigenVectors', ['orthogonal']);
/** SymPy EigenValues(X). */
export const EigenValues = factor('EigenValues', ['diagonal']);
/** SymPy UofSVD(X). */
export const UofSVD = factor('UofSVD', ['orthogonal']);
/** SymPy SofSVD(X). */
export const SofSVD = factor('SofSVD', ['diagonal']);
/** SymPy VofSVD(X). */
export const VofSVD = factor('VofSVD', ['orthogonal']);

/** SymPy lu(X): (LofLU(X), UofLU(X)). */
export function lu(expr: MatArg): [FactorizationNode, FactorizationNode] {
  return [LofLU(expr), UofLU(expr)];
}

/** SymPy qr(X): (QofQR(X), RofQR(X)). */
export function qr(expr: MatArg): [FactorizationNode, FactorizationNode] {
  return [QofQR(expr), RofQR(expr)];
}

/** SymPy eig(X): (EigenValues(X), EigenVectors(X)). */
export function eig(expr: MatArg): [FactorizationNode, FactorizationNode] {
  return [EigenValues(expr), EigenVectors(expr)];
}

/** SymPy svd(X): (UofSVD(X), SofSVD(X), VofSVD(X)). */
export function svd(expr: MatArg): [FactorizationNode, FactorizationNode, FactorizationNode] {
  return [UofSVD(expr), SofSVD(expr), VofSVD(expr)];
}

