// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Kernel of SymPy's matrix expressions (sympy.matrices.expressions):
 * the base class MatrixExpr and the classes that refer to each other
 * (MatrixSymbol, explicit matrices, MatAdd, MatMul, MatPow, Inverse,
 * Transpose, Adjoint, Identity, ZeroMatrix, OneMatrix, MatrixElement,
 * MatrixSlice, Trace, Determinant, Permanent, ElementwiseApplyFunction)
 * with their canonicalization rules and printers. They live in one module
 * so that the classes can build each other without import cycles; the
 * other modules of the directory extend MatrixExpr.
 */

import { callableClass } from '../../core/callable';
import { Concrete, Sum } from '../../core/concrete';
import { MatrixError, NonInvertibleMatrixError, NonSquareMatrixError, NotImplementedError } from '../../core/errors';
import { LambdaNode } from '../../core/lambda';
import type { ExprLike , Expr} from '../../core/nodes';
import { Dummy, ExtensionExpr, Float, Mul, Pow, Rational, S, Sym } from '../../core/nodes';
import { isIntegerQ, isNegative, isZero } from '../../core/assumptions';
import { and } from '../../core/boolalg';
import { Eq } from '../../core/logic';
import { add, mul, pow, sympify } from '../../core/ops';
import { freeSymbols, rebuild } from '../../core/traverse';
import type { Truth } from '../../core/truth';
import { doitConcrete } from '../../concrete/summations';
import { adjoint as adjointFn, conjugate as conjugateFn, transpose as transposeFn } from '../../functions/elementary';
import { KroneckerDelta } from '../../functions/hyper';
import { floor } from '../../functions/special';
import { latex } from '../../printing/latex';
import type { Key } from '../../printing/sortkey';
import { compareKeys, sortKey } from '../../printing/sortkey';
import { str } from '../../printing/str';
import { simplify as simplifyScalar } from '../../simplify/simplify';
import { permanent as explicitPermanent } from '../linalg';
import { Matrix } from '../matrix';
import { PRECEDENCE, isInt, isNumber, relTruth, same, sameList, scalarPrecTraditional, toInt } from './util';
import { precedence as scalarPrecedence } from '../../printing/str';

/** Anything accepted where SymPy sympifies a matrix argument: expressions and explicit matrices. */
export type MatArg = ExprLike | Matrix;

/** Hints of doit (SymPy keyword arguments). */
export interface DoitHints {
  /** Evaluate the arguments first (default true). */
  readonly deep?: boolean;
  /** false keeps Inverse unevaluated (SymPy inv_expand). */
  readonly invExpand?: boolean;
}

/** A slice of a matrix dimension: SymPy `a:b:c` as `[a, b, c]` (null for an omitted bound), or one index. */
export type SliceSpec = ExprLike | readonly [(ExprLike | null)?, (ExprLike | null)?, (ExprLike | null)?];

/** SymPy ShapeError: the shapes of matrices do not match. */
export class ShapeError extends MatrixError {
  constructor(message = 'Matrices are not aligned') {
    super(message);
    this.name = 'ShapeError';
  }
}

// ---------------------------------------------------------------------------
// sympify for matrices
// ---------------------------------------------------------------------------

/** sympify that turns explicit matrices into ImmutableMatrix nodes (SymPy _sympify of a Matrix). */
export function toExpr(x: MatArg): Expr {
  if (x instanceof Matrix) return new ImmutableMatrixNode(x);
  return sympify(x);
}

/** True for matrix expressions (SymPy is_Matrix), including explicit ImmutableMatrix nodes. */
export const isMatrix = (e: unknown): e is MatrixExpr => e instanceof MatrixExpr;

/** A matrix expression from an argument, or a TypeError. */
export function toMatrix(x: MatArg, message?: string): MatrixExpr {
  const e = toExpr(x);
  if (!(e instanceof MatrixExpr)) throw new TypeError(message ?? `${str(e)} is not a matrix`);
  return e;
}

/** SymPy MatrixExpr._check_dim: a dimension must be a nonnegative integer when that is known. */
export function checkDim(d: Expr): Expr {
  let bad = d instanceof Float;
  if (d instanceof Rational) bad = !d.isInteger || d.isNegative;
  else if (!bad) bad = isIntegerQ(d) === false || isNegative(d) === true;
  if (bad) throw new RangeError(`The dimension specification ${str(d)} should be a nonnegative integer.`);
  return d;
}

const dim = (x: ExprLike): Expr => checkDim(sympify(x));

// ---------------------------------------------------------------------------
// Printing helpers
// ---------------------------------------------------------------------------

/** SymPy precedence() of an expression that may be a matrix expression. */
export function strPrecedence(e: Expr): number {
  if (e instanceof MatrixExpr || e instanceof MatScalar) return e.strPrecedence();
  return scalarPrecedence(e);
}

/** SymPy precedence_traditional() of an expression that may be a matrix expression. */
export function latexPrecedence(e: Expr): number {
  if (e instanceof MatrixExpr || e instanceof MatScalar) return e.latexPrecedence();
  return scalarPrecTraditional(e);
}

/** StrPrinter.parenthesize. */
export function parenStr(e: Expr, level: number, strict = false): string {
  const p = strPrecedence(e);
  const s = str(e);
  return p < level || (!strict && p <= level) ? `(${s})` : s;
}

/** LatexPrinter.parenthesize. */
export function parenLatex(e: Expr, level: number, strict = false): string {
  const p = latexPrecedence(e);
  const s = latex(e);
  return p < level || (!strict && p <= level) ? `\\left(${s}\\right)` : s;
}

/** SymPy could_extract_minus_sign of a matrix product: a negative number in front. */
function mulCouldExtractMinus(e: Expr): boolean {
  if (!(e instanceof MatMulNode)) return false;
  const c = e.args[0];
  return c !== undefined && isNumber(c) && c.isNegative;
}

// ---------------------------------------------------------------------------
// Sort keys (SymPy default_sort_key and as_ordered_terms for matrix terms)
// ---------------------------------------------------------------------------

const ONE_KEY: Key = [[1, 0, 'Number'], [0, []], [], 1];

/** SymPy default_sort_key of an expression that may contain matrix expressions. */
export function matSortKey(e: Expr): Key {
  if (e instanceof Str) return [[2, 0, 'Str'], [1, [e.value]], ONE_KEY, 1];
  if (e instanceof MatMulNode) {
    let args = [...e.args];
    let coeff = 1;
    const c = args[0];
    if (c !== undefined && isNumber(c) && args.length > 1) {
      coeff = c.value;
      args = args.slice(1);
    }
    if (args.length === 1) {
      const k = matSortKey(args[0]!) as Key[];
      return [k[0]!, k[1]!, k[2]!, coeff];
    }
    const cpart = args.filter((a) => !(a instanceof MatrixExpr) && a.isCommutative);
    const ncpart = args.filter((a) => a instanceof MatrixExpr || !a.isCommutative);
    const ordered = [...cpart.map((a) => ({ a, k: matSortKey(a) })).sort((x, y) => compareKeys(x.k, y.k)).map((x) => x.k), ...ncpart.map(matSortKey)];
    return [[3, 0, 'MatMul'], [ordered.length, ordered], ONE_KEY, coeff];
  }
  if (e instanceof MatAddNode) {
    const ks = orderedTerms(e.args).map(matSortKey);
    return [[3, 1, 'MatAdd'], [ks.length, ks], ONE_KEY, 1];
  }
  if (e instanceof ImmutableMatrixNode) {
    const entries = e.matrix.data.map(matSortKey);
    return [[5, 0, 'ImmutableDenseMatrix'], [3, [sortKey(Rational.of(e.matrix.rows)), sortKey(Rational.of(e.matrix.cols)), [[5, 0, 'Tuple'], [entries.length, entries], ONE_KEY, 1]]], ONE_KEY, 1];
  }
  if (e instanceof MatrixExpr || e instanceof MatScalar) {
    const ks = e.sortArgs().map(matSortKey);
    return [[5, 0, e.name], [ks.length, ks], ONE_KEY, 1];
  }
  return sortKey(e);
}

/** SymPy Expr.as_ordered_terms() of the terms of a MatAdd (lex order of SymPy's printers). */
export function orderedTerms(terms: readonly Expr[]): Expr[] {
  const gens = new Map<string, Expr>();
  const parsed = terms.map((term) => {
    let re = 1;
    let im = 0;
    let factors: Expr[];
    if (term instanceof MatMulNode) {
      factors = [...term.args];
    } else factors = [term];
    const cpart = new Map<string, number>();
    const ncpart: Expr[] = [];
    for (const f of factors) {
      if (!(f instanceof MatrixExpr) && f.isCommutative && freeSymbols(f).size === 0 && !hasMatrix(f)) {
        try {
          const v = f.toComplex();
          [re, im] = [re * v.re - im * v.im, re * v.im + im * v.re];
          continue;
        } catch {
          // a generator
        }
      }
      if (!(f instanceof MatrixExpr) && f.isCommutative) {
        let base: Expr = f;
        let ex = 1;
        if (f instanceof Pow && isInt(f.exp)) {
          base = f.base;
          ex = toInt(f.exp);
        }
        cpart.set(base.key, (cpart.get(base.key) ?? 0) + ex);
        gens.set(base.key, base);
      } else ncpart.push(f);
    }
    return { term, re, im, cpart, ncpart };
  });
  const genList = [...gens.values()].map((g) => ({ g, k: matSortKey(g) })).sort((a, b) => compareKeys(a.k, b.k));
  const keyed = parsed.map(({ term, re, im, cpart, ncpart }) => {
    const monom: Key[] = genList.map(({ g }) => -(cpart.get(g.key) ?? 0));
    const ck: Key = [
      [im !== 0 ? 1 : 0, im],
      [re, im],
    ];
    return { term, k: [monom, ncpart.map(matSortKey), ck] as Key };
  });
  return keyed.sort((a, b) => compareKeys(a.k, b.k)).map((x) => x.term);
}

/** True when the expression contains a matrix expression. */
export function hasMatrix(e: Expr): boolean {
  return e instanceof MatrixExpr || e.args.some(hasMatrix);
}

/** True when the expression contains a node satisfying the predicate (SymPy has(cls)). */
export function hasNode(e: Expr, pred: (x: Expr) => boolean): boolean {
  return pred(e) || e.args.some((a) => hasNode(a, pred));
}

// ---------------------------------------------------------------------------
// doit
// ---------------------------------------------------------------------------

const doitable = (e: Expr): boolean => e instanceof MatrixExpr || e instanceof MatScalar || e instanceof Concrete || e.args.some(doitable);

/** SymPy doit of an argument: matrix nodes evaluate themselves, sums are carried out. */
export function doitArg(a: Expr, hints: DoitHints = {}): Expr {
  if (a instanceof MatrixExpr || a instanceof MatScalar) return a.doit(hints);
  if (!doitable(a)) return a;
  const r = a.args.length ? rebuild(a, a.args.map((x) => doitArg(x, hints))) : a;
  return r instanceof Concrete ? doitConcrete(r) : r;
}

// ---------------------------------------------------------------------------
// Str: a name as an argument (SymPy Str)
// ---------------------------------------------------------------------------

/** SymPy Str: a string as an expression argument (the name of a MatrixSymbol). */
export class Str extends ExtensionExpr {
  constructor(readonly value: string) {
    super('Str', []);
  }
  withArgs(): Expr {
    return this;
  }
  override printStr(): string {
    return this.value;
  }
  override printLatex(): string {
    return this.value;
  }
  protected override computeKey(): string {
    return `Str(${this.value})`;
  }
}

// ---------------------------------------------------------------------------
// The base classes
// ---------------------------------------------------------------------------

/** Context of entry(): the generator of summation dummies shared by nested products. */
export interface EntryContext {
  readonly dummy: () => Dummy;
}

/**
 * SymPy MatrixExpr: the base class of matrix expressions. Matrix expressions
 * do not commute; `A.mul(B)`, `A.add(B)` and `A.pow(n)` build and evaluate
 * MatMul, MatAdd and MatPow like SymPy's operators.
 */
export abstract class MatrixExpr extends ExtensionExpr {
  /** The shape (rows, cols). */
  abstract get shape(): [Expr, Expr];
  get rows(): Expr {
    return this.shape[0];
  }
  get cols(): Expr {
    return this.shape[1];
  }
  override get isScalar(): boolean {
    return false;
  }
  protected override computeCommutative(): boolean {
    return false;
  }
  /** SymPy is_MatrixExpr: false for explicit matrices. */
  get isMatrixExpr(): boolean {
    return true;
  }
  /** SymPy is_square. */
  get isSquare(): Truth {
    const [r, c] = this.shape;
    if (isInt(r) && isInt(c)) return r.p === c.p;
    if (same(r, c)) return true;
    return 'unknown';
  }
  /** SymPy is_Identity. */
  get isIdentity(): Truth {
    return 'unknown';
  }
  /** SymPy is_ZeroMatrix. */
  get isZeroMatrix(): boolean {
    return false;
  }

  // ---- arithmetic (SymPy operators) ----

  /** this + o (SymPy MatAdd(self, other).doit()). */
  override add(o: MatArg): Expr {
    return MatAddNode.create([this, toExpr(o)]).doit();
  }
  /** this - o. */
  override sub(o: MatArg): Expr {
    return MatAddNode.create([this, negate(toExpr(o))]).doit();
  }
  /** this * o (SymPy MatMul(self, other).doit()). */
  override mul(o: MatArg): Expr {
    return matMul(this, toExpr(o));
  }
  /** o * this (SymPy __rmul__). */
  rmul(o: MatArg): Expr {
    return matMul(toExpr(o), this);
  }
  /** this / o for a scalar o (SymPy self * other**-1). */
  override div(o: MatArg): Expr {
    const e = toExpr(o);
    return this.mul(e instanceof MatrixExpr ? e.pow(-1) : pow(e, -1));
  }
  /** this**o (SymPy MatPow(self, other).doit()). */
  override pow(o: ExprLike): Expr {
    return MatPowNode.create(this, sympify(o)).doit();
  }
  /** -this (SymPy MatMul(-1, self).doit()). */
  override neg(): Expr {
    return negate(this);
  }

  // ---- transposition, inversion ----

  /** The transpose (SymPy .T). */
  get T(): Expr {
    return this.transpose();
  }
  /** SymPy transpose(): Transpose(self).doit(deep=False). */
  transpose(): Expr {
    return this.evalTranspose();
  }
  /** SymPy adjoint(). */
  adjoint(): Expr {
    return this.evalAdjoint();
  }
  /** The Hermitian adjoint (adjoint()). */
  get H(): Expr {
    return this.adjoint();
  }
  /** SymPy conjugate(). */
  override conjugate(): Expr {
    return this.evalConjugate();
  }
  /** SymPy inverse(). */
  inverse(): Expr {
    if (this.isSquare === false) throw new NonSquareMatrixError('Inverse of non-square matrix');
    return this.evalInverse();
  }
  /** SymPy inv(). */
  inv(): Expr {
    return this.inverse();
  }
  /** The inverse (SymPy .I). */
  get I(): Expr {
    return this.inverse();
  }
  /** SymPy det(): the determinant. */
  det(): Expr {
    return det(this);
  }

  // ---- protocol (SymPy _eval_*); the defaults give the unevaluated forms ----

  /** SymPy _eval_transpose. @internal */
  evalTranspose(): Expr {
    return new TransposeNode(this);
  }
  /** SymPy _eval_adjoint. @internal */
  evalAdjoint(): Expr {
    return new AdjointNode(this);
  }
  /** SymPy _eval_conjugate. @internal */
  evalConjugate(): Expr {
    return new AdjointNode(new TransposeNode(this));
  }
  /** SymPy _eval_inverse. @internal */
  evalInverse(): Expr {
    return new InverseNode(this);
  }
  /** SymPy _eval_determinant. @internal */
  evalDeterminant(): Expr {
    return new DeterminantNode(this);
  }
  /** SymPy _eval_trace. @internal */
  evalTrace(): Expr {
    return new TraceNode(this);
  }
  /** SymPy _eval_power (the exponents -1, 0 and 1 are handled by MatPow.doit). @internal */
  evalPower(exp: Expr): Expr {
    return new MatPowNode(this, exp);
  }
  /** SymPy _entry(i, j): the entry without index validation. @internal */
  entry(_i: Expr, _j: Expr, _ctx?: EntryContext): Expr {
    throw new NotImplementedError(`Indexing not implemented for ${this.name}`);
  }
  /** SymPy as_coeff_mmul. */
  asCoeffMmul(): [Expr, MatMulNode] {
    return [S.One, new MatMulNode([this])];
  }
  /** Arguments used by the sort key (SymPy args). @internal */
  sortArgs(): readonly Expr[] {
    return this.args;
  }
  /** SymPy precedence() for the str printer. @internal */
  strPrecedence(): number {
    return PRECEDENCE.Atom;
  }
  /** SymPy precedence_traditional() for the LaTeX printer. @internal */
  latexPrecedence(): number {
    return this.strPrecedence();
  }

  // ---- indexing ----

  /** SymPy valid_index. */
  validIndex(i: Expr, j: Expr): boolean {
    const ok = (idx: Expr, d: Expr): boolean => relTruth('Ge', idx, mul(-1, d)) !== false && relTruth('Lt', idx, d) !== false;
    return ok(i, this.rows) && ok(j, this.cols);
  }
  /**
   * SymPy M[i, j] (an entry) or M[k] (row-major single index, which needs
   * a known number of columns).
   */
  at(i: ExprLike, j?: ExprLike): Expr {
    if (j === undefined) {
      const k = sympify(i);
      const cols = this.cols;
      if (!isInt(k)) throw new RangeError('Only integers may be used when addressing the matrix with a single index.');
      if (!isInt(cols)) throw new RangeError('Single indexing is only supported when the number of columns is known.');
      const c = cols.p;
      let q = k.p / c;
      if (k.p % c !== 0n && k.p < 0n) q -= 1n;
      const r = Rational.of(q);
      const s = Rational.of(k.p - q * c);
      if (this.validIndex(r, s)) return this.entry(r, s);
      throw new RangeError(`Invalid index ${str(k)}`);
    }
    const a = sympify(i);
    const b = sympify(j);
    if (this.validIndex(a, b)) return this.entry(a, b);
    throw new RangeError(`Invalid indices (${str(a)}, ${str(b)})`);
  }
  /** SymPy M[rows, cols] with slices: a MatrixSlice. A single index selects one row (or column). */
  slice(rows: SliceSpec, cols: SliceSpec = [null, null, null]): Expr {
    return MatrixSliceNode.create(this, rows, cols);
  }

  // ---- explicit forms ----

  /** SymPy as_explicit(): an explicit Matrix. */
  asExplicit(): Matrix {
    const [r, c] = this.shape;
    if (!isInt(r) || !isInt(c)) throw new RangeError('Matrix with symbolic shape cannot be represented explicitly.');
    return Matrix.fromFunction(toInt(r), toInt(c), (i, j) => this.at(i, j));
  }
  /** SymPy as_mutable(): an explicit matrix. */
  asMutable(): Matrix {
    return this.asExplicit();
  }
  /**
   * SymPy MatrixExpr.equals: entrywise equality with another matrix of
   * explicit shape (false when it cannot be shown). The method `equals` of
   * symjs expressions is SymPy's structural ==.
   */
  equalsExplicit(other: ExprLike | Matrix): boolean {
    const o = toExpr(other);
    if (same(this, o)) return true;
    if (!(o instanceof MatrixExpr)) return false;
    let a: Matrix;
    let b: Matrix;
    try {
      a = this.asExplicit();
      b = o.asExplicit();
    } catch {
      return false;
    }
    if (a.rows !== b.rows || a.cols !== b.cols) return false;
    return a.data.every((x, k) => {
      const y = b.data[k]!;
      if (same(x, y)) return true;
      const d = simplifyScalar(add(x, mul(-1, y)));
      return isZero(d) === true;
    });
  }

  // ---- evaluation ----

  /** SymPy doit(). */
  doit(hints: DoitHints = {}): Expr {
    if (hints.deep === false) return this;
    const args = this.args.map((a) => doitArg(a, hints));
    return sameList(args, this.args) ? this : this.withArgs(args);
  }
  override doitSelf(): Expr {
    return this.doit({ deep: false });
  }
  /** SymPy canonicalize(). */
  canonicalize(): Expr {
    return this;
  }
  /** SymPy applyfunc(f): the function applied to every entry (ElementwiseApplyFunction). */
  applyfunc(f: LambdaNode | ((x: Expr) => Expr)): Expr {
    return ElementwiseApplyFunctionNode.create(f, this);
  }
  /** SymPy simplify of a matrix expression: the arguments simplified. */
  override simplify(): Expr {
    if (!this.args.length || this instanceof MatrixSymbolNode) return this;
    return this.withArgs(this.args.map(simplifyArg));
  }
  /** SymPy expand: products distributed over sums. */
  override expand(): Expr {
    return this.withArgs(this.args.map(expandArg));
  }
  override transposeSelf(): Expr {
    return this.evalTranspose();
  }
  override adjointSelf(): Expr {
    return this.evalAdjoint();
  }
  override conjugateSelf(): Expr {
    return this.evalConjugate();
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    void x;
    void d;
    return undefined;
  }
}

/**
 * Scalars built from matrices (Trace, Determinant, Permanent, MatrixElement,
 * DotProduct): commutative expressions with SymPy's doit.
 */
export abstract class MatScalar extends ExtensionExpr {
  protected override computeCommutative(): boolean {
    return true;
  }
  /** SymPy doit(). */
  doit(hints: DoitHints = {}): Expr {
    if (hints.deep === false) return this;
    const args = this.args.map((a) => doitArg(a, hints));
    return sameList(args, this.args) ? this : this.withArgs(args);
  }
  override doitSelf(): Expr {
    return this.doit({ deep: false });
  }
  /** Arguments used by the sort key. @internal */
  sortArgs(): readonly Expr[] {
    return this.args;
  }
  /** SymPy precedence(). @internal */
  strPrecedence(): number {
    return PRECEDENCE.Atom;
  }
  /** SymPy precedence_traditional(). @internal */
  latexPrecedence(): number {
    return this.strPrecedence();
  }
  /** SymPy simplify: doit, then the scalar simplification. */
  override simplify(): Expr {
    const r = this.doit();
    if (r instanceof MatScalar) return r.withArgs(r.args.map(simplifyArg));
    return simplifyArg(r);
  }
  /** SymPy expand of the arguments. */
  override expand(): Expr {
    return this.withArgs(this.args.map(expandArg));
  }
}

function simplifyArg(a: Expr): Expr {
  if (a instanceof MatrixExpr || a instanceof MatScalar) return a.simplify();
  if (hasMatrix(a) || a instanceof ExtensionExpr) return a;
  return simplifyScalar(a);
}

function expandArg(a: Expr): Expr {
  if (a instanceof MatrixExpr || a instanceof MatScalar) return a.expand();
  if (hasMatrix(a)) return a;
  return a.expand();
}

/** -M (SymPy MatMul(-1, M).doit()); scalars are negated. */
export function negate(e: Expr): Expr {
  if (e instanceof MatrixExpr) return matMul(S.NegOne, e);
  return mul(-1, e);
}

/** A scalar or matrix derivative helper: zero matrices for matrix arguments free of x. */
function mdiff(e: Expr, x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
  if (e instanceof MatrixExpr && !e.has(x)) return new ZeroMatrixNode(e.rows, e.cols);
  return d(e, x);
}

// ---------------------------------------------------------------------------
// MatrixSymbol
// ---------------------------------------------------------------------------

/** SymPy MatrixSymbol(name, n, m): a symbolic n x m matrix. */
export class MatrixSymbolNode extends MatrixExpr {
  constructor(symbolName: string, rows: ExprLike, cols: ExprLike) {
    super('MatrixSymbol', [new Str(symbolName), dim(rows), dim(cols)]);
  }
  /** The name of the matrix (SymPy MatrixSymbol.name). */
  get symbolName(): string {
    return (this.args[0] as Str).value;
  }
  get shape(): [Expr, Expr] {
    return [this.args[1]!, this.args[2]!];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSymbolNode((args[0] as Str).value, args[1]!, args[2]!);
  }
  override entry(i: Expr, j: Expr): Expr {
    return new MatrixElementNode(this, i, j);
  }
  override printStr(): string {
    return this.symbolName;
  }
  override printLatex(): string {
    return latex(new Sym(this.symbolName));
  }
  override diffSelf(): Expr {
    return new ZeroMatrixNode(this.rows, this.cols);
  }
}

// ---------------------------------------------------------------------------
// Explicit matrices
// ---------------------------------------------------------------------------

/** Printed form of an explicit matrix (SymPy str: Matrix([[...], ...]) on one line). */
export function explicitStr(m: Matrix, print: (e: Expr) => string = str): string {
  if (m.rows === 0 || m.cols === 0) return `Matrix(${m.rows}, ${m.cols}, [])`;
  return `Matrix([${m
    .toArray()
    .map((r) => `[${r.map(print).join(', ')}]`)
    .join(', ')}])`;
}

/** The contents of an explicit matrix in LaTeX (SymPy _print_matrix_contents). */
export function explicitLatexContents(m: Matrix, print: (e: Expr) => string = latex): string {
  const lines = m.toArray().map((r) => r.map(print).join(' & '));
  const env = m.cols <= 10 ? 'matrix' : 'array';
  const spec = env === 'array' ? `{${'c'.repeat(m.cols)}}` : '';
  return `\\begin{${env}}${spec}${lines.join('\\\\')}\\end{${env}}`;
}

/** SymPy ImmutableMatrix (ImmutableDenseMatrix): an explicit matrix inside matrix expressions. */
export class ImmutableMatrixNode extends MatrixExpr {
  constructor(readonly matrix: Matrix) {
    super('ImmutableDenseMatrix', matrix.data);
  }
  get shape(): [Expr, Expr] {
    return [Rational.of(this.matrix.rows), Rational.of(this.matrix.cols)];
  }
  override get isMatrixExpr(): boolean {
    return false;
  }
  override get isIdentity(): Truth {
    const m = this.matrix;
    if (m.rows !== m.cols) return false;
    for (let i = 0; i < m.rows; i++) for (let j = 0; j < m.cols; j++) if (!same(m.get(i, j), i === j ? S.One : S.Zero)) return false;
    return true;
  }
  withArgs(args: readonly Expr[]): Expr {
    const { rows, cols } = this.matrix;
    return new ImmutableMatrixNode(Matrix.fromFunction(rows, cols, (i, j) => args[i * cols + j]!));
  }
  protected override computeKey(): string {
    return `ImmutableDenseMatrix(${this.matrix.rows},${this.matrix.cols};${this.args.map((a) => a.key).join(',')})`;
  }
  override entry(i: Expr, j: Expr): Expr {
    if (isInt(i) && isInt(j)) {
      const r = toInt(i) < 0 ? toInt(i) + this.matrix.rows : toInt(i);
      const c = toInt(j) < 0 ? toInt(j) + this.matrix.cols : toInt(j);
      return this.matrix.get(r, c);
    }
    return new MatrixElementNode(this, i, j);
  }
  override asExplicit(): Matrix {
    return this.matrix;
  }
  override evalTranspose(): Expr {
    return new ImmutableMatrixNode(this.matrix.transpose());
  }
  override evalAdjoint(): Expr {
    return new ImmutableMatrixNode(this.matrix.transpose().map((e) => conjugateFn(e)));
  }
  override evalConjugate(): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => conjugateFn(e)));
  }
  override evalInverse(): Expr {
    return new ImmutableMatrixNode(this.matrix.inv());
  }
  override evalDeterminant(): Expr {
    return this.matrix.det();
  }
  override evalTrace(): Expr {
    return this.matrix.trace();
  }
  override evalPower(exp: Expr): Expr {
    if (isInt(exp)) {
      const n = toInt(exp);
      return new ImmutableMatrixNode(n >= 0 ? this.matrix.pow(n) : this.matrix.inv().pow(-n));
    }
    return new MatPowNode(this, exp);
  }
  override doit(hints: DoitHints = {}): Expr {
    if (hints.deep === false) return this;
    return new ImmutableMatrixNode(this.matrix.map((e) => doitArg(e, hints)));
  }
  override simplify(): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => simplifyArg(e)));
  }
  override expand(): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => expandArg(e)));
  }
  override printStr(print: (e: Expr) => string): string {
    return explicitStr(this.matrix, print);
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\left[${explicitLatexContents(this.matrix, print)}\\right]`;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return new ImmutableMatrixNode(this.matrix.map((e) => d(e, x)));
  }
}

/** Explicit matrix product, sum or scaling used by the merge rules. */
function explicitOf(e: Expr): Matrix {
  return (e as ImmutableMatrixNode).matrix;
}

// ---------------------------------------------------------------------------
// MatrixElement
// ---------------------------------------------------------------------------

/** SymPy MatrixElement(parent, i, j): the entry M[i, j] of a matrix expression. */
export class MatrixElementNode extends MatScalar {
  constructor(parent: Expr, i: Expr, j: Expr) {
    super('MatrixElement', [parent, i, j]);
  }
  /** The matrix. */
  get parent(): Expr {
    return this.args[0]!;
  }
  /** The row index. */
  get i(): Expr {
    return this.args[1]!;
  }
  /** The column index. */
  get j(): Expr {
    return this.args[2]!;
  }
  /** [i, j]. */
  get indices(): [Expr, Expr] {
    return [this.i, this.j];
  }
  withArgs(args: readonly Expr[]): Expr {
    return matrixElement(args[0]!, args[1]!, args[2]!);
  }
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    const p = args[0]!;
    if (p instanceof MatrixExpr) return p.at(args[1]!, args[2]);
    return this;
  }
  override printStr(print: (e: Expr) => string): string {
    return `${parenStr(this.parent, PRECEDENCE.Atom, true)}[${print(this.i)}, ${print(this.j)}]`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `{${parenLatex(this.parent, PRECEDENCE.Atom, true)}}_{${print(this.i)},${print(this.j)}}`;
  }
  override diffSelf(v: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if (v instanceof MatrixElementNode) {
      if (same(v.parent, this.parent)) return mul(KroneckerDelta(this.i, v.i), KroneckerDelta(this.j, v.j));
      if (!this.parent.has(v.parent)) return S.Zero;
      return undefined;
    }
    const p = this.parent;
    if (p instanceof MatrixExpr) {
      const dp = mdiff(p, v, d);
      if (dp instanceof MatrixExpr) return dp.at(this.i, this.j);
    }
    return undefined;
  }
}

/** SymPy MatrixElement(parent, i, j): an explicit parent with integer indices gives the entry. */
export function matrixElement(parentIn: MatArg, iIn: ExprLike, jIn: ExprLike): Expr {
  const parent = toExpr(parentIn);
  const i = sympify(iIn);
  const j = sympify(jIn);
  if (parent instanceof ImmutableMatrixNode && isInt(i) && isInt(j)) return parent.entry(i, j);
  if (!(parent instanceof MatrixExpr)) throw new TypeError('First argument of MatrixElement should be a matrix');
  if (!parent.validIndex(i, j)) throw new RangeError('indices out of range');
  return new MatrixElementNode(parent, i, j);
}

// ---------------------------------------------------------------------------
// Special matrices
// ---------------------------------------------------------------------------

/** SymPy Identity(n): the n x n identity matrix, printed I. */
export class IdentityNode extends MatrixExpr {
  constructor(n: ExprLike) {
    super('Identity', [dim(n)]);
  }
  get shape(): [Expr, Expr] {
    return [this.args[0]!, this.args[0]!];
  }
  override get isSquare(): Truth {
    return true;
  }
  override get isIdentity(): Truth {
    return true;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new IdentityNode(args[0]!);
  }
  override evalTranspose(): Expr {
    return this;
  }
  override evalTrace(): Expr {
    return this.rows;
  }
  override evalInverse(): Expr {
    return this;
  }
  override evalConjugate(): Expr {
    return this;
  }
  override evalAdjoint(): Expr {
    return this;
  }
  override evalDeterminant(): Expr {
    return S.One;
  }
  override evalPower(): Expr {
    return this;
  }
  override entry(i: Expr, j: Expr): Expr {
    const t = relTruth('Eq', i, j);
    if (t === true) return S.One;
    if (t === false) return S.Zero;
    return KroneckerDelta(i, j);
  }
  override printStr(): string {
    return 'I';
  }
  override printLatex(): string {
    return '\\mathbb{I}';
  }
  override diffSelf(): Expr {
    return new ZeroMatrixNode(this.rows, this.cols);
  }
}

/** SymPy GenericIdentity: the identity of unspecified size (the empty MatMul). */
export class GenericIdentityNode extends IdentityNode {
  constructor() {
    super(0);
  }
  override get shape(): [Expr, Expr] {
    throw new TypeError('GenericIdentity does not have a specified shape');
  }
  override withArgs(): Expr {
    return this;
  }
  protected override computeKey(): string {
    return 'GenericIdentity()';
  }
}

/** SymPy ZeroMatrix(m, n): the zero matrix, printed 0. */
export class ZeroMatrixNode extends MatrixExpr {
  constructor(m: ExprLike, n: ExprLike) {
    super('ZeroMatrix', [dim(m), dim(n)]);
  }
  get shape(): [Expr, Expr] {
    return [this.args[0]!, this.args[1]!];
  }
  override get isZeroMatrix(): boolean {
    return true;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new ZeroMatrixNode(args[0]!, args[1]!);
  }
  override evalPower(exp: Expr): Expr {
    if (relTruth('Lt', exp, S.Zero) === true) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible');
    return this;
  }
  override evalTranspose(): Expr {
    return new ZeroMatrixNode(this.cols, this.rows);
  }
  override evalAdjoint(): Expr {
    return new ZeroMatrixNode(this.cols, this.rows);
  }
  override evalTrace(): Expr {
    return S.Zero;
  }
  override evalDeterminant(): Expr {
    return S.Zero;
  }
  override evalInverse(): Expr {
    throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  }
  override evalConjugate(): Expr {
    return this;
  }
  override entry(): Expr {
    return S.Zero;
  }
  override printStr(): string {
    return '0';
  }
  override printLatex(): string {
    return '0';
  }
  override diffSelf(): Expr {
    return this;
  }
}

/** SymPy GenericZeroMatrix: the zero matrix of unspecified size (the empty MatAdd). */
export class GenericZeroMatrixNode extends ZeroMatrixNode {
  constructor() {
    super(0, 0);
  }
  override get shape(): [Expr, Expr] {
    throw new TypeError('GenericZeroMatrix does not have a specified shape');
  }
  override withArgs(): Expr {
    return this;
  }
  protected override computeKey(): string {
    return 'GenericZeroMatrix()';
  }
}

/** SymPy OneMatrix(m, n): the matrix of ones, printed 1. */
export class OneMatrixNode extends MatrixExpr {
  constructor(m: ExprLike, n: ExprLike) {
    super('OneMatrix', [dim(m), dim(n)]);
  }
  /** SymPy OneMatrix(m, n, evaluate=True): Identity(1) for a 1 x 1 matrix. */
  static create(m: ExprLike, n: ExprLike, evaluate = false): MatrixExpr {
    const o = new OneMatrixNode(m, n);
    if (evaluate && o.is1x1() === true) return new IdentityNode(1);
    return o;
  }
  get shape(): [Expr, Expr] {
    return [this.args[0]!, this.args[1]!];
  }
  /** True when the matrix is known to be 1 x 1. */
  is1x1(): Truth {
    const a = relTruth('Eq', this.args[0]!, S.One);
    const b = relTruth('Eq', this.args[1]!, S.One);
    if (a === false || b === false) return false;
    return a === true && b === true ? true : 'unknown';
  }
  override get isIdentity(): Truth {
    return this.is1x1() === true;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new OneMatrixNode(args[0]!, args[1]!);
  }
  override asExplicit(): Matrix {
    const [r, c] = this.shape;
    if (!isInt(r) || !isInt(c)) throw new RangeError('Matrix with symbolic shape cannot be represented explicitly.');
    return Matrix.fromFunction(toInt(r), toInt(c), () => 1);
  }
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return OneMatrixNode.create(args[0]!, args[1]!, true);
  }
  override evalPower(exp: Expr): Expr {
    if (this.is1x1() === true) return new IdentityNode(1);
    if (relTruth('Lt', exp, S.Zero) === true) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible');
    if (isIntegerQ(exp) === true) return matMul(pow(this.rows, add(exp, -1)), new OneMatrixNode(this.rows, this.cols));
    return new MatPowNode(this, exp);
  }
  override evalTranspose(): Expr {
    return new OneMatrixNode(this.cols, this.rows);
  }
  override evalAdjoint(): Expr {
    return new OneMatrixNode(this.cols, this.rows);
  }
  override evalTrace(): Expr {
    return this.rows;
  }
  override evalDeterminant(): Expr {
    const c = this.is1x1();
    if (c === true) return S.One;
    if (c === false) return S.Zero;
    return new DeterminantNode(this);
  }
  override evalInverse(): Expr {
    const c = this.is1x1();
    if (c === true) return new IdentityNode(1);
    if (c === false) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
    return new InverseNode(this);
  }
  override evalConjugate(): Expr {
    return this;
  }
  override entry(): Expr {
    return S.One;
  }
  override printStr(): string {
    return '1';
  }
  override printLatex(): string {
    return '1';
  }
  override diffSelf(): Expr {
    return new ZeroMatrixNode(this.rows, this.cols);
  }
}

// ---------------------------------------------------------------------------
// Shape validation (sympy.matrices.expressions._shape)
// ---------------------------------------------------------------------------

/** SymPy validate_matadd_integer: integer dimensions of a sum must agree. */
export function validateMatAdd(args: readonly MatrixExpr[]): void {
  const rows = args.map((a) => a.rows);
  const cols = args.map((a) => a.cols);
  const fmt = (xs: Expr[]) => `(${xs.map(str).join(', ')}${xs.length === 1 ? ',' : ''})`;
  if (new Set(rows.filter(isInt).map((r) => r.key)).size > 1) throw new ShapeError(`Matrices have mismatching shape: ${fmt(rows)}`);
  if (new Set(cols.filter(isInt).map((r) => r.key)).size > 1) throw new ShapeError(`Matrices have mismatching shape: ${fmt(cols)}`);
}

/** SymPy validate_matmul_integer: integer inner dimensions of a product must agree. */
export function validateMatMul(args: readonly MatrixExpr[]): void {
  for (let k = 0; k + 1 < args.length; k++) {
    const i = args[k]!.cols;
    const j = args[k + 1]!.rows;
    if (isInt(i) && isInt(j) && i.p !== j.p) throw new ShapeError(`Matrices are not aligned: ${str(i)}, ${str(j)}`);
  }
}

/** SymPy is_matadd_valid: the condition for the matrices to be added. */
export function isMataddValid(...args: MatArg[]): Expr {
  const ms = args.map((a) => toMatrix(a));
  const conds: Expr[] = [];
  for (let k = 0; k + 1 < ms.length; k++) conds.push(Eq(ms[k]!.rows, ms[k + 1]!.rows));
  for (let k = 0; k + 1 < ms.length; k++) conds.push(Eq(ms[k]!.cols, ms[k + 1]!.cols));
  return and(...conds);
}

/** SymPy is_matmul_valid: the condition for the matrices to be multiplied. */
export function isMatmulValid(...args: MatArg[]): Expr {
  const ms = args.map(toExpr).filter((a): a is MatrixExpr => a instanceof MatrixExpr);
  const conds: Expr[] = [];
  for (let k = 0; k + 1 < ms.length; k++) conds.push(Eq(ms[k]!.cols, ms[k + 1]!.rows));
  return and(...conds);
}

/** SymPy is_square (of sympy.matrices.expressions._shape): the condition Eq(rows, cols). */
export function isSquare(arg: MatArg): Expr {
  const m = toMatrix(arg);
  return Eq(m.rows, m.cols);
}

// ---------------------------------------------------------------------------
// MatAdd
// ---------------------------------------------------------------------------

/** SymPy MatAdd: a sum of matrix expressions. */
export class MatAddNode extends MatrixExpr {
  constructor(args: readonly Expr[]) {
    super('MatAdd', args);
  }
  /** SymPy MatAdd(*args): validated, unevaluated (the empty sum is GenericZeroMatrix). */
  static create(argsIn: readonly MatArg[]): MatrixExpr {
    const args = argsIn.map(toExpr).filter((a) => !(a instanceof GenericZeroMatrixNode));
    if (!args.length) return new GenericZeroMatrixNode();
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    validateMatAdd(args);
    return new MatAddNode(args);
  }
  get shape(): [Expr, Expr] {
    return (this.args[0] as MatrixExpr).shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatAddNode(args);
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return add(...this.args.map((a) => (a as MatrixExpr).entry(i, j, ctx)));
  }
  override evalTranspose(): Expr {
    return MatAddNode.create(this.args.map(transposeOf)).doit();
  }
  override evalAdjoint(): Expr {
    return MatAddNode.create(this.args.map((a) => adjointFn(a))).doit();
  }
  override evalTrace(): Expr {
    return add(...this.args.map((a) => trace(a)));
  }
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return canonicalizeMatAdd(MatAddNode.create(args));
  }
  override canonicalize(): Expr {
    return canonicalizeMatAdd(this);
  }
  override expand(): Expr {
    return canonicalizeMatAdd(MatAddNode.create(this.args.map(expandArg)));
  }
  override strPrecedence(): number {
    return PRECEDENCE.Add;
  }
  override printStr(print: (e: Expr) => string): string {
    const parts: string[] = [];
    for (const term of orderedTerms(this.args)) {
      let t = print(term);
      let sign = '+';
      if (t.startsWith('-') && !(term instanceof MatAddNode)) {
        sign = '-';
        t = t.slice(1);
      }
      parts.push(sign, strPrecedence(term) < PRECEDENCE.Add || term instanceof MatAddNode ? `(${t})` : t);
    }
    const first = parts.shift();
    return (first === '-' ? '-' : '') + parts.join(' ');
  }
  override printLatex(print: (e: Expr) => string): string {
    let tex = '';
    orderedTerms(this.args).forEach((t0, k) => {
      let term = t0;
      if (k > 0) {
        if (mulCouldExtractMinus(term)) {
          tex += ' - ';
          term = negate(term);
        } else tex += ' + ';
      }
      const s = print(term);
      tex += term instanceof MatAddNode ? `\\left(${s}\\right)` : s;
    });
    return tex;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return MatAddNode.create(this.args.map((a) => mdiff(a, x, d))).doit();
  }
}

/** SymPy transpose() of a matrix expression or a scalar. */
export function transposeOf(e: Expr): Expr {
  return e instanceof MatrixExpr ? e.transpose() : transposeFn(e);
}

/** SymPy MatAdd(*args): an unevaluated sum of matrices. */
export const MatAdd = /* @__PURE__ */ callableClass(MatAddNode, (...args: MatArg[]): MatrixExpr => MatAddNode.create(args));
export type MatAdd = MatAddNode;

// ---- MatAdd rules (sympy.matrices.expressions.matadd.canonicalize) ----

type Rule = (e: Expr) => Expr;

function exhaustWhile(pred: (e: Expr) => boolean, rules: readonly Rule[]): Rule {
  return (e0) => {
    let e = e0;
    for (;;) {
      if (!pred(e)) return e;
      let next = e;
      for (const rule of rules) {
        const r = rule(e);
        if (!same(r, e)) {
          next = r;
          break;
        }
      }
      if (same(next, e)) return e;
      e = next;
    }
  };
}

/** sympy.strategies rm_id over the arguments of a node, rebuilt raw. */
function rmId(e: Expr, isId: (a: Expr) => boolean, raw: (args: readonly Expr[]) => Expr): Expr {
  const ids = e.args.map(isId);
  const n = ids.filter(Boolean).length;
  if (n === 0) return e;
  if (n !== ids.length) return raw(e.args.filter((_, k) => !ids[k]));
  return raw([e.args[0]!]);
}

const unpackRule = (e: Expr): Expr => (e.args.length === 1 && (e instanceof MatAddNode || e instanceof MatMulNode) ? e.args[0]! : e);

/** SymPy unpack of a single-argument MatMul. */
export const unpackMat = (e: Expr): Expr => (e instanceof MatMulNode && e.args.length === 1 ? e.args[0]! : e);

const flattenAdd = (e: Expr): Expr => new MatAddNode(e.args.flatMap((a) => (a instanceof MatAddNode ? a.args : [a])));

function glomAdd(e: Expr): Expr {
  const groups = new Map<string, { mat: Expr; cnt: Expr }>();
  for (const arg of e.args) {
    const [c, mm] = (arg as MatrixExpr).asCoeffMmul();
    const mat = unpackMat(mm);
    const g = groups.get(mat.key);
    if (g) g.cnt = add(g.cnt, c);
    else groups.set(mat.key, { mat, cnt: c });
  }
  const newargs = [...groups.values()].map(({ mat, cnt }) => (same(cnt, S.One) ? mat : matMul(cnt, mat)));
  const a = new Set(newargs.map((x) => x.key));
  const b = new Set(e.args.map((x) => x.key));
  if (a.size === b.size && [...a].every((k) => b.has(k))) return e;
  return new MatAddNode(newargs);
}

function mergeExplicitAdd(e: Expr): Expr {
  const explicit = e.args.filter((a) => a instanceof ImmutableMatrixNode);
  if (explicit.length <= 1) return e;
  const rest = e.args.filter((a) => !(a instanceof ImmutableMatrixNode));
  const total = explicit.map(explicitOf).reduce((x, y) => x.add(y));
  return MatAddNode.create([...rest, new ImmutableMatrixNode(total)]);
}

const sortAdd = (e: Expr): Expr =>
  new MatAddNode(
    e.args
      .map((a) => ({ a, k: matSortKey(a) }))
      .sort((x, y) => compareKeys(x.k, y.k))
      .map((x) => x.a),
  );

/** SymPy matadd.canonicalize. */
export const canonicalizeMatAdd: Rule = exhaustWhile(
  (e) => e instanceof MatAddNode,
  [(e) => rmId(e, (a) => same(a, S.Zero) || (a instanceof MatrixExpr && a.isZeroMatrix), (args) => new MatAddNode(args)), unpackRule, flattenAdd, glomAdd, mergeExplicitAdd, sortAdd],
);

/** SymPy matadd.merge_explicit: explicit matrices of a sum added together. */
export function mergeExplicitMatAdd(e: Expr): Expr {
  return e instanceof MatAddNode ? mergeExplicitAdd(e) : e;
}

// ---------------------------------------------------------------------------
// MatMul
// ---------------------------------------------------------------------------

/** SymPy MatMul: a product of scalars and matrix expressions. */
export class MatMulNode extends MatrixExpr {
  constructor(args: readonly Expr[]) {
    super('MatMul', args);
  }
  /** SymPy MatMul(*args): validated, unevaluated; a product without matrices is its scalar factor. */
  static create(argsIn: readonly MatArg[]): Expr {
    const args = argsIn.map(toExpr).filter((a) => !(a instanceof GenericIdentityNode));
    if (!args.length) return new GenericIdentityNode();
    const obj = new MatMulNode(args);
    const [factor, matrices] = obj.asCoeffMatrices();
    validateMatMul(matrices);
    if (!matrices.length) return factor;
    return obj;
  }
  get shape(): [Expr, Expr] {
    const ms = this.args.filter((a): a is MatrixExpr => a instanceof MatrixExpr);
    return [ms[0]!.rows, ms[ms.length - 1]!.cols];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatMulNode(args);
  }
  /** SymPy as_coeff_matrices: the scalar factor and the matrices. */
  asCoeffMatrices(): [Expr, MatrixExpr[]] {
    const scalars = this.args.filter((a) => !(a instanceof MatrixExpr));
    const matrices = this.args.filter((a): a is MatrixExpr => a instanceof MatrixExpr);
    const coeff = mul(...scalars);
    if (!coeff.isCommutative) throw new NotImplementedError('noncommutative scalars in MatMul are not supported.');
    return [coeff, matrices];
  }
  override asCoeffMmul(): [Expr, MatMulNode] {
    const [c, ms] = this.asCoeffMatrices();
    return [c, new MatMulNode(ms)];
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const [coeff, matrices] = this.asCoeffMatrices();
    if (matrices.length === 1) return mul(coeff, matrices[0]!.at(i, j));
    let counter = 0;
    const gen: EntryContext = ctx ?? { dummy: () => new Dummy(`i_${++counter}`) };
    const indices: Expr[] = [i];
    for (let k = 1; k < matrices.length; k++) indices.push(gen.dummy());
    indices.push(j);
    const ranges = matrices.slice(0, -1).map((m) => add(m.cols, -1));
    const entries = matrices.map((m, k) => m.entry(indices[k]!, indices[k + 1]!, gen));
    const summand = mul(...entries);
    const limits = indices.slice(1, -1).map((d, k) => [d as Sym, S.Zero, ranges[k]!] as [Sym, Expr, Expr]);
    const result = mul(coeff, Sum(summand, ...limits));
    const expand = ranges.some(isInt);
    return expand ? doitArg(result) : result;
  }
  override evalTranspose(): Expr {
    const [coeff, matrices] = this.asCoeffMatrices();
    return matMul(coeff, ...[...matrices].reverse().map((m) => m.transpose()));
  }
  override evalAdjoint(): Expr {
    return matMul(...[...this.args].reverse().map((a) => adjointFn(a)));
  }
  override evalTrace(): Expr {
    const [factor, mmul] = this.asCoeffMmul();
    if (!same(factor, S.One)) return mul(factor, trace(mmul.doit()));
    return super.evalTrace();
  }
  override evalDeterminant(): Expr {
    const [factor, matrices] = this.asCoeffMatrices();
    const squares = onlySquares(matrices);
    return mul(pow(factor, this.rows), ...squares.map((m) => new DeterminantNode(m)));
  }
  override evalInverse(): Expr {
    if (this.args.every((a) => !(a instanceof MatrixExpr) || a.isSquare === true)) {
      return matMul(...[...this.args].reverse().map((a) => (a instanceof MatrixExpr ? a.inverse() : pow(a, -1))));
    }
    return new InverseNode(this);
  }
  override doit(hints: DoitHints = {}): Expr {
    const args = hints.deep === false ? this.args : this.args.map((a) => doitArg(a, hints));
    return canonicalizeMatMul(MatMulNode.create(args));
  }
  override canonicalize(): Expr {
    return canonicalizeMatMul(this);
  }
  override expand(): Expr {
    const factors = this.args.map(expandArg);
    let products: Expr[][] = [[]];
    for (const f of factors) {
      const terms = f instanceof MatAddNode ? f.args : [f];
      products = products.flatMap((p) => terms.map((t) => [...p, t]));
    }
    if (products.length === 1) return canonicalizeMatMul(MatMulNode.create(products[0]!));
    return MatAddNode.create(products.map((p) => matMul(...p))).doit();
  }
  override strPrecedence(): number {
    return mulCouldExtractMinus(this) ? PRECEDENCE.Add : PRECEDENCE.Mul;
  }
  override printStr(): string {
    const [c, matrices] = this.asCoeffMatrices();
    let args: readonly Expr[] = this.args;
    let sign = '';
    let level = this.strPrecedence();
    if (freeSymbols(c).size === 0 && !hasMatrix(c)) {
      let v: { re: number; im: number } | undefined;
      try {
        v = c.toComplex();
      } catch {
        v = undefined;
      }
      if (v && ((v.im === 0 && v.re < 0) || (v.re === 0 && v.im < 0))) {
        sign = '-';
        const nc = mul(-1, c);
        args = same(nc, S.One) ? matrices : [nc, ...matrices];
        level = PRECEDENCE.Mul;
      }
    }
    return sign + args.map((a) => parenStr(a, level)).join('*');
  }
  override printLatex(): string {
    const level = this.latexPrecedence();
    const parens = (x: Expr): string => (x instanceof Mul ? latex(x) : parenLatex(x, level));
    let args = [...this.args];
    if (mulCouldExtractMinus(this)) {
      if (same(args[0]!, S.NegOne)) args = args.slice(1);
      else args[0] = mul(-1, args[0]!);
      return `- ${args.map(parens).join(' ')}`;
    }
    return args.map(parens).join(' ');
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const terms: Expr[] = [];
    this.args.forEach((a, k) => {
      if (!a.has(x)) return;
      terms.push(matMul(...this.args.map((b, l) => (l === k ? mdiff(b, x, d) : b))));
    });
    if (!terms.length) return new ZeroMatrixNode(this.rows, this.cols);
    return MatAddNode.create(terms).doit();
  }
}

/** SymPy MatMul(*args).doit(): the evaluated product (a scalar when there is no matrix). */
function matMul(...args: MatArg[]): Expr {
  const r = MatMulNode.create(args);
  return r instanceof MatrixExpr ? r.doit() : r;
}

/** SymPy MatMul(*args): an unevaluated product of scalars and matrices. */
export const MatMul = /* @__PURE__ */ callableClass(MatMulNode, (...args: MatArg[]): Expr => MatMulNode.create(args));
export type MatMul = MatMulNode;

/** SymPy only_squares: consecutive matrices grouped into square products. */
export function onlySquares(matrices: readonly MatrixExpr[]): Expr[] {
  if (!same(matrices[0]!.rows, matrices[matrices.length - 1]!.cols)) throw new MatrixError('Invalid matrices being multiplied');
  const out: Expr[] = [];
  let start = 0;
  matrices.forEach((m, i) => {
    if (same(m.cols, matrices[start]!.rows)) {
      out.push(matMul(...matrices.slice(start, i + 1)));
      start = i + 1;
    }
  });
  return out;
}

// ---- MatMul rules (sympy.matrices.expressions.matmul.canonicalize) ----

function newmul(args: readonly Expr[]): Expr {
  return new MatMulNode(args.length && same(args[0]!, S.One) ? args.slice(1) : args);
}

function distributeMonom(e: Expr): Expr {
  const [a, b] = e.args;
  if (e.args.length === 2 && a && b) {
    const rat = (x: Expr) => x instanceof Rational;
    if (a instanceof MatAddNode && rat(b)) return MatAddNode.create(a.args.map((m) => matMul(m, b)));
    if (b instanceof MatAddNode && rat(a)) return MatAddNode.create(b.args.map((m) => matMul(a, m)));
  }
  return e;
}

function anyZeros(e: Expr): Expr {
  if (e.args.some((a) => (a instanceof MatrixExpr ? a.isZeroMatrix : isZero(a) === true))) {
    const ms = e.args.filter((a): a is MatrixExpr => a instanceof MatrixExpr);
    return new ZeroMatrixNode(ms[0]!.rows, ms[ms.length - 1]!.cols);
  }
  return e;
}

function removeIds(e: Expr): Expr {
  const [factor, mmul] = (e as MatMulNode).asCoeffMmul();
  const result = rmId(mmul, (a) => a instanceof MatrixExpr && a.isIdentity === true, (args) => new MatMulNode(args));
  if (!same(result, mmul)) return newmul([factor, ...result.args]);
  return e;
}

function combineOneMatrices(e: Expr): Expr {
  const [f0, args] = (e as MatMulNode).asCoeffMatrices();
  let factor = f0;
  const newArgs: Expr[] = [args[0]!];
  for (const B of args.slice(1)) {
    const A = newArgs[newArgs.length - 1]!;
    if (!(A instanceof OneMatrixNode) || !(B instanceof OneMatrixNode)) {
      newArgs.push(B);
      continue;
    }
    newArgs.pop();
    newArgs.push(new OneMatrixNode(A.rows, B.cols));
    factor = mul(factor, A.cols);
  }
  return newmul([factor, ...newArgs]);
}

function combinePowers(e: Expr): Expr {
  const [factor, args0] = (e as MatMulNode).asCoeffMatrices();
  const args: MatrixExpr[] = [...args0];
  let newArgs: MatrixExpr[] = [args[0]!];
  for (let i = 1; i < args.length; i++) {
    const A = newArgs[newArgs.length - 1]!;
    const B = args[i]!;
    if (B instanceof InverseNode && B.arg instanceof MatMulNode) {
      const bargs = B.arg.args;
      const l = bargs.length;
      if (l <= newArgs.length && sameList(bargs, newArgs.slice(-l))) {
        newArgs = [...newArgs.slice(0, newArgs.length - l), new IdentityNode(B.rows)];
        continue;
      }
    }
    if (A instanceof InverseNode && A.arg instanceof MatMulNode) {
      const aargs = A.arg.args;
      const l = aargs.length;
      if (sameList(aargs, args.slice(i, i + l))) {
        const identity = new IdentityNode(A.rows);
        newArgs[newArgs.length - 1] = identity;
        for (let j = i; j < i + l; j++) args[j] = identity;
        continue;
      }
    }
    if (A.isSquare === false || B.isSquare === false) {
      newArgs.push(B);
      continue;
    }
    const [aBase, aExp] = A instanceof MatPowNode ? [A.base, A.exp] : [A, S.One];
    const [bBase, bExp] = B instanceof MatPowNode ? [B.base, B.exp] : [B, S.One];
    if (same(aBase, bBase)) {
      newArgs[newArgs.length - 1] = asMat(MatPowNode.create(aBase, add(aExp, bExp)).doit({ deep: false }));
      continue;
    } else if (!(bBase instanceof ImmutableMatrixNode) && bBase instanceof MatrixExpr) {
      let inv: Expr | undefined;
      try {
        inv = bBase.inverse();
      } catch (err) {
        if (!(err instanceof NonInvertibleMatrixError)) throw err;
        inv = undefined;
      }
      if (inv !== undefined && same(aBase, inv)) {
        newArgs[newArgs.length - 1] = asMat(MatPowNode.create(aBase, add(aExp, mul(-1, bExp))).doit({ deep: false }));
        continue;
      }
    }
    newArgs.push(B);
  }
  return newmul([factor, ...newArgs]);
}

const asMat = (e: Expr): MatrixExpr => e as MatrixExpr;

const rmOnes = (e: Expr): Expr => rmId(e, (a) => same(a, S.One), (args) => new MatMulNode(args));

function mulExplicit(a: Expr, b: Expr): Expr {
  if (a instanceof ImmutableMatrixNode && b instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(a.matrix.mul(b.matrix));
  if (a instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(a.matrix.scale(b));
  if (b instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(b.matrix.scale(a));
  return mul(a, b);
}

function mergeExplicitMul(e: Expr): Expr {
  if (!e.args.some((a) => a instanceof ImmutableMatrixNode)) return e;
  const ok = (x: Expr) => x instanceof ImmutableMatrixNode || isNumber(x);
  const newArgs: Expr[] = [];
  let last = e.args[0]!;
  for (const arg of e.args.slice(1)) {
    if (ok(arg) && ok(last)) last = mulExplicit(last, arg);
    else {
      newArgs.push(last);
      last = arg;
    }
  }
  newArgs.push(last);
  return MatMulNode.create(newArgs);
}

function factorInFront(e: Expr): Expr {
  const [factor, matrices] = (e as MatMulNode).asCoeffMatrices();
  if (!same(factor, S.One)) return newmul([factor, ...matrices]);
  return e;
}

const flattenMul = (e: Expr): Expr => new MatMulNode(e.args.flatMap((a) => (a instanceof MatMulNode ? a.args : [a])));

/** A matrix that composes with its right neighbour in a product (PermutationMatrix). */
interface Composable {
  composeWith(other: MatrixExpr): Expr;
}
const isComposable = (e: Expr): e is MatrixExpr & Composable => e instanceof MatrixExpr && e.name === 'PermutationMatrix';

function combinePermutations(e: Expr): Expr {
  const args = e.args;
  if (args.length < 2) return e;
  const result: Expr[] = [args[0]!];
  for (const B of args.slice(1)) {
    const A = result[result.length - 1]!;
    if (isComposable(A) && isComposable(B)) result[result.length - 1] = A.composeWith(B);
    else result.push(B);
  }
  return MatMulNode.create(result);
}

/** SymPy matmul.canonicalize. */
export const canonicalizeMatMul: Rule = exhaustWhile(
  (e) => e instanceof MatMulNode,
  [distributeMonom, anyZeros, removeIds, combineOneMatrices, combinePowers, unpackRule, rmOnes, mergeExplicitMul, factorInFront, flattenMul, combinePermutations],
);

/** SymPy matmul.merge_explicit: adjacent explicit matrices (and numbers) of a product multiplied. */
export function mergeExplicitMatMul(e: Expr): Expr {
  return e instanceof MatMulNode ? mergeExplicitMul(e) : e;
}

// ---------------------------------------------------------------------------
// MatPow and Inverse
// ---------------------------------------------------------------------------

/** SymPy MatPow(base, exp): a power of a square matrix. */
export class MatPowNode extends MatrixExpr {
  constructor(base: Expr, exp: Expr, name = 'MatPow') {
    super(name, [base, exp]);
  }
  /** SymPy MatPow(base, exp): validated, unevaluated. */
  static create(baseIn: MatArg, expIn: ExprLike): MatPowNode {
    const base = toExpr(baseIn);
    if (!(base instanceof MatrixExpr)) throw new TypeError('MatPow base should be a matrix');
    if (base.isSquare === false) throw new NonSquareMatrixError(`Power of non-square matrix ${str(base)}`);
    return new MatPowNode(base, sympify(expIn));
  }
  /** The base. */
  get base(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  /** The exponent. */
  get exp(): Expr {
    return this.args[1]!;
  }
  get shape(): [Expr, Expr] {
    return this.base.shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatPowNode(args[0]!, args[1]!);
  }
  override entry(i: Expr, j: Expr): Expr {
    let A = this.doit();
    if (A instanceof MatPowNode) {
      const e = A.exp;
      if (isInt(e) && e.p > 0n) {
        A = new MatMulNode(Array.from({ length: toInt(e) }, () => (A as MatPowNode).base));
      } else if (isInt(this.rows) && isInt(this.cols)) {
        const m = A.base.asExplicit();
        const p = isInt(e) ? (toInt(e) >= 0 ? m.pow(toInt(e)) : m.inv().pow(-toInt(e))) : undefined;
        if (p) return p.get(toInt(i), toInt(j));
        return new MatrixElementNode(this, i, j);
      } else return new MatrixElementNode(this, i, j);
    }
    return (A as MatrixExpr).at(i, j);
  }
  override doit(hints: DoitHints = {}): Expr {
    let base: Expr = this.args[0]!;
    let exp: Expr = this.args[1]!;
    if (hints.deep !== false) {
      base = doitArg(base, hints);
      exp = doitArg(exp, hints);
    }
    while (base instanceof MatPowNode) {
      exp = mul(exp, base.args[1]!);
      base = base.args[0]!;
    }
    const b = base as MatrixExpr;
    if (b instanceof ImmutableMatrixNode) return b.evalPower(exp);
    if (same(exp, S.One)) return b;
    if (same(exp, S.Zero)) return new IdentityNode(b.rows);
    if (same(exp, S.NegOne)) return InverseNode.create(b).doit(hints);
    return b.evalPower(exp);
  }
  override evalTranspose(): Expr {
    return new MatPowNode(this.base.transpose(), this.exp);
  }
  override evalAdjoint(): Expr {
    return new MatPowNode(this.base.adjoint(), this.exp);
  }
  override evalConjugate(): Expr {
    return new MatPowNode(this.base.conjugate(), this.exp);
  }
  override evalInverse(): Expr {
    return new MatPowNode(this.base, mul(-1, this.exp));
  }
  override strPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  override printStr(): string {
    return `${parenStr(this.base, PRECEDENCE.Pow)}**${parenStr(this.exp, PRECEDENCE.Pow)}`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const base = this.base;
    const e = print(this.exp);
    if (!(base instanceof MatrixSymbolNode) && base.isMatrixExpr) return `\\left(${print(base)}\\right)^{${e}}`;
    const b = print(base);
    return b.includes('^') ? `\\left(${b}\\right)^{${e}}` : `${b}^{${e}}`;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    const e = this.exp;
    if (e.has(x)) return undefined;
    if (isInt(e) && e.p > 0n) return new MatMulNode(Array.from({ length: toInt(e) }, () => this.base)).diffSelf(x, d);
    if (isInt(e) && e.p < 0n) return new MatMulNode(Array.from({ length: -toInt(e) }, () => new InverseNode(this.base))).diffSelf(x, d);
    return undefined;
  }
}

/** SymPy MatPow(base, exp): an unevaluated power. */
export const MatPow = /* @__PURE__ */ callableClass(MatPowNode, (base: MatArg, exp: ExprLike): MatPowNode => MatPowNode.create(base, exp));
export type MatPow = MatPowNode;

/** SymPy Inverse(A): the inverse of a square matrix, printed A**(-1). */
export class InverseNode extends MatPowNode {
  constructor(mat: Expr) {
    super(mat, S.NegOne, 'Inverse');
  }
  /** SymPy Inverse(mat): validated, unevaluated. */
  static override create(matIn: MatArg): InverseNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError('mat should be a matrix');
    if (mat.isSquare === false) throw new NonSquareMatrixError(`Inverse of non-square matrix ${str(mat)}`);
    return new InverseNode(mat);
  }
  /** The inverted matrix. */
  get arg(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  override withArgs(args: readonly Expr[]): Expr {
    return new InverseNode(args[0]!);
  }
  override evalInverse(): Expr {
    return this.arg;
  }
  override evalTranspose(): Expr {
    return new InverseNode(asMat(this.arg.transpose()));
  }
  override evalAdjoint(): Expr {
    return new InverseNode(asMat(this.arg.adjoint()));
  }
  override evalConjugate(): Expr {
    return new InverseNode(asMat(this.arg.conjugate()));
  }
  override evalDeterminant(): Expr {
    return pow(det(this.arg), -1);
  }
  override doit(hints: DoitHints = {}): Expr {
    if (hints.invExpand === false) return this;
    const arg = hints.deep === false ? this.arg : doitArg(this.arg, hints);
    return asMat(arg).inverse();
  }
  override printStr(): string {
    return `${parenStr(this.arg, PRECEDENCE.Pow)}**(-1)`;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return matMul(-1, this, mdiff(this.arg, x, d), this);
  }
}

/** SymPy Inverse(A): an unevaluated inverse. */
export const Inverse = /* @__PURE__ */ callableClass(InverseNode, (mat: MatArg): InverseNode => InverseNode.create(mat));
export type Inverse = InverseNode;

// ---------------------------------------------------------------------------
// Transpose and Adjoint
// ---------------------------------------------------------------------------

/** SymPy Transpose(A): the transpose, printed A.T. */
export class TransposeNode extends MatrixExpr {
  constructor(arg: Expr) {
    super('Transpose', [arg]);
  }
  /** The transposed matrix. */
  get arg(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  get shape(): [Expr, Expr] {
    const [r, c] = this.arg.shape;
    return [c, r];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new TransposeNode(args[0]!);
  }
  override doit(hints: DoitHints = {}): Expr {
    const arg = hints.deep === false ? this.args[0]! : doitArg(this.args[0]!, hints);
    return arg instanceof MatrixExpr ? arg.evalTranspose() : transposeFn(arg);
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return this.arg.entry(j, i, ctx);
  }
  override evalAdjoint(): Expr {
    return this.arg.conjugate();
  }
  override evalConjugate(): Expr {
    return this.arg.adjoint();
  }
  override evalTranspose(): Expr {
    return this.arg;
  }
  override evalTrace(): Expr {
    return new TraceNode(this.arg);
  }
  override evalDeterminant(): Expr {
    return det(this.arg);
  }
  override latexPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  override printStr(): string {
    return `${parenStr(this.arg, PRECEDENCE.Pow)}.T`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return postfixLatex(this.arg, 'T', print);
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return transposeOf(mdiff(this.arg, x, d));
  }
}

/** LaTeX of A^{T} and A^{\dagger} (SymPy _print_Transpose and _print_Adjoint). */
function postfixLatex(mat: MatrixExpr, sup: string, print: (e: Expr) => string): string {
  if (!(mat instanceof MatrixSymbolNode) && mat.name !== 'BlockMatrix' && mat.name !== 'BlockDiagMatrix' && mat.isMatrixExpr) return `\\left(${print(mat)}\\right)^{${sup}}`;
  const s = parenLatex(mat, PRECEDENCE.Pow, true);
  return s.includes('^') ? `\\left(${s}\\right)^{${sup}}` : `${s}^{${sup}}`;
}

/** SymPy Transpose(A): an unevaluated transpose. */
export const Transpose = /* @__PURE__ */ callableClass(TransposeNode, (arg: MatArg): TransposeNode => new TransposeNode(toMatrix(arg)));
export type Transpose = TransposeNode;

/** SymPy Adjoint(A): the conjugate transpose. */
export class AdjointNode extends MatrixExpr {
  constructor(arg: Expr) {
    super('Adjoint', [arg]);
  }
  /** The matrix. */
  get arg(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  get shape(): [Expr, Expr] {
    const [r, c] = this.arg.shape;
    return [c, r];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new AdjointNode(args[0]!);
  }
  override doit(hints: DoitHints = {}): Expr {
    const arg = hints.deep === false ? this.args[0]! : doitArg(this.args[0]!, hints);
    return adjointFn(arg);
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return conjugateFn(this.arg.entry(j, i, ctx));
  }
  override evalAdjoint(): Expr {
    return this.arg;
  }
  override evalTranspose(): Expr {
    return this.arg.conjugate();
  }
  override evalConjugate(): Expr {
    return this.arg.transpose();
  }
  override evalTrace(): Expr {
    return conjugateFn(new TraceNode(this.arg));
  }
  override latexPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  override printLatex(print: (e: Expr) => string): string {
    return postfixLatex(this.arg, '\\dagger', print);
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return adjointFn(mdiff(this.arg, x, d));
  }
}

/** SymPy Adjoint(A): an unevaluated adjoint. */
export const Adjoint = /* @__PURE__ */ callableClass(AdjointNode, (arg: MatArg): AdjointNode => new AdjointNode(toMatrix(arg)));
export type Adjoint = AdjointNode;

// ---------------------------------------------------------------------------
// MatrixSlice
// ---------------------------------------------------------------------------

type Triple = [Expr, Expr, Expr];

/** SymPy slice.normalize. */
function normalizeSlice(spec: SliceSpec, size: Expr): Triple {
  let parts: (Expr | null)[];
  if (Array.isArray(spec)) parts = (spec as readonly (ExprLike | null | undefined)[]).map((x) => (x === null || x === undefined ? null : sympify(x)));
  else {
    let i = sympify(spec as ExprLike);
    if (relTruth('Lt', i, S.Zero) === true) i = add(i, size);
    parts = [i, add(i, 1), S.One];
  }
  while (parts.length < 3) parts.push(null);
  let start = parts[0] ?? S.Zero;
  let stop = parts[1] ?? size;
  if (relTruth('Lt', start, S.Zero) === true) start = add(start, size);
  if (relTruth('Lt', stop, S.Zero) === true) stop = add(stop, size);
  const step = parts[2] === null || same(parts[2]!, S.Zero) ? S.One : parts[2]!;
  if (relTruth('Lt', mul(add(stop, mul(-1, start)), step), S.One) === true) throw new RangeError('Invalid slice');
  return [start, stop, step];
}

function sliceOfSlice(s: Triple, t: Triple): Triple {
  const [start1, stop1, step1] = s;
  const [start2, stop2, step2] = t;
  const start = add(start1, mul(start2, step1));
  const step = mul(step1, step2);
  const stop = add(start1, mul(step1, stop2));
  if (relTruth('Gt', stop, stop1) === true) throw new RangeError('Invalid slice');
  return [start, stop, step];
}

/** SymPy MatrixSlice(parent, rowslice, colslice): a slice of a matrix expression. */
export class MatrixSliceNode extends MatrixExpr {
  constructor(parent: Expr, rowslice: Triple, colslice: Triple) {
    super('MatrixSlice', [parent, ...rowslice, ...colslice]);
  }
  /** SymPy MatrixSlice(parent, rowslice, colslice) with normalization and bounds checks. */
  static create(parentIn: MatArg, rowSpec: SliceSpec, colSpec: SliceSpec): Expr {
    const parent = toMatrix(parentIn);
    const rs = normalizeSlice(rowSpec, parent.rows);
    const cs = normalizeSlice(colSpec, parent.cols);
    if (relTruth('Gt', S.Zero, rs[0]) === true || relTruth('Lt', parent.rows, rs[1]) === true || relTruth('Gt', S.Zero, cs[0]) === true || relTruth('Lt', parent.cols, cs[1]) === true) {
      throw new RangeError('Invalid slice');
    }
    if (parent instanceof MatrixSliceNode) return new MatrixSliceNode(parent.parent, sliceOfSlice(parent.rowslice, rs), sliceOfSlice(parent.colslice, cs));
    return new MatrixSliceNode(parent, rs, cs);
  }
  /** The sliced matrix. */
  get parent(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  /** (start, stop, step) of the rows. */
  get rowslice(): Triple {
    return [this.args[1]!, this.args[2]!, this.args[3]!];
  }
  /** (start, stop, step) of the columns. */
  get colslice(): Triple {
    return [this.args[4]!, this.args[5]!, this.args[6]!];
  }
  /** SymPy on_diag: the row and column slices agree. */
  get onDiag(): boolean {
    return sameList(this.rowslice, this.colslice);
  }
  get shape(): [Expr, Expr] {
    const len = ([a, b, s]: Triple): Expr => {
      const n = add(b, mul(-1, a));
      return same(s, S.One) ? n : floor(mul(n, pow(s, -1)));
    };
    return [len(this.rowslice), len(this.colslice)];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSliceNode(args[0]!, [args[1]!, args[2]!, args[3]!], [args[4]!, args[5]!, args[6]!]);
  }
  override sortArgs(): readonly Expr[] {
    return [this.parent, new TupleNode(this.rowslice), new TupleNode(this.colslice)];
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const [r0, , rs] = this.rowslice;
    const [c0, , cs] = this.colslice;
    return this.parent.entry(add(mul(i, rs), r0), add(mul(j, cs), c0), ctx);
  }
  override printStr(print: (e: Expr) => string): string {
    const sl = (x: Triple, d: Expr): string => {
      const parts: string[] = [same(x[0], S.Zero) ? '' : print(x[0]), same(x[1], d) ? '' : print(x[1])];
      if (!same(x[2], S.One)) parts.push(print(x[2]));
      return parts.join(':');
    };
    return `${parenStr(this.parent, PRECEDENCE.Atom, true)}[${sl(this.rowslice, this.parent.rows)}, ${sl(this.colslice, this.parent.cols)}]`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const sl = (x: Triple, d: Expr): string => {
      const parts: string[] = [same(x[0], S.Zero) ? '' : print(x[0]), same(x[1], d) ? '' : print(x[1])];
      if (!same(x[2], S.One)) parts.push(print(x[2]));
      return parts.join(':');
    };
    return `${parenLatex(this.parent, PRECEDENCE.Atom, true)}\\left[${sl(this.rowslice, this.parent.rows)}, ${sl(this.colslice, this.parent.cols)}\\right]`;
  }
}

/** A tuple used only in sort keys (SymPy Tuple). */
class TupleNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Tuple', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new TupleNode(args);
  }
}

/** SymPy MatrixSlice(parent, rowslice, colslice). */
export const MatrixSlice = /* @__PURE__ */ callableClass(MatrixSliceNode, (parent: MatArg, rowslice: SliceSpec, colslice: SliceSpec): Expr => MatrixSliceNode.create(parent, rowslice, colslice));
export type MatrixSlice = MatrixSliceNode;

// ---------------------------------------------------------------------------
// Trace, Determinant, Permanent
// ---------------------------------------------------------------------------

/** SymPy Trace(A): the unevaluated trace of a square matrix. */
export class TraceNode extends MatScalar {
  constructor(mat: Expr) {
    super('Trace', [mat]);
  }
  /** SymPy Trace(mat): validated, unevaluated. */
  static create(matIn: MatArg): TraceNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError(`input to Trace, ${str(mat)}, is not a matrix`);
    if (mat.isSquare === false) throw new NonSquareMatrixError('Trace of a non-square matrix');
    return new TraceNode(mat);
  }
  /** The matrix. */
  get arg(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new TraceNode(args[0]!);
  }
  override doit(hints: DoitHints = {}): Expr {
    if (hints.deep !== false) {
      const arg = doitArg(this.arg, hints);
      return arg instanceof MatrixExpr ? arg.evalTrace() : new TraceNode(arg);
    }
    return this.arg instanceof ImmutableMatrixNode ? trace(this.arg) : this;
  }
  /** SymPy Trace.as_explicit: the trace of the explicit matrix. */
  asExplicit(): Expr {
    return new TraceNode(new ImmutableMatrixNode(this.arg.asExplicit())).doit();
  }
  /** SymPy Trace.rewrite(Sum): the sum of the diagonal entries. */
  rewriteAsSum(): Expr {
    const i = new Sym(uniqueName('i', this));
    return doitArg(Sum(this.arg.at(i, i), [i, S.Zero, add(this.arg.rows, -1)]));
  }
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'Sum' ? this.rewriteAsSum() : undefined;
  }
  override transposeSelf(): Expr {
    return this;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{tr}\\left(${print(this.arg)} \\right)`;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if (x instanceof MatrixElementNode) return d(this.rewriteAsSum(), x);
    const r = mdiff(this.arg, x, d);
    return r instanceof MatrixExpr ? trace(r) : undefined;
  }
}

/** A symbol name not used in the expression (SymPy uniquely_named_symbol). */
function uniqueName(base: string, e: Expr): string {
  const used = new Set([...freeSymbols(e)].map((s) => s.name));
  if (!used.has(base)) return base;
  for (let k = 0; ; k++) if (!used.has(`${base}${k}`)) return `${base}${k}`;
}

/** SymPy Trace(A): an unevaluated trace. */
export const Trace = /* @__PURE__ */ callableClass(TraceNode, (mat: MatArg): TraceNode => TraceNode.create(mat));
export type Trace = TraceNode;

/** SymPy trace(A): the trace, evaluated where possible (trace(eye(3)) = 3, trace(2*X) = 2*Trace(X)). */
export function trace(expr: MatArg): Expr {
  if (expr instanceof Matrix) return expr.trace();
  return TraceNode.create(expr).doit();
}

/** SymPy Determinant(A): the unevaluated determinant of a square matrix. */
export class DeterminantNode extends MatScalar {
  constructor(mat: Expr) {
    super('Determinant', [mat]);
  }
  /** SymPy Determinant(mat): validated, unevaluated. */
  static create(matIn: MatArg): DeterminantNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError(`Input to Determinant, ${str(mat)}, not a matrix`);
    if (mat.isSquare === false) throw new NonSquareMatrixError('Det of a non-square matrix');
    return new DeterminantNode(mat);
  }
  /** The matrix. */
  get arg(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DeterminantNode(args[0]!);
  }
  override doit(hints: DoitHints = {}): Expr {
    const arg = hints.deep === false ? this.arg : doitArg(this.arg, hints);
    return arg instanceof MatrixExpr ? arg.evalDeterminant() : this;
  }
  override printLatex(print: (e: Expr) => string): string {
    const m = this.arg;
    if (m instanceof ImmutableMatrixNode) return `\\left|{${explicitLatexContents(m.matrix, print)}}\\right|`;
    if (m.name === 'BlockMatrix' || m.name === 'BlockDiagMatrix') {
      const blocks = (m as unknown as { blocks: Matrix }).blocks;
      return `\\left|{${explicitLatexContents(blocks, print)}}\\right|`;
    }
    return `\\left|{${print(m)}}\\right|`;
  }
}

/** SymPy Determinant(A): an unevaluated determinant. */
export const Determinant = /* @__PURE__ */ callableClass(DeterminantNode, (mat: MatArg): DeterminantNode => DeterminantNode.create(mat));
export type Determinant = DeterminantNode;

/** SymPy det(A): the determinant, evaluated where possible (det(A) = Determinant(A), det(eye(3)) = 1). */
export function det(matexpr: MatArg): Expr {
  if (matexpr instanceof Matrix) return matexpr.det();
  return DeterminantNode.create(matexpr).doit();
}

/** SymPy Permanent(A): the unevaluated permanent of a matrix. */
export class PermanentNode extends MatScalar {
  constructor(mat: Expr) {
    super('Permanent', [mat]);
  }
  /** SymPy Permanent(mat): validated, unevaluated. */
  static create(matIn: MatArg): PermanentNode {
    const mat = toExpr(matIn);
    if (!(mat instanceof MatrixExpr)) throw new TypeError(`Input to Permanent, ${str(mat)}, not a matrix`);
    return new PermanentNode(mat);
  }
  /** The matrix. */
  get arg(): MatrixExpr {
    return this.args[0] as MatrixExpr;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new PermanentNode(args[0]!);
  }
  override doit(): Expr {
    if (this.arg instanceof ImmutableMatrixNode) return explicitPermanent(this.arg.matrix);
    return this;
  }
}

/** SymPy Permanent(A): an unevaluated permanent. */
export const Permanent = /* @__PURE__ */ callableClass(PermanentNode, (mat: MatArg): PermanentNode => PermanentNode.create(mat));
export type Permanent = PermanentNode;

/** SymPy per(A): the permanent, evaluated for explicit matrices (per(ones(5, 5)) = 120). */
export function per(matexpr: MatArg): Expr {
  return PermanentNode.create(matexpr).doit();
}

// ---------------------------------------------------------------------------
// ElementwiseApplyFunction
// ---------------------------------------------------------------------------

/** A function given to applyfunc: a Lambda or a JavaScript function of one expression. */
export type ElementFunction = LambdaNode | ((x: Expr) => Expr);

const toLambda = (f: ElementFunction): LambdaNode => {
  if (f instanceof LambdaNode) return f;
  const d = new Dummy('d');
  return new LambdaNode([d, f(d)]);
};

/** SymPy ElementwiseApplyFunction(function, expr): a function applied to every entry, printed f.(X). */
export class ElementwiseApplyFunctionNode extends MatrixExpr {
  constructor(fn: LambdaNode, expr: Expr) {
    super('ElementwiseApplyFunction', [fn, expr]);
  }
  /** SymPy ElementwiseApplyFunction(function, expr). */
  static create(f: ElementFunction, exprIn: MatArg): Expr {
    const expr = toExpr(exprIn);
    if (!(expr instanceof MatrixExpr)) throw new TypeError(`${str(expr)} must be a matrix instance.`);
    if (same(expr.rows, S.One) && same(expr.cols, S.One)) {
      const ret = f instanceof LambdaNode ? f.call(expr) : f(expr);
      if (ret instanceof MatrixExpr) return ret;
    }
    const lam = toLambda(f);
    if (lam.variables.length !== 1) throw new TypeError(`${str(lam)} should be able to accept 1 arguments.`);
    return new ElementwiseApplyFunctionNode(lam, expr);
  }
  /** The function (a Lambda). */
  get function(): LambdaNode {
    return this.args[0] as LambdaNode;
  }
  /** The matrix. */
  get expr(): MatrixExpr {
    return this.args[1] as MatrixExpr;
  }
  get shape(): [Expr, Expr] {
    return this.expr.shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new ElementwiseApplyFunctionNode(args[0] as LambdaNode, args[1]!);
  }
  override doit(hints: DoitHints = {}): Expr {
    const expr = hints.deep === false ? this.expr : doitArg(this.expr, hints);
    const f = this.function;
    if (f.variables.length === 1 && same(f.variables[0]!, f.expr)) return expr;
    if (expr instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(expr.matrix.map((e) => f.call(e)));
    if (expr instanceof ElementwiseApplyFunctionNode) {
      const g = expr.function;
      const r = ElementwiseApplyFunctionNode.create((x: Expr) => f.call(g.call(x)), expr.expr);
      return r instanceof MatrixExpr ? r.doit(hints) : r;
    }
    return expr === this.expr ? this : new ElementwiseApplyFunctionNode(f, expr);
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return this.function.call(this.expr.entry(i, j, ctx));
  }
  override evalTranspose(): Expr {
    return new ElementwiseApplyFunctionNode(this.function, this.expr.transpose());
  }
  override printStr(print: (e: Expr) => string): string {
    return `${print(this.function)}.(${print(this.expr)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `{${print(this.function)}}_{\\circ}\\left({${print(this.expr)}}\\right)`;
  }
}

/** SymPy ElementwiseApplyFunction(function, expr). */
export const ElementwiseApplyFunction = /* @__PURE__ */ callableClass(ElementwiseApplyFunctionNode, (f: ElementFunction, expr: MatArg): Expr => ElementwiseApplyFunctionNode.create(f, expr));
export type ElementwiseApplyFunction = ElementwiseApplyFunctionNode;

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

/** SymPy MatrixSymbol(name, n, m): a symbolic n x m matrix (also usable with new). */
export const MatrixSymbol = /* @__PURE__ */ callableClass(MatrixSymbolNode, (name: string, n: ExprLike, m: ExprLike): MatrixSymbolNode => new MatrixSymbolNode(name, n, m));
export type MatrixSymbol = MatrixSymbolNode;

/** SymPy Identity(n). */
export const Identity = /* @__PURE__ */ callableClass(IdentityNode, (n: ExprLike): IdentityNode => new IdentityNode(n));
export type Identity = IdentityNode;

/** SymPy ZeroMatrix(m, n). */
export const ZeroMatrix = /* @__PURE__ */ callableClass(ZeroMatrixNode, (m: ExprLike, n: ExprLike): ZeroMatrixNode => new ZeroMatrixNode(m, n));
export type ZeroMatrix = ZeroMatrixNode;

/** SymPy OneMatrix(m, n, evaluate=false). */
export const OneMatrix = /* @__PURE__ */ callableClass(OneMatrixNode, (m: ExprLike, n: ExprLike, evaluate = false): MatrixExpr => OneMatrixNode.create(m, n, evaluate));
export type OneMatrix = OneMatrixNode;

/** SymPy GenericIdentity(). */
export const GenericIdentity = /* @__PURE__ */ callableClass(GenericIdentityNode, (): GenericIdentityNode => new GenericIdentityNode());
export type GenericIdentity = GenericIdentityNode;

/** SymPy GenericZeroMatrix(). */
export const GenericZeroMatrix = /* @__PURE__ */ callableClass(GenericZeroMatrixNode, (): GenericZeroMatrixNode => new GenericZeroMatrixNode());
export type GenericZeroMatrix = GenericZeroMatrixNode;

/** SymPy MatrixElement(parent, i, j). */
export const MatrixElement = /* @__PURE__ */ callableClass(MatrixElementNode, matrixElement);
export type MatrixElement = MatrixElementNode;

/**
 * SymPy ImmutableMatrix: an explicit matrix as a matrix expression, from a
 * Matrix, nested rows, or (rows, cols, entries).
 */
export const ImmutableMatrix = /* @__PURE__ */ callableClass(
  ImmutableMatrixNode,
  (a: Matrix | readonly (readonly ExprLike[])[] | number, cols?: number, entries?: readonly ExprLike[] | ((i: number, j: number) => ExprLike)): ImmutableMatrixNode => {
    if (a instanceof Matrix) return new ImmutableMatrixNode(a);
    if (typeof a === 'number') {
      const c = cols ?? 0;
      const f = typeof entries === 'function' ? entries : (i: number, j: number): ExprLike => entries?.[i * c + j] ?? 0;
      return new ImmutableMatrixNode(Matrix.fromFunction(a, c, f));
    }
    return new ImmutableMatrixNode(Matrix.of(a));
  },
);
export type ImmutableMatrix = ImmutableMatrixNode;

/** SymPy matrix_symbols(expr): the MatrixSymbols of an expression. */
export function matrixSymbols(expr: MatArg): MatrixSymbolNode[] {
  const out = new Map<string, MatrixSymbolNode>();
  const go = (e: Expr): void => {
    if (e instanceof MatrixSymbolNode) out.set(e.key, e);
    else e.args.forEach(go);
  };
  go(toExpr(expr));
  return [...out.values()];
}
