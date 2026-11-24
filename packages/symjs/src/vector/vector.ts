// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/vector.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.vector: Vector and its classes (BaseVector,
 * VectorAdd, VectorMul, VectorZero), the unevaluated products Cross and
 * Dot, and the functions cross and dot.
 *
 * `C.i.mul(3).add(C.j)` (or `add(mul(3, C.i), C.j)`) is the vector
 * `3*C.i + C.j`; SymPy's operators `&`, `^` and `|` are the methods dot,
 * cross and outer.
 */

import { Add, Dummy, ExtensionExpr, Mul, Pow, Rational, S } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sqrt, sympify } from '../core/ops';
import { ExprMap } from '../core/exprmap';
import { callableClass } from '../core/callable';
import { at, cast, defined } from '../core/guard';
import { NumberKind } from '../core/kind';
import type { Kind } from '../core/kind';
import { Matrix } from '../matrices/matrix';
import { vectorProducts } from '../matrices/linalg';
import { compareKeys, sortKey } from '../printing/sortkey';
import { PREC, declaredPrecedence, precedence } from '../printing/str';
import { prettyHooks } from '../printing/pretty/pretty';
import { PrettyForm } from '../printing/pretty/stringpict';
import type { PrettyPrinter } from '../printing/pretty/pretty';
import { NotImplementedError } from '../core/errors';
import { exprEquals } from '../geometry/point';
import { minimalPolynomial } from '../polys/numberfields';
import { BasisDependent, CoordSysBase, DelBase, basisAdd, basisMul, expressHook, registerFamily, vectorHooks } from './basisdependent';
import type { BasisFamily, ScaledBase } from './basisdependent';
import { VectorKind } from './kind';
import { BaseScalarNode } from './scalar';

/** A dyadic, as vector.ts sees it (dyadic.ts registers the family 'Dyadic'). */
const isDyadic = (e: Expr): e is BasisDependent => e instanceof BasisDependent && e.family.name === 'Dyadic';

/** The zero dyadic (registered by dyadic.ts). */
function dyadicZero(): Expr {
  return defined(dyadicFamilyRef.family, 'Dyadic').zero;
}

/** The dyadic family, set by dyadic.ts through registerDyadicFamily. */
const dyadicFamilyRef: { family?: BasisFamily } = {};

/** Registers the dyadic family (called by dyadic.ts). */
export function registerDyadicFamily(f: BasisFamily): void {
  dyadicFamilyRef.family = f;
  registerFamily(f);
}

/** The options of Vector.projection. */
export interface ProjectionOptions {
  /** Return the scalar projection. */
  readonly scalar?: boolean;
}

/**
 * The super class of all vector classes.
 *
 * @see SymPy `sympy.vector.vector.Vector`
 */
export abstract class Vector extends BasisDependent {
  /**
   * The operations shared by elements of this basis family.
   *
   * @returns The operations shared by elements of this basis family.
   */
  override get family(): BasisFamily {
    return VECTOR;
  }

  /**
   * The zero vector.
   *
   * @returns The zero vector.
   * @see SymPy `sympy.vector.vector.Vector.zero`
   */
  static get zero(): VectorZeroNode {
    return ZERO;
  }

  /**
   * Whether this expression is a vector.
   *
   * @returns Whether this expression is a vector.
   * @see SymPy `sympy.vector.vector.Vector.is_Vector`
   */
  get isVector(): boolean {
    return true;
  }

  /**
   * VectorKind(NumberKind).
   *
   * @returns The kind of this expression.
   * @see SymPy `sympy.vector.vector.Vector.kind`
   */
  override kindSelf(): Kind {
    return VectorKind(NumberKind);
  }

  /**
   * The length sqrt(v & v).
   *
   * @returns The length sqrt(v & v).
   * @see SymPy `sympy.vector.vector.Vector.magnitude`
   */
  magnitude(): Expr {
    return sqrt(this.dot(this));
  }

  /**
   * The vector divided by its magnitude.
   *
   * @returns The vector divided by its magnitude.
   * @see SymPy `sympy.vector.vector.Vector.normalize`
   */
  normalize(): Expr {
    return this.div(this.magnitude());
  }

  /**
   * The vectors are equal for all values of the symbols (also across coordinate systems). An
   * undecided comparison is false.
   *
   * @param other - Object to compare with this one.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.vector.vector.Vector.equals`
   */
  override equals(other: ExprLike): boolean {
    const d = this.sub(other);
    return equalsZero(dot(d, d)) === true;
  }

  /**
   * The dot product with a vector (a scalar) or a dyadic (a vector). With a Del operator it is the
   * directional derivative operator, a function of a scalar field.
   *
   * @param other - Other operand of the inner product.
   * @returns The inner product, or a directional derivative operator when `other` is `Del`.
   * @throws TypeError when the operand is not a vector, dyadic or del operator.
   * @see SymPy `sympy.vector.vector.Vector.dot`
   */
  dot(other: DelBase): (field: ExprLike) => Expr;
  dot(other: Expr): Expr;
  dot(other: Expr): Expr | ((field: ExprLike) => Expr) {
    if (isDyadic(other)) {
      let out: Expr = ZERO;
      if (this instanceof VectorZeroNode) return out;
      for (const [k, v] of other.components) out = add(out, mul(dot(at(k.args, 0), this), v, at(k.args, 1)));
      return out;
    }
    if (other instanceof DelBase) return (field: ExprLike) => defined(vectorHooks.directionalDerivative, 'directional_derivative')(sympify(field), this);
    if (!(other instanceof Vector)) throw new TypeError(`${String(other)} is not a vector, dyadic or del operator`);
    return dot(this, other);
  }

  /**
   * The cross product with a vector (a vector) or a dyadic (a dyadic).
   *
   * @param other - Other operand of the cross product.
   * @returns The cross product with a vector (a vector) or a dyadic (a dyadic).
   * @see SymPy `sympy.vector.vector.Vector.cross`
   */
  cross(other: Expr): Expr {
    if (isDyadic(other)) {
      let out = dyadicZero();
      if (this instanceof VectorZeroNode) return out;
      for (const [k, v] of other.components) out = add(out, mul(v, outer(cross(this, at(k.args, 0)), at(k.args, 1))));
      return out;
    }
    return cross(this, other);
  }

  /**
   * The outer product, a dyadic.
   *
   * @param other - Right operand of the outer product.
   * @returns The outer product, a dyadic.
   * @see SymPy `sympy.vector.vector.Vector.outer`
   */
  outer(other: Expr): Expr {
    return outer(this, other);
  }

  /**
   * The vector (or with `scalar`, scalar) projection of other on this vector.
   *
   * @param other - Operand to project.
   * @param opts - Settings described by {@link ProjectionOptions}.
   * @returns The vector (or with `scalar`, scalar) projection of other on this vector.
   * @see SymPy `sympy.vector.vector.Vector.projection`
   */
  projection(other: Expr, opts: ProjectionOptions = {}): Expr {
    if (this.equals(ZERO)) return opts.scalar === true ? S.Zero : ZERO;
    const c = mul(dot(this, other), dot(this, this).pow(-1));
    return opts.scalar === true ? c : mul(c, this);
  }

  /**
   * The column of the components along the base vectors of system.
   *
   * @param system - Coordinate system in which to express components.
   * @returns The column of the components along the base vectors of system.
   * @see SymPy `sympy.vector.vector.Vector.to_matrix`
   */
  toMatrix(system: CoordSysBase): Matrix {
    return Matrix.col(...system.baseVectors().map((u) => dot(this, u)));
  }

  /**
   * The constituents of the vector in each coordinate system.
   *
   * @returns The constituents of the vector in each coordinate system.
   * @see SymPy `sympy.vector.vector.Vector.separate`
   */
  separate(): ExprMap<Expr> {
    const parts = new ExprMap<Expr>();
    for (const [k, v] of this.components) {
      const sys = baseVectorOf(k).system;
      parts.set(sys, add(parts.get(sys) ?? ZERO, mul(k, v)));
    }
    return parts;
  }

  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    if (this instanceof VectorZeroNode) return VECTOR_ZERO_LATEX;
    const items: [Expr, Expr][] = [];
    for (const part of this.separate().values()) {
      const inner = [...asVector(part).components].sort((a, b) => compareStr(String(a[0]), String(b[0])));
      items.push(...inner);
    }
    return basisLatex(items, print);
  }
}

/** An algebraic number: rationals and I under sums, products and rational powers. */
const isAlgebraicNumber = (e: Expr): boolean =>
  e instanceof Rational || e === S.I || ((e instanceof Add || e instanceof Mul) && e.args.every(isAlgebraicNumber)) || (e instanceof Pow && e.exp instanceof Rational && isAlgebraicNumber(e.base));

/**
 * SymPy Expr.equals(0): exprEquals of the geometry, and for an algebraic
 * number that it cannot decide, SymPy's proof by its minimal polynomial.
 */
export function equalsZero(e: Expr): boolean | undefined {
  const r = exprEquals(e, S.Zero);
  if (r !== undefined || !isAlgebraicNumber(e)) return r;
  const x = new Dummy('x');
  return minimalPolynomial(e, x).key === x.key;
}

const asVector = (e: Expr): Vector => cast(e, Vector, 'vector');

/** Order of printed names (they are distinct). */
export const compareStr = (a: string, b: string): number => (a < b ? -1 : 1);

/** The LaTeX of the zero vector (SymPy VectorZero._latex_form). */
const VECTOR_ZERO_LATEX = '\\mathbf{\\hat{0}}';

/**
 * SymPy LatexPrinter._print_BasisDependent: the terms (base instance,
 * measure) in printing order.
 */
export function basisLatex(items: readonly (readonly [Expr, Expr])[], print: (e: Expr) => string): string {
  const parts = items.map(([k, v]) => {
    const form = latexFormOf(k);
    if (v instanceof Rational && v.isOne) return ` + ${form}`;
    if (v instanceof Rational && v.p === -1n && v.q === 1n) return ` - ${form}`;
    return ` + \\left(${print(v)}\\right)${form}`;
  });
  const out = parts.join('');
  return out[1] !== '-' ? out.slice(3) : out.slice(1);
}

/** The LaTeX form of a base vector or base dyadic (SymPy _latex_form). */
function latexFormOf(k: Expr): string {
  return k.toLatex();
}

/**
 * A base vector of a coordinate system.
 *
 * @see SymPy `sympy.vector.vector.BaseVector`
 */
export class BaseVectorNode extends Vector implements ScaledBase {
  /** Zero-based index or indices selecting the desired component. */
  readonly index: number;
  /**
   * The coordinate system that supplies the basis.
   *
   * @see SymPy `sympy.vector.vector.BaseVector.system`
   */
  readonly system: CoordSysBase;
  readonly #pretty: string;
  /** LaTeX representation of this basis element. */
  readonly latexForm: string;
  #components: ExprMap<Expr> | undefined;

  /**
   * Constructs an instance of `BaseVectorNode`.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @param system - Coordinate system in which to express components.
   * @param prettyStr - Label for the pretty printer.
   * @param latexStr - Label for the LaTeX printer.
   * @throws RangeError when the basis index is outside 0 through 2.
   * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
   */
  constructor(index: number, system: CoordSysBase, prettyStr?: string, latexStr?: string) {
    if (!Number.isInteger(index) || index < 0 || index > 2) throw new RangeError('index must be 0, 1 or 2');
    if (!(system instanceof CoordSysBase)) throw new TypeError('system should be a CoordSys3D');
    super('BaseVector', []);
    this.index = index;
    this.system = system;
    this.#pretty = prettyStr ?? `x${index}`;
    this.latexForm = latexStr ?? `x_${index}`;
  }
  /**
   * The base vector as an attribute of its system.
   *
   * @param repr - Formatter for expression arguments.
   * @returns The constructor representation.
   */
  printRepr(repr: (e: Expr) => string): string {
    return `${repr(this.system)}.${at(this.system.vectorNames, this.index)}`;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @returns This expression.
   */
  withArgs(): Expr {
    return this;
  }
  /**
   * The label used by the pretty printer.
   *
   * @returns The label used by the pretty printer.
   */
  override get prettyForm(): string {
    return this.#pretty;
  }
  /**
   * The scalar coefficients keyed by their basis vectors.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.vector.BaseVector.components`
   */
  override get components(): ExprMap<Expr> {
    return (this.#components ??= new ExprMap<Expr>([[this, S.One]]));
  }
  /**
   * The scalar coefficient multiplying the basis element.
   *
   * @returns The scalar coefficient multiplying the basis element.
   */
  get measureNumber(): Expr {
    return S.One;
  }
  /**
   * The basis element carrying the scalar coefficient.
   *
   * @returns The basis element carrying the scalar coefficient.
   */
  get baseInstance(): BaseVectorNode {
    return this;
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return `${this.system.sysName}.${at(this.system.vectorNames, this.index)}`;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @returns The formatted LaTeX.
   */
  override printLatex(): string {
    return this.latexForm;
  }
  /**
   * A base vector is its own conjugate.
   *
   * @returns A base vector is its own conjugate.
   * @see SymPy `sympy.vector.vector.BaseVector._eval_conjugate`
   */
  override conjugateSelf(): Expr {
    return this;
  }
  protected override computeKey(): string {
    return `BaseVector(${this.index};${this.system.key})`;
  }
}

/**
 * A scalar multiple of a base vector.
 *
 * @see SymPy `sympy.vector.vector.VectorMul`
 */
export class VectorMulNode extends Vector implements ScaledBase {
  /**
   * Constructs an instance of `VectorMulNode`.
   *
   * @param measureNumber - Scalar coefficient of the basis element.
   * @param baseInstance - Basis element multiplied by the coefficient.
   */
  constructor(
    /**
     * The scalar coefficient multiplying the basis element.
     *
     * @see SymPy `sympy.vector.vector.VectorMul.measure_number`
     */
    readonly measureNumber: Expr,
    /** The basis element carrying the scalar coefficient. */
    readonly baseInstance: BaseVectorNode,
  ) {
    super('VectorMul', [measureNumber, baseInstance]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return basisMul(VECTOR, args);
  }
  /**
   * The scalar coefficients keyed by their basis vectors.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.vector.VectorMul.components`
   */
  override get components(): ExprMap<Expr> {
    return new ExprMap<Expr>([[this.baseInstance, this.measureNumber]]);
  }
  /**
   * The base vector of the product.
   *
   * @returns The base vector of the product.
   * @see SymPy `sympy.vector.vector.VectorMul.base_vector`
   */
  get baseVector(): BaseVectorNode {
    return this.baseInstance;
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return mulStr(this.measureNumber, this.baseInstance, print);
  }
}

/** SymPy BasisDependentMul._sympystr: the measure (in parentheses when it has (, - or +) times the base instance. */
export function mulStr(measure: Expr, base: Expr, print: (e: Expr) => string): string {
  let m = print(measure);
  if (m.includes('(') || m.includes('-') || m.includes('+')) m = `(${m})`;
  return `${m}*${print(base)}`;
}

/**
 * A sum of multiples of base vectors.
 *
 * @see SymPy `sympy.vector.vector.VectorAdd`
 */
export class VectorAddNode extends Vector {
  readonly #components: ExprMap<Expr>;
  /**
   * Constructs an instance of `VectorAddNode`.
   *
   * @param terms - Terms of the sum.
   * @param components - Coefficients indexed by basis elements.
   */
  constructor(terms: readonly Expr[], components: ExprMap<Expr>) {
    super('VectorAdd', [...terms].sort((a, b) => compareKeys(sortKey(a), sortKey(b))));
    this.#components = components;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return basisAdd(VECTOR, args);
  }
  /**
   * The scalar coefficients keyed by their basis vectors.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.vector.VectorAdd.components`
   */
  override get components(): ExprMap<Expr> {
    return this.#components;
  }
  /**
   * The terms by system (in order of the names), then by base vector.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    const items = [...this.separate()].sort((a, b) => compareStr(String(a[0]), String(b[0])));
    const out: string[] = [];
    for (const [system, part] of items) {
      const comps = asVector(part).components;
      for (const x of cast2sys(system).baseVectors()) {
        if (comps.has(x)) out.push(print(basisMul(VECTOR, [defined(this.components.get(x), 'component'), x])));
      }
    }
    return out.join(' + ');
  }
}

const cast2sys = (e: Expr): CoordSysBase => cast(e, CoordSysBase, 'coordinate system');

/**
 * The zero vector.
 *
 * @see SymPy `sympy.vector.vector.VectorZero`
 */
export class VectorZeroNode extends Vector {
  /** Constructs an instance of `VectorZeroNode`. */
  constructor() {
    super('VectorZero', []);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @returns The rebuilt expression.
   */
  withArgs(): Expr {
    return ZERO;
  }
  /**
   * The scalar coefficients keyed by their basis vectors.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.vector.VectorZero.components`
   */
  override get components(): ExprMap<Expr> {
    return new ExprMap<Expr>();
  }
  /**
   * Returns the zero vector.
   *
   * @returns The zero vector.
   * @see SymPy `sympy.vector.vector.VectorZero.normalize`
   */
  override normalize(): Expr {
    return this;
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return '0';
  }
  /**
   * The label used by the pretty printer.
   *
   * @returns The label used by the pretty printer.
   * @see SymPy `sympy.vector.vector.VectorZero._pretty_form`
   */
  override get prettyForm(): string {
    return '0';
  }
}

const ZERO = new VectorZeroNode();

/** The base vector of a key of the components of a vector. */
function baseVectorOf(k: Expr): BaseVectorNode {
  return cast(k, BaseVectorNode, 'base vector');
}

const VECTOR: BasisFamily = {
  name: 'Vector',
  is: (e: Expr): e is BasisDependent => e instanceof Vector,
  isBase: (e) => e instanceof BaseVectorNode,
  isMul: (e) => e instanceof VectorMulNode,
  isAdd: (e) => e instanceof VectorAddNode,
  isZero: (e) => e instanceof VectorZeroNode,
  zero: ZERO,
  addNode: (terms, components) => new VectorAddNode(terms, components),
  mulNode: (measure, base) => new VectorMulNode(measure, baseVectorOf(base)),
};
registerFamily(VECTOR);

/** The vector family (vector.ts). */
export const vectorFamily: BasisFamily = VECTOR;

/**
 * The unevaluated cross product, with its operands in canonical order (Cross(b, a) is -Cross(a,
 * b)).
 *
 * @see SymPy `sympy.vector.vector.Cross`
 * @example
 * ```ts
 * import { CoordSys3D, Cross, doit } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const v = R.i.add(R.j).add(R.k);
 * const w = R.i.mul(R.x).add(R.j.mul(R.y)).add(R.k.mul(R.z));
 * doit(Cross(v, w)); // => (-R.y + R.z)*R.i + (R.x - R.z)*R.j + (-R.x + R.y)*R.k
 * ```
 */
export class CrossNode extends Vector {
  /**
   * Constructs an instance of `CrossNode`.
   *
   * @param expr1 - First operand of the product.
   * @param expr2 - Second operand of the product.
   */
  constructor(expr1: Expr, expr2: Expr) {
    super('Cross', [expr1, expr2]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new CrossNode(at(args, 0), at(args, 1));
  }
  /**
   * Evaluate the cross product with `doit` before accessing its components.
   *
   * @returns Accessing components on an unevaluated cross product always throws a `TypeError`.
   * @throws TypeError when components are requested before evaluating the cross product.
   * @see SymPy `sympy.vector.vector.Cross.components`
   */
  override get components(): ExprMap<Expr> {
    throw new TypeError('Cross has no components: evaluate it with doit()');
  }
  /**
   * Computes the derivative of this expression.
   *
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.vector.Cross._eval_derivative`
   */
  override diffSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Simplifies the operands of the expression.
   *
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.vector.Cross._eval_simplify`
   */
  override simplifySelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Integrates the expression with respect to the given variable.
   *
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.vector.Cross._eval_Integral`
   */
  override integrateSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Evaluates the components to the requested numerical precision.
   *
   * @returns The numerically evaluated expression.
   * @see SymPy `sympy.vector.vector.Cross._eval_evalf`
   */
  override evalfSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Computes the complex conjugate.
   *
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.vector.Cross._eval_conjugate`
   */
  override conjugateSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Cross of the operands as they are (not deep).
   *
   * @returns Cross of the operands as they are (not deep).
   */
  override get doitDeep(): boolean {
    return false;
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return cross(at(this.args, 0), at(this.args, 1));
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `${parenMul(at(this.args, 0), print)} \\times ${parenMul(at(this.args, 1), print)}`;
  }
  /**
   * Binding strength used to insert parentheses when printing LaTeX.
   *
   * @returns The LaTeX printer’s precedence for this node.
   */
  latexPrecedence(): number {
    return OPERATOR_PRECEDENCE;
  }
}

/** SymPy LatexPrinter.parenthesize(e, PRECEDENCE['Mul']): sums and products (scaled vectors among them) in parentheses. */
export function parenMul(e: Expr, print: (e: Expr) => string): string {
  const s = print(e);
  return e instanceof VectorAddNode || e instanceof VectorMulNode || latexPrecedence(e) <= PREC.MUL ? `\\left(${s}\\right)` : s;
}

/** SymPy PRECEDENCE_TRADITIONAL of Dot, Cross and the differential operators: just below a product. */
export const OPERATOR_PRECEDENCE = PREC.MUL - 1;

/** The precedence of an operand: the one a node declares for LaTeX, else the str precedence. */
const latexPrecedence = (e: Expr): number => declaredPrecedence(e, 'latexPrecedence') ?? precedence(e);

/**
 * An unevaluated cross product with operands in canonical order.
 *
 * @param expr1In - First operand of the product.
 * @param expr2In - Second operand of the product.
 * @returns The resulting `Cross` expression.
 * @see SymPy `sympy.vector.vector.Cross`
 * @example
 * ```ts
 * import { CoordSys3D, Cross, doit } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const v = R.i.add(R.j).add(R.k);
 * const w = R.i.mul(R.x).add(R.j.mul(R.y)).add(R.k.mul(R.z));
 * doit(Cross(v, w)); // => (-R.y + R.z)*R.i + (R.x - R.z)*R.j + (-R.x + R.y)*R.k
 * ```
 */
export const Cross = /* @__PURE__ */ callableClass(CrossNode, (expr1In: ExprLike, expr2In: ExprLike): Expr => {
  const [a, b] = [sympify(expr1In), sympify(expr2In)];
  if (compareKeys(sortKey(a), sortKey(b)) > 0) return mul(-1, new CrossNode(b, a));
  return new CrossNode(a, b);
});
export type Cross = CrossNode;

/**
 * The unevaluated dot product, with its operands in canonical order.
 *
 * @see SymPy `sympy.vector.vector.Dot`
 * @example
 * ```ts
 * import { CoordSys3D, Dot, doit, ex } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const v = R.i.add(R.j).add(R.k);
 * const w = R.i.mul(ex`a`).add(R.j.mul(ex`b`)).add(R.k.mul(ex`c`));
 * doit(Dot(v, w)); // => a + b + c
 * ```
 */
export class DotNode extends ExtensionExpr {
  /**
   * Constructs an instance of `DotNode`.
   *
   * @param expr1 - First operand of the product.
   * @param expr2 - Second operand of the product.
   */
  constructor(expr1: Expr, expr2: Expr) {
    super('Dot', [expr1, expr2]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DotNode(at(args, 0), at(args, 1));
  }
  /**
   * Dot of the operands as they are (not deep).
   *
   * @returns Dot of the operands as they are (not deep).
   */
  override get doitDeep(): boolean {
    return false;
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return dot(at(this.args, 0), at(this.args, 1));
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `${parenMul(at(this.args, 0), print)} \\cdot ${parenMul(at(this.args, 1), print)}`;
  }
  /**
   * Binding strength used to insert parentheses when printing LaTeX.
   *
   * @returns The LaTeX printer’s precedence for this node.
   */
  latexPrecedence(): number {
    return OPERATOR_PRECEDENCE;
  }
}

/**
 * An unevaluated dot product with operands in canonical order.
 *
 * @param expr1In - First operand of the product.
 * @param expr2In - Second operand of the product.
 * @returns The resulting `Dot` expression.
 * @see SymPy `sympy.vector.vector.Dot`
 * @example
 * ```ts
 * import { CoordSys3D, Dot, doit, ex } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const v = R.i.add(R.j).add(R.k);
 * const w = R.i.mul(ex`a`).add(R.j.mul(ex`b`)).add(R.k.mul(ex`c`));
 * doit(Dot(v, w)); // => a + b + c
 * ```
 */
export const Dot = /* @__PURE__ */ callableClass(DotNode, (expr1In: ExprLike, expr2In: ExprLike): DotNode => {
  const [a, b] = [sympify(expr1In), sympify(expr2In)].sort((x, y) => compareKeys(sortKey(x), sortKey(y)));
  return new DotNode(defined(a, 'operand'), defined(b, 'operand'));
});
export type Dot = DotNode;

/** The terms of a sum (SymPy isinstance(v, Add): VectorAdd is an Add in SymPy). */
const sumTerms = (v: Expr): readonly Expr[] | undefined => (v instanceof VectorAddNode || v instanceof Add ? v.args : undefined);

/** The single component of a VectorMul. */
const single = (v: VectorMulNode): [BaseVectorNode, Expr] => [v.baseInstance, v.measureNumber];

/** Two coordinate systems of one tree (express can relate them). */
export const connected = (a: CoordSysBase, b: CoordSysBase): boolean => a.rootSystem.key === b.rootSystem.key;

/** SymPy cross(vect1, vect2): the cross product of two vectors. */
export function cross(vect1In: ExprLike, vect2In: ExprLike): Expr {
  const [vect1, vect2] = [sympify(vect1In), sympify(vect2In)];
  const t1 = sumTerms(vect1);
  if (t1) return basisAdd(VECTOR, t1.map((t) => cross(t, vect2)));
  const t2 = sumTerms(vect2);
  if (t2) return basisAdd(VECTOR, t2.map((t) => cross(vect1, t)));
  if (vect1 instanceof BaseVectorNode && vect2 instanceof BaseVectorNode) {
    if (vect1.system.key === vect2.system.key) {
      const [n1, n2] = [vect1.index, vect2.index];
      if (n1 === n2) return ZERO;
      const n3 = 3 - n1 - n2;
      const sign = (n1 + 1) % 3 === n2 ? 1 : -1;
      return mul(sign, at(vect1.system.baseVectors(), n3));
    }
    // (SymPy catches the ValueError of express for systems without a connecting path)
    if (!connected(vect1.system, vect2.system)) return new CrossNode(vect1, vect2);
    return cross(expressHook(vect1, vect2.system), vect2);
  }
  if (vect1 instanceof VectorZeroNode || vect2 instanceof VectorZeroNode) return ZERO;
  if (vect1 instanceof VectorMulNode) {
    const [v1, m1] = single(vect1);
    return mul(m1, cross(v1, vect2));
  }
  if (vect2 instanceof VectorMulNode) {
    const [v2, m2] = single(vect2);
    return mul(m2, cross(vect1, v2));
  }
  return Cross(vect1, vect2);
}

/** SymPy dot(vect1, vect2): the dot product of two vectors. */
export function dot(vect1In: ExprLike, vect2In: ExprLike): Expr {
  const [vect1, vect2] = [sympify(vect1In), sympify(vect2In)];
  const t1 = sumTerms(vect1);
  if (t1) return add(...t1.map((t) => dot(t, vect2)));
  const t2 = sumTerms(vect2);
  if (t2) return add(...t2.map((t) => dot(vect1, t)));
  if (vect1 instanceof BaseVectorNode && vect2 instanceof BaseVectorNode) {
    if (vect1.system.key === vect2.system.key) return vect1.key === vect2.key ? S.One : S.Zero;
    if (!connected(vect1.system, vect2.system)) return Dot(vect1, vect2);
    return dot(vect1, expressHook(vect2, vect1.system));
  }
  if (vect1 instanceof VectorZeroNode || vect2 instanceof VectorZeroNode) return S.Zero;
  if (vect1 instanceof VectorMulNode) {
    const [v1, m1] = single(vect1);
    return mul(m1, dot(v1, vect2));
  }
  if (vect2 instanceof VectorMulNode) {
    const [v2, m2] = single(vect2);
    return mul(m2, dot(vect1, v2));
  }
  return Dot(vect1, vect2);
}

/** SymPy Vector.outer: the dyadic sum of the products of the components. */
export function outer(vect1: Expr, vect2: Expr): Expr {
  if (!(vect1 instanceof Vector) || !(vect2 instanceof Vector)) throw new TypeError('Invalid operand for outer product');
  if (vect1 instanceof VectorZeroNode || vect2 instanceof VectorZeroNode) return dyadicZero();
  const make = defined(vectorHooks.baseDyadic, 'BaseDyadic');
  const terms: Expr[] = [];
  for (const [k1, v1] of vect1.components) for (const [k2, v2] of vect2.components) terms.push(mul(mul(v1, v2), make(k1, k2)));
  return basisAdd(defined(dyadicFamilyRef.family, 'Dyadic'), terms);
}

/**
 * The coordinate systems an expression is defined in (SymPy
 * _get_coord_systems), in order of appearance.
 */
export function coordSystems(e: Expr): CoordSysBase[] {
  const out = new ExprMap<CoordSysBase>();
  const go = (x: Expr): void => {
    if (x instanceof CoordSysBase) out.set(x, x);
    else if (x instanceof BaseVectorNode || x instanceof BaseScalarNode) out.set(x.system, x.system);
    else x.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

/**
 * SymPy Vector._projections: the components along the base vectors of the
 * system of the vector, zeros included.
 */
export function projections(v: Expr): [Expr, Expr, Expr] {
  if (v instanceof VectorZeroNode) return [S.Zero, S.Zero, S.Zero];
  const [i, j, k] = defined(coordSystems(v)[0], 'coordinate system').baseVectors();
  return [dot(v, i), dot(v, j), dot(v, k)];
}

/**
 * A basis vector of a three-dimensional coordinate system.
 *
 * @param index - Zero-based index or indices selecting the desired component.
 * @param system - Coordinate system in which to express components.
 * @param prettyStr - Label for the pretty printer.
 * @param latexStr - Label for the LaTeX printer.
 * @returns The resulting `BaseVector` expression.
 * @throws RangeError when the basis index is outside 0 through 2.
 * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
 * @see SymPy `sympy.vector.vector.BaseVector`
 */
export const BaseVector = /* @__PURE__ */ callableClass(
  BaseVectorNode,
  (index: number, system: CoordSysBase, prettyStr?: string, latexStr?: string): BaseVectorNode => new BaseVectorNode(index, system, prettyStr, latexStr),
);
export type BaseVector = BaseVectorNode;

/**
 * The sum of vectors.
 *
 * @param args - Operands in their defining order.
 * @returns The resulting `VectorAdd` expression.
 * @see SymPy `sympy.vector.vector.VectorAdd`
 */
export const VectorAdd = /* @__PURE__ */ callableClass(VectorAddNode, (...args: ExprLike[]): Expr => basisAdd(VECTOR, args.map(sympify)));
export type VectorAdd = VectorAddNode;

/**
 * The product of scalars and a vector.
 *
 * @param args - Operands in their defining order.
 * @returns The resulting `VectorMul` expression.
 * @see SymPy `sympy.vector.vector.VectorMul`
 */
export const VectorMul = /* @__PURE__ */ callableClass(VectorMulNode, (...args: ExprLike[]): Expr => basisMul(VECTOR, args.map(sympify)));
export type VectorMul = VectorMulNode;

/**
 * The zero vector.
 *
 * @returns The resulting `VectorZero` expression.
 * @see SymPy `sympy.vector.vector.VectorZero`
 */
export const VectorZero = /* @__PURE__ */ callableClass(VectorZeroNode, (): VectorZeroNode => ZERO);
export type VectorZero = VectorZeroNode;

// SymPy sympy.vector.dot and cross are the dot and cross of @symjs/symjs/matrices given vectors
vectorProducts.dot = dot;
vectorProducts.cross = cross;

/** The pretty form of a base vector or base dyadic (SymPy _pretty_form). */
function prettyFormOf(k: Expr): string {
  return cast(k, BasisDependent, 'base vector or dyadic').prettyForm;
}

/**
 * SymPy PrettyPrinter._print_BasisDependent: the terms (base instance,
 * measure) of a vector or dyadic side by side, each measure in parentheses
 * (unicode only, as in SymPy).
 */
export function basisPretty(expr: BasisDependent, items: readonly (readonly [Expr, Expr])[], printer: PrettyPrinter): PrettyForm {
  if (!printer.useUnicode) throw new NotImplementedError('ASCII pretty printing of BasisDependent is not implemented');
  if (expr.family.isZero(expr)) return new PrettyForm(prettyFormOf(expr));
  const o1: string[] = [];
  const vectstrs: string[] = [];
  for (const [k, v] of items) {
    const form = prettyFormOf(k);
    if (v instanceof Rational && v.isOne) o1.push(form);
    else if (v instanceof Rational && v.p === -1n && v.q === 1n) o1.push(`(-1) ${form}`);
    else o1.push(`${printer.print(v).parens()[0]} ${form}`);
    vectstrs.push(form);
  }
  // SymPy xobj(')_ext', 1) and xobj(')_lower_hook', 1): RIGHT PARENTHESIS EXTENSION and LOWER HOOK
  const ext = '\u239f';
  const hook = '\u23a0';
  const flag: number[] = [];
  o1.forEach((partstr, i) => {
    flag.push(0);
    if (!partstr.includes('\n')) return;
    let tempstr = partstr.replace(at(vectstrs, i), '');
    if (tempstr.includes(ext)) {
      for (let paren = 0; paren < tempstr.length; paren++) {
        flag[i] = 1;
        if (tempstr[paren] === ext && tempstr[paren + 1] === '\n') {
          // the vector string goes after all the right parentheses
          tempstr = `${tempstr.slice(0, paren)}${ext} ${at(vectstrs, i)}${tempstr.slice(paren + 1)}`;
          break;
        }
      }
    } else {
      // (a picture of two lines: its right parenthesis ends with the lower hook)
      const index = tempstr.lastIndexOf(hook);
      flag[i] = 1;
      tempstr = `${tempstr.slice(0, index)}${hook} ${at(vectstrs, i)}${tempstr.slice(index + 1)}`;
    }
    o1[i] = tempstr;
  });
  const parts = o1.map((x) => x.split('\n'));
  const nNewlines = Math.max(...parts.map((x) => x.length));
  if (flag.includes(1)) {
    parts.forEach((p, i) => {
      if (p.length === 1) {
        p.unshift(' '.repeat(at(p, 0).length));
        flag[i] = 1;
      }
    });
  }
  // (SymPy appends a line padded to the parts before it; the first part creates all the lines)
  const strs: string[] = Array.from({ length: nNewlines }, () => '');
  parts.forEach((p, i) => {
    const fi = at(flag, i);
    const last = at(p, fi).length;
    for (let j = 0; j < nNewlines; j++) {
      if (j + 1 <= p.length) {
        strs[j] += j === fi ? `${at(p, fi)} + ` : `${at(p, j)}${' '.repeat(last - at(p, j).length + 3)}`;
      } else strs[j] += ' '.repeat(last + 3);
    }
  });
  return new PrettyForm(strs.map((x) => x.slice(0, -3)).join('\n'));
}

/** The terms of a vector in printing order (SymPy separate().items(), then by the printed base vector). */
function vectorItems(v: Vector): [Expr, Expr][] {
  if (v instanceof VectorZeroNode) return [];
  const out: [Expr, Expr][] = [];
  for (const part of v.separate().values()) out.push(...[...asVector(part).components].sort((a, b) => compareStr(String(a[0]), String(b[0]))));
  return out;
}

for (const name of ['BaseVector', 'VectorMul', 'VectorAdd', 'VectorZero']) {
  prettyHooks.extension.set(name, (e, printer) => basisPretty(asVector(e), vectorItems(asVector(e)), printer));
}

/** SymPy _print_Cross and _print_Dot: (a)\u00d7(b) and (a)\u22c5(b). */
function prettyProduct(e: Expr, op: string, printer: PrettyPrinter): PrettyForm {
  let p = PrettyForm.of(printer.print(at(e.args, 1)).parens());
  p = PrettyForm.of(p.left(op));
  p = PrettyForm.of(p.left(')'));
  p = PrettyForm.of(p.left(printer.print(at(e.args, 0))));
  return PrettyForm.of(p.left('('));
}
prettyHooks.extension.set('Cross', (e, printer) => prettyProduct(e, '\u00d7', printer));
prettyHooks.extension.set('Dot', (e, printer) => prettyProduct(e, '\u22c5', printer));
