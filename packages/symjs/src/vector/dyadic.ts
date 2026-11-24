// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/dyadic.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.dyadic: Dyadic and its classes (BaseDyadic,
 * DyadicAdd, DyadicMul, DyadicZero), the outer products of vectors.
 */

import { S } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { ExprMap } from '../core/exprmap';
import { callableClass } from '../core/callable';
import { at, cast as guardCast } from '../core/guard';
import { Matrix } from '../matrices/matrix';
import { compareKeys, sortKey } from '../printing/sortkey';
import { BasisDependent, basisAdd, basisMul, vectorHooks } from './basisdependent';
import type { BasisFamily, CoordSysBase, ScaledBase } from './basisdependent';
import { BaseVectorNode, Vector, VectorZeroNode, basisLatex, basisPretty, compareStr, dot, mulStr, registerDyadicFamily } from './vector';
import { prettyHooks } from '../printing/pretty/pretty';


/**
 * The super class of all dyadic classes.
 *
 * @see SymPy `sympy.vector.dyadic.Dyadic`
 */
export abstract class Dyadic extends BasisDependent {
  /**
   * Identifies the operations common to this family of basis-dependent expressions.
   *
   * @returns The family descriptor.
   */
  override get family(): BasisFamily {
    return DYADIC;
  }

  /**
   * Provides the additive identity for dyadics.
   *
   * @returns The zero dyadic.
   * @see SymPy `sympy.vector.dyadic.Dyadic.zero`
   */
  static get zero(): DyadicZeroNode {
    return ZERO;
  }

  /**
   * Contracts the dyadic with a vector or another dyadic.
   *
   * @param other - Other operand of the inner product.
   * @returns A vector or dyadic matching the operand.
   * @throws TypeError when the operand cannot form an inner product with a dyadic.
   * @see SymPy `sympy.vector.dyadic.Dyadic.dot`
   */
  dot(other: Expr): Expr {
    if (other instanceof VectorZeroNode || other instanceof DyadicZeroNode) return Vector.zero;
    if (other instanceof Vector) {
      let out: Expr = Vector.zero;
      for (const [k, v] of this.components) out = add(out, mul(dot(at(k.args, 1), other), v, at(k.args, 0)));
      return out;
    }
    if (other instanceof Dyadic) {
      let out: Expr = ZERO;
      for (const [k1, v1] of this.components) {
        for (const [k2, v2] of other.components) {
          const d = dot(at(k1.args, 1), at(k2.args, 0));
          out = add(out, mul(d, v1, v2, asVector(at(k1.args, 0)).outer(at(k2.args, 1))));
        }
      }
      return out;
    }
    throw new TypeError(`Inner product is not defined for ${String(other)} and Dyadics.`);
  }

  /**
   * Takes the cross product of the dyadic with a vector.
   *
   * @param other - Other operand of the cross product.
   * @returns The resulting dyadic.
   * @throws TypeError when the operand cannot form a cross product with a dyadic.
   * @see SymPy `sympy.vector.dyadic.Dyadic.cross`
   */
  cross(other: Expr): Expr {
    if (other instanceof VectorZeroNode) return ZERO;
    if (!(other instanceof Vector)) throw new TypeError(`${String(other)} not supported for cross with dyadics`);
    let out: Expr = ZERO;
    for (const [k, v] of this.components) out = add(out, mul(v, asVector(at(k.args, 0)).outer(asVector(at(k.args, 1)).cross(other))));
    return out;
  }

  /**
   * Expresses the dyadic in a row basis from the first system and a column basis from the second,
   * defaulting to the first.
   *
   * @param system - Coordinate system in which to express components.
   * @param secondSystem - Basis for the second vector of the dyadic.
   * @returns The component matrix.
   * @see SymPy `sympy.vector.dyadic.Dyadic.to_matrix`
   */
  toMatrix(system: CoordSysBase, secondSystem: CoordSysBase = system): Matrix {
    return Matrix.fromFunction(3, 3, (r, c) => dot(asVector(at(system.baseVectors(), r)).dot(this), at(secondSystem.baseVectors(), c)));
  }

  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    if (this instanceof DyadicZeroNode) return DYADIC_ZERO_LATEX;
    return basisLatex(
      [...this.components].sort((a, b) => compareStr(String(a[0]), String(b[0]))),
      print,
    );
  }
}

const asVector = (e: Expr): Vector => guardCast(e, Vector, 'vector');

/** The LaTeX of the zero dyadic (SymPy DyadicZero._latex_form). */
const DYADIC_ZERO_LATEX = '(\\mathbf{\\hat{0}}|\\mathbf{\\hat{0}})';

/**
 * The outer product of two base vectors.
 *
 * @see SymPy `sympy.vector.dyadic.BaseDyadic`
 */
export class BaseDyadicNode extends Dyadic implements ScaledBase {
  #components: ExprMap<Expr> | undefined;
  /**
   * Constructs an instance of `BaseDyadicNode`.
   *
   * @param vector1 - First vector operand.
   * @param vector2 - Second vector operand.
   */
  constructor(vector1: BaseVectorNode, vector2: BaseVectorNode) {
    super('BaseDyadic', [vector1, vector2]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return BaseDyadic(at(args, 0), at(args, 1));
  }
  /**
   * Associates each basis dyadic with its scalar coefficient.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.dyadic.BaseDyadic.components`
   */
  override get components(): ExprMap<Expr> {
    return (this.#components ??= new ExprMap<Expr>([[this, S.One]]));
  }
  /**
   * Extracts the scalar weight of the basis element.
   *
   * @returns The measure number.
   */
  get measureNumber(): Expr {
    return S.One;
  }
  /**
   * Identifies the basis element multiplied by the scalar coefficient.
   *
   * @returns The basis factor.
   */
  get baseInstance(): BaseDyadicNode {
    return this;
  }
  /**
   * Supplies the label used in pretty-printed expressions.
   *
   * @returns The display label.
   */
  get prettyForm(): string {
    return `(${this.vectors.map((v) => v.prettyForm).join('|')})`;
  }
  /**
   * Formats the basis element as LaTeX.
   *
   * @returns The formatted text.
   */
  get latexForm(): string {
    const [a, b] = this.vectors;
    return `\\left(${a.latexForm}{\\middle|}${b.latexForm}\\right)`;
  }
  /**
   * Identifies the two basis vectors forming the dyadic.
   *
   * @returns The ordered vector pair.
   */
  get vectors(): [BaseVectorNode, BaseVectorNode] {
    return [guardCast(at(this.args, 0), BaseVectorNode, 'base vector'), guardCast(at(this.args, 1), BaseVectorNode, 'base vector')];
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return `(${print(at(this.args, 0))}|${print(at(this.args, 1))})`;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @returns The formatted LaTeX.
   */
  override printLatex(): string {
    return this.latexForm;
  }
}

/**
 * A scalar multiple of a base dyadic.
 *
 * @see SymPy `sympy.vector.dyadic.DyadicMul`
 */
export class DyadicMulNode extends Dyadic implements ScaledBase {
  /**
   * Constructs an instance of `DyadicMulNode`.
   *
   * @param measureNumber - Scalar coefficient of the basis element.
   * @param baseInstance - Basis element multiplied by the coefficient.
   */
  constructor(
    /**
     * The scalar coefficient multiplying the basis element.
     *
     * @see SymPy `sympy.vector.dyadic.DyadicMul.measure_number`
     */
    readonly measureNumber: Expr,
    /** The basis element carrying the scalar coefficient. */
    readonly baseInstance: BaseDyadicNode,
  ) {
    super('DyadicMul', [measureNumber, baseInstance]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return basisMul(DYADIC, args);
  }
  /**
   * Associates each basis dyadic with its scalar coefficient.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.dyadic.DyadicMul.components`
   */
  override get components(): ExprMap<Expr> {
    return new ExprMap<Expr>([[this.baseInstance, this.measureNumber]]);
  }
  /**
   * Extracts the basis dyadic from the scalar multiple.
   *
   * @returns The dyadic factor.
   * @see SymPy `sympy.vector.dyadic.DyadicMul.base_dyadic`
   */
  get baseDyadic(): BaseDyadicNode {
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

/**
 * A sum of multiples of base dyadics.
 *
 * @see SymPy `sympy.vector.dyadic.DyadicAdd`
 */
export class DyadicAddNode extends Dyadic {
  readonly #components: ExprMap<Expr>;
  /**
   * Constructs an instance of `DyadicAddNode`.
   *
   * @param terms - Terms of the sum.
   * @param components - Coefficients indexed by basis elements.
   */
  constructor(terms: readonly Expr[], components: ExprMap<Expr>) {
    super('DyadicAdd', [...terms].sort((a, b) => compareKeys(sortKey(a), sortKey(b))));
    this.#components = components;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return basisAdd(DYADIC, args);
  }
  /**
   * Associates each basis dyadic with its scalar coefficient.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.dyadic.DyadicAdd.components`
   */
  override get components(): ExprMap<Expr> {
    return this.#components;
  }
  /**
   * Orders terms by the printed forms of their basis dyadics.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return [...this.components]
      .sort((a, b) => compareStr(String(a[0]), String(b[0])))
      .map(([k, v]) => print(basisMul(DYADIC, [k, v])))
      .join(' + ');
  }
}

/**
 * The zero dyadic.
 *
 * @see SymPy `sympy.vector.dyadic.DyadicZero`
 */
export class DyadicZeroNode extends Dyadic {
  /** Constructs an instance of `DyadicZeroNode`. */
  constructor() {
    super('DyadicZero', []);
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
   * Associates each basis dyadic with its scalar coefficient.
   *
   * @returns The scalar coefficients keyed by basis element.
   * @see SymPy `sympy.vector.dyadic.DyadicZero.components`
   */
  override get components(): ExprMap<Expr> {
    return new ExprMap<Expr>();
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
   * Supplies the label used in pretty-printed expressions.
   *
   * @returns The display label.
   * @see SymPy `sympy.vector.dyadic.DyadicZero._pretty_form`
   */
  get prettyForm(): string {
    return '(0|0)';
  }
}

const ZERO = new DyadicZeroNode();

function baseDyadicOf(k: Expr): BaseDyadicNode {
  return guardCast(k, BaseDyadicNode, 'base dyadic');
}

const DYADIC: BasisFamily = {
  name: 'Dyadic',
  is: (e: Expr): e is BasisDependent => e instanceof Dyadic,
  isBase: (e) => e instanceof BaseDyadicNode,
  isMul: (e) => e instanceof DyadicMulNode,
  isAdd: (e) => e instanceof DyadicAddNode,
  isZero: (e) => e instanceof DyadicZeroNode,
  zero: ZERO,
  addNode: (terms, components) => new DyadicAddNode(terms, components),
  mulNode: (measure, base) => new DyadicMulNode(measure, baseDyadicOf(base)),
};
registerDyadicFamily(DYADIC);

/**
 * Constructs a basis dyadic formed by the outer product of two basis vectors.
 *
 * @param vector1In - First vector operand.
 * @param vector2In - Second vector operand.
 * @returns The resulting `BaseDyadic` expression.
 * @throws TypeError when either operand is not a basis vector.
 * @see SymPy `sympy.vector.dyadic.BaseDyadic`
 */
export const BaseDyadic = /* @__PURE__ */ callableClass(BaseDyadicNode, (vector1In: ExprLike, vector2In: ExprLike): Expr => {
  const [v1, v2] = [sympify(vector1In), sympify(vector2In)];
  const ok = (v: Expr): boolean => v instanceof BaseVectorNode || v instanceof VectorZeroNode;
  if (!ok(v1) || !ok(v2)) throw new TypeError('BaseDyadic cannot be composed of non-base vectors');
  if (!(v1 instanceof BaseVectorNode) || !(v2 instanceof BaseVectorNode)) return ZERO;
  return new BaseDyadicNode(v1, v2);
});
export type BaseDyadic = BaseDyadicNode;
vectorHooks.baseDyadic = (v1, v2) => BaseDyadic(v1, v2);

/**
 * Adds the supplied dyadic terms.
 *
 * @param args - Operands in their defining order.
 * @returns The resulting `DyadicAdd` expression.
 * @see SymPy `sympy.vector.dyadic.DyadicAdd`
 */
export const DyadicAdd = /* @__PURE__ */ callableClass(DyadicAddNode, (...args: ExprLike[]): Expr => basisAdd(DYADIC, args.map(sympify)));
export type DyadicAdd = DyadicAddNode;

/**
 * Constructs the product of scalars and a dyadic.
 *
 * @param args - Operands in their defining order.
 * @returns The resulting `DyadicMul` expression.
 * @see SymPy `sympy.vector.dyadic.DyadicMul`
 */
export const DyadicMul = /* @__PURE__ */ callableClass(DyadicMulNode, (...args: ExprLike[]): Expr => basisMul(DYADIC, args.map(sympify)));
export type DyadicMul = DyadicMulNode;

/**
 * Provides the additive identity for dyadics.
 *
 * @returns The resulting `DyadicZero` expression.
 * @see SymPy `sympy.vector.dyadic.DyadicZero`
 */
export const DyadicZero = /* @__PURE__ */ callableClass(DyadicZeroNode, (): DyadicZeroNode => ZERO);
export type DyadicZero = DyadicZeroNode;

/** The dyadic family (dyadic.ts). */
export const dyadicFamily: BasisFamily = DYADIC;

for (const name of ['BaseDyadic', 'DyadicMul', 'DyadicAdd', 'DyadicZero']) {
  prettyHooks.extension.set(name, (e, printer) => {
    const d = guardCast(e, Dyadic, 'dyadic');
    return basisPretty(
      d,
      [...d.components].sort((a, b) => compareStr(String(a[0]), String(b[0]))),
      printer,
    );
  });
}
