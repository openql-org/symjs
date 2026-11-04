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


/** SymPy Dyadic: the super class of all dyadic classes. */
export abstract class Dyadic extends BasisDependent {
  override get family(): BasisFamily {
    return DYADIC;
  }

  /** SymPy Dyadic.zero: the zero dyadic. */
  static get zero(): DyadicZeroNode {
    return ZERO;
  }

  /**
   * SymPy Dyadic.dot (the operator &): the inner product with a vector (a
   * vector) or a dyadic (a dyadic).
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

  /** SymPy Dyadic.cross (the operator ^): the cross product with a vector, a dyadic. */
  cross(other: Expr): Expr {
    if (other instanceof VectorZeroNode) return ZERO;
    if (!(other instanceof Vector)) throw new TypeError(`${String(other)} not supported for cross with dyadics`);
    let out: Expr = ZERO;
    for (const [k, v] of this.components) out = add(out, mul(v, asVector(at(k.args, 0)).outer(asVector(at(k.args, 1)).cross(other))));
    return out;
  }

  /**
   * SymPy to_matrix(system, second_system): the matrix of the dyadic with
   * rows along the base vectors of system and columns along those of
   * second_system (system by default).
   */
  toMatrix(system: CoordSysBase, secondSystem: CoordSysBase = system): Matrix {
    return Matrix.fromFunction(3, 3, (r, c) => dot(asVector(at(system.baseVectors(), r)).dot(this), at(secondSystem.baseVectors(), c)));
  }

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

/** SymPy BaseDyadic(vector1, vector2): the outer product of two base vectors. */
export class BaseDyadicNode extends Dyadic implements ScaledBase {
  #components: ExprMap<Expr> | undefined;
  constructor(vector1: BaseVectorNode, vector2: BaseVectorNode) {
    super('BaseDyadic', [vector1, vector2]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return BaseDyadic(at(args, 0), at(args, 1));
  }
  override get components(): ExprMap<Expr> {
    return (this.#components ??= new ExprMap<Expr>([[this, S.One]]));
  }
  get measureNumber(): Expr {
    return S.One;
  }
  get baseInstance(): BaseDyadicNode {
    return this;
  }
  /** SymPy _pretty_form. */
  get prettyForm(): string {
    return `(${this.vectors.map((v) => v.prettyForm).join('|')})`;
  }
  /** SymPy _latex_form. */
  get latexForm(): string {
    const [a, b] = this.vectors;
    return `\\left(${a.latexForm}{\\middle|}${b.latexForm}\\right)`;
  }
  /** The two base vectors. */
  get vectors(): [BaseVectorNode, BaseVectorNode] {
    return [guardCast(at(this.args, 0), BaseVectorNode, 'base vector'), guardCast(at(this.args, 1), BaseVectorNode, 'base vector')];
  }
  override printStr(print: (e: Expr) => string): string {
    return `(${print(at(this.args, 0))}|${print(at(this.args, 1))})`;
  }
  override printLatex(): string {
    return this.latexForm;
  }
}

/** SymPy DyadicMul: a scalar multiple of a base dyadic. */
export class DyadicMulNode extends Dyadic implements ScaledBase {
  constructor(
    readonly measureNumber: Expr,
    readonly baseInstance: BaseDyadicNode,
  ) {
    super('DyadicMul', [measureNumber, baseInstance]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return basisMul(DYADIC, args);
  }
  override get components(): ExprMap<Expr> {
    return new ExprMap<Expr>([[this.baseInstance, this.measureNumber]]);
  }
  /** SymPy base_dyadic: the base dyadic of the product. */
  get baseDyadic(): BaseDyadicNode {
    return this.baseInstance;
  }
  override printStr(print: (e: Expr) => string): string {
    return mulStr(this.measureNumber, this.baseInstance, print);
  }
}

/** SymPy DyadicAdd: a sum of multiples of base dyadics. */
export class DyadicAddNode extends Dyadic {
  readonly #components: ExprMap<Expr>;
  constructor(terms: readonly Expr[], components: ExprMap<Expr>) {
    super('DyadicAdd', [...terms].sort((a, b) => compareKeys(sortKey(a), sortKey(b))));
    this.#components = components;
  }
  withArgs(args: readonly Expr[]): Expr {
    return basisAdd(DYADIC, args);
  }
  override get components(): ExprMap<Expr> {
    return this.#components;
  }
  /** SymPy DyadicAdd._sympystr: the terms in order of the printed base dyadics. */
  override printStr(print: (e: Expr) => string): string {
    return [...this.components]
      .sort((a, b) => compareStr(String(a[0]), String(b[0])))
      .map(([k, v]) => print(basisMul(DYADIC, [k, v])))
      .join(' + ');
  }
}

/** SymPy DyadicZero: the zero dyadic. */
export class DyadicZeroNode extends Dyadic {
  constructor() {
    super('DyadicZero', []);
  }
  withArgs(): Expr {
    return ZERO;
  }
  override get components(): ExprMap<Expr> {
    return new ExprMap<Expr>();
  }
  override printStr(): string {
    return '0';
  }
  /** SymPy _pretty_form. */
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

/** SymPy BaseDyadic(vector1, vector2): the zero dyadic when one of the vectors is zero. */
export const BaseDyadic = /* @__PURE__ */ callableClass(BaseDyadicNode, (vector1In: ExprLike, vector2In: ExprLike): Expr => {
  const [v1, v2] = [sympify(vector1In), sympify(vector2In)];
  const ok = (v: Expr): boolean => v instanceof BaseVectorNode || v instanceof VectorZeroNode;
  if (!ok(v1) || !ok(v2)) throw new TypeError('BaseDyadic cannot be composed of non-base vectors');
  if (!(v1 instanceof BaseVectorNode) || !(v2 instanceof BaseVectorNode)) return ZERO;
  return new BaseDyadicNode(v1, v2);
});
export type BaseDyadic = BaseDyadicNode;
vectorHooks.baseDyadic = (v1, v2) => BaseDyadic(v1, v2);

/** SymPy DyadicAdd(*args): the sum of dyadics. */
export const DyadicAdd = /* @__PURE__ */ callableClass(DyadicAddNode, (...args: ExprLike[]): Expr => basisAdd(DYADIC, args.map(sympify)));
export type DyadicAdd = DyadicAddNode;

/** SymPy DyadicMul(*args): the product of scalars and a dyadic. */
export const DyadicMul = /* @__PURE__ */ callableClass(DyadicMulNode, (...args: ExprLike[]): Expr => basisMul(DYADIC, args.map(sympify)));
export type DyadicMul = DyadicMulNode;

/** SymPy DyadicZero(): the zero dyadic. */
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
