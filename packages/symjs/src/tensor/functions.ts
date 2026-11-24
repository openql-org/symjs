// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Tensor products and shapes of array-like objects (SymPy tensor.functions).
 */

import { Expr, ExtensionExpr, Integral, S, impl, type ExprLike } from '../core/nodes';
import { at, cast } from '../core/guard';
import { callableClass } from '../core/callable';
import { Indexed, IndexedBase } from '../core/indexed';
import { IdxNode } from './idx';
import { add, mul } from '../core/ops';
import { isNoMatch } from '../core/truth';
import { Matrix } from '../matrices/matrix';
import { MatrixExpr } from '../matrices/expressions/matexpr';
import { NDimArray } from './ndimarray';
import { tensorproduct, type TensorArg } from './arrayop';
import { ArrayElement } from './array/expressions/arrayexpressions';

/**
 * Shape() of an object that is not array-like.
 *
 * @see SymPy `sympy.tensor.functions.NoShapeError`
 * @example
 * ```ts
 * import { NoShapeError, ex, shape } from '@symjs/symjs';
 *
 * let error: unknown;
 * try { shape(ex`x`); } catch (cause) { error = cause; }
 * error instanceof NoShapeError; // => True
 * ```
 */
export class NoShapeError extends TypeError {
  /**
   * Constructs an instance of `NoShapeError`.
   *
   * @param message - Explanation of the error.
   */
  constructor(message: string) {
    super(message);
    this.name = 'NoShapeError';
  }
}

/** A dimension: a number, or an expression for a symbolic shape. */
export type Dimension = number | Expr;

const hasShape = (x: unknown): x is { readonly shape: readonly Dimension[] } => typeof x === 'object' && x !== null && 'shape' in x && Array.isArray(x.shape);

/**
 * The shape of a matrix, an N-dimensional array or a matrix expression, also inside an Integral;
 * a NoShapeError for other objects.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The lengths of the axes in order.
 * @throws NoShapeError when the index ranges do not specify all dimensions or the object has no registered shape.
 * @see SymPy `sympy.tensor.functions.shape`
 * @remarks SymPy prints the one-dimensional shape as `(2,)`.
 * @example
 * ```ts
 * import { SymArray, shape } from '@symjs/symjs';
 *
 * shape(SymArray([1, 2])); // => [2]
 * ```
 */
export function shape(expr: unknown): Dimension[] {
  if (expr instanceof Matrix) return [expr.rows, expr.cols];
  if (expr instanceof Indexed && expr.base instanceof IndexedBase && !isNoMatch(expr.base.shape)) return [...expr.base.shape];
  if (expr instanceof Indexed) return expr.indices.map((i) => {
    if (!(i instanceof IdxNode) || isNoMatch(i.lower)) throw new NoShapeError('index ranges do not define a shape');
    return add(cast(i.upper, Expr), mul(-1, i.lower), 1);
  });
  if (hasShape(expr)) return [...expr.shape];
  if (expr instanceof Integral) return shape(expr.integrand);
  const s = expr instanceof Expr ? impl.str(expr) : String(expr);
  throw new NoShapeError(`${s} does not have shape, or its type is not registered to shape().`);
}

/**
 * Generic tensor product of explicit arrays and symbolic matrices.
 *
 * @see SymPy `sympy.tensor.functions.TensorProduct`
 */
export class TensorProductNode extends ExtensionExpr {
  /**
   * Constructs an instance of `TensorProductNode`.
   *
   * @param args - Operands in their defining order.
   */
  constructor(args: readonly Expr[]) { super('TensorProduct', args); }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new TensorProductNode(args); }
  /**
   * The lengths of the axes in order.
   *
   * @returns The lengths of the axes in order.
   * @see SymPy `sympy.tensor.functions.TensorProduct.shape`
   */
  get shape(): Dimension[] { return this.args.flatMap((arg) => hasShape(arg) ? [...arg.shape] : []); }
  /**
   * The number of free index slots.
   *
   * @returns The number of free index slots.
   * @see SymPy `sympy.tensor.functions.TensorProduct.rank`
   */
  rank(): number { return this.shape.length; }
  /**
   * Selects the entry at the given indices.
   *
   * @param indices - Indices in slot order.
   * @returns The selected entry.
   * @throws RangeError when the number of indices does not match the rank.
   * @see SymPy `sympy.tensor.functions.TensorProduct.__getitem__`
   */
  at(...indices: ExprLike[]): Expr {
    if (indices.length !== this.rank()) throw new RangeError('tensor product index rank does not match the shape');
    let offset = 0;
    return mul(...this.args.map((arg) => {
      const size = hasShape(arg) ? arg.shape.length : 0;
      const index = indices.slice(offset, offset + size);
      offset += size;
      if (arg instanceof MatrixExpr) return arg.at(at(index, 0), at(index, 1));
      if (arg instanceof NDimArray) return arg.get(index);
      if (arg instanceof TensorProductNode) return arg.at(...index);
      return size ? new ArrayElement(arg, index) : arg;
    }));
  }
}

/** SymPy TensorProduct; evaluate:false preserves the supplied factors. */
function createTensorProduct(...args: (TensorArg | { evaluate: boolean })[]): Expr {
  const options = args.at(-1);
  const hasOptions = typeof options === 'object' && 'evaluate' in options;
  const factors = (hasOptions ? args.slice(0, -1) : args).map((arg) => {
    if (typeof arg === 'object' && 'evaluate' in arg) throw new TypeError('options must follow the tensor factors');
    return tensorproduct(arg);
  });
  if (hasOptions && !options.evaluate) return new TensorProductNode(factors);
  const flatten = (arg: Expr): readonly Expr[] => arg instanceof TensorProductNode ? arg.args.flatMap(flatten) : [arg];
  const flat = factors.flatMap(flatten);
  const matrices = flat.filter((arg) => arg instanceof MatrixExpr);
  const coefficient = tensorproduct(...flat.filter((arg) => !(arg instanceof MatrixExpr)));
  return matrices.length ? new TensorProductNode(coefficient.key === S.One.key ? matrices : [coefficient, ...matrices]) : coefficient;
}

/**
 * Forms the tensor product of scalar, matrix or array factors.
 *
 * @param args - Tensor factors, optionally followed by `{ evaluate: false }` to retain the product.
 * @returns The tensor product of the factors.
 * @see SymPy `sympy.tensor.functions.TensorProduct`
 */
export const TensorProduct = callableClass(TensorProductNode, createTensorProduct);
