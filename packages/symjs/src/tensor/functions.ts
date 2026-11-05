// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The shape of array-like objects (SymPy sympy.tensor.functions.shape).
 */

import { Expr, Integral, impl } from '../core/nodes';
import { Matrix } from '../matrices/matrix';

/** SymPy NoShapeError: shape() of an object that is not array-like. */
export class NoShapeError extends TypeError {
  constructor(message: string) {
    super(message);
    this.name = 'NoShapeError';
  }
}

/** A dimension: a number, or an expression for a symbolic shape. */
export type Dimension = number | Expr;

const hasShape = (x: unknown): x is { readonly shape: readonly Dimension[] } => typeof x === 'object' && x !== null && 'shape' in x && Array.isArray(x.shape);

/**
 * SymPy shape: the shape of a matrix, an N-dimensional array or a matrix
 * expression, also inside an Integral; a NoShapeError for other objects.
 */
export function shape(expr: unknown): Dimension[] {
  if (expr instanceof Matrix) return [expr.rows, expr.cols];
  if (hasShape(expr)) return [...expr.shape];
  if (expr instanceof Integral) return shape(expr.integrand);
  const s = expr instanceof Expr ? impl.str(expr) : String(expr);
  throw new NoShapeError(`${s} does not have shape, or its type is not registered to shape().`);
}
