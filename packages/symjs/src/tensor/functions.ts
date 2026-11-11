// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The shape of array-like objects (SymPy sympy.tensor.functions.shape).
 */

import { Expr, Integral, impl } from '../core/nodes';
import { cast } from '../core/guard';
import { Indexed, IndexedBase } from '../core/indexed';
import { IdxNode } from './idx';
import { add, mul } from '../core/ops';
import { isNoMatch } from '../core/truth';
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
