// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/deloperator.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.deloperator: Del, the vector differential
 * operator nabla. `delop.gradient(f)` is SymPy's `delop(f)`, `delop.dot(v)`
 * and `delop.cross(v)` are `delop & v` and `delop ^ v`.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { callableClass } from '../core/callable';
import { DelBase } from './basisdependent';
import { curl, divergence, gradient } from './operators';
import type { OperatorOptions } from './operators';

/**
 * The vector differential operator (printed delop).
 *
 * @see SymPy `sympy.vector.deloperator.Del`
 */
export class DelNode extends DelBase {
  /** Constructs an instance of `DelNode`. */
  constructor() {
    super('Del', []);
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
   * The gradient of a scalar field (unevaluated unless doit).
   *
   * @param scalarField - Scalar field to differentiate.
   * @param opts - Settings described by {@link OperatorOptions}.
   * @returns The gradient of a scalar field (unevaluated unless doit).
   * @see SymPy `sympy.vector.deloperator.Del.gradient`
   */
  gradient(scalarField: ExprLike, opts: OperatorOptions = {}): Expr {
    return gradient(scalarField, { doit: opts.doit ?? false });
  }
  /**
   * The divergence of a vector field.
   *
   * @param vect - Vector field to which the operator is applied.
   * @param opts - Settings described by {@link OperatorOptions}.
   * @returns The divergence of a vector field.
   * @see SymPy `sympy.vector.deloperator.Del.dot`
   */
  dot(vect: ExprLike, opts: OperatorOptions = {}): Expr {
    return divergence(vect, { doit: opts.doit ?? false });
  }
  /**
   * The curl of a vector field.
   *
   * @param vect - Vector field to which the operator is applied.
   * @param opts - Settings described by {@link OperatorOptions}.
   * @returns The curl of a vector field.
   * @see SymPy `sympy.vector.deloperator.Del.cross`
   */
  cross(vect: ExprLike, opts: OperatorOptions = {}): Expr {
    return curl(vect, { doit: opts.doit ?? false });
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return 'delop';
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @returns The formatted LaTeX.
   */
  override printLatex(): string {
    return 'delop';
  }
}

/**
 * The vector differential operator used to form gradients, curls and divergences.
 *
 * @returns The resulting `Del` expression.
 * @see SymPy `sympy.vector.deloperator.Del`
 */
export const Del = /* @__PURE__ */ callableClass(DelNode, (): DelNode => new DelNode());
export type Del = DelNode;
