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

/** SymPy Del(): the vector differential operator (printed delop). */
export class DelNode extends DelBase {
  constructor() {
    super('Del', []);
  }
  withArgs(): Expr {
    return this;
  }
  /** SymPy Del.gradient (and __call__): the gradient of a scalar field (unevaluated unless doit). */
  gradient(scalarField: ExprLike, opts: OperatorOptions = {}): Expr {
    return gradient(scalarField, { doit: opts.doit ?? false });
  }
  /** SymPy Del.dot (the operator &): the divergence of a vector field. */
  dot(vect: ExprLike, opts: OperatorOptions = {}): Expr {
    return divergence(vect, { doit: opts.doit ?? false });
  }
  /** SymPy Del.cross (the operator ^): the curl of a vector field. */
  cross(vect: ExprLike, opts: OperatorOptions = {}): Expr {
    return curl(vect, { doit: opts.doit ?? false });
  }
  override printStr(): string {
    return 'delop';
  }
  override printLatex(): string {
    return 'delop';
  }
}

/** SymPy Del(). */
export const Del = /* @__PURE__ */ callableClass(DelNode, (): DelNode => new DelNode());
export type Del = DelNode;
