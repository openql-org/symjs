// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/arrayexpr_derivatives.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import type { Expr } from '../../../core/nodes';
import { first } from '../../../core/guard';
import { NotImplementedError } from '../../../core/errors';
import { Identity, MatrixSymbolNode } from '../../../matrices/expressions/matexpr';
import { ArraySymbol, ArrayAdd, ArrayContraction, ArrayDiagonal, ArrayTensorProduct, PermuteDims, ZeroArray, getShape, getRank } from './arrayexpressions';
import { convertMatrixToArray } from './frommatrixtoarray';

/** Derivative with variable axes first, then the expression's axes. */
export function arrayDerive(expr: Expr, variable: Expr): Expr {
  if (!(variable instanceof ArraySymbol || variable instanceof MatrixSymbolNode)) throw new NotImplementedError('array differentiation requires an array or matrix symbol');
  const shape = getShape(variable), rank = shape.length, prefix = Array.from({ length: rank }, (_, i) => i);
  if (expr.key === variable.key) {
    const product = new ArrayTensorProduct(...shape.map((d) => Identity(d))).doit();
    return new PermuteDims(product, [...prefix.map((i) => 2 * i), ...prefix.map((i) => 2 * i + 1)]).doit();
  }
  const converted = convertMatrixToArray(expr);
  if (converted.key !== expr.key) return arrayDerive(converted, variable);
  if (expr instanceof ArrayAdd) return new ArrayAdd(...expr.args.map((a) => arrayDerive(a, variable)));
  if (expr instanceof ArrayTensorProduct) {
    const terms: Expr[] = [];
    let offset = 0;
    expr.args.forEach((a, i) => {
      const derivative = arrayDerive(a, variable);
      if (!(derivative instanceof ZeroArray)) {
        const product = new ArrayTensorProduct(...expr.args.map((b, j) => j === i ? derivative : b));
        const permutation = [...prefix.map((k) => offset + k), ...Array.from({ length: offset }, (_, k) => k), ...Array.from({ length: getRank(expr) - offset }, (_, k) => offset + rank + k)];
        terms.push(new PermuteDims(product, permutation).doit());
      }
      offset += getRank(a);
    });
    return terms.length === 0 ? new ZeroArray(...shape, ...expr.shape) : terms.length === 1 ? first(terms) : new ArrayAdd(...terms);
  }
  if (expr instanceof ArrayContraction) return new ArrayContraction(arrayDerive(expr.expr, variable), ...expr.contractionIndices.map((g) => g.map((i) => i + rank))).doit();
  if (expr instanceof ArrayDiagonal) return new ArrayDiagonal(arrayDerive(expr.expr, variable), ...expr.diagonalIndices.map((g) => g.map((i) => i + rank)));
  if (expr instanceof PermuteDims) return new PermuteDims(arrayDerive(expr.expr, variable), [...prefix, ...expr.permutation.arrayForm.map((i) => i + rank)]).doit();
  if (expr.has(variable)) throw new NotImplementedError('array derivative of this expression is not implemented');
  return new ZeroArray(...shape, ...getShape(expr));
}
