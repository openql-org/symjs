// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/arrayexpr_derivatives.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { mul, pow } from '../../../core/ops';
import { rebuild } from '../../../core/traverse';
import { diff } from '../../../calculus/diff';
import { Add, Mul, Pow, Fn, Dummy, type Expr } from '../../../core/nodes';
import { at, first } from '../../../core/guard';
import { NotImplementedError } from '../../../core/errors';
import { Identity, InverseNode, MatPowNode, MatMulNode, MatrixSymbolNode } from '../../../matrices/expressions/matexpr';
import { ArraySymbol, ArrayElementwiseApplyFunc, ArrayAdd, ArrayContraction, ArrayDiagonal, ArrayTensorProduct, PermuteDims, Reshape, ZeroArray, getShape, getRank } from './arrayexpressions';
import { convertMatrixToArray } from './frommatrixtoarray';

/** Distribute the product rule while retaining factorized input array expressions. */
function product(...args: Expr[]): Expr {
  const index = args.findIndex((arg) => arg instanceof ArrayAdd);
  if (index >= 0) return new ArrayAdd(...at(args, index).args.map((term) => product(...args.map((arg, i) => i === index ? term : arg))));
  return new ArrayTensorProduct(...args).doit();
}

/** Derivative with variable axes first, then the expression's axes. */
export function arrayDerive(expr: Expr, variable: Expr): Expr {
  if (!(variable instanceof ArraySymbol || variable instanceof MatrixSymbolNode)) throw new NotImplementedError('array differentiation requires an array or matrix symbol');
  const shape = getShape(variable), rank = shape.length, prefix = Array.from({ length: rank }, (_, i) => i);
  if (expr.key === variable.key) {
    const product = new ArrayTensorProduct(...shape.map((d) => Identity(d))).doit();
    return new PermuteDims(product, [...prefix.map((i) => 2 * i), ...prefix.map((i) => 2 * i + 1)]).doit();
  }
  if (!expr.has(variable)) return new ZeroArray(...shape, ...getShape(expr));
  if (expr instanceof InverseNode) {
    const derivative = arrayDerive(expr.arg, variable);
    const multiplied = product(mul(-1, expr), derivative, expr);
    const contracted = new ArrayContraction(multiplied, [1, rank + 2], [rank + 3, rank + 4]).doit();
    return new PermuteDims(contracted, [...prefix.map((i) => i + 1), 0, rank + 1]).doit();
  }
  if (expr instanceof MatPowNode && expr.base.rows.key === '1' && expr.base.cols.key === '1' && !expr.exp.has(variable)) {
    const factor = new MatMulNode([expr.exp, new MatPowNode(expr.base, expr.exp.sub(1))]).doit();
    return new ArrayContraction(product(arrayDerive(expr.base, variable), factor), [rank + 1, rank + 2]).doit();
  }
  if (expr instanceof ArrayElementwiseApplyFunc) {
    if (expr.function.has(variable)) throw new NotImplementedError('array derivatives with array-dependent function parameters require a formal derivative');
    const factor = new ArrayElementwiseApplyFunc((x) => diff(expr.function.call(x), x), expr.expr);
    const product = new ArrayTensorProduct(arrayDerive(expr.expr, variable), factor).doit();
    return new ArrayDiagonal(product, ...expr.shape.map((_, i) => [rank + i, rank + expr.shape.length + i]));
  }
  if (expr instanceof Add) return new ArrayAdd(...expr.args.filter((arg) => arg.has(variable)).map((arg) => arrayDerive(arg, variable)));
  if (expr instanceof Mul) {
    const terms = expr.args.flatMap((arg, i) => {
      if (!arg.has(variable)) return [];
      return [product(arrayDerive(arg, variable), mul(...expr.args.filter((_, j) => j !== i)))];
    });
    return new ArrayAdd(...terms);
  }
  if (expr instanceof Pow && !expr.exp.has(variable)) {
    return product(mul(expr.exp, pow(expr.base, expr.exp.sub(1))), arrayDerive(expr.base, variable));
  }
  if (expr instanceof Fn && expr.args.length === 1) {
    const arg = first(expr.args), dummy = new Dummy('xi');
    return product(diff(rebuild(expr, [dummy]), dummy).subs(dummy, arg), arrayDerive(arg, variable));
  }
  const converted = convertMatrixToArray(expr);
  if (converted.key !== expr.key) return arrayDerive(converted, variable);
  if (expr instanceof ArrayAdd) {
    const terms = expr.args.filter((a) => a.has(variable)).map((a) => arrayDerive(a, variable));
    return terms.length === 1 ? first(terms) : new ArrayAdd(...terms);
  }
  if (expr instanceof ArrayTensorProduct) {
    const terms: Expr[] = [];
    let offset = 0;
    expr.args.forEach((a, i) => {
      const derivative = arrayDerive(a, variable);
      if (!(derivative instanceof ZeroArray)) {
        const multiplied = product(...expr.args.map((b, j) => j === i ? derivative : b));
        const permutation = [...prefix.map((k) => offset + k), ...Array.from({ length: offset }, (_, k) => k), ...Array.from({ length: getRank(expr) - offset }, (_, k) => offset + rank + k)];
        terms.push(new PermuteDims(multiplied, permutation).doit());
      }
      offset += getRank(a);
    });
    return terms.length === 1 ? first(terms) : new ArrayAdd(...terms);
  }
  if (expr instanceof ArrayContraction) return new ArrayContraction(arrayDerive(expr.expr, variable), ...expr.contractionIndices.map((g) => g.map((i) => i + rank))).doit();
  if (expr instanceof Reshape) return new Reshape(arrayDerive(expr.expr, variable), [...shape, ...expr.shape]);
  if (expr instanceof ArrayDiagonal) return new ArrayDiagonal(arrayDerive(expr.expr, variable), ...expr.diagonalIndices.map((g) => g.map((i) => i + rank))).doit();
  if (expr instanceof PermuteDims) return new PermuteDims(arrayDerive(expr.expr, variable), [...prefix, ...expr.permutation.arrayForm.map((i) => i + rank)]).doit();
  throw new NotImplementedError('array derivative of this expression is not implemented');
}
