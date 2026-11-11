// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/array_derivatives.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Derivative, Expr, ExtensionExpr, Rational, S, Sym, UndefFn, type ExprLike } from '../../core/nodes';
import { Indexed } from '../../core/indexed';
import { at, first } from '../../core/guard';
import { callableClass } from '../../core/callable';
import { sympify } from '../../core/ops';
import { NoMatch, isNoMatch, type NoMatchResult } from '../../core/truth';
import { NotImplementedError } from '../../core/errors';
import { diff } from '../../calculus/diff';
import { Matrix } from '../../matrices/matrix';
import { Identity, ImmutableMatrixNode, MatrixExpr, MatrixSymbolNode, ZeroMatrixNode } from '../../matrices/expressions/matexpr';
import { NDimArray, deriveByArray } from '../ndimarray';
import { ArrayExpr, getShape } from './expressions/arrayexpressions';
import { arrayDerive } from './expressions/arrayexprderivatives';
import { convertArrayToMatrix } from './expressions/fromarraytomatrix';

/** Derivative variables, optionally followed by their multiplicity. */
export type ArrayDerivativeVariable = Expr | Matrix | number | readonly [Expr | Matrix, number];
export interface ArrayDerivativeOptions { evaluate?: boolean }
const normalize = (expr: ExprLike | Matrix): Expr => expr instanceof Matrix ? new ImmutableMatrixNode(expr) : expr instanceof NDimArray ? expr.asImmutable() : sympify(expr);
const shaped = (expr: Expr): boolean => expr instanceof MatrixExpr || expr instanceof NDimArray || expr instanceof ArrayExpr || expr instanceof ArrayDerivativeNode;
const scalar = (expr: Expr): boolean => !shaped(expr) && (!(expr instanceof ExtensionExpr) || expr.isScalar);
const explicit = (expr: Expr): expr is ImmutableMatrixNode | NDimArray => expr instanceof ImmutableMatrixNode || expr instanceof NDimArray;
const unbox = (expr: Expr): Expr | Matrix => expr instanceof ImmutableMatrixNode ? expr.matrix : expr;
const validVariable = (variable: Expr): boolean => variable instanceof Sym || variable instanceof UndefFn || variable instanceof Derivative || variable instanceof Indexed || shaped(variable) ||
  (variable instanceof ExtensionExpr && (!variable.isScalar || variable.name === 'MatrixElement' || variable.name === 'ArrayElement'));

function once(expr: Expr, variable: Expr): Expr | NoMatchResult {
  if (scalar(expr)) {
    if (explicit(variable)) {
      const entries = variable instanceof ImmutableMatrixNode ? variable.matrix.data : variable.flatElements();
      if (!entries.every(validVariable)) throw new RangeError('cannot derive by this array');
      return variable instanceof ImmutableMatrixNode ? new ImmutableMatrixNode(variable.matrix.map((v) => diff(expr, v))) : variable.applyfunc((v) => diff(expr, v));
    }
    if (scalar(variable)) return diff(expr, variable);
    if (variable instanceof MatrixExpr && !expr.has(variable)) return new ZeroMatrixNode(variable.rows, variable.cols);
  } else if (scalar(variable)) {
    if (expr instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(expr.matrix.diff(variable));
    if (expr instanceof NDimArray) return expr.applyfunc((e) => diff(e, variable));
    if (expr instanceof MatrixExpr) return expr.diffSelf(variable, diff) ?? NoMatch;
  }
  if (explicit(expr) && explicit(variable)) return deriveByArray(unbox(expr), unbox(variable));
  if (explicit(expr) || explicit(variable)) return NoMatch;
  // Matrix differentiation suppresses the singleton axes of vector Jacobians.
  if (variable instanceof MatrixSymbolNode && expr.key === variable.key) {
    if (variable.rows.key === '1') return variable.cols.key === '1' ? S.One : Identity(variable.cols);
    if (variable.cols.key === '1') return Identity(variable.rows);
  }
  if (variable instanceof MatrixExpr || variable instanceof ArrayExpr) {
    // SymPy retains independent symbolic matrix derivatives unevaluated.
    if (!scalar(expr) && !expr.has(variable)) return NoMatch;
    try { return convertArrayToMatrix(arrayDerive(expr, variable)); }
    catch (error) { if (error instanceof NotImplementedError) return NoMatch; throw error; }
  }
  return NoMatch;
}

/** Unevaluated array derivative; variable axes precede expression axes. */
export class ArrayDerivativeNode extends Derivative {
  readonly shape: readonly Expr[];
  readonly isScalar = false;
  constructor(args: readonly Expr[]) {
    super(args);
    this.shape = Object.freeze([...this.variableCount.flatMap(([variable, count]) => Array.from({ length: count }, () => getShape(variable)).flat()), ...getShape(this.expr)]);
  }
  override withArgs(args: readonly Expr[]): ArrayDerivativeNode { return new ArrayDerivativeNode(args); }
  override doit(): Expr {
    let result = this.expr;
    const variables = this.variableCount;
    for (const [i, [variable, count]] of variables.entries()) {
      for (let j = 0; j < count; j++) {
        const next = once(result, variable);
        if (isNoMatch(next)) return new ArrayDerivativeNode([result, variable, Rational.of(count - j), ...variables.slice(i + 1).flatMap(([v, n]) => [v, Rational.of(n)])]);
        result = next;
      }
    }
    return result;
  }
}

const isPair = (value: ArrayDerivativeVariable | ArrayDerivativeOptions): value is readonly [Expr | Matrix, number] => Array.isArray(value);
/** Construct ArrayDerivative(expr, variable, [variable, count], {evaluate}). */
function create(expr: ExprLike | Matrix, ...spec: (ArrayDerivativeVariable | ArrayDerivativeOptions)[]): Expr {
  let expression = normalize(expr), evaluate = false;
  const variables: [Expr, number][] = [];
  for (const item of spec) {
    if (typeof item === 'number') {
      if (!variables.length) throw new TypeError('a derivative count requires a variable');
      at(variables, variables.length - 1)[1] = item;
    } else if (item instanceof Expr || item instanceof Matrix || isPair(item)) {
      variables.push(isPair(item) ? [normalize(item[0]), item[1]] : [normalize(item), 1]);
    } else evaluate = item.evaluate ?? false;
  }
  if (!variables.length) {
    const free = [...expression.freeSymbols()];
    if (!free.length) return S.Zero;
    if (free.length !== 1) throw new RangeError('specify the derivative variable');
    variables.push([first(free), 1]);
  }
  const merged: [Expr, number][] = expression instanceof ArrayDerivativeNode ? expression.variableCount : [];
  if (expression instanceof ArrayDerivativeNode) expression = expression.expr;
  for (const [variable, count] of variables) {
    if (!Number.isSafeInteger(count) || count < 0) throw new RangeError('derivative order must be a nonnegative integer');
    if (!count) continue;
    if (!validVariable(variable)) throw new RangeError('invalid derivative variable');
    const previous = merged[merged.length - 1];
    if (previous && previous[0].key === variable.key) previous[1] += count;
    else merged.push([variable, count]);
  }
  if (!merged.length) return expression;
  const node = new ArrayDerivativeNode([expression, ...merged.flatMap(([v, n]) => [v, Rational.of(n)])]);
  return evaluate ? node.doit() : node;
}

/** SymPy ArrayDerivative; use evaluate: true or doit() to compute its value. */
export const ArrayDerivative = /* @__PURE__ */ callableClass(ArrayDerivativeNode, create);
export type ArrayDerivative = ArrayDerivativeNode;
