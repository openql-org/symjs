// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/array_derivatives.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Derivative, Expr, ExtensionExpr, Rational, S, Sym, UndefFn, type ExprLike } from '../../core/nodes';
import { Indexed } from '../../core/indexed';
import { at, first } from '../../core/guard';
import { callableClass } from '../../core/callable';
import { add, mul, pow, sympify } from '../../core/ops';
import { NoMatch, isNoMatch, type NoMatchResult } from '../../core/truth';
import { NotImplementedError } from '../../core/errors';
import { diff, diffHooks } from '../../calculus/diff';
import { Matrix } from '../../matrices/matrix';
import { Identity, ImmutableMatrixNode, MatAddNode, MatMulNode, MatPowNode, MatrixExpr, MatrixSymbolNode, TraceNode, TransposeNode, ZeroMatrixNode, transposeOf } from '../../matrices/expressions/matexpr';
import { HadamardPowerNode, HadamardProductNode, hadamardPower, hadamardProduct } from '../../matrices/expressions/hadamard';
import { KroneckerProduct } from '../../matrices/expressions/kronecker';
import { diagonalizeVector } from '../../matrices/expressions/diagonal';
import { NDimArray, deriveByArray } from '../ndimarray';
import { ArrayExpr, ArrayContraction, getShape } from './expressions/arrayexpressions';
import { arrayDerive } from './expressions/arrayexprderivatives';
import { convertArrayToMatrix } from './expressions/fromarraytomatrix';

/** Derivative variables, optionally followed by their multiplicity. */
export type ArrayDerivativeVariable = Expr | Matrix | number | readonly [Expr | Matrix, number];
/** Options controlling evaluation of an array derivative. */
export interface ArrayDerivativeOptions {
  /** Evaluate the derivative immediately when true. */
  evaluate?: boolean
}
const normalize = (expr: ExprLike | Matrix): Expr => expr instanceof Matrix ? new ImmutableMatrixNode(expr) : expr instanceof NDimArray ? expr.asImmutable() : sympify(expr);
const shaped = (expr: Expr): boolean => expr instanceof MatrixExpr || expr instanceof NDimArray || expr instanceof ArrayExpr || expr instanceof ArrayDerivativeNode;
const scalar = (expr: Expr): boolean => !shaped(expr) && (!(expr instanceof ExtensionExpr) || expr.isScalar);
const explicit = (expr: Expr): expr is ImmutableMatrixNode | NDimArray => expr instanceof ImmutableMatrixNode || expr instanceof NDimArray;
const unbox = (expr: Expr): Expr | Matrix => expr instanceof ImmutableMatrixNode ? expr.matrix : expr;
const validVariable = (variable: Expr): boolean => variable instanceof Sym || variable instanceof UndefFn || variable instanceof Derivative || variable instanceof Indexed || shaped(variable) ||
  (variable instanceof ExtensionExpr && (!variable.isScalar || variable.name === 'MatrixElement' || variable.name === 'ArrayElement'));

/** Pull the coefficient of dX back through the factors of a scalar matrix differential. */
function matrixGradient(expr: Expr, variable: MatrixSymbolNode): Expr | NoMatchResult {
  const unit = (e: MatrixExpr): boolean => e.rows.key === '1' && e.cols.key === '1';
  // A vector's elementwise Jacobian is diagonal.
  if (variable.rows.key === '1' || variable.cols.key === '1') {
    if (expr instanceof HadamardPowerNode && expr.base.key === variable.key && scalar(expr.exp) && !expr.exp.has(variable)) {
      return mul(expr.exp, diagonalizeVector(hadamardPower(variable, add(expr.exp, -1))));
    }
    if (expr instanceof HadamardProductNode && expr.args.length > 1 && expr.args.filter((a) => a.has(variable)).length === 1 && expr.args.some((a) => a.key === variable.key)) {
      return diagonalizeVector(hadamardProduct(...expr.args.filter((a) => a.key !== variable.key)));
    }
  }
  const vectorJacobian = expr instanceof MatMulNode && variable.cols.key === '1' && expr.cols.key === '1' && !unit(expr)
    && expr.args.every((a) => !a.has(variable) || a.key === variable.key || a instanceof TransposeNode && a.arg.key === variable.key);
  if (!(expr instanceof TraceNode || expr instanceof MatrixExpr && (unit(expr) || vectorJacobian))) return NoMatch;
  const terms: Expr[] = [];
  // Keep the two free derivative axes separate through products and transposes.
  const contract = (left: Expr, middle: Expr, right: Expr): Expr =>
    right instanceof MatrixExpr && unit(right) ? mul(left, right, middle) : mul(left, middle, transposeOf(right));
  const visit = (node: Expr, left: Expr, middle: Expr, right: Expr): boolean => {
    if (!node.has(variable)) return true;
    if (node.key === variable.key) {
      if (vectorJacobian && right instanceof MatrixExpr) {
        if (unit(right)) terms.push(right.isIdentity === true ? left : KroneckerProduct(left, right));
        else terms.push(mul(left, right));
      } else terms.push(contract(left, middle, right));
      return true;
    }
    if (node instanceof TransposeNode) return visit(node.arg, right, middle instanceof MatrixExpr && unit(middle) ? middle : transposeOf(middle), left);
    if (node instanceof MatAddNode) return node.args.every((a) => visit(a, left, middle, right));
    if (node instanceof MatMulNode) {
      const [coeff, factors] = node.asCoeffMatrices();
      if (coeff.has(variable)) return false;
      const sum = factors.findIndex((f) => f instanceof MatAddNode);
      const product: Expr[] = [...factors];
      const distribute = sum >= 0 && coeff instanceof Rational && !coeff.isOne;
      if (distribute) product[sum] = mul(coeff, at(factors, sum));
      const multiplier = distribute ? S.One : coeff;
      return product.every((a, i) => !a.has(variable) || visit(a,
        mul(mul(multiplier, ...product.slice(0, i).reverse().map(transposeOf)), left), middle,
        mul(...product.slice(i + 1), right)));
    }
    if (node instanceof HadamardProductNode) {
      const weight = contract(left, middle, right);
      return node.args.every((a, i) => !a.has(variable) || visit(a, hadamardProduct(weight, ...node.args.filter((_, j) => i !== j)), S.One, S.One));
    }
    if ((node instanceof MatPowNode || node instanceof HadamardPowerNode) && node.base instanceof MatrixExpr && unit(node.base) && scalar(node.exp) && !node.exp.has(variable)) {
      const weight = mul(node.exp, pow(node.base, add(node.exp, -1)), contract(left, middle, right));
      return visit(node.base, Identity(1), weight, Identity(1));
    }
    return false;
  };
  const value = expr instanceof TraceNode ? expr.arg : expr;
  return visit(value, Identity(value.rows), S.One, Identity(value.cols)) && terms.length ? add(...terms) : NoMatch;
}

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
    if (variable instanceof MatrixSymbolNode) {
      const gradient = matrixGradient(expr, variable);
      if (!isNoMatch(gradient)) return gradient;
    }
    try {
      let derived = arrayDerive(expr, variable);
      const dims = getShape(derived);
      const singleton = dims.flatMap((dim, i) => dim.key === S.One.key ? [i] : []);
      if (dims.length > 2 && singleton.length >= dims.length - 2 && dims.length % 2 === 0) {
        const removed = singleton.slice(-(dims.length - 2));
        derived = new ArrayContraction(derived, ...Array.from({ length: removed.length / 2 }, (_, i) => [at(removed, 2 * i), at(removed, 2 * i + 1)])).doit();
      }
      return convertArrayToMatrix(derived);
    }
    catch (error) { if (error instanceof NotImplementedError) return NoMatch; throw error; }
  }
  return NoMatch;
}

/**
 * An unevaluated derivative whose shape includes the axes of its array variables.
 *
 * @see SymPy `sympy.tensor.array.array_derivatives.ArrayDerivative`
 * @example
 * ```ts
 * import { ArrayDerivative, ex } from '@symjs/symjs';
 *
 * ArrayDerivative(ex`x**2`, ex`x`, { evaluate: true }); // => 2*x
 * ```
 */
export class ArrayDerivativeNode extends Derivative {
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.array_derivatives.ArrayDerivative.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Whether this expression represents a scalar.
   *
   * @see SymPy `sympy.tensor.array.array_derivatives.ArrayDerivative.is_scalar`
   */
  readonly isScalar = false;
  /**
   * Constructs an instance of `ArrayDerivativeNode`.
   *
   * @param args - Operands in their defining order.
   */
  constructor(args: readonly Expr[]) {
    super(args);
    this.shape = Object.freeze([...this.variableCount.flatMap(([variable, count]) => Array.from({ length: count }, () => getShape(variable)).flat()), ...getShape(this.expr)]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): ArrayDerivativeNode { return new ArrayDerivativeNode(args); }
  /**
   * Evaluates the derivative with respect to each variable in turn.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.array_derivatives.ArrayDerivative.doit`
   */
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

/**
 * Differentiates scalar, matrix or array expressions with respect to scalar or array variables.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param spec - Differentiation variables, optional repetition counts and evaluation options.
 * @returns The unevaluated derivative, or its value when evaluation is requested.
 * @throws RangeError when a variable or repetition count is invalid or the differentiation variable is ambiguous.
 * @throws TypeError when a repetition count precedes the first variable.
 * @see SymPy `sympy.tensor.array.array_derivatives.ArrayDerivative`
 * @example
 * ```ts
 * import { ArrayDerivative, ex } from '@symjs/symjs';
 *
 * ArrayDerivative(ex`x**2`, ex`x`, { evaluate: true }); // => 2*x
 * ```
 */
export const ArrayDerivative = /* @__PURE__ */ callableClass(ArrayDerivativeNode, create);
export type ArrayDerivative = ArrayDerivativeNode;

// Array derivatives are loaded above scalar calculus and register their dispatch here.
diffHooks.array = (expr, variable, count) => ArrayDerivative(expr, [variable, count], { evaluate: true });
