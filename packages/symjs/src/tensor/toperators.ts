// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 tensor/toperators.py, BSD-3-Clause; see LICENSE.

import { callableClass } from '../core/callable';
import { NotImplementedError } from '../core/errors';
import type { ExprMap } from '../core/exprmap';
import { at, cast, first } from '../core/guard';
import { S, Sym } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { mul, pow, splitCoeff, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { PREC, precedence } from '../printing/str';
import { NDimArray, ImmutableDenseNDimArray, deriveByArray } from './ndimarray';
import { permutedims, tensorcontraction } from './arrayop';
import { TensExpr, Tensor, contractIndices } from './tensor';
import type { TensorHeadNode, TensorIndexNode } from './tensor';

function mirror(expr: Expr): Expr {
  return expr instanceof Tensor ? expr.replaceIndices(new Map(expr.getFreeIndices().map((i) => [i.key, i.neg()]))) : expr;
}

/**
 * Tensor partial derivative; deriving indices have the opposite variance.
 *
 * @see SymPy `sympy.tensor.toperators.PartialDerivative`
 * @example
 * ```ts
 * import { PartialDerivative, TensorHead, TensorIndex, TensorIndexType } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const A = TensorHead('A', [L]);
 * const i = TensorIndex('i', L), j = TensorIndex('j', L);
 * PartialDerivative(A.at(i), A.at(j)).getIndices(); // => [i, -j]
 * ```
 */
export class PartialDerivativeNode extends TensExpr {
  private readonly indices: TensorIndexNode[];
  private readonly freeIndices: TensorIndexNode[];
  /**
   * Constructs an instance of `PartialDerivativeNode`.
   *
   * @param expression - Expression to transform.
   * @param variables - Variables in the order they are supplied.
   * @throws TypeError when a differentiation variable is neither a tensor nor a symbol.
   */
  constructor(expression: ExprLike, ...variables: Expr[]) {
    const value = sympify(expression);
    const expr = value instanceof PartialDerivativeNode ? value.expr : value;
    const vars = value instanceof PartialDerivativeNode ? [...value.variables, ...variables] : variables;
    if (vars.some((v) => !(v instanceof Tensor || v instanceof Sym))) throw new TypeError('derivative variables must be tensors or symbols');
    const contracted = contractIndices([expr, ...vars.map(mirror)], true);
    super('PartialDerivative', [first(contracted.args), ...contracted.args.slice(1).map(mirror)]);
    this.indices = contracted.indices;
    this.freeIndices = [...contracted.free].sort((a, b) => a[1] - b[1]).map(([i]) => i);
  }
  /**
   * Identifies the operand of this tensor operation.
   *
   * @returns The underlying expression.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.expr`
   */
  get expr(): Expr { return first(this.args); }
  /**
   * Variables in the order they are supplied.
   *
   * @returns The differentiation variables in their original order.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.variables`
   */
  get variables(): readonly Expr[] { return this.args.slice(1); }
  /**
   * Formats the tensor partial derivative as a LaTeX fraction, parenthesizing it when needed inside a
   * product.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    const body = precedence(this.expr) <= PREC.MUL ? `\\left(${print(this.expr)}\\right)` : print(this.expr);
    const vars = this.variables;
    if (vars.length === 1) return `\\frac{\\partial}{\\partial {${print(first(vars))}}}{${body}}`;
    return `\\frac{\\partial^{${vars.length}}}{${vars.map((v) => `\\partial {${print(v)}}`).join(' ')}}{${body}}`;
  }
  /**
   * Extracts the numerical or symbolic scalar factor of the tensor expression.
   *
   * @returns The scalar coefficient.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.coeff`
   */
  get coEff(): Expr { return S.One; }
  /**
   * Factors out the scalar multiplier of the tensor expression.
   *
   * @returns The coefficient-free tensor expression.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.nocoeff`
   */
  get nocoeff(): Expr { return this; }
  /**
   * Lists the tensor indices in slot order, including contracted indices.
   *
   * @returns The ordered tensor indices.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.get_indices`
   */
  getIndices(): TensorIndexNode[] { return [...this.indices]; }
  /**
   * Lists the uncontracted indices in slot order.
   *
   * @returns The uncontracted indices.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.get_free_indices`
   */
  getFreeIndices(): TensorIndexNode[] { return [...this.freeIndices]; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): PartialDerivativeNode { return new PartialDerivativeNode(first(args), ...args.slice(1)); }
  /**
   * Evaluates the outer tensor operation with the current operands.
   *
   * @returns The resulting partial derivative.
   */
  doitShallow(): PartialDerivativeNode { return this.withArgs(this.args); }
  /**
   * Rebuilds the derivative with contracted indices without differentiating the operand.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative.doit`
   */
  doit(): PartialDerivativeNode { return this.doitShallow(); }
  /**
   * Canonicalizes tensor products under index symmetries using the Butler–Portugal algorithm.
   *
   * @returns The transformed tensor expression.
   */
  canonBp(): PartialDerivativeNode { return this.doitShallow(); }
  /**
   * Metric contraction through a partial derivative is unsupported.
   *
   * @param _g - Metric tensor head to contract.
   * @returns This operation always throws a `NotImplementedError`.
   * @throws NotImplementedError when the contraction would pass through a partial derivative.
   */
  contractMetric(_g: TensorHeadNode): Expr { throw new NotImplementedError('metric contraction through a partial derivative'); }
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   */
  replaceIndices(repl: ReadonlyMap<string, TensorIndexNode>): PartialDerivativeNode {
    const replace = (e: Expr): Expr => e instanceof TensExpr ? e.replaceIndices(repl) : e;
    return new PartialDerivativeNode(replace(this.expr), ...this.variables.map((v) => mirror(replace(mirror(v)))));
  }
  /**
   * Substitutes index pairs while respecting index variance.
   *
   * @param pairs - Old and replacement tensor indices.
   * @returns The transformed tensor expression.
   */
  substituteIndices(...pairs: [TensorIndexNode, TensorIndexNode][]): PartialDerivativeNode {
    return this.replaceIndices(new Map(pairs.flatMap(([a, b]) => [[a.key, b], [a.neg().key, b.neg()]])));
  }
  /**
   * Builds the component array from tensor replacements and tracks its remaining indices.
   *
   * @param repl - Existing replacement map.
   * @returns The remaining indices and their component array.
   * @see SymPy `sympy.tensor.toperators.PartialDerivative._extract_data`
   */
  extractData(repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr] {
    let [indices, array] = this.expr instanceof TensExpr ? this.expr.extractData(repl) : [[], this.expr];
    for (const variable of this.variables) {
      if (variable instanceof Sym) {
        array = array instanceof NDimArray ? array.applyfunc((e) => diff(e, variable)) : diff(array, variable);
        continue;
      }
      const [varIndices, values] = cast(variable, Tensor).extractData(repl);
      const variables = cast(values, NDimArray);
      const entries = variables.flatElements().map((e) => splitCoeff(e));
      const bases = new ImmutableDenseNDimArray(entries.map(([, e]) => e), variables.shape);
      const rank = array instanceof NDimArray ? array.rank() : 0;
      const derived = cast(deriveByArray(array, bases), NDimArray);
      const n = variables.rank();
      const reordered = permutedims(derived, [...Array.from({ length: rank }, (_, i) => n + i), ...Array.from({ length: n }, (_, i) => i)]);
      const scaled = new ImmutableDenseNDimArray(reordered.flatElements().map((e, i) => mul(e, pow(at(entries, i % entries.length)[0], -1))), reordered.shape);
      const all = [...indices, ...varIndices.map((i) => i.neg())];
      const contracted: number[][] = [];
      const removed = new Set<number>();
      all.forEach((index, i) => {
        const j = all.findIndex((other, k) => k > i && other.key === index.neg().key);
        if (j >= 0) { contracted.push([i, j]); removed.add(i); removed.add(j); }
      });
      array = contracted.length ? tensorcontraction(scaled, ...contracted) : scaled;
      indices = all.filter((_, i) => !removed.has(i));
    }
    return [indices, array];
  }
}

/**
 * Constructs a partial derivative for a tensor expression.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param variables - Tensor or scalar variables of differentiation.
 * @returns The resulting `PartialDerivative` expression.
 * @throws TypeError when a differentiation variable is neither a tensor nor a symbol.
 * @see SymPy `sympy.tensor.toperators.PartialDerivative`
 * @example
 * ```ts
 * import { PartialDerivative, TensorHead, TensorIndex, TensorIndexType } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const A = TensorHead('A', [L]);
 * const i = TensorIndex('i', L), j = TensorIndex('j', L);
 * PartialDerivative(A.at(i), A.at(j)).getIndices(); // => [i, -j]
 * ```
 */
export const PartialDerivative = callableClass(PartialDerivativeNode, (expr: ExprLike, ...variables: Expr[]): PartialDerivativeNode => new PartialDerivativeNode(expr, ...variables));
export type PartialDerivative = PartialDerivativeNode;
