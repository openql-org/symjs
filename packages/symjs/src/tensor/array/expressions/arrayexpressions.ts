// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/array_expressions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { Dummy, Expr, ExtensionExpr, Rational, S, Sym, type ExprLike } from '../../../core/nodes';
import { Lambda, LambdaNode } from '../../../core/lambda';
import { TupleNode } from '../../../core/containers';
import { at, cast, first } from '../../../core/guard';
import { add, mul, sub, sympify } from '../../../core/ops';
import { isNegative, isNonNegative, isReal } from '../../../core/assumptions';
import { NotImplementedError } from '../../../core/errors';
import { MatrixExpr, checkDim, strPrecedence, latexPrecedence } from '../../../matrices/expressions/matexpr';
import { ImmutableDenseNDimArray, NDimArray } from '../../ndimarray';
import { tensorproduct, tensorcontraction, tensordiagonal, permutedims, type PermutationLike } from '../../arrayop';
import { Permutation } from '../../../combinatorics/permutations';
import { KroneckerDelta } from '../../../functions/special/hyper';
import { PREC } from '../../../printing/str';
import { compareKeys, sortKey } from '../../../printing/sortkey';
import { diagonalizeVector } from '../../../matrices/expressions/diagonal';
import { sortContractionIndices } from './utils';

/** Axis lengths of a symbolic array in dimension order. */
export type ArrayShape = readonly ExprLike[];
/** Groups of zero-based array axes. */
export type ArrayAxes = readonly (readonly number[])[];
const tuple = (items: readonly ExprLike[]): TupleNode => new TupleNode(items.map(sympify));
const values = (arg: Expr): readonly Expr[] => cast(arg, TupleNode).args;
const integer = (e: Expr): number => {
  if (!(e instanceof Rational) || !e.isInteger || e.p < 0n || e.p > BigInt(Number.MAX_SAFE_INTEGER)) throw new RangeError('a nonnegative, safely representable integer is required');
  return Number(e.p);
};
const indices = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const sameShape = (a: readonly Expr[], b: readonly Expr[]): boolean => a.length === b.length && a.every((s, i) => s.key === at(b, i).key);
const isExpressionShape = (value: unknown): value is readonly (Expr | number)[] => Array.isArray(value) && value.every((d: unknown) => d instanceof Expr || typeof d === 'number');

/**
 * Finds the dimensions of an array, array expression, matrix, or scalar.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The axis lengths in order.
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.get_shape`
 */
export function getShape(expr: Expr): readonly Expr[] {
  if (expr instanceof ArrayExpr || expr instanceof MatrixExpr) return expr.shape;
  if (expr instanceof NDimArray) return expr.shape.map((n) => Rational.of(n));
  if ('shape' in expr && isExpressionShape(expr.shape)) return expr.shape.map(sympify);
  return [];
}
/**
 * Counts the axes of an expression, assigning rank zero to a scalar.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The expression rank.
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.get_rank`
 */
export function getRank(expr: Expr): number { return getShape(expr).length; }

/** An array expression represented explicitly, preserving scalar results. @internal */
export function explicitArray(expr: Expr): Expr {
  if (expr instanceof ArrayExpr) return expr.asExplicit();
  if (expr instanceof MatrixExpr) return new ImmutableDenseNDimArray(expr.asExplicit());
  return expr;
}

/**
 * Base of lazy N-dimensional array expressions.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions._ArrayExpr`
 */
export abstract class ArrayExpr extends ExtensionExpr {
  /** The lengths of the axes in order. */
  abstract readonly shape: readonly Expr[];
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   */
  abstract asExplicit(): Expr;
  /**
   * Counts the axes of the array expression.
   *
   * @returns The array rank.
   */
  rank(): number { return this.shape.length; }
  /**
   * Selects the entry at the given indices.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The selected entry.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions._ArrayExpr.__getitem__`
   */
  at(...index: ExprLike[]): Expr { return new ArrayElement(this, index); }
  /**
   * Returns the symbolic array expression in its current form.
   *
   * @returns This symbolic array expression.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions._ArrayExpr.doit`
   */
  doit(): Expr { return this; }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr { return this.doit(); }
}

/**
 * An array of symbolic entries with a specified shape.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArraySymbol`
 */
export class ArraySymbol extends ArrayExpr {
  /**
   * Selects the entry at the given indices.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The selected entry.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArraySymbol.__getitem__`
   */
  override at(...index: ExprLike[]): ArrayElement { return new ArrayElement(this, index); }
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArraySymbol.shape`
   */
  readonly shape: readonly Expr[];
  /** Symbolic label used to identify this object. */
  readonly label: Sym;
  /**
   * Constructs an instance of `ArraySymbol`.
   *
   * @param name - Symbolic name.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(name: string | Sym, shape: ArrayShape) {
    const label = typeof name === 'string' ? new Sym(name) : name;
    const dims = shape.map((s) => checkDim(sympify(s)));
    super('ArraySymbol', [label, tuple(dims)]);
    this.shape = Object.freeze(dims);
    this.label = label;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArraySymbol(cast(first(args), Sym), values(at(args, 1))); }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string { return print(this.label); }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string { return print(this.label); }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @throws TypeError when a rank-zero array symbol is expanded.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArraySymbol.as_explicit`
   */
  asExplicit(): ImmutableDenseNDimArray {
    if (!this.shape.length) throw new TypeError('a rank-zero ArraySymbol cannot be expanded');
    const shape = this.shape.map(integer);
    let coordinates: number[][] = [[]];
    for (const size of shape) coordinates = coordinates.flatMap((c) => indices(size).map((i) => [...c, i]));
    return new ImmutableDenseNDimArray(coordinates.map((c) => this.at(...c)), shape);
  }
}

/**
 * A scalar entry of a symbolic array.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElement`
 */
export class ArrayElement extends ExtensionExpr {
  /**
   * The indices in the order of the tensor or array slots.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElement.indices`
   */
  readonly indices: readonly Expr[];
  /**
   * Constructs an instance of `ArrayElement`.
   *
   * @param parent - Array expression whose entries are indexed.
   * @param index - Zero-based index or indices selecting the desired component.
   * @throws RangeError when an index is outside the array bounds or the number of indices does not match the rank.
   */
  constructor(
    /** The indexed array expression. */
    readonly parent: Expr, index: ArrayShape) {
    const ind = index.map(sympify), shape = getShape(parent);
    const shaped = parent instanceof ArrayExpr || parent instanceof MatrixExpr || parent instanceof NDimArray || shape.length > 0;
    if (shaped && ind.length !== shape.length) throw new RangeError('array index rank does not match the shape');
    ind.forEach((i, k) => {
      if (isNegative(i) === true || (shaped && isReal(i) === true && isReal(at(shape, k)) === true && isNonNegative(sub(i, at(shape, k))) === true)) throw new RangeError('array index out of bounds');
    });
    super('ArrayElement', [parent, tuple(ind)]);
    this.indices = Object.freeze(ind);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArrayElement(first(args), values(at(args, 1))); }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    const parent = print(this.parent);
    return `${strPrecedence(this.parent) < PREC.FUNC ? '(' + parent + ')' : parent}[${this.indices.map(print).join(', ')}]`;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    const parent = print(this.parent);
    return `{{${latexPrecedence(this.parent) < PREC.FUNC ? '\\left(' + parent + '\\right)' : parent}}_{${this.indices.map(print).join(', ')}}}`;
  }
  /**
   * Computes the derivative of this expression.
   *
   * @param x - Variable of differentiation.
   * @returns The derivative of the selected entry.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElement._eval_derivative`
   */
  override diffSelf(x: Expr): Expr {
    if (x instanceof ArrayElement && x.parent.key === this.parent.key) return mul(...this.indices.map((i, k) => KroneckerDelta(i, at(x.indices, k))));
    return S.Zero;
  }
}

/**
 * Unevaluated outer product; axis blocks follow argument order.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayTensorProduct`
 */
export class ArrayTensorProduct extends ArrayExpr {
  /**
   * Returns the ranks of the objects in the uppermost tensor product inside the current object. In
   * case no tensor products are contained, return the atomic ranks.
   *
   * @returns The ranks of the objects in the uppermost tensor product inside the current object.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayTensorProduct.subranks`
   */
  get subranks(): number[] { return this.args.map(getRank); }
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayTensorProduct.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `ArrayTensorProduct`.
   *
   * @param args - Operands in their defining order.
   */
  constructor(...args: Expr[]) { super('ArrayTensorProduct', args); this.shape = Object.freeze(args.flatMap((a) => [...getShape(a)])); }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArrayTensorProduct(...args); }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayTensorProduct.as_explicit`
   */
  asExplicit(): Expr { return tensorproduct(...this.args.map(explicitArray)); }
  /**
   * Flattens nested tensor products and combines axis permutations.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayTensorProduct.doit`
   */
  override doit(): Expr {
    const args = this.args.flatMap((a) => a instanceof ArrayTensorProduct ? a.args : [a]);
    if (args.length === 0) return S.One;
    if (args.length === 1) return first(args);
    if (args.some((arg) => arg instanceof PermuteDims)) {
      let offset = 0;
      const permutation = args.flatMap((arg) => {
        const axes = arg instanceof PermuteDims ? arg.permutation.arrayForm : indices(getRank(arg));
        const shifted = axes.map((axis) => axis + offset);
        offset += axes.length;
        return shifted;
      });
      const product = new ArrayTensorProduct(...args.map((arg) => arg instanceof PermuteDims ? arg.expr : arg)).doit();
      return new PermuteDims(product, permutation).doit();
    }
    if (args.some((arg) => arg instanceof ArrayDiagonal)) {
      let offset = 0;
      const groups: number[][] = [], desired: number[] = [];
      const factors = args.map((arg) => {
        const base = arg instanceof ArrayDiagonal ? arg.expr : arg;
        const diagonals = arg instanceof ArrayDiagonal ? arg.diagonalIndices : [];
        groups.push(...diagonals.map((group) => group.map((axis) => axis + offset)));
        desired.push(...remainingAxes(getRank(base), diagonals).map((axis) => axis + offset), ...diagonals.map((group) => first(group) + offset));
        offset += getRank(base);
        return base;
      });
      const actual = [...remainingAxes(offset, groups), ...groups.map(first)];
      const diagonal = new ArrayDiagonal(new ArrayTensorProduct(...factors).doit(), ...groups).doit();
      return new PermuteDims(diagonal, desired.map((axis) => actual.indexOf(axis))).doit();
    }
    // Lift contractions out of the product without changing its free axes.
    let offset = 0;
    const groups: number[][] = [];
    const factors = args.map((a) => {
      const base = a instanceof ArrayContraction ? a.expr : a;
      if (a instanceof ArrayContraction) groups.push(...a.contractionIndices.map((g) => g.map((i) => i + offset)));
      offset += getRank(base);
      return base;
    });
    return groups.length ? new ArrayContraction(new ArrayTensorProduct(...factors).doit(), ...groups).doit() : new ArrayTensorProduct(...args);
  }
}

function validateGroups(expr: Expr, groups: ArrayAxes, diagonal: boolean): number[][] {
  const shape = getShape(expr), used = new Set<number>();
  for (const group of groups) {
    if (group.length < (diagonal ? 2 : 1)) throw new RangeError('too few axes in an index group');
    for (const i of group) {
      if (!Number.isInteger(i) || i < 0 || i >= shape.length || used.has(i)) throw new RangeError('invalid or repeated array axis');
      if (at(shape, i).key !== at(shape, first(group)).key) throw new RangeError('axes must have equal dimensions');
      used.add(i);
    }
  }
  return sortContractionIndices(groups);
}
/** Surviving axes in the original coordinate order. @internal */
export function remainingAxes(rank: number, groups: ArrayAxes): number[] {
  const used = new Set(groups.flat());
  return indices(rank).filter((i) => !used.has(i));
}

/**
 * Sum over coincident indices; each group removes its axes.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction`
 */
export class ArrayContraction extends ArrayExpr {
  /**
   * Returns the ranks of the objects in the uppermost tensor product inside the current object. In
   * case no tensor products are contained, return the atomic ranks.
   *
   * @returns The ranks of the objects in the uppermost tensor product inside the current object.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.subranks`
   */
  get subranks(): number[] { return this.expr instanceof ArrayTensorProduct ? this.expr.subranks : [getRank(this.expr)]; }
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Groups of axes summed over a common index.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.contraction_indices`
   */
  readonly contractionIndices: readonly (readonly number[])[];
  /**
   * Constructs an instance of `ArrayContraction`.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param groups - Groups of axes constrained to have equal indices.
   */
  constructor(
    /**
     * The underlying expression on which this operation acts.
     *
     * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.expr`
     */
    readonly expr: Expr, ...groups: (readonly number[])[]) {
    const axes = validateGroups(expr, groups, false);
    super('ArrayContraction', [expr, ...axes.map(tuple)]);
    this.contractionIndices = axes;
    this.shape = remainingAxes(getRank(expr), axes).map((i) => at(getShape(expr), i));
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArrayContraction(first(args), ...args.slice(1).map((g) => values(g).map(integer))); }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.as_explicit`
   */
  asExplicit(): Expr { return this.contractionIndices.length ? tensorcontraction(explicitArray(this.expr), ...this.contractionIndices) : explicitArray(this.expr); }
  /**
   * Combines nested contractions and distributes contraction over array sums.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.doit`
   */
  override doit(): Expr {
    if (!this.contractionIndices.length) return this.expr;
    if (this.expr instanceof ArrayAdd) return new ArrayAdd(...this.expr.args.map((a) => new ArrayContraction(a, ...this.contractionIndices).doit()));
    if (this.expr instanceof ArrayContraction) {
      const inner = this.expr, remaining = remainingAxes(getRank(inner.expr), inner.contractionIndices);
      return new ArrayContraction(inner.expr, ...inner.contractionIndices, ...this.contractionIndices.map((g) => g.map((i) => at(remaining, i)))).doit();
    }
    if (this.expr instanceof ArrayDiagonal) {
      const inner = this.expr, rank = getRank(inner.expr);
      const coordinates = [...remainingAxes(rank, inner.diagonalIndices).map((i) => [i]), ...inner.diagonalIndices];
      const groups = this.contractionIndices.map((g) => g.flatMap((i) => at(coordinates, i)));
      const used = new Set(groups.flat()), remaining = remainingAxes(rank, groups);
      const diagonals = inner.diagonalIndices.filter((g) => !used.has(first(g))).map((g) => g.map((i) => remaining.indexOf(i)));
      const contracted = new ArrayContraction(inner.expr, ...groups).doit();
      return diagonals.length ? new ArrayDiagonal(contracted, ...diagonals) : contracted;
    }
    if (this.expr instanceof PermuteDims) {
      const inner = this.expr, p = inner.permutation.arrayForm;
      const groups = this.contractionIndices.map((g) => g.map((i) => at(p, i)));
      const actual = remainingAxes(getRank(inner.expr), groups);
      const desired = remainingAxes(p.length, this.contractionIndices).map((i) => at(p, i));
      const contracted = new ArrayContraction(inner.expr, ...groups).doit();
      return new PermuteDims(contracted, desired.map((i) => actual.indexOf(i))).doit();
    }
    if (this.expr instanceof ArrayTensorProduct) {
      const inner = this.expr.doit();
      if (inner.key !== this.expr.key) return new ArrayContraction(inner, ...this.contractionIndices).doit();
      const taken = new Set(this.contractionIndices.flat()), blocks = factorBlocks(this.expr);
      const order = indices(blocks.length).sort((i, j) => {
        const a = at(blocks, i).every((k) => taken.has(k)), b = at(blocks, j).every((k) => taken.has(k));
        return a && b ? compareKeys(sortKey(at(this.expr.args, i)), sortKey(at(this.expr.args, j))) : Number(b) - Number(a);
      });
      return reorderContraction(this, order);
    }
    return this;
  }
  /**
   * Split a shared summation index into pairwise links through diagonal vectors.
   *
   * @returns The equivalent expression with separable multiple contractions split.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.split_multiple_contractions`
   */
  splitMultipleContractions(): Expr {
    if (!(this.expr instanceof ArrayTensorProduct)) return this;
    const factors = [...this.expr.args], blocks = factorBlocks(this.expr);
    const groups = this.contractionIndices.map((group) => [...group]);
    const occupied = new Set(groups.flat()), padding = new Set<number>();
    for (const group of [...groups]) {
      if (group.length < 3) continue;
      const endpoints: number[] = [], vectors: number[] = [];
      for (const axis of group) {
        const i = blocks.findIndex((block) => block.includes(axis));
        const block = at(blocks, i), mat = at(factors, i);
        const other = block.find((k) => k !== axis);
        if (mat instanceof MatrixExpr && other !== undefined && !occupied.has(other) &&
            at(this.expr.shape, other).equals(1)) vectors.push(axis);
        else endpoints.push(axis);
      }
      if (endpoints.length > 2) continue;
      const chain = [...endpoints.slice(0, 1), ...vectors, ...endpoints.slice(1)];
      groups.splice(groups.indexOf(group), 1);
      let previous = first(chain);
      for (const axis of chain.slice(1, -1)) {
        const i = blocks.findIndex((block) => block.includes(axis));
        factors[i] = diagonalizeVector(at(factors, i));
        padding.add(i);
        groups.push([previous, axis]);
        previous = at(at(blocks, i), 1 - at(blocks, i).indexOf(axis));
      }
      groups.push([previous, at(chain, chain.length - 1)]);
    }
    if (!padding.size) return this;
    const axes = blocks.flatMap((block, i) => padding.has(i) ? [...block, -1] : block);
    const product = new ArrayTensorProduct(...factors.flatMap((mat, i) => padding.has(i) ? [mat, new OneArray(1)] : [mat]));
    return new ArrayContraction(product, ...groups.map((group) => group.map((axis) => axes.indexOf(axis)))).doit();
  }
  /**
   * Sort arguments in the tensor product so that their order is lexicographical.
   *
   * @returns The equivalent contraction with tensor factors ordered by name.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayContraction.sort_args_by_name`
   */
  sortArgsByName(): Expr {
    if (!(this.expr instanceof ArrayTensorProduct)) return this;
    const order = indices(this.expr.args.length).sort((i, j) => compareKeys(sortKey(at(this.expr.args, i)), sortKey(at(this.expr.args, j))));
    return reorderContraction(this, order).doit();
  }
}

/** Axes of each tensor-product factor. @internal */
export function factorBlocks(expr: ArrayTensorProduct): number[][] {
  let offset = 0;
  return expr.args.map((a) => { const block = indices(getRank(a)).map((i) => i + offset); offset += block.length; return block; });
}
/** Reorder whole factor blocks and update every contracted axis. @internal */
export function reorderContraction(expr: ArrayContraction, order: readonly number[]): ArrayContraction {
  const product = cast(expr.expr, ArrayTensorProduct), blocks = factorBlocks(product);
  const permutation = order.flatMap((i) => at(blocks, i));
  return new ArrayContraction(new ArrayTensorProduct(...order.map((i) => at(product.args, i))), ...expr.contractionIndices.map((g) => g.map((i) => permutation.indexOf(i))));
}

/**
 * Coincident indices retained as new trailing diagonal axes.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayDiagonal`
 */
export class ArrayDiagonal extends ArrayExpr {
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayDiagonal.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Groups of axes restricted to a common index.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayDiagonal.diagonal_indices`
   */
  readonly diagonalIndices: readonly (readonly number[])[];
  /**
   * Constructs an instance of `ArrayDiagonal`.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param groups - Groups of axes constrained to have equal indices.
   */
  constructor(
    /**
     * The underlying expression on which this operation acts.
     *
     * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayDiagonal.expr`
     */
    readonly expr: Expr, ...groups: (readonly number[])[]) {
    const axes = validateGroups(expr, groups, true), shape = getShape(expr);
    super('ArrayDiagonal', [expr, ...axes.map(tuple)]);
    this.diagonalIndices = axes;
    this.shape = [...remainingAxes(shape.length, axes).map((i) => at(shape, i)), ...axes.map((g) => at(shape, first(g)))];
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArrayDiagonal(first(args), ...args.slice(1).map((g) => values(g).map(integer))); }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayDiagonal.as_explicit`
   */
  asExplicit(): Expr { return this.diagonalIndices.length ? tensordiagonal(explicitArray(this.expr), ...this.diagonalIndices) : explicitArray(this.expr); }
  /**
   * Combines a diagonal extraction with a nested diagonal or axis permutation.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayDiagonal.doit`
   */
  override doit(): Expr {
    if (!this.diagonalIndices.length) return this.expr;
    if (!(this.expr instanceof ArrayDiagonal || this.expr instanceof PermuteDims)) return this;
    const inner = this.expr, base = inner.expr;
    const coordinates = inner instanceof ArrayDiagonal
      ? [...remainingAxes(getRank(base), inner.diagonalIndices).map((i) => [i]), ...inner.diagonalIndices]
      : inner.permutation.arrayForm.map((i) => [i]);
    const desired = [...remainingAxes(coordinates.length, this.diagonalIndices).map((i) => [...at(coordinates, i)]), ...this.diagonalIndices.map((g) => g.flatMap((i) => [...at(coordinates, i)]))];
    const groups = desired.filter((g) => g.length > 1);
    const result = new ArrayDiagonal(base, ...groups);
    const actual = [...remainingAxes(getRank(base), result.diagonalIndices).map((i) => [i]), ...result.diagonalIndices];
    const permutation = desired.map((g) => actual.findIndex((h) => g.length === h.length && g.every((i) => h.includes(i))));
    return new PermuteDims(result.doit(), permutation).doit();
  }

}

/**
 * Array sum with matching shapes.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayAdd`
 */
export class ArrayAdd extends ArrayExpr {
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayAdd.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `ArrayAdd`.
   *
   * @param args - Operands in their defining order.
   * @throws RangeError when no summands are supplied or the arrays have different shapes.
   * @throws TypeError when a summand does not have a shape.
   */
  constructor(...args: Expr[]) {
    if (args.length === 0) throw new RangeError('ArrayAdd requires at least one argument');
    if (args.some((a) => !(a instanceof ArrayExpr || a instanceof MatrixExpr || a instanceof NDimArray))) throw new TypeError('ArrayAdd arguments require shapes');
    const shape = getShape(first(args));
    if (args.some((a) => !sameShape(shape, getShape(a)))) throw new RangeError('array shapes do not match');
    super('ArrayAdd', args);
    this.shape = shape;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArrayAdd(...args); }
  /**
   * Flattens nested sums and removes zero arrays.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayAdd.doit`
   */
  override doit(): Expr {
    const args = this.args.flatMap((arg) => {
      const value = arg instanceof ArrayAdd ? arg.doit() : arg;
      return value instanceof ArrayAdd ? value.args : [value];
    }).filter((arg) => !(arg instanceof ZeroArray));
    if (!args.length) return new ZeroArray(...this.shape);
    return args.length === 1 ? first(args) : new ArrayAdd(...args);
  }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayAdd.as_explicit`
   */
  asExplicit(): Expr {
    const arrays = this.args.map(explicitArray), firstArray = first(arrays);
    if (!(firstArray instanceof NDimArray)) return add(...arrays);
    const elements = arrays.map((a) => cast(a, NDimArray).flatElements());
    return new ImmutableDenseNDimArray(firstArray.flatElements().map((_, i) => add(...elements.map((a) => at(a, i)))), firstArray.shape);
  }
}

/**
 * Reorder axes: output axis i is input axis permutation[i].
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims`
 * @remarks SymPy prints the resulting shape as `(3, 1, 2, 5, 4)`.
 * @example
 * ```ts
 * import { ArraySymbol, PermuteDims } from '@symjs/symjs';
 *
 * const a = new ArraySymbol('M', [1, 2, 3, 4, 5]);
 * new PermuteDims(a, undefined, { indexOrderOld: 'ijklm', indexOrderNew: 'kijml' }).shape; // => [3, 1, 2, 5, 4]
 * ```
 */
export class PermuteDims extends ArrayExpr {
  /**
   * Permutation of the input axes.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims.permutation`
   */
  readonly permutation: Permutation;
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `PermuteDims`.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param permutation - Permutation of the input axes.
   * @param opts - `indexOrderOld` label the original axes; `indexOrderNew` specify the new axis order.
   * @throws RangeError when the axis permutation is invalid or only one index order is supplied or the two axis label sequences are incompatible.
   */
  constructor(
    /**
     * The underlying expression on which this operation acts.
     *
     * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims.expr`
     */
    readonly expr: Expr, permutation?: PermutationLike, opts: { indexOrderOld?: string; indexOrderNew?: string } = {}) {
    let perm = permutation;
    if (perm === undefined) {
      const old = opts.indexOrderOld, next = opts.indexOrderNew;
      if (old === undefined || next === undefined) throw new RangeError('provide both index orders');
      const oldLabels = Array.from(old), newLabels = Array.from(next);
      if (oldLabels.length !== newLabels.length || new Set(oldLabels).size !== oldLabels.length) throw new RangeError('provide matching index orders');
      perm = newLabels.map((label) => oldLabels.indexOf(label));
    }
    const p = 'arrayForm' in perm ? [...perm.arrayForm] : [...perm], shape = getShape(expr);
    if (p.length !== shape.length || new Set(p).size !== p.length || p.some((i) => !Number.isInteger(i) || i < 0 || i >= p.length)) throw new RangeError('invalid axis permutation');
    super('PermuteDims', [expr, tuple(p)]);
    this.permutation = new Permutation(p);
    this.shape = p.map((i) => at(shape, i));
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new PermuteDims(first(args), values(at(args, 1)).map(integer)); }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string { return `PermuteDims(${print(this.expr)}, ${String(this.permutation)})`; }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string { return `\\operatorname{PermuteDims}\\left(${print(this.expr)}, ${print(this.permutation)}\\right)`; }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims.as_explicit`
   */
  asExplicit(): Expr { return permutedims(explicitArray(this.expr), this.permutation); }
  /**
   * Distribute permutations over sums and normalize tensor-product axis blocks.
   *
   * @returns The equivalent expression with the axis permutation moved into its operand where possible.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims.nest_permutation`
   */
  nestPermutation(): Expr {
    return this.doit();
  }
  /**
   * Evaluate objects that are not evaluated by default like limits, integrals, sums and products.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.PermuteDims.doit`
   */
  override doit(): Expr {
    const p = this.permutation.arrayForm;
    if (this.expr instanceof ArrayAdd) return new ArrayAdd(...this.expr.args.map((arg) => new PermuteDims(arg, p).doit())).doit();
    if (this.expr instanceof ArrayDiagonal) {
      const inner = this.expr.doit();
      if (inner.key !== this.expr.key) return new PermuteDims(inner, p).doit();
    }
    if (p.every((v, i) => v === i)) return this.expr;
    if (this.expr instanceof PermuteDims) { const inner = this.expr; return new PermuteDims(inner.expr, p.map((i) => at(inner.permutation.arrayForm, i))).doit(); }
    // Whole blocks can be moved into the tensor product itself.
    const contraction = this.expr instanceof ArrayContraction ? this.expr : undefined;
    const product = contraction ? contraction.expr : this.expr;
    if (!(product instanceof ArrayTensorProduct)) return this;
    const remaining = contraction ? remainingAxes(getRank(product), contraction.contractionIndices) : indices(getRank(product));
    const requested = p.map((i) => at(remaining, i)), blocks = factorBlocks(product);
    const order = indices(blocks.length).sort((i, j) => {
      const position = (k: number): number => { const hits = at(blocks, k).map((axis) => requested.indexOf(axis)).filter((n) => n >= 0); return hits.length ? Math.min(...hits) : -1; };
      return position(i) - position(j);
    });
    const base = contraction ? reorderContraction(contraction, order) : new ArrayTensorProduct(...order.map((i) => at(product.args, i)));
    const output = order.flatMap((i) => at(blocks, i)).filter((i) => remaining.includes(i));
    const rest = requested.map((axis) => output.indexOf(axis));
    return rest.every((v, i) => v === i) ? base : new PermuteDims(base, rest);
  }
}

/**
 * Row-major reshaping, with an unchanged number of entries.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.Reshape`
 * @example
 * ```ts
 * import { ArraySymbol, Reshape } from '@symjs/symjs';
 *
 * const a = new ArraySymbol('A', [6]);
 * new Reshape(a, [3, 2]).asExplicit(); // => [[A[0], A[1]], [A[2], A[3]], [A[4], A[5]]]
 * ```
 */
export class Reshape extends ArrayExpr {
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.Reshape.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `Reshape`.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param shape - Axis lengths in dimension order.
   * @throws RangeError when the new dimensions would change the number of entries.
   */
  constructor(
    /**
     * The underlying expression on which this operation acts.
     *
     * @see SymPy `sympy.tensor.array.expressions.array_expressions.Reshape.expr`
     */
    readonly expr: Expr, shape: ArrayShape) {
    const dims = shape.map((s) => checkDim(sympify(s)));
    const difference = sub(mul(...dims), mul(...getShape(expr)));
    if (difference.isNumber && !difference.equals(0)) throw new RangeError('reshape must preserve the number of entries');
    super('Reshape', [expr, tuple(dims)]);
    this.shape = dims;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new Reshape(first(args), values(at(args, 1))); }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.Reshape.as_explicit`
   */
  asExplicit(): Expr { return cast(explicitArray(this.expr), NDimArray).reshape(...this.shape.map(integer)); }
  /**
   * Reshapes explicit array entries when the operand is available as an array.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.Reshape.doit`
   */
  override doit(): Expr { return this.expr instanceof NDimArray ? this.asExplicit() : this; }
}

/**
 * Constant zero array, including symbolic dimensions.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ZeroArray`
 */
export class ZeroArray extends ArrayExpr {
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ZeroArray.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `ZeroArray`.
   *
   * @param shape - Axis lengths in dimension order.
   */
  constructor(...shape: ExprLike[]) { const dims = shape.map((s) => checkDim(sympify(s))); super('ZeroArray', dims); this.shape = dims; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ZeroArray(...args); }
  /**
   * Selects the entry at the given indices.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The selected entry.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ZeroArray.__getitem__`
   */
  override at(...index: ExprLike[]): Expr { super.at(...index); return S.Zero; }
  /**
   * Evaluates a rank-zero array to the scalar zero.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ZeroArray.doit`
   */
  override doit(): Expr { return this.shape.length ? this : S.Zero; }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @throws NotImplementedError when the array is too large to materialize.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ZeroArray.as_explicit`
   */
  asExplicit(): Expr {
    const shape = this.shape.map(integer), size = shape.reduce((a, b) => a * b, 1);
    if (!Number.isSafeInteger(size)) throw new NotImplementedError('array is too large to materialize');
    return new ImmutableDenseNDimArray(Array.from({ length: size }, () => S.Zero), shape);
  }
}

/**
 * Constant array whose entries are one.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.OneArray`
 */
export class OneArray extends ArrayExpr {
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.OneArray.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `OneArray`.
   *
   * @param shape - Axis lengths in dimension order.
   */
  constructor(...shape: ExprLike[]) { const dims = shape.map((s) => checkDim(sympify(s))); super('OneArray', dims); this.shape = dims; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new OneArray(...args); }
  /**
   * Selects the entry at the given indices.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The selected entry.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.OneArray.__getitem__`
   */
  override at(...index: ExprLike[]): Expr { super.at(...index); return S.One; }
  /**
   * Evaluates a rank-zero array to the scalar one.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.OneArray.doit`
   */
  override doit(): Expr { return this.shape.length ? this : S.One; }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @throws NotImplementedError when the array is too large to materialize.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.OneArray.as_explicit`
   */
  asExplicit(): Expr {
    const shape = this.shape.map(integer), size = shape.reduce((a, b) => a * b, 1);
    if (!Number.isSafeInteger(size)) throw new NotImplementedError('array is too large to materialize');
    return new ImmutableDenseNDimArray(Array.from({ length: size }, () => S.One), shape);
  }
}

/**
 * Applies a scalar function independently to every entry of an array expression.
 *
 * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElementwiseApplyFunc`
 * @example
 * ```ts
 * import { ArrayElementwiseApplyFunc, SymArray } from '@symjs/symjs';
 *
 * const squares = new ArrayElementwiseApplyFunc(x => x.pow(2), SymArray([1, 2, 3]));
 * squares.asExplicit(); // => [1, 4, 9]
 * ```
 */
export class ArrayElementwiseApplyFunc extends ArrayExpr {
  /**
   * Function applied to each entry.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElementwiseApplyFunc.function`
   */
  readonly function: LambdaNode;
  /**
   * The lengths of the axes in order.
   *
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElementwiseApplyFunc.shape`
   */
  readonly shape: readonly Expr[];
  /**
   * Constructs an instance of `ArrayElementwiseApplyFunc`.
   *
   * @param func - Function applied to each entry.
   * @param expr - Symbolic expression on which to operate.
   * @throws RangeError when the elementwise function does not take exactly one argument.
   */
  constructor(func: LambdaNode | ((value: Expr) => Expr),
    /**
     * The underlying expression on which this operation acts.
     *
     * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElementwiseApplyFunc.expr`
     */
    readonly expr: Expr) {
    const variable = new Dummy('d');
    const lambda = func instanceof LambdaNode ? func : Lambda(variable, func(variable));
    if (lambda.variables.length !== 1) throw new RangeError('an elementwise function requires one argument');
    super('ArrayElementwiseApplyFunc', [lambda, expr]);
    this.function = lambda;
    this.shape = getShape(expr);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new ArrayElementwiseApplyFunc(cast(first(args), LambdaNode), at(args, 1)); }
  /**
   * Expands the array expression into its individual entries.
   *
   * @returns The scalar result or explicit array of entries.
   * @see SymPy `sympy.tensor.array.expressions.array_expressions.ArrayElementwiseApplyFunc.as_explicit`
   */
  asExplicit(): Expr {
    const expr = explicitArray(this.expr);
    return expr instanceof NDimArray ? expr.applyfunc((e) => this.function.call(e)) : this.function.call(expr);
  }
}
