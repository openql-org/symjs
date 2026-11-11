// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/array_expressions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { Dummy, Expr, ExtensionExpr, Rational, S, Sym, type ExprLike } from '../../../core/nodes';
import { Lambda, LambdaNode } from '../../../core/lambda';
import { TupleNode } from '../../../core/containers';
import { at, cast, first } from '../../../core/guard';
import { add, mul, sub, sympify } from '../../../core/ops';
import { isNegative, isNonNegative } from '../../../core/assumptions';
import { NotImplementedError } from '../../../core/errors';
import { MatrixExpr, checkDim } from '../../../matrices/expressions/matexpr';
import { ImmutableDenseNDimArray, NDimArray } from '../../ndimarray';
import { tensorproduct, tensorcontraction, tensordiagonal, permutedims, type PermutationLike } from '../../arrayop';
import { Permutation } from '../../../combinatorics/permutations';
import { KroneckerDelta } from '../../../functions/special/hyper';
import { compareKeys, sortKey } from '../../../printing/sortkey';
import { sortContractionIndices } from './utils';

export type ArrayShape = readonly ExprLike[];
export type ArrayAxes = readonly (readonly number[])[];
const tuple = (items: readonly ExprLike[]): TupleNode => new TupleNode(items.map(sympify));
const values = (arg: Expr): readonly Expr[] => cast(arg, TupleNode).args;
const integer = (e: Expr): number => {
  if (!(e instanceof Rational) || !e.isInteger || e.p < 0n || e.p > BigInt(Number.MAX_SAFE_INTEGER)) throw new RangeError('a nonnegative, safely representable integer is required');
  return Number(e.p);
};
const indices = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const sameShape = (a: readonly Expr[], b: readonly Expr[]): boolean => a.length === b.length && a.every((s, i) => s.key === at(b, i).key);
const isExpressionShape = (value: unknown): value is readonly Expr[] => Array.isArray(value) && value.every((d: unknown) => d instanceof Expr);

/** The shape of an array expression, explicit array, matrix or scalar. */
export function getShape(expr: Expr): readonly Expr[] {
  if (expr instanceof ArrayExpr || expr instanceof MatrixExpr) return expr.shape;
  if (expr instanceof NDimArray) return expr.shape.map((n) => Rational.of(n));
  if ('shape' in expr && isExpressionShape(expr.shape)) return expr.shape;
  return [];
}
/** Number of axes (scalars have rank zero). */
export function getRank(expr: Expr): number { return getShape(expr).length; }

/** An array expression represented explicitly, preserving scalar results. @internal */
export function explicitArray(expr: Expr): Expr {
  if (expr instanceof ArrayExpr) return expr.asExplicit();
  if (expr instanceof MatrixExpr) return new ImmutableDenseNDimArray(expr.asExplicit());
  return expr;
}

/** Base of lazy N-dimensional array expressions. */
export abstract class ArrayExpr extends ExtensionExpr {
  abstract readonly shape: readonly Expr[];
  abstract asExplicit(): Expr;
  rank(): number { return this.shape.length; }
  at(...index: ExprLike[]): ArrayElement { return new ArrayElement(this, index); }
  doit(): Expr { return this; }
  override doitSelf(): Expr { return this.doit(); }
}

/** An array of symbolic entries with a specified shape. */
export class ArraySymbol extends ArrayExpr {
  readonly shape: readonly Expr[];
  readonly label: Sym;
  constructor(name: string | Sym, shape: ArrayShape) {
    const label = typeof name === 'string' ? new Sym(name) : name;
    const dims = shape.map((s) => checkDim(sympify(s)));
    super('ArraySymbol', [label, tuple(dims)]);
    this.shape = Object.freeze(dims);
    this.label = label;
  }
  withArgs(args: readonly Expr[]): Expr { return new ArraySymbol(cast(first(args), Sym), values(at(args, 1))); }
  override printStr(print: (e: Expr) => string): string { return print(this.label); }
  override printLatex(print: (e: Expr) => string): string { return print(this.label); }
  asExplicit(): ImmutableDenseNDimArray {
    if (!this.shape.length) throw new TypeError('a rank-zero ArraySymbol cannot be expanded');
    const shape = this.shape.map(integer);
    let coordinates: number[][] = [[]];
    for (const size of shape) coordinates = coordinates.flatMap((c) => indices(size).map((i) => [...c, i]));
    return new ImmutableDenseNDimArray(coordinates.map((c) => this.at(...c)), shape);
  }
}

/** A scalar entry of a symbolic array. */
export class ArrayElement extends ExtensionExpr {
  readonly indices: readonly Expr[];
  constructor(readonly parent: Expr, index: ArrayShape) {
    const ind = index.map(sympify), shape = getShape(parent);
    const shaped = parent instanceof ArrayExpr || parent instanceof MatrixExpr || parent instanceof NDimArray || shape.length > 0;
    if (shaped && ind.length !== shape.length) throw new RangeError('array index rank does not match the shape');
    ind.forEach((i, k) => {
      if (isNegative(i) === true || (shaped && isNonNegative(sub(i, at(shape, k))) === true)) throw new RangeError('array index out of bounds');
    });
    super('ArrayElement', [parent, tuple(ind)]);
    this.indices = Object.freeze(ind);
  }
  withArgs(args: readonly Expr[]): Expr { return new ArrayElement(first(args), values(at(args, 1))); }
  override printStr(print: (e: Expr) => string): string { return `${print(this.parent)}[${this.indices.map(print).join(', ')}]`; }
  override printLatex(print: (e: Expr) => string): string { return `{{${print(this.parent)}}_{${this.indices.map(print).join(', ')}}}`; }
  override diffSelf(x: Expr): Expr {
    if (x instanceof ArrayElement && x.parent.key === this.parent.key) return mul(...this.indices.map((i, k) => KroneckerDelta(i, at(x.indices, k))));
    return S.Zero;
  }
}

/** Unevaluated outer product; axis blocks follow argument order. */
export class ArrayTensorProduct extends ArrayExpr {
  get subranks(): number[] { return this.args.map(getRank); }
  readonly shape: readonly Expr[];
  constructor(...args: Expr[]) { super('ArrayTensorProduct', args); this.shape = Object.freeze(args.flatMap((a) => [...getShape(a)])); }
  withArgs(args: readonly Expr[]): Expr { return new ArrayTensorProduct(...args); }
  asExplicit(): Expr { return tensorproduct(...this.args.map(explicitArray)); }
  override doit(): Expr {
    const args = this.args.flatMap((a) => a instanceof ArrayTensorProduct ? a.args : [a]);
    if (args.length === 0) return S.One;
    if (args.length === 1) return first(args);
    // Lift contractions out of the product without changing its free axes.
    let offset = 0;
    const groups: number[][] = [];
    const factors = args.map((a) => {
      const base = a instanceof ArrayContraction ? a.expr : a;
      if (a instanceof ArrayContraction) groups.push(...a.contractionIndices.map((g) => g.map((i) => i + offset)));
      offset += getRank(base);
      return base;
    });
    return groups.length ? new ArrayContraction(new ArrayTensorProduct(...factors), ...groups).doit() : new ArrayTensorProduct(...args);
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

/** Sum over coincident indices; each group removes its axes. */
export class ArrayContraction extends ArrayExpr {
  get subranks(): number[] { return this.expr instanceof ArrayTensorProduct ? this.expr.subranks : [getRank(this.expr)]; }
  readonly shape: readonly Expr[];
  readonly contractionIndices: readonly (readonly number[])[];
  constructor(readonly expr: Expr, ...groups: (readonly number[])[]) {
    const axes = validateGroups(expr, groups, false);
    super('ArrayContraction', [expr, ...axes.map(tuple)]);
    this.contractionIndices = axes;
    this.shape = remainingAxes(getRank(expr), axes).map((i) => at(getShape(expr), i));
  }
  withArgs(args: readonly Expr[]): Expr { return new ArrayContraction(first(args), ...args.slice(1).map((g) => values(g).map(integer))); }
  asExplicit(): Expr { return this.contractionIndices.length ? tensorcontraction(explicitArray(this.expr), ...this.contractionIndices) : explicitArray(this.expr); }
  override doit(): Expr {
    if (!this.contractionIndices.length) return this.expr;
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
    if (this.expr instanceof ArrayTensorProduct) {
      const taken = new Set(this.contractionIndices.flat()), blocks = factorBlocks(this.expr);
      const order = indices(blocks.length).sort((i, j) => {
        const a = at(blocks, i).every((k) => taken.has(k)), b = at(blocks, j).every((k) => taken.has(k));
        return a && b ? compareKeys(sortKey(at(this.expr.args, i)), sortKey(at(this.expr.args, j))) : Number(b) - Number(a);
      });
      return reorderContraction(this, order);
    }
    return this;
  }
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

/** Coincident indices retained as new trailing diagonal axes. */
export class ArrayDiagonal extends ArrayExpr {
  readonly shape: readonly Expr[];
  readonly diagonalIndices: readonly (readonly number[])[];
  constructor(readonly expr: Expr, ...groups: (readonly number[])[]) {
    const axes = validateGroups(expr, groups, true), shape = getShape(expr);
    super('ArrayDiagonal', [expr, ...axes.map(tuple)]);
    this.diagonalIndices = axes;
    this.shape = [...remainingAxes(shape.length, axes).map((i) => at(shape, i)), ...axes.map((g) => at(shape, first(g)))];
  }
  withArgs(args: readonly Expr[]): Expr { return new ArrayDiagonal(first(args), ...args.slice(1).map((g) => values(g).map(integer))); }
  asExplicit(): Expr { return this.diagonalIndices.length ? tensordiagonal(explicitArray(this.expr), ...this.diagonalIndices) : explicitArray(this.expr); }
}

/** Array sum with matching shapes. */
export class ArrayAdd extends ArrayExpr {
  readonly shape: readonly Expr[];
  constructor(...args: Expr[]) {
    if (args.length === 0) throw new RangeError('ArrayAdd requires at least one argument');
    if (args.some((a) => !(a instanceof ArrayExpr || a instanceof MatrixExpr || a instanceof NDimArray))) throw new TypeError('ArrayAdd arguments require shapes');
    const shape = getShape(first(args));
    if (args.some((a) => !sameShape(shape, getShape(a)))) throw new RangeError('array shapes do not match');
    super('ArrayAdd', args);
    this.shape = shape;
  }
  withArgs(args: readonly Expr[]): Expr { return new ArrayAdd(...args); }
  asExplicit(): Expr {
    const arrays = this.args.map(explicitArray), firstArray = first(arrays);
    if (!(firstArray instanceof NDimArray)) return add(...arrays);
    const elements = arrays.map((a) => cast(a, NDimArray).flatElements());
    return new ImmutableDenseNDimArray(firstArray.flatElements().map((_, i) => add(...elements.map((a) => at(a, i)))), firstArray.shape);
  }
}

/** Reorder axes: output axis i is input axis permutation[i]. */
export class PermuteDims extends ArrayExpr {
  readonly permutation: Permutation;
  readonly shape: readonly Expr[];
  constructor(readonly expr: Expr, permutation?: PermutationLike, opts: { indexOrderOld?: string; indexOrderNew?: string } = {}) {
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
  withArgs(args: readonly Expr[]): Expr { return new PermuteDims(first(args), values(at(args, 1)).map(integer)); }
  override printStr(print: (e: Expr) => string): string { return `PermuteDims(${print(this.expr)}, ${String(this.permutation)})`; }
  override printLatex(print: (e: Expr) => string): string { return `\\operatorname{PermuteDims}\\left(${print(this.expr)}, ${print(this.permutation)}\\right)`; }
  asExplicit(): Expr { return permutedims(explicitArray(this.expr), this.permutation); }
  override doit(): Expr {
    const p = this.permutation.arrayForm;
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

/** Row-major reshaping, with an unchanged number of entries. */
export class Reshape extends ArrayExpr {
  readonly shape: readonly Expr[];
  constructor(readonly expr: Expr, shape: ArrayShape) {
    const dims = shape.map((s) => checkDim(sympify(s)));
    if (mul(...dims).key !== mul(...getShape(expr)).key) throw new RangeError('reshape must preserve the number of entries');
    super('Reshape', [expr, tuple(dims)]);
    this.shape = dims;
  }
  withArgs(args: readonly Expr[]): Expr { return new Reshape(first(args), values(at(args, 1))); }
  asExplicit(): Expr { return cast(explicitArray(this.expr), NDimArray).reshape(...this.shape.map(integer)); }
}

/** Constant zero array, including symbolic dimensions. */
export class ZeroArray extends ArrayExpr {
  readonly shape: readonly Expr[];
  constructor(...shape: ExprLike[]) { const dims = shape.map((s) => checkDim(sympify(s))); super('ZeroArray', dims); this.shape = dims; }
  withArgs(args: readonly Expr[]): Expr { return new ZeroArray(...args); }
  asExplicit(): Expr {
    const shape = this.shape.map(integer), size = shape.reduce((a, b) => a * b, 1);
    if (!Number.isSafeInteger(size)) throw new NotImplementedError('array is too large to materialize');
    return new ImmutableDenseNDimArray(Array.from({ length: size }, () => S.Zero), shape);
  }
}

/** Constant array whose entries are one. */
export class OneArray extends ArrayExpr {
  readonly shape: readonly Expr[];
  constructor(...shape: ExprLike[]) { const dims = shape.map((s) => checkDim(sympify(s))); super('OneArray', dims); this.shape = dims; }
  withArgs(args: readonly Expr[]): Expr { return new OneArray(...args); }
  asExplicit(): Expr {
    const shape = this.shape.map(integer), size = shape.reduce((a, b) => a * b, 1);
    if (!Number.isSafeInteger(size)) throw new NotImplementedError('array is too large to materialize');
    return new ImmutableDenseNDimArray(Array.from({ length: size }, () => S.One), shape);
  }
}

/** Apply a scalar function independently to each array entry. */
export class ArrayElementwiseApplyFunc extends ArrayExpr {
  readonly function: LambdaNode;
  readonly shape: readonly Expr[];
  constructor(func: LambdaNode | ((value: Expr) => Expr), readonly expr: Expr) {
    const variable = new Dummy('d');
    const lambda = func instanceof LambdaNode ? func : Lambda(variable, func(variable));
    if (lambda.variables.length !== 1) throw new RangeError('an elementwise function requires one argument');
    super('ArrayElementwiseApplyFunc', [lambda, expr]);
    this.function = lambda;
    this.shape = getShape(expr);
  }
  withArgs(args: readonly Expr[]): Expr { return new ArrayElementwiseApplyFunc(cast(first(args), LambdaNode), at(args, 1)); }
  asExplicit(): Expr {
    const expr = explicitArray(this.expr);
    return expr instanceof NDimArray ? expr.applyfunc((e) => this.function.call(e)) : this.function.call(expr);
  }
}
