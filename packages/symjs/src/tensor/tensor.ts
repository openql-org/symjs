// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy 1.14 tensor/tensor.py, BSD-3-Clause; see LICENSE.
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, S, Sym, registerArithmetic } from '../core/nodes';
import { callableClass } from '../core/callable';
import { at, cast, first } from '../core/guard';
import { Tuple } from '../core/containers';
import { mul, sympify } from '../core/ops';
import { NotImplementedError } from '../core/errors';

export class TensorIndexTypeNode extends ExtensionExpr {
  constructor(name: string, readonly dim: Expr = new Sym('dim_' + name), readonly dummyName = name) {
    super('TensorIndexType', [new Sym(name), dim, new Sym(dummyName)]);
  }
  get typeName(): string { return cast(first(this.args), Sym).name; }
  get metric(): TensorHeadNode { return new TensorHeadNode('metric', [this, this], TensorSymmetry.fullySymmetric(2)); }
  withArgs(args: readonly Expr[]): Expr { return new TensorIndexTypeNode(cast(first(args), Sym).name, at(args, 1), cast(at(args, 2), Sym).name); }
  override printStr(): string { return this.typeName; }
}
export const TensorIndexType = /* @__PURE__ */ callableClass(TensorIndexTypeNode, (name: string, options: { dim?: ExprLike; dummyName?: string } = {}): TensorIndexTypeNode =>
  new TensorIndexTypeNode(name, options.dim === undefined ? undefined : sympify(options.dim), options.dummyName));
export type TensorIndexType = TensorIndexTypeNode;

export class TensorIndexNode extends ExtensionExpr {
  constructor(readonly indexName: string, readonly tensorIndexType: TensorIndexTypeNode, readonly isUp = true) {
    super('TensorIndex', [new Sym(indexName), tensorIndexType, isUp ? S.One : S.Zero]);
  }
  override neg(): TensorIndexNode { return new TensorIndexNode(this.indexName, this.tensorIndexType, !this.isUp); }
  withArgs(args: readonly Expr[]): Expr { return new TensorIndexNode(cast(first(args), Sym).name, cast(at(args, 1), TensorIndexTypeNode), at(args, 2).equals(1)); }
  override printStr(): string { return `${this.isUp ? '' : '-'}${this.indexName}`; }
  get labelKey(): string { return `${this.tensorIndexType.key}:${this.indexName}`; }
}
export const TensorIndex = /* @__PURE__ */ callableClass(TensorIndexNode, (name: string, type: TensorIndexTypeNode, isUp = true): TensorIndexNode => new TensorIndexNode(name, type, isUp));
export type TensorIndex = TensorIndexNode;
export function tensorIndices(names: string, type: TensorIndexTypeNode): TensorIndexNode[] {
  return names.split(/[\s,]+/).filter(Boolean).map((n) => new TensorIndexNode(n, type));
}

/** Slot symmetries: none, completely symmetric, or completely antisymmetric. */
export class TensorSymmetry extends ExtensionExpr {
  constructor(readonly rank: number, readonly sign: -1 | 0 | 1 = 0) {
    if (!Number.isInteger(rank) || rank < 0) throw new RangeError('Tensor rank must be a nonnegative integer');
    super('TensorSymmetry', [sympify(rank), sympify(sign)]);
  }
  static noSymmetry(rank: number): TensorSymmetry { return new TensorSymmetry(rank); }
  static fullySymmetric(rank: number): TensorSymmetry { return new TensorSymmetry(Math.abs(rank), rank < 0 ? -1 : 1); }
  withArgs(args: readonly Expr[]): Expr {
    const sign = at(args, 1).equals(-1) ? -1 : at(args, 1).equals(1) ? 1 : 0;
    return new TensorSymmetry(Number(first(args).toString()), sign);
  }
}

export class TensorHeadNode extends ExtensionExpr {
  constructor(readonly tensorName: string, readonly indexTypes: readonly TensorIndexTypeNode[], readonly symmetry = TensorSymmetry.noSymmetry(indexTypes.length)) {
    if (symmetry.rank !== indexTypes.length) throw new RangeError('Tensor rank and symmetry rank differ');
    if (symmetry.sign && indexTypes.some((t) => !t.equals(first(indexTypes)))) throw new TypeError('Symmetric slots must have the same index type');
    super('TensorHead', [new Sym(tensorName), Tuple(...indexTypes), symmetry]);
  }
  get rank(): number { return this.indexTypes.length; }
  at(...indices: TensorIndexNode[]): Tensor { return new Tensor(this, indices); }
  withArgs(args: readonly Expr[]): Expr { return new TensorHeadNode(cast(first(args), Sym).name, at(args, 1).args.map((t) => cast(t, TensorIndexTypeNode)), cast(at(args, 2), TensorSymmetry)); }
  override printStr(): string { return `${this.tensorName}(${this.indexTypes.map((t) => t.typeName).join(', ')})`; }
}
export const TensorHead = /* @__PURE__ */ callableClass(TensorHeadNode, (name: string, types: readonly TensorIndexTypeNode[], symmetry?: TensorSymmetry): TensorHeadNode => new TensorHeadNode(name, types, symmetry));
export type TensorHead = TensorHeadNode;
export function tensorHeads(names: string, types: readonly TensorIndexTypeNode[], symmetry?: TensorSymmetry): TensorHeadNode[] {
  return names.split(/[\s,]+/).filter(Boolean).map((n) => new TensorHeadNode(n, types, symmetry));
}

function occurrences(indices: readonly TensorIndexNode[]): Map<string, TensorIndexNode[]> {
  const labels = new Map<string, TensorIndexNode[]>();
  for (const i of indices) { const found = labels.get(i.labelKey) ?? []; found.push(i); labels.set(i.labelKey, found); }
  for (const group of labels.values()) {
    if (group.length > 2 || (group.length === 2 && first(group).isUp === at(group, 1).isUp)) throw new RangeError('Repeated tensor index must occur once up and once down');
  }
  return labels;
}

abstract class TensorExpression extends ExtensionExpr {
  abstract getIndices(): TensorIndexNode[];
  getFreeIndices(): TensorIndexNode[] { return [...occurrences(this.getIndices()).values()].filter((g) => g.length === 1).map(first); }
  override get isScalar(): boolean { return this.getFreeIndices().length === 0; }
  protected override computeCommutative(): boolean { return false; }
  canonBp(): Expr { return canonBp(this); }
  contractMetric(metric: TensorHeadNode): Expr { return contractMetric(this, metric); }
}
export class Tensor extends TensorExpression {
  constructor(readonly component: TensorHeadNode, readonly indices: readonly TensorIndexNode[]) {
    if (component.rank !== indices.length) throw new RangeError('Wrong number of tensor indices');
    if (indices.some((i, n) => !i.tensorIndexType.equals(at(component.indexTypes, n)))) throw new TypeError('Tensor index type mismatch');
    occurrences(indices);
    super('Tensor', [component, Tuple(...indices)]);
  }
  getIndices(): TensorIndexNode[] { return [...this.indices]; }
  withArgs(args: readonly Expr[]): Expr { return new Tensor(cast(first(args), TensorHeadNode), at(args, 1).args.map((i) => cast(i, TensorIndexNode))); }
  override printStr(print: (e: Expr) => string): string { return `${this.component.tensorName}(${this.indices.map(print).join(', ')})`; }
}
export class TensMul extends TensorExpression {
  constructor(readonly coefficient: Expr, readonly factors: readonly Tensor[]) {
    occurrences(factors.flatMap((f) => f.indices));
    super('TensMul', [coefficient, ...factors]);
  }
  getIndices(): TensorIndexNode[] { return this.factors.flatMap((f) => f.indices); }
  withArgs(args: readonly Expr[]): Expr { return tensorProduct(first(args), args.slice(1).map((f) => cast(f, Tensor))); }
  override printStr(print: (e: Expr) => string): string {
    return (this.coefficient.equals(1) ? '' : this.coefficient.equals(-1) ? '-' : `(${print(this.coefficient)})*`) + this.factors.map(print).join('*');
  }
}
function tensorProduct(coefficient: Expr, factors: readonly Tensor[]): Expr {
  if (coefficient.equals(0)) return S.Zero;
  if (!factors.length) return coefficient;
  if (coefficient.equals(1) && factors.length === 1) return first(factors);
  return new TensMul(coefficient, factors);
}

// Einstein multiplication. Bound indices of separate operands are renamed
// before combining them, so a product of traces does not become a fourfold sum.
registerArithmetic((op, args) => {
  if (!args.some((e) => e instanceof TensorExpression)) return undefined;
  if (op !== 'mul') throw new NotImplementedError('Abstract tensor arithmetic currently supports multiplication; sums and powers require a separate implementation');
  const used = new Set(args.flatMap((e) => e instanceof TensorExpression ? e.getIndices().map((i) => i.labelKey) : []));
  const factors: Tensor[] = [], scalars: Expr[] = [];
  let serial = 0;
  for (const arg of args) {
    if (!(arg instanceof TensorExpression)) { if (!arg.isCommutative) throw new TypeError('Tensor coefficients must commute'); scalars.push(arg); continue; }
    const groups = occurrences(arg.getIndices()), rename = new Map<string, string>();
    for (const [key, group] of groups) if (group.length === 2) {
      const i = first(group); let name: string;
      do { name = `${i.tensorIndexType.dummyName}_${serial++}`; } while (used.has(`${i.tensorIndexType.key}:${name}`));
      used.add(`${i.tensorIndexType.key}:${name}`); rename.set(key, name);
    }
    const fs = arg instanceof TensMul ? arg.factors : [cast(arg, Tensor)];
    if (arg instanceof TensMul) scalars.push(arg.coefficient);
    factors.push(...fs.map((f) => new Tensor(f.component, f.indices.map((i) => new TensorIndexNode(rename.get(i.labelKey) ?? i.indexName, i.tensorIndexType, i.isUp)))));
  }
  return tensorProduct(mul(...scalars), factors);
});

/**
 * Canonicalize fully symmetric/antisymmetric slots with free indices.
 * General dummy-index canonicalization (Butler–Portugal) is not implemented.
 */
export function canonBp(expression: Expr): Expr {
  if (!(expression instanceof TensorExpression)) return expression;
  const factors = expression instanceof TensMul ? expression.factors : [cast(expression, Tensor)];
  let coefficient = expression instanceof TensMul ? expression.coefficient : S.One;
  const result: Tensor[] = [];
  for (const f of factors) {
    const sign = f.component.symmetry.sign;
    if (sign === -1 && [...occurrences(f.indices).values()].some((g) => g.length === 2)) return S.Zero;
    if ([...occurrences(expression.getIndices()).values()].some((g) => g.length === 2)) throw new NotImplementedError('canonBp: general dummy-index canonicalization is not implemented');
    const indices = [...f.indices];
    if (sign) for (let i = 0; i < indices.length; i++) for (let j = i + 1; j < indices.length; j++) {
      if (at(indices, i).indexName > at(indices, j).indexName) { [indices[i], indices[j]] = [at(indices, j), at(indices, i)]; coefficient = mul(coefficient, sign); }
    }
    result.push(new Tensor(f.component, indices));
  }
  return tensorProduct(coefficient, result.sort((a, b) => a.key.localeCompare(b.key)));
}

/** Contract a symmetric metric with tensors, including metric traces. */
export function contractMetric(expression: Expr, metric: TensorHeadNode): Expr {
  if (metric.rank !== 2 || metric.symmetry.sign !== 1) throw new NotImplementedError('Only symmetric rank-two metrics are supported');
  if (!(expression instanceof TensorExpression)) return expression;
  let coefficient = expression instanceof TensMul ? expression.coefficient : S.One;
  const factors = expression instanceof TensMul ? [...expression.factors] : [cast(expression, Tensor)];
  for (let n = 0; n < factors.length; n++) {
    const f = at(factors, n);
    if (!f.component.equals(metric)) continue;
    const [i, j] = [at(f.indices, 0), at(f.indices, 1)];
    if (i.labelKey === j.labelKey) { coefficient = mul(coefficient, i.tensorIndexType.dim); factors.splice(n--, 1); continue; }
    for (let k = 0; k < factors.length; k++) {
      if (k === n) continue;
      const other = at(factors, k);
      const slot = other.indices.findIndex((v) => (v.labelKey === i.labelKey && v.isUp !== i.isUp) || (v.labelKey === j.labelKey && v.isUp !== j.isUp));
      if (slot >= 0) {
        const replacement = at(other.indices, slot).labelKey === i.labelKey ? j : i;
        factors[k] = new Tensor(other.component, other.indices.map((v, s) => s === slot ? replacement : v));
        factors.splice(n, 1); n = -1; break;
      }
    }
  }
  return tensorProduct(coefficient, factors);
}
