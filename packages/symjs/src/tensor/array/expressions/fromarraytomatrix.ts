// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_array_to_matrix.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Mul, Pow, S, type Expr } from '../../../core/nodes';
import { at, getOrThrow, first } from '../../../core/guard';
import { HadamardPower, hadamardProduct } from '../../../matrices/expressions/hadamard';
import { DiagonalMatrixNode, DiagMatrixNode, diagonalizeVector } from '../../../matrices/expressions/diagonal';
import { mul } from '../../../core/ops';
import { ElementwiseApplyFunction, IdentityNode, OneMatrix, MatAdd, MatMulNode, MatrixElementNode, MatrixExpr, Trace, Transpose, ZeroMatrix } from '../../../matrices/expressions/matexpr';
import { ArrayExpr, ArraySymbol, ArrayAdd, ArrayContraction, ArrayDiagonal, ArrayElement, ArrayElementwiseApplyFunc, ArrayTensorProduct, PermuteDims, ZeroArray, OneArray, factorBlocks, getRank, remainingAxes } from './arrayexpressions';

type Factor = { value: Expr; axes: number[] };

/** Rebuild the contraction and diagonal groups from the labels on their factors. */
function assemble(factors: Factor[], free: number[]): Expr {
  const axes = factors.flatMap((factor) => factor.axes);
  const labels = [...new Set(axes)];
  const positions = (label: number) => axes.flatMap((v, i) => v === label ? [i] : []);
  const contracted = labels.filter((v) => !free.includes(v));
  let result = new ArrayTensorProduct(...factors.map((f) => f.value)).doit();
  if (contracted.length) result = new ArrayContraction(result, ...contracted.map(positions)).doit();
  const remaining = axes.filter((v) => free.includes(v));
  const repeated = labels.filter((v) => remaining.indexOf(v) !== remaining.lastIndexOf(v));
  if (repeated.length) result = new ArrayDiagonal(result, ...repeated.map((v) => remaining.flatMap((x, i) => x === v ? [i] : [])));
  const actual = [...remaining.filter((v) => !repeated.includes(v)), ...repeated];
  const permutation = free.map((v) => actual.indexOf(v));
  return permutation.every((v, i) => v === i) ? result : new PermuteDims(result, permutation);
}

function labeledFactors(product: ArrayTensorProduct, groups: readonly (readonly number[])[]): Factor[] {
  return factorBlocks(product).map((block, i) => ({
    value: at(product.args, i),
    axes: block.map((axis) => first(groups.find((g) => g.includes(axis)) ?? [axis])),
  }));
}

/** Eliminate identities inside a summation and split a repeated diagonal-matrix index. */
export function identifyRemovableIdentityMatrices(expr: ArrayContraction): Expr {
  if (!(expr.expr instanceof ArrayTensorProduct)) return expr;
  const factors = labeledFactors(expr.expr, expr.contractionIndices);
  const free = remainingAxes(getRank(expr.expr), expr.contractionIndices);
  let fresh = getRank(expr.expr), changed = false;
  for (const f of [...factors]) {
    if (f.axes.length !== 2) continue;
    const [a, b] = [first(f.axes), at(f.axes, 1)];
    if (f.value instanceof IdentityNode && free.includes(a) !== free.includes(b)) {
      const [summed, retained] = free.includes(a) ? [b, a] : [a, b];
      if (!factors.some((other) => other !== f && other.axes.includes(summed))) {
        f.value = new OneArray(f.value.rows);
        f.axes = [retained];
        changed = true;
      }
    }
    if (a !== b) continue;
    const others = factors.filter((g) => g !== f && g.axes.includes(a));
    if (f.value instanceof IdentityNode && others.length) {
      factors.splice(factors.indexOf(f), 1);
      changed = true;
    } else if ((f.value instanceof DiagonalMatrixNode || f.value instanceof DiagMatrixNode) && others.length === 2) {
      const last = at(others, 1);
      last.axes = last.axes.map((v) => v === a ? fresh : v);
      f.axes[1] = fresh++;
      changed = true;
    }
  }
  return changed ? assemble(factors, free) : expr;
}

/** Recognize shared matrix entries before tracing pairwise multiplication chains. */
function reduceGroups(expr: ArrayContraction | ArrayDiagonal): Expr {
  const diagonal = expr instanceof ArrayDiagonal;
  const inner = diagonal && expr.expr instanceof ArrayContraction ? expr.expr : undefined;
  const product = inner ? inner.expr : expr.expr;
  if (!(product instanceof ArrayTensorProduct)) return expr;
  const rank = getRank(product);
  const contractions = inner ? inner.contractionIndices : expr instanceof ArrayContraction ? expr.contractionIndices : [];
  const surviving = remainingAxes(rank, contractions);
  const diagonals = diagonal ? expr.diagonalIndices.map((g) => g.map((i) => at(surviving, i))) : [];
  const groups = [...contractions, ...diagonals];
  const free = [...remainingAxes(rank, groups), ...diagonals.map(first)];
  const factors = labeledFactors(product, groups);
  const others = (f: Factor) => factors.filter((other) => other !== f);
  for (const f of factors) {
    if (!(f.value instanceof MatrixExpr)) continue;
    const [a, b] = [first(f.axes), at(f.axes, 1)];
    const peers = others(f);
    const matching = peers.filter((g) => g.value instanceof MatrixExpr && g.axes.includes(a) && g.axes.includes(b) && (a !== b || g.axes.every((x) => x === a)));
    if ((a !== b || !free.includes(a)) && matching.length && groups.some((g) => g.length > 2) && groups.some((g) => g.includes(a)) && groups.some((g) => g.includes(b))) {
      const parallel = [f, ...matching];
      const rest = factors.filter((g) => !parallel.includes(g));
      const closed = ![a, b].some((x) => free.includes(x) || rest.some((g) => g.axes.includes(x)));
      const matrices = parallel.map((g) => first(g.axes) === a ? g.value : Transpose(g.value).doit());
      if (closed) {
        const hp = a === b ? hadamardProduct(...matrices.map((m) => Transpose(m).doit())) :
          new MatMulNode([hadamardProduct(...matrices.slice(1).map((m) => Transpose(m).doit())), first(matrices)]).doit();
        return assemble([{ value: Trace(hp).doit(), axes: [] }, ...rest], free);
      }
      f.value = hadamardProduct(...matrices);
      return assemble(factors.filter((g) => !matching.includes(g)), free);
    }
    if (f.value instanceof IdentityNode && a !== b && !free.includes(a) && !free.includes(b) && peers.some((g) => g.axes.includes(a) || g.axes.includes(b))) {
      return assemble(peers.map((g) => ({ value: g.value, axes: g.axes.map((x) => x === b ? a : x) })), free);
    }
    for (const [i, axis] of f.axes.entries()) {
      if (!diagonals.some((g) => first(g) === axis) || at(f.value.shape, i).equals(1) || !at(f.value.shape, 1 - i).equals(1)) continue;
      const partner = peers.find((g) => g.axes.includes(axis));
      if (!partner || factors.flatMap((g) => g.axes).filter((v) => v === axis).length !== 2) continue;
      const singleton = at(f.axes, 1 - i);
      const link = rank;
      partner.axes = partner.axes.map((v) => v === axis ? link : v);
      f.value = diagonalizeVector(f.value);
      f.axes = [link, axis];
      factors.push({ value: new OneArray(1), axes: [singleton] });
      return assemble(factors, free);
    }
  }
  for (const group of contractions.filter((g) => g.length === 2)) {
    const axis = first(group), pair = factors.filter((f) => f.axes.includes(axis));
    if (pair.length !== 2 || !pair.every((f) => f.value instanceof MatrixExpr)) continue;
    const [left, right] = [first(pair), at(pair, 1)];
    const i = left.axes.indexOf(axis), j = right.axes.indexOf(axis);
    left.value = new MatMulNode([i === 1 ? left.value : Transpose(left.value).doit(), j === 0 ? right.value : Transpose(right.value).doit()]).doit();
    left.axes = [at(left.axes, 1 - i), at(right.axes, 1 - j)];
    return assemble(factors.filter((f) => f !== right), free);
  }
  return expr;
}

/** Recognize matrix chains and traces in pairwise tensor contractions. */
function recognizeMatrix(expr: Expr): Expr {
  if (expr instanceof ZeroArray && expr.shape.length === 2) return ZeroMatrix(first(expr.shape), at(expr.shape, 1));
  if (expr instanceof ArrayElement) {
    const parent = recognizeMatrix(expr.parent);
    return parent instanceof MatrixExpr ? new MatrixElementNode(parent, first(expr.indices), at(expr.indices, 1)) : new ArrayElement(parent, expr.indices);
  }
  if (expr instanceof ArrayElementwiseApplyFunc) {
    const inner = recognizeMatrix(expr.expr);
    if (!(inner instanceof MatrixExpr)) return new ArrayElementwiseApplyFunc(expr.function, inner);
    if (inner.rows.key !== '1' || inner.cols.key !== '1') {
      const variable = first(expr.function.variables), body = expr.function.expr;
      const factors = body instanceof Mul ? body.args : [body];
      const dependent = factors.filter((factor) => factor.has(variable));
      let exponent: Expr | undefined;
      if (dependent.length === 0) exponent = S.Zero;
      else if (dependent.length === 1) {
        const power = first(dependent);
        if (power.key === variable.key) exponent = S.One;
        else if (power instanceof Pow && power.base.key === variable.key && !power.exp.has(variable)) exponent = power.exp;
      }
      if (exponent !== undefined) return new MatMulNode([mul(...factors.filter((factor) => !factor.has(variable))), HadamardPower(inner, exponent)]).doit();
    }
    return ElementwiseApplyFunction(expr.function, inner);
  }
  if (expr instanceof ArrayDiagonal || expr instanceof ArrayContraction && expr.contractionIndices.some((g) => g.length > 2)) {
    const reduced = reduceGroups(expr);
    if (reduced !== expr) return recognizeMatrix(reduced);
  }
  if (expr instanceof ArrayDiagonal && expr.expr instanceof ArrayTensorProduct && expr.diagonalIndices.length === 2 && expr.shape.length === 2) {
    const product = expr.expr, groups = expr.diagonalIndices;
    const blocks = factorBlocks(product);
    if (product.args.every((a) => a instanceof MatrixExpr) && blocks.every((block) => groups.every((g) => block.filter((axis) => g.includes(axis)).length === 1))) {
      return hadamardProduct(...product.args.map((arg, i) => at(groups, 0).includes(first(at(blocks, i))) ? arg : Transpose(arg).doit()));
    }
  }
  if (expr instanceof ArrayAdd) {
    const args = expr.args.map(recognizeMatrix);
    if (args.some((a) => a instanceof ArrayExpr && !(a instanceof ArraySymbol))) return new ArrayAdd(...args);
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    return MatAdd(...args).doit();
  }
  if (expr instanceof PermuteDims) {
    const inner = recognizeMatrix(expr.expr);
    if (inner instanceof MatrixExpr) return first(expr.permutation.arrayForm) === 0 ? inner : Transpose(inner).doit();
    if (inner instanceof ArrayTensorProduct) {
      const p = expr.permutation.arrayForm, axes: number[] = [];
      const blocks = factorBlocks(inner);
      const args = inner.args.map((arg, i) => {
        const block = at(blocks, i);
        if (arg instanceof MatrixExpr && p.indexOf(first(block)) > p.indexOf(at(block, 1))) {
          axes.push(...[...block].reverse());
          return Transpose(arg).doit();
        }
        axes.push(...block);
        return arg;
      });
      return new PermuteDims(new ArrayTensorProduct(...args), p.map((axis) => axes.indexOf(axis))).doit();
    }
    return new PermuteDims(inner, expr.permutation).doit();
  }
  if (expr instanceof ArrayTensorProduct) {
    return recognizeMatrixProduct(expr.args.map(recognizeMatrix));
  }
  if (!(expr instanceof ArrayContraction)) return expr;
  const normalized = expr.doit();
  if (!(normalized instanceof ArrayContraction)) return recognizeMatrix(normalized);
  const product = normalized.expr instanceof ArrayTensorProduct ? normalized.expr : new ArrayTensorProduct(normalized.expr);
  if (normalized.contractionIndices.some((g) => g.length > 2)) {
    const reduced = identifyRemovableIdentityMatrices(normalized);
    if (reduced !== normalized) return recognizeMatrix(reduced);
    const split = normalized.splitMultipleContractions();
    if (split !== normalized) return recognizeMatrix(split);
  }
  if (normalized.expr instanceof MatrixExpr && normalized.contractionIndices.every((g) => g.length === 1)) {
    const mat = normalized.expr;
    const axes = normalized.contractionIndices.flat();
    return new MatMulNode([...(axes.includes(0) ? [OneMatrix(1, mat.rows)] : []), mat, ...(axes.includes(1) ? [OneMatrix(mat.cols, 1)] : [])]).doit();
  }
  const hasTensorSum = product.args.some((factor) => factor instanceof ArrayAdd && getRank(factor) > 2);
  if (hasTensorSum) {
    let products: Expr[][] = [[]];
    for (const factor of product.args) {
      const terms = factor instanceof ArrayAdd ? factor.args : [factor];
      products = products.flatMap((prefix) => terms.map((term) => [...prefix, term]));
    }
    const terms = products.map((factors) => recognizeMatrix(new ArrayContraction(new ArrayTensorProduct(...factors).doit(), ...normalized.contractionIndices)));
    return recognizeMatrix(new ArrayAdd(...terms));
  }
  const args = product.args.map(recognizeMatrix);
  const blocks = factorBlocks(product), contracted = new Set(normalized.contractionIndices.flat());
  const supported = args.every((arg, i) => !getRank(arg) || arg instanceof MatrixExpr || arg instanceof OneArray && at(blocks, i).every((axis) => !contracted.has(axis)));
  if (!supported || normalized.contractionIndices.some((g) => g.length !== 2)) return normalized;
  const edges = new Map<number, number>();
  for (const g of normalized.contractionIndices) { edges.set(first(g), at(g, 1)); edges.set(at(g, 1), first(g)); }
  const owner = new Map<number, number>();
  blocks.forEach((block, i) => block.forEach((axis) => owner.set(axis, i)));
  const used = new Set<number>(), scalars = args.filter((a) => getRank(a) === 0);
  const remaining = remainingAxes(getRank(product), normalized.contractionIndices);
  const matrices: Expr[] = [], outputAxes: number[] = [];
  const walk = (start: number): { value: Expr; end: number } => {
    let axis = start, end = start;
    const chain: Expr[] = [];
    for (;;) {
      const i = getOrThrow(owner, axis);
      if (used.has(i)) break;
      used.add(i);
      const block = at(blocks, i), A = at(args, i), forward = axis === first(block);
      chain.push(forward ? A : Transpose(A).doit());
      end = forward ? at(block, 1) : first(block);
      const next = edges.get(end);
      if (next === undefined) break;
      axis = next;
    }
    return { value: new MatMulNode(chain).doit(), end };
  };
  for (const axis of remaining) {
    if (used.has(getOrThrow(owner, axis))) continue;
    const i = getOrThrow(owner, axis);
    if (at(args, i) instanceof OneArray) {
      used.add(i);
      matrices.push(at(args, i));
      outputAxes.push(...at(blocks, i));
      continue;
    }
    const result = walk(axis);
    matrices.push(result.value);
    outputAxes.push(axis, result.end);
  }
  for (const [i, arg] of args.entries()) if (arg instanceof MatrixExpr && !used.has(i)) scalars.push(Trace(walk(first(at(blocks, i))).value).doit());
  const scalar = mul(...scalars);
  if (matrices.length === 0) return scalar;
  if (!scalar.equals(1)) matrices.unshift(scalar);
  const result = recognizeMatrixProduct(matrices);
  const permutation = remaining.map((axis) => outputAxes.indexOf(axis));
  return permutation.every((axis, i) => axis === i) ? result : new PermuteDims(result, permutation);
}

function recognizeMatrixProduct(args: Expr[]): Expr {
  const scalars = args.filter((a) => getRank(a) === 0), arrays = args.filter((a) => getRank(a) > 0);
  if (!arrays.length) return mul(...scalars);
  if (scalars.length && first(arrays) instanceof MatrixExpr) arrays[0] = new MatMulNode([...scalars, first(arrays)]).doit();
  else arrays.unshift(...scalars);
  return new ArrayTensorProduct(...arrays).doit();
}

/** Remove singleton axes after all contractions and permutations have been recognized. */
function squeeze(expr: Expr): [Expr, number[]] {
  if (expr instanceof ArrayDiagonal) {
    const [inner, kept] = squeeze(recognizeMatrix(expr.expr));
    if (inner.key === expr.expr.key) return [expr, Array.from({ length: getRank(expr) }, (_, i) => i)];
    const groups = expr.diagonalIndices.map((g) => g.filter((axis) => kept.includes(axis)).map((axis) => kept.indexOf(axis)));
    const free = remainingAxes(getRank(expr.expr), expr.diagonalIndices);
    const labels = [...free.map((axis) => kept.indexOf(axis)), ...groups.map((g) => g[0] ?? -1)];
    const surviving = labels.flatMap((v, i) => v < 0 ? [] : [i]);
    const diagonals = groups.filter((g) => g.length > 1);
    const diagonal = new ArrayDiagonal(inner, ...diagonals);
    const base = diagonals.length ? diagonal : inner;
    const actual = [...remainingAxes(kept.length, diagonals), ...diagonal.diagonalIndices.map(first)];
    const order = surviving.map((i) => actual.indexOf(at(labels, i)));
    return [order.every((v, i) => v === i) ? base : recognizeMatrix(new PermuteDims(base, order)), surviving];
  }
  if (expr instanceof ArrayContraction && expr.expr instanceof ArrayTensorProduct) {
    const product = expr.expr, factors = labeledFactors(product, expr.contractionIndices);
    const free = remainingAxes(getRank(product), expr.contractionIndices);
    for (const g of expr.contractionIndices) {
      const label = first(g);
      const ends = factors.filter((f) => f.value instanceof IdentityNode && f.axes.includes(label) && f.axes.some((v) => free.includes(v)));
      if (ends.length < 2) continue;
      const dropped = ends.slice(1), removed = dropped.flatMap((f) => f.axes);
      const kept = free.filter((v) => !removed.includes(v));
      return [recognizeMatrix(assemble(factors.filter((f) => !dropped.includes(f)), kept)), kept.map((v) => free.indexOf(v))];
    }
  }
  if (expr instanceof PermuteDims) {
    const [inner, kept] = squeeze(expr.expr);
    const order = expr.permutation.arrayForm.filter((v) => kept.includes(v));
    const perm = order.map((v) => kept.indexOf(v));
    return [perm.every((v, i) => v === i) ? inner : recognizeMatrix(new PermuteDims(inner, perm)), order.map((v) => expr.permutation.arrayForm.indexOf(v))];
  }
  if (!(expr instanceof ArrayTensorProduct)) return [expr, Array.from({ length: getRank(expr) }, (_, i) => i)];
  const factors: Factor[] = [];
  const blocks = factorBlocks(expr);
  for (const [i, mat] of expr.args.entries()) {
    const block = at(blocks, i);
    if (mat instanceof OneArray && mat.shape.every((d) => d.equals(1)) || mat instanceof IdentityNode && mat.rows.equals(1)) continue;
    const prev = factors.at(-1);
    if (mat instanceof MatrixExpr && prev?.value instanceof MatrixExpr && mat.shape.some((d) => d.equals(1)) && prev.value.shape.some((d) => d.equals(1))) {
      const left = prev.value;
      if (mat.rows.equals(1) && mat.cols.equals(1)) {
        prev.value = new MatMulNode(left.cols.equals(1) ? [left, mat] : [mat, left]).doit();
      } else {
        prev.value = new MatMulNode([left.cols.equals(1) ? left : Transpose(left).doit(), mat.rows.equals(1) ? mat : Transpose(mat).doit()]).doit();
        prev.axes = [at(prev.axes, left.cols.equals(1) ? 0 : 1), at(block, mat.rows.equals(1) ? 1 : 0)];
      }
    } else factors.push({ value: mat, axes: block });
  }
  return [recognizeMatrixProduct(factors.map((f) => f.value)), factors.flatMap((f) => f.axes)];
}

export function convertArrayToMatrix(expr: Expr): Expr {
  return squeeze(recognizeMatrix(expr))[0];
}
