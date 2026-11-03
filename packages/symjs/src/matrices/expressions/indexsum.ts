// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy MatrixExpr.from_index_summation: sums over products of
 * matrix entries with contracted indices turned back into matrix
 * expressions (Sum(A[i, j]*B[j, k], (j, 0, N-1)) -> A*B).
 */

import { Concrete } from '../../core/concrete';
import { NotImplementedError } from '../../core/errors';
import type { ExprLike , Expr} from '../../core/nodes';
import { Add, Mul, S } from '../../core/nodes';
import { add, mul, sympify } from '../../core/ops';
import { compareKeys, sortKey } from '../../printing/sortkey';
import { MatAddNode, MatMulNode, MatrixElementNode, MatrixExpr, TraceNode, transposeOf } from './matexpr';
import { same } from './util';
import { at, cast, pair } from '../../core/guard';

interface Edge {
  readonly mat: MatrixExpr;
  readonly a: Expr;
  readonly b: Expr;
}

type Limit = [Expr, Expr, Expr];

function peel(e: Expr): [Expr, Limit[]] {
  const limits: Limit[] = [];
  let body = e;
  while (body instanceof Concrete && body.kind2 === 'Sum') {
    limits.push(...body.limits);
    body = body.function;
  }
  return [body, limits];
}

// every product has at least one matrix factor
const prod = (coeff: Expr, mats: readonly Expr[]): Expr => cast(MatMulNode.create([coeff, ...mats]), MatrixExpr).doit();

function convertProduct(body: Expr, limits: readonly Limit[], first?: Expr, last?: Expr): Expr {
  const summed = new Map(limits.map((l) => [l[0].key, l]));
  const factors = body instanceof Mul ? body.args : [body];
  const edges: Edge[] = [];
  const scalars: Expr[] = [];
  for (const f of factors) {
    if (f instanceof MatrixElementNode && f.parent instanceof MatrixExpr) edges.push({ mat: f.parent, a: f.i, b: f.j });
    else if (limits.some(([v]) => f.has(v))) throw new NotImplementedError(`from_index_summation: cannot convert ${String(f)}`);
    else scalars.push(f);
  }
  const coeff = mul(...scalars);
  const count = new Map<string, number>();
  for (const { a, b } of edges) for (const x of [a, b]) count.set(x.key, (count.get(x.key) ?? 0) + 1);
  // the summation limits must cover the dimension of every contracted index
  const checkRange = (idx: Expr, dim: Expr): void => {
    const l = summed.get(idx.key);
    if (l && (!same(l[1], S.Zero) || !same(l[2], add(dim, -1)))) throw new RangeError(`summation index and array dimension mismatch: ${String(idx)}`);
  };
  for (const { mat, a, b } of edges) {
    checkRange(a, mat.rows);
    checkRange(b, mat.cols);
  }
  const free: Expr[] = [];
  for (const { a, b } of edges) {
    for (const x of [a, b]) {
      if (summed.has(x.key)) continue;
      if (count.get(x.key) !== 1) throw new NotImplementedError('from_index_summation: an index appears twice without summation');
      free.push(x);
    }
  }
  const used = new Set<number>();
  const walk = (start: Expr, stop?: Expr): Expr[] => {
    const mats: Expr[] = [];
    let cur = start;
    for (;;) {
      const k = edges.findIndex((e, n) => !used.has(n) && (same(e.a, cur) || same(e.b, cur)));
      // the chain of indices ends before closing (SymPy raises IndexError)
      if (k < 0) throw new NotImplementedError('from_index_summation: unsupported index structure');
      used.add(k);
      const e = at(edges, k);
      if (same(e.a, cur)) {
        mats.push(e.mat);
        cur = e.b;
      } else {
        mats.push(transposeOf(e.mat));
        cur = e.a;
      }
      if (stop !== undefined && same(cur, stop)) break;
      if (stop === undefined && same(cur, start)) break;
    }
    return mats;
  };
  let matrix: Expr | undefined;
  if (free.length === 2) {
    const ordered = [...free].sort((x, y) => compareKeys(sortKey(x), sortKey(y)));
    const [o0, o1] = pair(ordered);
    let start = first ?? o0;
    let stop = start === o0 ? o1 : o0;
    if (first === undefined && last !== undefined) {
      stop = last;
      start = same(last, o0) ? o1 : o0;
    } else if (last !== undefined) stop = last;
    matrix = prod(S.One, walk(start, stop));
  } else if (free.length !== 0) throw new NotImplementedError('from_index_summation: unsupported index structure');
  let result: Expr = coeff;
  for (const [k, edge] of edges.entries()) {
    if (used.has(k)) continue;
    const mats = walk(edge.a);
    result = mul(result, new TraceNode(prod(S.One, mats)));
  }
  if (matrix === undefined) return result;
  return prod(result, [matrix]);
}

/**
 * SymPy MatrixExpr.from_index_summation(expr, first_index, last_index):
 * a matrix expression from a sum over products of entries, with
 * transposes and traces detected.
 */
export function fromIndexSummation(exprIn: ExprLike, firstIndex?: Expr, lastIndex?: Expr): Expr {
  const expr = sympify(exprIn);
  const [body, limits] = peel(expr);
  if (body instanceof Add) {
    const terms = body.args.map((t) => {
      const ls = limits.filter(([v]) => t.has(v));
      const r = convertProduct(t, ls, firstIndex, lastIndex);
      // a term free of a summation index is summed upper - lower + 1 times (SymPy drops the factor)
      const n = mul(...limits.filter(([v]) => !t.has(v)).map(([, lo, hi]) => add(hi, mul(-1, lo), 1)));
      return r instanceof MatrixExpr ? prod(n, [r]) : mul(n, r);
    });
    if (terms.every((t) => t instanceof MatrixExpr)) return MatAddNode.create(terms).doit();
    return add(...terms);
  }
  return convertProduct(body, limits, firstIndex, lastIndex);
}
