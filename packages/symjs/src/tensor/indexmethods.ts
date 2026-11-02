// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.tensor.index_methods: the free (outer) indices of an
 * expression of Indexed objects and its contraction structure (the
 * repeated indices summed over, Einstein convention).
 */

import { at, getOrThrow } from '../core/guard';
import type { Expr } from '../core/nodes';
import { Add, Fn, Mul, Piecewise, Pow, UndefFn } from '../core/nodes';
import { Indexed } from '../core/indexed';
import { some } from '../core/traverse';
import { IdxNode } from './idx';

/** The indices of the terms of a sum do not agree (SymPy IndexConformanceException). */
export class IndexConformanceException extends RangeError {
  override readonly name = 'IndexConformanceException';
}

/** A set of expressions in insertion order, keyed structurally. */
class ExprSet {
  private readonly m = new Map<string, Expr>();
  constructor(xs: Iterable<Expr> = []) {
    for (const x of xs) this.m.set(x.key, x);
  }
  add(x: Expr): void {
    this.m.set(x.key, x);
  }
  get size(): number {
    return this.m.size;
  }
  sameAs(o: ExprSet): boolean {
    return this.size === o.size && [...this.m.keys()].every((k) => o.m.has(k));
  }
  toSet(): Set<Expr> {
    return new Set(this.m.values());
  }
  values(): Expr[] {
    return [...this.m.values()];
  }
}

/** The indices that occur once, and those repeated (contracted), in order of first occurrence. */
function uniqueAndRepeated(inds: readonly Expr[]): [Expr[], Expr[]] {
  const count = new Map<string, [Expr, number]>();
  for (const i of inds) {
    const c = count.get(i.key);
    count.set(i.key, [i, (c?.[1] ?? 0) + 1]);
  }
  const u: Expr[] = [];
  const r: Expr[] = [];
  for (const [i, n] of count.values()) (n === 1 ? u : r).push(i);
  return [u, r];
}

const isFunction = (e: Expr): boolean => e instanceof Fn || e instanceof UndefFn;
const hasIndexed = (e: Expr): boolean => some(e, (x) => x instanceof Indexed);

function mulIndices(e: Expr): [ExprSet, Expr[]] {
  const all = e.args.flatMap((a) => indicesOf(a).values());
  const [u, r] = uniqueAndRepeated(all);
  return [new ExprSet(u), r];
}

function indicesOf(e: Expr): ExprSet {
  if (e instanceof Indexed) return new ExprSet(uniqueAndRepeated(e.indices)[0]);
  if (e instanceof IdxNode) return new ExprSet([e]);
  if (!e.args.length) return new ExprSet();
  if (e instanceof Mul) return mulIndices(e)[0];
  if (e instanceof Add) {
    const nonScalar = e.args.map(indicesOf).filter((s) => s.size > 0);
    if (!nonScalar.length) return new ExprSet();
    if (!nonScalar.every((s) => s.sameAs(at(nonScalar, 0)))) throw new IndexConformanceException(`Indices are not consistent: ${e.toString()}`);
    return at(nonScalar, 0);
  }
  if (e instanceof Pow) {
    const out = new ExprSet();
    for (const a of e.args) for (const i of indicesOf(a).values()) out.add(i);
    return out;
  }
  if (e instanceof Piecewise) return new ExprSet();
  if (isFunction(e)) {
    const out = new ExprSet();
    for (const a of e.args) for (const i of indicesOf(a).values()) out.add(i);
    return out;
  }
  if (!hasIndexed(e)) return new ExprSet();
  throw new TypeError(`get_indices: no handling of ${e.toString()}`);
}

/**
 * SymPy get_indices(expr): the set of outer indices of expr (repeated
 * indices are summed over and left out) and the symmetries (always empty,
 * as in SymPy); terms of a sum must have the same indices.
 */
export function getIndices(expr: Expr): [Set<Expr>, Map<Expr, Expr>] {
  return [indicesOf(expr).toSet(), new Map()];
}

/** A key of the contraction structure: the contracted indices, or null for none. */
export type ContractionKey = readonly Expr[] | null;
/** The contraction structure: key -> terms, and nested structures under the expressions that contain them. */
export type ContractionStructure = Map<ContractionKey | Expr, Set<Expr> | ContractionStructure[]>;

const isKeyList = (k: ContractionKey | Expr): k is readonly Expr[] => Array.isArray(k);

/** Keys compare by their indices. */
function keyOf(k: ContractionKey | Expr): string {
  if (k === null) return 'None';
  if (isKeyList(k)) return `(${k.map((i) => i.key).join(',')})`;
  return `expr:${k.key}`;
}

function isTrivial(d: ContractionStructure): boolean {
  return d.size === 1 && d.has(null);
}

function structure(e: Expr): ContractionStructure {
  if (e instanceof Indexed) {
    const r = uniqueAndRepeated(e.indices)[1];
    return new Map<ContractionKey | Expr, Set<Expr> | ContractionStructure[]>([[r.length ? r : null, new Set([e])]]);
  }
  if (!e.args.length) return new Map([[null, new Set([e])]]);
  if (e instanceof Mul) {
    const r = mulIndices(e)[1];
    const result: ContractionStructure = new Map([[r.length ? r : null, new Set([e])]]);
    const nested = e.args.map(structure).filter((d) => !isTrivial(d));
    if (nested.length) result.set(e, nested);
    return result;
  }
  if (e instanceof Pow) {
    const dicts = e.args.map(structure).filter((d) => !isTrivial(d));
    const result: ContractionStructure = new Map([[null, new Set([e])]]);
    if (dicts.length) result.set(e, dicts);
    return result;
  }
  if (e instanceof Add) {
    const result: ContractionStructure = new Map();
    const keys = new Map<string, ContractionKey | Expr>();
    for (const term of e.args) {
      for (const [k, v] of structure(term)) {
        const id = keyOf(k);
        const existing = keys.get(id);
        if (existing === undefined) {
          keys.set(id, k);
          result.set(k, v instanceof Set ? new Set(v) : [...v]);
        } else {
          const cur = getOrThrow(result, existing);
          if (cur instanceof Set && v instanceof Set) for (const x of v) cur.add(x);
          else if (Array.isArray(cur) && Array.isArray(v)) cur.push(...v);
        }
      }
    }
    return result;
  }
  if (e instanceof Piecewise) return new Map([[null, new Set([e])]]);
  if (isFunction(e)) {
    const deep = e.args.map(structure).filter((d) => !isTrivial(d));
    const d: ContractionStructure = new Map([[null, new Set([e])]]);
    if (deep.length) d.set(e, deep);
    return d;
  }
  if (!hasIndexed(e)) return new Map([[null, new Set([e])]]);
  throw new TypeError(`get_contraction_structure: no handling of ${e.toString()}`);
}

/**
 * SymPy get_contraction_structure(expr): the terms of expr grouped by the
 * indices they are summed over (null for none), with the structures of
 * nested factors and function arguments under the expressions containing
 * them.
 */
export function getContractionStructure(expr: Expr): ContractionStructure {
  return structure(expr);
}
