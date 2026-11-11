// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/utils.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { at, first } from '../../../core/guard';
import { Expr, Rational } from '../../../core/nodes';
import { NoMatch, type NoMatchResult } from '../../../core/truth';
import type { PermutationLike } from '../../arrayop';

/** Flat axis -> (factor, local axis). @internal */
export function getMappingFromSubranks(subranks: readonly number[]): Map<number, readonly [number, number]> {
  const mapping = new Map<number, readonly [number, number]>();
  subranks.forEach((rank, i) => { for (let j = 0; j < rank; j++) mapping.set(mapping.size, [i, j]); });
  return mapping;
}

/** Pairwise contraction links, keyed by factor and local axis. @internal */
export function getContractionLinks<T>(args: readonly T[], subranks: readonly number[], ...groups: (readonly number[])[]): [readonly T[], Map<number, Map<number, readonly [number, number]>>] {
  const mapping = getMappingFromSubranks(subranks), links = new Map<number, Map<number, readonly [number, number]>>();
  for (const group of groups) {
    const positions = group.map((i) => {
      const p = mapping.get(i);
      if (p === undefined) throw new RangeError('contraction axis out of range');
      return p;
    });
    if (positions.length !== 2) continue;
    for (let i = 0; i < 2; i++) {
      const [arg, pos] = at(positions, i), neighbors = links.get(arg) ?? new Map<number, readonly [number, number]>();
      neighbors.set(pos, at(positions, 1 - i));
      links.set(arg, neighbors);
    }
  }
  return [args, links];
}

/** Canonical order of axes within groups, then of the groups. @internal */
export function sortContractionIndices(groups: readonly (readonly number[])[]): number[][] {
  return groups.map((g) => [...g].sort((a, b) => a - b)).sort((a, b) => first(a) - first(b));
}

/** Repeated symbolic indices form trailing diagonal axes; integers remain fixed. @internal */
export function getDiagonalIndices(indices: readonly Expr[]): [number[][], Expr[]] {
  const groups = new Map<string, number[]>();
  indices.forEach((index, i) => {
    if (index instanceof Rational && index.isInteger) return;
    const group = groups.get(index.key) ?? [];
    group.push(i);
    groups.set(index.key, group);
  });
  const repeated = [...groups.values()].filter((g) => g.length > 1), used = new Set(repeated.flat());
  return [repeated, [...indices.filter((_, i) => !used.has(i)), ...repeated.map((g) => at(indices, first(g)))]];
}

/** Locate an index, including indices collected into a set. @internal */
export function getArgindex<T>(subindices: readonly (T | ReadonlySet<T>)[], index: T): number {
  const equal = (a: unknown, b: unknown): boolean => a instanceof Expr && b instanceof Expr ? a.key === b.key : a === b;
  const position = subindices.findIndex((item) => equal(item, index) || (item instanceof Set && [...item].some((value) => equal(value, index))));
  if (position < 0) throw new RangeError('index not found');
  return position;
}

/** A nested list of axis values. @internal */
export type NestedIndices<T> = T | readonly NestedIndices<T>[];
const isList = <T>(value: NestedIndices<T>): value is readonly NestedIndices<T>[] => Array.isArray(value);
/** Apply a scalar transformation without changing nested group structure. @internal */
export function applyRecursivelyOverNestedLists<T, U>(func: (value: T) => U, values: NestedIndices<T>): NestedIndices<U> {
  return isList(values) ? values.map((value) => applyRecursivelyOverNestedLists(func, value)) : func(values);
}

/** Map original axes to surviving axes; a contracted axis has no image. @internal */
export function buildPushIndicesUpFuncTransformation(contracted: readonly number[]): (axis: number) => number | NoMatchResult {
  return (axis) => contracted.includes(axis) ? NoMatch : axis - contracted.filter((i) => i < axis).length;
}
/** Map surviving axes back to original axes. @internal */
export function buildPushIndicesDownFuncTransformation(contracted: readonly number[]): (axis: number) => number {
  const sorted = [...contracted].sort((a, b) => a - b);
  return (axis) => {
    let result = axis;
    for (const i of sorted) if (i <= result) result++;
    return result;
  };
}
/** Scatter indices: the output at perm[i] receives input i. @internal */
export function applyPermutationToList<T>(perm: PermutationLike, target: readonly T[]): T[] {
  const p = 'arrayForm' in perm ? perm.arrayForm : perm;
  if (p.length !== target.length || new Set(p).size !== p.length || p.some((i) => !Number.isInteger(i) || i < 0 || i >= p.length)) throw new RangeError('permutation and list must have matching sizes');
  return p.map((_, i) => at(target, p.indexOf(i)));
}
