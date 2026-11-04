// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/partitions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.partitions: set partitions (Partition),
 * integer partitions (IntegerPartition) and restricted growth strings.
 */

import { at, cast, first, getOrThrow, last } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr } from '../core/nodes';
import { sympify } from '../core/ops';
import { Matrix } from '../matrices/matrix';
import { parse } from '../parsing/parser';
import { compareKeys, sortKey } from '../printing/sortkey';
import { FiniteSet, SetExpr } from '../sets/sets';

/** An element of a set partition (a string is parsed, as SymPy sympifies it). */
export type PartitionElement = ExprLike | string;
/** A block of a set partition: a list, a JavaScript Set or a FiniteSet of its elements. */
export type PartitionBlock = readonly PartitionElement[] | ReadonlySet<PartitionElement> | SetExpr;

const cmpExpr = (a: Expr, b: Expr): number => compareKeys(sortKey(a), sortKey(b));
const sortExprs = (xs: readonly Expr[]): Expr[] => [...xs].sort(cmpExpr);
/** Python comparison of two lists of expressions (lexicographic, then by length). */
function cmpLists(a: readonly Expr[], b: readonly Expr[]): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = cmpExpr(at(a, i), at(b, i));
    if (c) return c;
  }
  return a.length - b.length;
}

/** Python a % n for a positive n. */
const pmod = (a: bigint, n: bigint): bigint => ((a % n) + n) % n;

const NOT_A_BLOCK = 'Each argument to Partition should be a list, set, or a FiniteSet';

/** The elements of a block (duplicates in a list are an error, as in SymPy). */
function blockElements(arg: PartitionBlock): { elems: Expr[]; dups: boolean } {
  if (arg instanceof SetExpr) {
    if (!(arg instanceof FiniteSet)) throw new RangeError(NOT_A_BLOCK);
    return { elems: [...arg.args], dups: false };
  }
  // strings are parsed, as SymPy's FiniteSet sympifies its elements
  const items = [...arg].map((v) => (typeof v === 'string' ? parse(v) : sympify(v)));
  // an empty list or set is the EmptySet in SymPy, which is not a FiniteSet
  if (!items.length) throw new RangeError(NOT_A_BLOCK);
  const keys = new Set(items.map((e) => e.key));
  return { elems: sortExprs([...new Map(items.map((e) => [e.key, e])).values()]), dups: keys.size < items.length };
}

/** The blocks of a partition as sets in SymPy's FiniteSet order, checked for duplicate elements. */
function partitionBlocks(partition: readonly PartitionBlock[]): FiniteSet[] {
  const blocks: Expr[][] = [];
  let dups = false;
  for (const arg of partition) {
    const b = blockElements(arg);
    dups ||= b.dups;
    blocks.push(b.elems);
  }
  const all = new Set<string>();
  for (const b of blocks) for (const e of b) all.add(e.key);
  if (dups || all.size < blocks.reduce((n, b) => n + b.length, 0)) throw new RangeError('Partition contained duplicate elements.');
  return blocks.map((b) => new FiniteSet(b)).sort(cmpExpr);
}

/**
 * SymPy Partition(*blocks): a partition of a set into disjoint blocks (each a
 * list, a JavaScript Set or a FiniteSet). As SymPy's Partition (a FiniteSet
 * of its blocks), it is an expression node: it prints like SymPy,
 * `Partition({3}, {1, 2})`, and its LaTeX and pretty forms are those of the
 * set of its blocks.
 */
export class Partition extends ExtensionExpr {
  /** The blocks as sets. */
  declare readonly args: readonly FiniteSet[];
  /** SymPy members: the elements of all blocks, in the order of their union. */
  readonly members: readonly Expr[];
  /** SymPy size: the number of elements. */
  readonly size: number;
  #rank: bigint | undefined;
  #partition: Expr[][] | undefined;

  constructor(...partition: PartitionBlock[]) {
    super('Partition', partitionBlocks(partition));
    const all = new Map<string, Expr>();
    for (const b of this.args) for (const e of b.args) all.set(e.key, e);
    this.members = sortExprs([...all.values()]);
    this.size = all.size;
  }

  /** A partition of the new blocks (SymPy Partition(*args)). */
  withArgs(args: readonly Expr[]): Expr {
    return new Partition(...args.map((a) => cast(a, FiniteSet)));
  }

  /** SymPy str: Partition({3}, {1, 2}) (the blocks in sort-key order). */
  override printStr(print: (e: Expr) => string): string {
    return `Partition(${this.args.map(print).join(', ')})`;
  }

  /** SymPy latex: the LaTeX form of the set of the blocks (SymPy _print_FiniteSet). */
  override printLatex(print: (e: Expr) => string): string {
    return print(new FiniteSet(this.args));
  }

  /** SymPy sort_key(): the size, the members and the rank. */
  compare(other: Partition): number {
    return this.size - other.size || cmpLists(this.members, other.members) || (this.rank < other.rank ? -1 : this.rank > other.rank ? 1 : 0);
  }

  /** SymPy partition: the blocks as a sorted list of sorted lists. */
  get partition(): Expr[][] {
    this.#partition ??= this.args.map((p) => sortExprs(p.args)).sort(cmpLists);
    return this.#partition.map((p) => [...p]);
  }

  /** SymPy a + k: the partition whose rank is k higher (modulo the number of partitions). */
  add(other: number | bigint): Partition {
    const offset = this.rank + BigInt(other);
    const result = RGSUnrank(pmod(offset, RGSEnum(this.size)), this.size);
    return Partition.fromRgs(result, this.members);
  }

  /** SymPy a - k: the partition whose rank is k lower. */
  sub(other: number | bigint): Partition {
    return this.add(-BigInt(other));
  }

  /** SymPy a <= b (by the sort key). */
  le(other: Partition): boolean {
    return this.compare(other) <= 0;
  }

  /** SymPy a < b (by the sort key). */
  lt(other: Partition): boolean {
    return this.compare(other) < 0;
  }

  /** SymPy rank: the rank of the restricted growth string. */
  get rank(): bigint {
    this.#rank ??= RGSRank(this.RGS);
    return this.#rank;
  }

  /** SymPy RGS: the restricted growth string (the block of each element, in sorted element order). */
  get RGS(): number[] {
    const rgs = new Map<string, number>();
    const partition = this.partition;
    partition.forEach((part, i) => {
      for (const j of part) rgs.set(j.key, i);
    });
    return sortExprs(partition.flat()).map((e) => getOrThrow(rgs, e.key));
  }

  /**
   * SymPy Partition.from_rgs(rgs, elements): the partition whose block of
   * elements[i] is rgs[i] (the elements are taken as given, not sorted).
   */
  static fromRgs(rgs: readonly (number | bigint)[], elements: readonly PartitionElement[]): Partition {
    if (rgs.length !== elements.length) throw new RangeError('mismatch in rgs and element lengths');
    const maxElem = Math.max(...rgs.map(Number)) + 1;
    const partition: PartitionElement[][] = Array.from({ length: maxElem }, () => []);
    rgs.forEach((i, j) => at(partition, Number(i)).push(at(elements, j)));
    if (!partition.every((p) => p.length)) throw new RangeError('some blocks of the partition were empty.');
    return new Partition(...partition);
  }
}

/** An integer partition given as a list of parts or as a map part -> multiplicity. */
export type IntegerPartitionInput = readonly (number | bigint)[] | ReadonlyMap<number | bigint, number | bigint>;

const asInt = (v: number | bigint): number => {
  const n = Number(v);
  if (!Number.isInteger(n)) throw new RangeError(`${String(v)} is not an integer`);
  return n;
};
const isPartsList = (v: IntegerPartitionInput): v is readonly (number | bigint)[] => Array.isArray(v);

/**
 * SymPy IntegerPartition(partition) or IntegerPartition(integer, partition):
 * a partition of a positive integer into positive parts, given as a list or
 * as a map part -> multiplicity; with the integer first, the parts must sum
 * to it.
 */
export class IntegerPartition {
  /** The parts in decreasing order. */
  readonly partition: readonly number[];
  /** The partitioned integer. */
  readonly integer: number;

  constructor(partition: IntegerPartitionInput);
  constructor(integer: number | bigint, partition: IntegerPartitionInput);
  constructor(a: IntegerPartitionInput | number | bigint, b?: IntegerPartitionInput) {
    let partitionIn: IntegerPartitionInput;
    let integer: number | undefined;
    if (typeof a === 'number' || typeof a === 'bigint') {
      if (b === undefined) throw new TypeError('IntegerPartition: the parts are missing');
      integer = asInt(a);
      partitionIn = b;
    } else partitionIn = a;
    let parts: number[];
    if (isPartsList(partitionIn)) parts = partitionIn.map(asInt).sort((x, y) => y - x);
    else {
      parts = [];
      const entries = [...partitionIn].map(([k, v]) => [asInt(k), asInt(v)] as const).sort((x, y) => y[0] - x[0]);
      for (const [k, v] of entries) for (let i = 0; i < v; i++) parts.push(k);
    }
    const sum = parts.reduce((s, p) => s + p, 0);
    if (integer !== undefined && sum !== integer) throw new RangeError(`Partition did not add to ${integer}`);
    if (parts.some((p) => p < 1)) throw new RangeError('All integer summands must be greater than one');
    this.partition = parts;
    this.integer = integer ?? sum;
  }

  /** SymPy prev_lex(): the previous partition of the integer in lexical order (wrapping to [1, ..., 1]). */
  prevLex(): IntegerPartition {
    const [d, keys] = this.#groups();
    const get = (k: number): number => d.get(k) ?? 0;
    if (keys.length === 1 && first(keys) === 1) return new IntegerPartition(new Map([[this.integer, 1]]));
    const kl = last(keys);
    if (kl !== 1) {
      d.set(kl, get(kl) - 1);
      if (kl === 2) d.set(1, 2);
      else {
        d.set(kl - 1, 1);
        d.set(1, 1);
      }
    } else {
      const k2 = at(keys, keys.length - 2);
      d.set(k2, get(k2) - 1);
      let left = get(1) + k2;
      let next = k2;
      d.set(1, 0);
      while (left) {
        next -= 1;
        if (left - next >= 0) {
          d.set(next, get(next) + Math.floor(left / next));
          left -= get(next) * next;
        }
      }
    }
    return new IntegerPartition(this.integer, d);
  }

  /** SymPy next_lex(): the next partition of the integer in lexical order (wrapping to [n]). */
  nextLex(): IntegerPartition {
    const [d, key] = this.#groups();
    const get = (k: number): number => d.get(k) ?? 0;
    const a = last(key);
    if (a === this.integer) {
      d.clear();
      d.set(1, this.integer);
    } else if (a === 1) {
      if (get(a) > 1) {
        d.set(a + 1, get(a + 1) + 1);
        d.set(a, get(a) - 2);
      } else {
        const b = at(key, key.length - 2);
        d.set(b + 1, get(b + 1) + 1);
        d.set(1, (get(b) - 1) * b);
        d.set(b, 0);
      }
    } else if (get(a) > 1) {
      if (key.length === 1) {
        d.clear();
        d.set(a + 1, 1);
        d.set(1, this.integer - a - 1);
      } else {
        const a1 = a + 1;
        d.set(a1, get(a1) + 1);
        d.set(1, get(a) * a - a1);
        d.set(a, 0);
      }
    } else {
      const b = at(key, key.length - 2);
      const b1 = b + 1;
      d.set(b1, get(b1) + 1);
      const need = get(b) * b + get(a) * a - b1;
      d.set(a, 0);
      d.set(b, 0);
      d.set(1, need);
    }
    return new IntegerPartition(this.integer, d);
  }

  /** SymPy as_dict(): the map part -> multiplicity (parts in decreasing order). */
  asDict(): Map<number, number> {
    return this.#groups()[0];
  }

  /** The multiplicities and the distinct parts in decreasing order (SymPy _dict and _keys). */
  #groups(): [Map<number, number>, number[]] {
    const d = new Map<number, number>();
    for (const p of this.partition) d.set(p, (d.get(p) ?? 0) + 1);
    return [d, [...d.keys()]];
  }

  /** SymPy conjugate: the conjugate partition (the transposed Ferrers diagram). */
  get conjugate(): number[] {
    let j = 1;
    const temp = [...this.partition, 0];
    let k = first(temp);
    const b = Array.from({ length: k }, () => 0);
    while (k > 0) {
      while (k > at(temp, j)) {
        b[k - 1] = j;
        k -= 1;
      }
      j += 1;
    }
    return b;
  }

  /** SymPy a < b: the parts from smallest to largest compare lexicographically less. */
  lt(other: IntegerPartition): boolean {
    return cmpNumberLists([...this.partition].reverse(), [...other.partition].reverse()) < 0;
  }

  /** SymPy a <= b. */
  le(other: IntegerPartition): boolean {
    return cmpNumberLists([...this.partition].reverse(), [...other.partition].reverse()) <= 0;
  }

  /** SymPy as_ferrers(char='#'): the Ferrers diagram. */
  asFerrers(char = '#'): string {
    return this.partition.map((i) => char.repeat(i)).join('\n');
  }

  /** SymPy repr: IntegerPartition(14, (5, 4, 3, 1, 1)). */
  repr(): string {
    const parts = this.partition.length === 1 ? `(${first(this.partition)},)` : `(${this.partition.join(', ')})`;
    return `IntegerPartition(${this.integer}, ${parts})`;
  }

  /** SymPy str: the list of parts, [5, 4, 3, 1, 1]. */
  toString(): string {
    return `[${this.partition.join(', ')}]`;
  }
}

function cmpNumberLists(a: readonly number[], b: readonly number[]): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) if (at(a, i) !== at(b, i)) return at(a, i) - at(b, i);
  return a.length - b.length;
}

/**
 * SymPy random_integer_partition(n, seed=None): a random partition of n as
 * a list of parts in decreasing order; a seed list gives the random values
 * to use, in order.
 */
export function randomIntegerPartition(nIn: number | bigint, seed?: readonly number[]): number[] {
  let n = asInt(nIn);
  if (n < 1) throw new RangeError('n must be a positive integer');
  const seq = seed === undefined ? undefined : [...seed].reverse();
  const randint = (a: number, b: number): number => {
    if (seq === undefined) return a + Math.floor(Math.random() * (b - a + 1));
    const x = seq.pop();
    if (x === undefined || x < a || x > b) throw new RangeError('_randint sequence was too short or out of range');
    return x;
  };
  const partition: [number, number][] = [];
  while (n > 0) {
    const k = randint(1, n);
    const mult = randint(1, Math.floor(n / k));
    partition.push([k, mult]);
    n -= k * mult;
  }
  partition.sort((x, y) => y[0] - x[0] || y[1] - x[1]);
  return partition.flatMap(([k, m]) => Array.from({ length: m }, () => k));
}

/** SymPy RGS_generalized(m): the (m + 1) x (m + 1) matrix of generalized unrestricted growth string counts. */
export function RGSGeneralized(m: number): Matrix {
  return Matrix.of(rgsTable(m).map((row) => row.map((v) => v)));
}

function rgsTable(m: number): bigint[][] {
  const d = Array.from({ length: m + 1 }, () => Array.from({ length: m + 1 }, () => 0n));
  for (let i = 0; i <= m; i++) at(d, 0)[i] = 1n;
  for (let i = 1; i <= m; i++) {
    for (let j = 0; j < m; j++) if (j <= m - i) at(d, i)[j] = BigInt(j) * at(at(d, i - 1), j) + at(at(d, i - 1), j + 1);
  }
  return d;
}

/** SymPy RGS_enum(m): the number of restricted growth strings of length m (the Bell number). */
export function RGSEnum(m: number): bigint {
  if (m < 1) return 0n;
  // Bell numbers by the Bell triangle
  let row = [1n];
  for (let i = 1; i < m; i++) {
    const next = [last(row)];
    for (const v of row) next.push(last(next) + v);
    row = next;
  }
  return last(row);
}

/** SymPy RGS_unrank(rank, m): the restricted growth string of length m with the given rank. */
export function RGSUnrank(rankIn: number | bigint, m: number): number[] {
  if (m < 1) throw new RangeError('The superset size must be >= 1');
  let rank = BigInt(rankIn);
  if (rank < 0n || RGSEnum(m) <= rank) throw new RangeError('Invalid arguments');
  const L = Array.from({ length: m + 1 }, () => 1);
  let j = 1;
  const D = rgsTable(m);
  for (let i = 2; i <= m; i++) {
    const v = at(at(D, m - i), j);
    const cr = BigInt(j) * v;
    if (cr <= rank) {
      L[i] = j + 1;
      rank -= cr;
      j += 1;
    } else {
      L[i] = Number(rank / v) + 1;
      rank %= v;
    }
  }
  return L.slice(1).map((x) => x - 1);
}

/** SymPy RGS_rank(rgs): the rank of a restricted growth string. */
export function RGSRank(rgs: readonly (number | bigint)[]): bigint {
  const r = rgs.map(Number);
  const size = r.length;
  let rank = 0n;
  const D = rgsTable(size);
  for (let i = 1; i < size; i++) {
    const n = size - i - 1;
    const m = Math.max(...r.slice(0, i));
    rank += at(at(D, n), m + 1) * BigInt(at(r, i));
  }
  return rank;
}
