// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/prufer.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.prufer: the Prufer correspondence between
 * labelled trees and Prufer sequences.
 */

import { at, defined } from '../core/guard';

/** An edge of a labelled tree: the labels of its two nodes. */
export type PruferEdge = readonly [number, number] | readonly number[];

const toBig = (n: number | bigint): bigint => BigInt(n);
/** Python a % n for a positive n (the result has the sign of n). */
const pmod = (a: bigint, n: bigint): bigint => ((a % n) + n) % n;

/** The message of SymPy's error for missing node labels. */
function missingMessage(missing: readonly number[]): string {
  const sorted = [...missing].sort((a, b) => a - b);
  return sorted.length === 1 ? `Node ${at(sorted, 0)} is missing.` : `Nodes [${sorted.join(', ')}] are missing.`;
}

/** The argument is a list of edges (not a Prufer sequence). */
const isEdgeList = (arg: readonly PruferEdge[] | readonly number[]): arg is readonly PruferEdge[] => arg[0] !== undefined && typeof arg[0] !== 'number';

/**
 * SymPy Prufer: a labelled tree with nodes 0 through n - 1, given by its
 * edges (`new Prufer([[0, 1], [0, 2], [0, 3]])`, optionally with the number
 * of nodes, which is then not checked) or by its Prufer sequence
 * (`new Prufer([1, 3])`, a tree with two more nodes than the sequence has
 * entries).
 */
export class Prufer {
  #prufer: number[] | undefined;
  #tree: number[][] | undefined;
  readonly #nodes: number;
  #rank: bigint | undefined;
  readonly #input: readonly (readonly number[])[] | readonly number[];
  readonly #nInput: number | undefined;

  constructor(arg: readonly PruferEdge[] | readonly number[], n?: number) {
    this.#input = arg;
    this.#nInput = n;
    if (isEdgeList(arg)) {
      const edges = arg.map((e) => [...e]);
      if (!at(edges, 0).length) throw new RangeError('Prufer expects at least one edge in the tree.');
      let nnodes: number;
      if (n !== undefined) nnodes = n;
      else {
        const nodes = new Set(edges.flat());
        nnodes = Math.max(...nodes) + 1;
        if (nnodes !== nodes.size) throw new RangeError(missingMessage([...Array(nnodes).keys()].filter((i) => !nodes.has(i))));
      }
      this.#tree = edges;
      this.#nodes = nnodes;
    } else {
      this.#prufer = [...arg];
      this.#nodes = this.#prufer.length + 2;
    }
  }

  /** SymPy prufer_repr: the Prufer sequence. */
  get pruferRepr(): number[] {
    this.#prufer ??= Prufer.toPrufer(defined(this.#tree).map((e) => [...e]), this.#nodes);
    return [...this.#prufer];
  }

  /** SymPy tree_repr: the tree as a list of edges. */
  get treeRepr(): number[][] {
    this.#tree ??= Prufer.toTree(defined(this.#prufer));
    return this.#tree.map((e) => [...e]);
  }

  /** SymPy nodes: the number of nodes of the tree. */
  get nodes(): number {
    return this.#nodes;
  }

  /** SymPy rank: the rank of the Prufer sequence. */
  get rank(): bigint {
    this.#rank ??= this.pruferRank();
    return this.#rank;
  }

  /** SymPy size: the number of trees with this number of nodes. */
  get size(): bigint {
    return this.prev(this.rank).prev().rank + 1n;
  }

  /** SymPy Prufer.to_prufer(tree, n): the Prufer sequence of a tree of n nodes given by its edges. */
  static toPrufer(treeIn: readonly PruferEdge[], n: number): number[] {
    const tree = treeIn.map((e) => [...e]);
    const d = new Map<number, number>();
    const deg = (k: number): number => d.get(k) ?? 0;
    for (const edge of tree) {
      d.set(at(edge, 0), deg(at(edge, 0)) + 1);
      d.set(at(edge, 1), deg(at(edge, 1)) + 1);
    }
    const L: number[] = [];
    for (let i = 0; i < n - 2; i++) {
      // the smallest leaf
      let x = 0;
      while (x < n - 1 && deg(x) !== 1) x++;
      // the node it is connected to
      const k = tree.findIndex((edge) => x === at(edge, 0) || x === at(edge, 1));
      const edge = at(tree, k);
      const y = x === at(edge, 0) ? at(edge, 1) : at(edge, 0);
      L.push(y);
      for (const j of [x, y]) {
        d.set(j, deg(j) - 1);
        if (!deg(j)) d.delete(j);
      }
      tree.splice(k, 1);
    }
    return L;
  }

  /** SymPy Prufer.to_tree(prufer): the edges of the tree of a Prufer sequence. */
  static toTree(prufer: readonly number[]): number[][] {
    const tree: number[][] = [];
    const n = prufer.length + 2;
    const d = new Map<number, number>();
    const deg = (k: number): number => d.get(k) ?? 1;
    for (const p of prufer) d.set(p, deg(p) + 1);
    for (const i of prufer) {
      // the smallest leaf (degree 1)
      let j = 0;
      while (j < n - 1 && deg(j) !== 1) j++;
      d.set(i, deg(i) - 1);
      d.set(j, deg(j) - 1);
      tree.push([i, j].sort((a, b) => a - b));
    }
    // two nodes of degree 1 always remain (SymPy's fallback [0, 1] is never taken)
    tree.push([...Array(n).keys()].filter((i) => deg(i) === 1));
    return tree;
  }

  /**
   * SymPy Prufer.edges(*runs): the unique edges of the paths given as runs
   * of node labels, relabelled so that the smallest node is 0, and the
   * number of nodes.
   */
  static edges(...runs: (readonly number[])[]): [number[][], number] {
    const e = new Map<string, [number, number]>();
    for (const r of runs) {
      for (let i = 0; i < r.length - 1; i++) {
        let a = at(r, i);
        let b = at(r, i + 1);
        if (b < a) [a, b] = [b, a];
        e.set(`${a},${b}`, [a, b]);
      }
    }
    if (!e.size) throw new RangeError('Prufer.edges: the runs have no edge');
    const got = new Set<number>();
    let nmin = Infinity;
    let nmax = -Infinity;
    for (const [a, b] of e.values()) {
      got.add(a).add(b);
      nmin = Math.min(a, nmin);
      nmax = Math.max(b, nmax);
    }
    const missing: number[] = [];
    for (let i = nmin; i <= nmax; i++) if (!got.has(i)) missing.push(i);
    // SymPy reports the missing labels shifted by the smallest label
    if (missing.length) throw new RangeError(missingMessage(missing.map((i) => i + nmin)));
    const rv = [...e.values()].map(([a, b]) => [a - nmin, b - nmin]);
    rv.sort((u, v) => at(u, 0) - at(v, 0) || at(u, 1) - at(v, 1));
    return [rv, nmax - nmin + 1];
  }

  /** SymPy prufer_rank(): the rank of the Prufer sequence. */
  pruferRank(): bigint {
    const seq = this.pruferRepr;
    let r = 0n;
    let p = 1n;
    for (let i = this.#nodes - 3; i >= 0; i--) {
      r += p * BigInt(at(seq, i));
      p *= BigInt(this.#nodes);
    }
    return r;
  }

  /** SymPy Prufer.unrank(rank, n): the Prufer sequence of a tree of n nodes with the given rank. */
  static unrank(rankIn: number | bigint, nIn: number | bigint): Prufer {
    const n = toBig(nIn);
    let rank = toBig(rankIn);
    const L = Array.from({ length: Math.max(Number(n) - 2, 0) }, () => 0);
    for (let i = Number(n) - 3; i >= 0; i--) {
      const v = pmod(rank, n);
      L[i] = Number(v);
      rank = (rank - v) / n;
    }
    return new Prufer(L);
  }

  /** SymPy next(delta=1): the tree whose rank is delta higher. */
  next(delta: number | bigint = 1): Prufer {
    return Prufer.unrank(this.rank + toBig(delta), this.#nodes);
  }

  /** SymPy prev(delta=1): the tree whose rank is delta lower. */
  prev(delta: number | bigint = 1): Prufer {
    return Prufer.unrank(this.rank - toBig(delta), this.#nodes);
  }

  /** SymPy str: Prufer([0, 0]), Prufer([[0, 1], [0, 2]], 3). */
  toString(): string {
    const items: readonly (number | readonly number[])[] = this.#input;
    const show = (v: number | readonly number[]): string => (typeof v === 'number' ? String(v) : `[${v.join(', ')}]`);
    const arg = items.length ? `[${items.map(show).join(', ')}]` : '()';
    return `Prufer(${arg}${this.#nInput === undefined ? '' : `, ${this.#nInput}`})`;
  }
}
