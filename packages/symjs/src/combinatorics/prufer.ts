// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/prufer.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.prufer: the Prufer correspondence between
 * labelled trees and Prufer sequences.
 */

import { at, defined } from '../core/guard';
import type { Expr } from '../core/nodes';
import { ExtensionExpr } from '../core/nodes';

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

/**
 * SymPy's LaTeX of the array of a Prufer sequence or of the edges (_print_NDimArray with the
 * default settings): a 'matrix' environment in brackets ('array' when a row has more than 10
 * entries), a two-dimensional array of one row in extra brackets; an empty sequence is the
 * empty tuple.
 */
function arrayLatex(input: readonly (readonly number[])[] | readonly number[]): string {
  if (!input.length) return '\\left( \\right)';
  const rows = input.map((v) => (typeof v === 'number' ? [v] : [...v]));
  const twoDim = typeof input[0] !== 'number';
  const cols = twoDim ? at(rows, 0).length : rows.length;
  const block = (body: string, nRows: number): string =>
    cols <= 10 ? `\\left[\\begin{matrix}${body}\\end{matrix}\\right]` : `\\left[\\begin{array}{${'c'.repeat(nRows)}}${body}\\end{array}\\right]`;
  if (!twoDim) return block(rows.map((r) => at(r, 0)).join(' & '), rows.length);
  const m = block(rows.map((r) => r.join(' & ')).join('\\\\'), rows.length);
  return rows.length === 1 ? `\\left[${m}\\right]` : m;
}

/** The argument is a list of edges (not a Prufer sequence). */
const isEdgeList = (arg: readonly PruferEdge[] | readonly number[]): arg is readonly PruferEdge[] => arg[0] !== undefined && typeof arg[0] !== 'number';

/**
 * A labelled tree with nodes 0 through n - 1, given by its
 * edges (`new Prufer([[0, 1], [0, 2], [0, 3]])`, optionally with the number
 * of nodes, which is then not checked) or by its Prufer sequence
 * (`new Prufer([1, 3])`, a tree with two more nodes than the sequence has
 * entries).
 * @see SymPy `sympy.combinatorics.prufer.Prufer`
 * @example
 * ```ts
 * import { Prufer } from '@symjs/symjs';
 * new Prufer([0, 1]).rank; // => 1
 * ```
 */
export class Prufer extends ExtensionExpr {
  #prufer: number[] | undefined;
  #tree: number[][] | undefined;
  readonly #nodes: number;
  #rank: bigint | undefined;
  readonly #input: readonly (readonly number[])[] | readonly number[];
  readonly #nInput: number | undefined;

  /**
   * Constructs a `Prufer`.
   * @param arg - The edge list of a tree or its Prüfer sequence.
   * @param n - The number of labeled vertices.
   * @throws RangeError when the input contains no edges or node labels are missing from the tree.
   */
  constructor(arg: readonly PruferEdge[] | readonly number[], n?: number) {
    super('Prufer', []);
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

  /**
   * Gets the Prufer sequence.
   * @returns The Prufer sequence.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.prufer_repr`
   */
  get pruferRepr(): number[] {
    this.#prufer ??= Prufer.toPrufer(defined(this.#tree).map((e) => [...e]), this.#nodes);
    return [...this.#prufer];
  }

  /**
   * Gets the tree as a list of edges.
   * @returns The tree as a list of edges.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.tree_repr`
   */
  get treeRepr(): number[][] {
    this.#tree ??= Prufer.toTree(defined(this.#prufer));
    return this.#tree.map((e) => [...e]);
  }

  /**
   * Gets the number of nodes of the tree.
   * @returns The number of nodes of the tree.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.nodes`
   */
  get nodes(): number {
    return this.#nodes;
  }

  /**
   * Gets the rank of the Prufer sequence.
   * @returns The rank of the Prufer sequence.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.rank`
   */
  get rank(): bigint {
    this.#rank ??= this.pruferRank();
    return this.#rank;
  }

  /**
   * The number of trees with this number of nodes.
   * @returns The size of the object.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.size`
   */
  get size(): bigint {
    return this.prev(this.rank).prev().rank + 1n;
  }

  /**
   * Returns the Prufer sequence of a tree of n nodes given by its edges.
   * @param treeIn - The edges of the labeled tree.
   * @param n - The number of labeled vertices.
   * @returns The Prufer sequence of a tree of n nodes given by its edges.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.to_prufer`
   */
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

  /**
   * Returns the edges of the tree of a Prufer sequence.
   * @param prufer - The Prüfer sequence of node labels.
   * @returns The edges of the tree of a Prufer sequence.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.to_tree`
   * @example
   * ```ts
   * import { Prufer } from '@symjs/symjs';
   * Prufer.toTree([0, 0]); // => [[0, 1], [0, 2], [0, 3]]
   * ```
   */
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
   * The unique edges of the paths given as runs
   * of node labels, relabelled so that the smallest node is 0, and the
   * number of nodes.
   * @param runs - The sequences of adjacent vertex labels.
   * @returns The unique edges of the paths given as runs of node labels, relabelled so that the smallest node is 0, and the number of nodes.
   * @throws RangeError when the input contains no edges or node labels are missing from the tree.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.edges`
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

  /**
   * Returns the rank of the Prufer sequence.
   * @returns The rank of the Prufer sequence.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.prufer_rank`
   */
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

  /**
   * Returns the Prufer sequence of a tree of n nodes with the given rank.
   * @param rankIn - The zero-based position in the enumeration.
   * @param nIn - The number of labeled vertices.
   * @returns The Prufer sequence of a tree of n nodes with the given rank.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.unrank`
   */
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

  /**
   * Returns the tree whose rank is delta higher.
   * @param delta - The signed displacement in enumeration order.
   * @returns The tree whose rank is delta higher.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.next`
   */
  next(delta: number | bigint = 1): Prufer {
    return Prufer.unrank(this.rank + toBig(delta), this.#nodes);
  }

  /**
   * Returns the tree whose rank is delta lower.
   * @param delta - The signed displacement in enumeration order.
   * @returns The tree whose rank is delta lower.
   * @see SymPy `sympy.combinatorics.prufer.Prufer.prev`
   */
  prev(delta: number | bigint = 1): Prufer {
    return Prufer.unrank(this.rank - toBig(delta), this.#nodes);
  }

  /**
   * Rebuilds the expression with replacement operands.
   * @param _args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(_args: readonly Expr[]): Expr {
    return this;
  }

  protected override computeKey(): string {
    return this.printStr();
  }

  /**
   * Formats the expression as plain text.
   * @returns The plain-text representation.
   */
  override printStr(): string {
    const items: readonly (number | readonly number[])[] = this.#input;
    const show = (v: number | readonly number[]): string => (typeof v === 'number' ? String(v) : `[${v.join(', ')}]`);
    const arg = items.length ? `[${items.map(show).join(', ')}]` : '()';
    return `Prufer(${arg}${this.#nInput === undefined ? '' : `, ${this.#nInput}`})`;
  }

  /**
   * Formats the expression in LaTeX.
   * @returns The LaTeX representation.
   */
  override printLatex(): string {
    const n = this.#nInput === undefined ? '' : `, ${this.#nInput}`;
    return `\\operatorname{Prufer}\\left(${arrayLatex(this.#input)}${n}\\right)`;
  }
}
