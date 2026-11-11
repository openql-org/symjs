// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/galois.py, BSD-3-Clause; see LICENSE.

/**
 * @file Transitive subgroups of the symmetric groups S1 through S6, useful in
 * Galois theory, and names for them. A name is a member of one of the
 * enumerations S1TransitiveSubgroups ... S6TransitiveSubgroups; its
 * getPermGroup method returns the group. The names follow Cohen, *A Course in
 * Computational Algebraic Number Theory*.
 */

import { at, defined } from '../core/guard';
import { Permutation, permutationRepr } from './permutations';
import { PermutationGroup } from './permgroups';
import type { PermutationGroupNode } from './permgroups';
import { AlternatingGroup, CyclicGroup, DihedralGroup, SymmetricGroup, setAlternatingGroupProperties, setSymmetricGroupProperties } from './namedgroups';

/**
 * A member of one of the S<n>TransitiveSubgroups enumerations (SymPy Enum
 * members): it has a name and a value, prints as `S4TransitiveSubgroups.V`,
 * and members are compared by identity.
 */
export abstract class TransitiveSubgroup {
  protected constructor(readonly name: string, readonly value: string) {}
  /** The n of S_n. */
  abstract get degree(): number;
  /** The transitive subgroup of S_n this name stands for. */
  abstract getPermGroup(): PermutationGroupNode;
  /** SymPy str: `S4TransitiveSubgroups.V`. */
  toString(): string { return `S${this.degree}TransitiveSubgroups.${this.name}`; }
  /** SymPy repr: `<S6TransitiveSubgroups.S4p: 'S4+'>`. */
  repr(): string { return `<${this.toString()}: '${this.value}'>`; }
}

/** Names for the transitive subgroups of S1. */
export class S1TransitiveSubgroups extends TransitiveSubgroup {
  static readonly S1 = new S1TransitiveSubgroups('S1', 'S1');
  private constructor(name: string, value: string) { super(name, value); }
  /** The members in definition order (iteration over SymPy's Enum). */
  static *[Symbol.iterator](): Generator<S1TransitiveSubgroups> { yield S1TransitiveSubgroups.S1; }
  get degree(): number { return 1; }
  getPermGroup(): PermutationGroupNode { return SymmetricGroup(1); }
}

/** Names for the transitive subgroups of S2. */
export class S2TransitiveSubgroups extends TransitiveSubgroup {
  static readonly S2 = new S2TransitiveSubgroups('S2', 'S2');
  private constructor(name: string, value: string) { super(name, value); }
  /** The members in definition order (iteration over SymPy's Enum). */
  static *[Symbol.iterator](): Generator<S2TransitiveSubgroups> { yield S2TransitiveSubgroups.S2; }
  get degree(): number { return 2; }
  getPermGroup(): PermutationGroupNode { return SymmetricGroup(2); }
}

/** Names for the transitive subgroups of S3. */
export class S3TransitiveSubgroups extends TransitiveSubgroup {
  static readonly A3 = new S3TransitiveSubgroups('A3', 'A3', () => AlternatingGroup(3));
  static readonly S3 = new S3TransitiveSubgroups('S3', 'S3', () => SymmetricGroup(3));
  private constructor(name: string, value: string, private readonly make: () => PermutationGroupNode) { super(name, value); }
  /** The members in definition order (iteration over SymPy's Enum). */
  static *[Symbol.iterator](): Generator<S3TransitiveSubgroups> { yield* [S3TransitiveSubgroups.A3, S3TransitiveSubgroups.S3]; }
  get degree(): number { return 3; }
  getPermGroup(): PermutationGroupNode { return this.make(); }
}

/** Names for the transitive subgroups of S4. */
export class S4TransitiveSubgroups extends TransitiveSubgroup {
  static readonly C4 = new S4TransitiveSubgroups('C4', 'C4', () => CyclicGroup(4));
  static readonly V = new S4TransitiveSubgroups('V', 'V', () => fourGroup());
  static readonly D4 = new S4TransitiveSubgroups('D4', 'D4', () => DihedralGroup(4));
  static readonly A4 = new S4TransitiveSubgroups('A4', 'A4', () => AlternatingGroup(4));
  static readonly S4 = new S4TransitiveSubgroups('S4', 'S4', () => SymmetricGroup(4));
  private constructor(name: string, value: string, private readonly make: () => PermutationGroupNode) { super(name, value); }
  /** The members in definition order (iteration over SymPy's Enum). */
  static *[Symbol.iterator](): Generator<S4TransitiveSubgroups> {
    const G = S4TransitiveSubgroups;
    yield* [G.C4, G.V, G.D4, G.A4, G.S4];
  }
  get degree(): number { return 4; }
  getPermGroup(): PermutationGroupNode { return this.make(); }
}

/** Names for the transitive subgroups of S5. */
export class S5TransitiveSubgroups extends TransitiveSubgroup {
  static readonly C5 = new S5TransitiveSubgroups('C5', 'C5', () => CyclicGroup(5));
  static readonly D5 = new S5TransitiveSubgroups('D5', 'D5', () => DihedralGroup(5));
  static readonly M20 = new S5TransitiveSubgroups('M20', 'M20', () => M20());
  static readonly A5 = new S5TransitiveSubgroups('A5', 'A5', () => AlternatingGroup(5));
  static readonly S5 = new S5TransitiveSubgroups('S5', 'S5', () => SymmetricGroup(5));
  private constructor(name: string, value: string, private readonly make: () => PermutationGroupNode) { super(name, value); }
  /** The members in definition order (iteration over SymPy's Enum). */
  static *[Symbol.iterator](): Generator<S5TransitiveSubgroups> {
    const G = S5TransitiveSubgroups;
    yield* [G.C5, G.D5, G.M20, G.A5, G.S5];
  }
  get degree(): number { return 5; }
  getPermGroup(): PermutationGroupNode { return this.make(); }
}

/** Names for the transitive subgroups of S6. */
export class S6TransitiveSubgroups extends TransitiveSubgroup {
  static readonly C6 = new S6TransitiveSubgroups('C6', 'C6', () => CyclicGroup(6));
  static readonly S3 = new S6TransitiveSubgroups('S3', 'S3', () => S3InS6());
  static readonly D6 = new S6TransitiveSubgroups('D6', 'D6', () => DihedralGroup(6));
  static readonly A4 = new S6TransitiveSubgroups('A4', 'A4', () => A4InS6());
  static readonly G18 = new S6TransitiveSubgroups('G18', 'G18', () => G18());
  static readonly A4xC2 = new S6TransitiveSubgroups('A4xC2', 'A4 x C2', () => A4xC2());
  static readonly S4m = new S6TransitiveSubgroups('S4m', 'S4-', () => S4m());
  static readonly S4p = new S6TransitiveSubgroups('S4p', 'S4+', () => S4p());
  static readonly G36m = new S6TransitiveSubgroups('G36m', 'G36-', () => G36m());
  static readonly G36p = new S6TransitiveSubgroups('G36p', 'G36+', () => G36p());
  static readonly S4xC2 = new S6TransitiveSubgroups('S4xC2', 'S4 x C2', () => S4xC2());
  static readonly PSL2F5 = new S6TransitiveSubgroups('PSL2F5', 'PSL2(F5)', () => PSL2F5());
  static readonly G72 = new S6TransitiveSubgroups('G72', 'G72', () => G72());
  static readonly PGL2F5 = new S6TransitiveSubgroups('PGL2F5', 'PGL2(F5)', () => PGL2F5());
  static readonly A6 = new S6TransitiveSubgroups('A6', 'A6', () => AlternatingGroup(6));
  static readonly S6 = new S6TransitiveSubgroups('S6', 'S6', () => SymmetricGroup(6));
  private constructor(name: string, value: string, private readonly make: () => PermutationGroupNode) { super(name, value); }
  /** The members in definition order (iteration over SymPy's Enum). */
  static *[Symbol.iterator](): Generator<S6TransitiveSubgroups> {
    const G = S6TransitiveSubgroups;
    yield* [G.C6, G.S3, G.D6, G.A4, G.G18, G.A4xC2, G.S4m, G.S4p, G.G36m, G.G36p, G.S4xC2, G.PSL2F5, G.G72, G.PGL2F5, G.A6, G.S6];
  }
  get degree(): number { return 6; }
  getPermGroup(): PermutationGroupNode { return this.make(); }
}

/** SymPy Permutation(*cycles[0])(*cycles[1])...: the product of the cycles. */
function cycles(...cs: (readonly number[])[]): Permutation {
  const [first = [], ...rest] = cs;
  return rest.reduce((p, c) => p.call(...c), new Permutation(...first));
}

/** The Klein four-group as a transitive subgroup of S4. */
export function fourGroup(): PermutationGroupNode {
  return PermutationGroup(cycles([0, 1], [2, 3]), cycles([0, 2], [1, 3]));
}

/** The metacyclic group M20, a transitive subgroup of S5 (Cohen, p. 323). */
export function M20(): PermutationGroupNode {
  const G = PermutationGroup(cycles([0, 1, 2, 3, 4]), cycles([1, 2, 4, 3]));
  G.degreeValue = 5;
  Object.assign(G.known, { order: 20n, isTransitive: true, isSym: false, isAlt: false, isCyclic: false, isDihedral: false });
  return G;
}

/** S3 as a transitive subgroup of S6: the symmetries of a triangular prism. */
export function S3InS6(): PermutationGroupNode {
  const G = PermutationGroup(cycles([0, 1, 2], [3, 4, 5]), cycles([0, 3], [2, 4], [1, 5]));
  setSymmetricGroupProperties(G, 3, 6);
  return G;
}

/** A4 as a transitive subgroup of S6. */
export function A4InS6(): PermutationGroupNode {
  const G = PermutationGroup(cycles([0, 4, 5], [1, 3, 2]), cycles([0, 1, 2], [3, 5, 4]));
  setAlternatingGroupProperties(G, 4, 6);
  return G;
}

/** The S4- transitive subgroup of S6 (S4 not contained in A6). */
export function S4m(): PermutationGroupNode {
  const G = PermutationGroup(cycles([1, 4, 5, 3]), cycles([0, 4], [1, 5], [2, 3]));
  setSymmetricGroupProperties(G, 4, 6);
  return G;
}

/** The S4+ transitive subgroup of S6 (S4 contained in A6). */
export function S4p(): PermutationGroupNode {
  const G = PermutationGroup(cycles([0, 2, 4, 1], [3, 5]), cycles([0, 3], [4, 5]));
  setSymmetricGroupProperties(G, 4, 6);
  return G;
}

/** The (A4 x C2) transitive subgroup of S6. */
export function A4xC2(): PermutationGroupNode {
  return PermutationGroup(cycles([0, 4, 5], [1, 3, 2]), cycles([0, 1, 2], [3, 5, 4]), cycles([5], [2, 4]));
}

/** The (S4 x C2) transitive subgroup of S6. */
export function S4xC2(): PermutationGroupNode {
  return PermutationGroup(cycles([1, 4, 5, 3]), cycles([0, 4], [1, 5], [2, 3]), cycles([1, 4], [3, 5]));
}

/** G18, the transitive subgroup of S6 isomorphic to C3^2 ⋊ C2. */
export function G18(): PermutationGroupNode {
  return PermutationGroup(cycles([5], [0, 1, 2]), cycles([3, 4, 5]), cycles([0, 4], [1, 5], [2, 3]));
}

/** G36-, the transitive subgroup of S6 isomorphic to C3^2 ⋊ C2^2. */
export function G36m(): PermutationGroupNode {
  return PermutationGroup(cycles([5], [0, 1, 2]), cycles([3, 4, 5]), cycles([1, 2], [3, 5]), cycles([0, 4], [1, 5], [2, 3]));
}

/** G36+, the transitive subgroup of S6 isomorphic to C3^2 ⋊ C4. */
export function G36p(): PermutationGroupNode {
  return PermutationGroup(cycles([5], [0, 1, 2]), cycles([3, 4, 5]), cycles([0, 5, 2, 3], [1, 4]));
}

/** G72, the transitive subgroup of S6 isomorphic to C3^2 ⋊ D4 (Cohen, p. 325). */
export function G72(): PermutationGroupNode {
  return PermutationGroup(cycles([5], [0, 1, 2]), cycles([0, 4, 1, 3], [2, 5]), cycles([0, 3], [1, 4], [2, 5]));
}

/** PSL2(F5) as a transitive subgroup of S6, isomorphic to A5. */
export function PSL2F5(): PermutationGroupNode {
  const G = PermutationGroup(cycles([0, 4, 5], [1, 3, 2]), cycles([0, 4, 3, 1, 5]));
  setAlternatingGroupProperties(G, 5, 6);
  return G;
}

/** PGL2(F5) as a transitive subgroup of S6, isomorphic to S5 (Cohen, p. 325). */
export function PGL2F5(): PermutationGroupNode {
  const G = PermutationGroup(cycles([0, 1, 2, 3, 4]), cycles([0, 5], [1, 2], [3, 4]));
  setSymmetricGroupProperties(G, 5, 6);
  return G;
}

/** Options of findTransitiveSubgroupsOfS6. */
export interface FindTransitiveSubgroupsOptions {
  /** Receives a report of the generators found for each group (SymPy print_report). */
  printReport?: (text: string) => void;
}

/**
 * Search S6 for generators of transitive instances of the named subgroups
 * (A4, S4-, S4+, A4 x C2, S4 x C2, G18, G36-, G36+, G72, PSL2(F5), PGL2(F5)
 * and the evident C6, S3, D6, A6, S6). The dedicated functions of this module
 * return generators found by this search. Returns a Map from each requested
 * name to the group found.
 */
export function findTransitiveSubgroupsOfS6(...input: (S6TransitiveSubgroups | FindTransitiveSubgroupsOptions)[]): Map<S6TransitiveSubgroups, PermutationGroupNode> {
  const targets = input.filter((t) => t instanceof S6TransitiveSubgroups);
  const report = input.find((t): t is FindTransitiveSubgroupsOptions => !(t instanceof S6TransitiveSubgroups))?.printReport;
  const ts = S6TransitiveSubgroups;
  const wanted = (...names: S6TransitiveSubgroups[]): boolean => names.some((n) => targets.includes(n));
  const byOrder = (G: PermutationGroupNode): Map<number, Permutation[]> => {
    const elts = new Map<number, Permutation[]>();
    for (const g of G.elements) {
      const o = Number(g.order());
      elts.set(o, [...elts.get(o) ?? [], g]);
    }
    return elts;
  };
  const profile = (G: PermutationGroupNode): string => [...byOrder(G)].map(([o, e]) => `${o}:${e.length}`).sort().join(',');
  const S6 = SymmetricGroup(6);
  const A6 = AlternatingGroup(6);
  const S6ByOrder = byOrder(S6);
  const search = (existing: readonly Permutation[], neededOrders: readonly number[], order: number, opts: { alt?: boolean; profile?: string; antiProfile?: string } = {}): PermutationGroupNode => {
    const pools = neededOrders.map((n) => defined(S6ByOrder.get(n)));
    const product = function* (i: number, chosen: Permutation[]): Generator<Permutation[]> {
      if (i === pools.length) {
        yield chosen;
        return;
      }
      for (const g of at(pools, i)) yield* product(i + 1, [...chosen, g]);
    };
    const candidates = function* (): Generator<PermutationGroupNode> {
      for (const gens of product(0, [])) {
        if (new Set(gens.map((g) => g.arrayForm.join(','))).size < gens.length) continue;
        const G = PermutationGroup([...existing, ...gens]);
        const accepted = Number(G.order()) === order && G.isTransitive()
          && (opts.alt === undefined || G.isSubgroup(A6) === opts.alt)
          && (opts.profile === undefined || profile(G) === opts.profile)
          && (opts.antiProfile === undefined || profile(G) !== opts.antiProfile);
        if (!accepted) continue;
        yield G;
      }
    };
    return defined(candidates().next().value, 'a transitive subgroup of S6 with these properties');
  };
  const matchKnownGroup = (G: PermutationGroupNode, alt?: boolean): PermutationGroupNode =>
    search([], G.generators.map((g) => Number(g.order())), Number(G.order()), { alt, profile: profile(G) });
  const found = new Map<S6TransitiveSubgroups, PermutationGroupNode>();
  const finishUp = (name: S6TransitiveSubgroups, G: PermutationGroupNode): PermutationGroupNode => {
    found.set(name, G);
    report?.(`${'='.repeat(40)}\n${name.toString()}:\n[${G.generators.map((g) => permutationRepr(g)).join(', ')}]`);
    return G;
  };
  const a4 = wanted(ts.A4, ts.A4xC2) ? finishUp(ts.A4, matchKnownGroup(AlternatingGroup(4))) : undefined;
  const s4m = wanted(ts.S4m, ts.S4xC2) ? finishUp(ts.S4m, matchKnownGroup(SymmetricGroup(4), false)) : undefined;
  if (wanted(ts.S4p)) finishUp(ts.S4p, matchKnownGroup(SymmetricGroup(4), true));
  if (a4 !== undefined && wanted(ts.A4xC2)) finishUp(ts.A4xC2, search(a4.generators, [2], 24, { antiProfile: profile(SymmetricGroup(4)) }));
  if (s4m !== undefined && wanted(ts.S4xC2)) finishUp(ts.S4xC2, search(s4m.generators, [2], 48));
  // The normal factor C3^2 of the groups G18, G36-, G36+ and G72.
  const N = [cycles([5], [0, 1, 2]), cycles([5], [3, 4, 5])];
  if (wanted(ts.G18)) finishUp(ts.G18, search(N, [2], 18));
  if (wanted(ts.G36m)) finishUp(ts.G36m, search(N, [2, 2], 36, { alt: false }));
  if (wanted(ts.G36p)) finishUp(ts.G36p, search(N, [4], 36, { alt: true }));
  if (wanted(ts.G72)) finishUp(ts.G72, search(N, [4, 2], 72));
  // PSL2(F5) and PGL2(F5) are isomorphic to A5 and S5.
  if (wanted(ts.PSL2F5)) finishUp(ts.PSL2F5, matchKnownGroup(AlternatingGroup(5)));
  if (wanted(ts.PGL2F5)) finishUp(ts.PGL2F5, matchKnownGroup(SymmetricGroup(5)));
  if (wanted(ts.C6)) finishUp(ts.C6, matchKnownGroup(CyclicGroup(6)));
  if (wanted(ts.S3)) finishUp(ts.S3, matchKnownGroup(SymmetricGroup(3)));
  if (wanted(ts.D6)) finishUp(ts.D6, matchKnownGroup(DihedralGroup(6)));
  if (wanted(ts.A6)) finishUp(ts.A6, matchKnownGroup(A6));
  if (wanted(ts.S6)) finishUp(ts.S6, matchKnownGroup(S6));
  return found;
}
