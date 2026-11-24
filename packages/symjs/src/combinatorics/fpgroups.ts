// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/fp_groups.py and the
// GroupHomomorphism class of homomorphisms.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.fp_groups: finitely presented groups
 * (FpGroup), their subgroups (FpSubgroup), low index subgroups, the
 * simplification of presentations and the Reidemeister-Schreier
 * presentation of a subgroup; and the group homomorphisms between
 * permutation groups, finitely presented groups and free groups
 * (GroupHomomorphism, homomorphism), which SymPy's homomorphisms module
 * defines and the finitely presented groups use.
 */

import { NotImplementedError } from '../core/errors';
import { at, cast, defined } from '../core/guard';
import type { Expr } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { Matrix } from '../matrices/matrix';
import { invariantFactors } from '../matrices/normalforms';
import { rng } from '../ntheory/random';
import type { CosetEnumerationOptions, CosetRow } from './cosettable';
import { CosetTable, conjugatesByLetter, cosetEnumerationC, cosetEnumerationR, listStr } from './cosettable';
import type { FreeGroupSymbols } from './freegroups';
import { FreeGroup, FreeGroupElement, freeGroup, tupleStr, uniqueWords } from './freegroups';
import { PermutationGroupNode } from './permgroups';
import { Permutation } from './permutations';
import { RewritingSystem } from './rewritingsystem';

const sortWords = (ws: FreeGroupElement[]): FreeGroupElement[] => ws.sort((a, b) => FreeGroupElement.compare(a, b));
const sameWordSet = (a: readonly FreeGroupElement[], b: readonly FreeGroupElement[]): boolean => {
  const ka = new Set(a.map((w) => w.key));
  const kb = new Set(b.map((w) => w.key));
  return ka.size === kb.size && [...ka].every((k) => kb.has(k));
};
/** The gcd of two machine integers. */
const gcd = (a: number, b: number): number => {
  let x = Math.abs(a);
  let y = Math.abs(b);
  while (y) [x, y] = [y, x % y];
  return x;
};
const hasWord = (ws: readonly FreeGroupElement[], w: FreeGroupElement): boolean => ws.some((v) => v.equals(w));

/** The strategies of a coset enumeration. */
export type CosetStrategy = 'relator_based' | 'coset_table_based';

/** Options of FpGroup.cosetEnumeration and FpGroup.cosetTable. */
export interface FpCosetOptions extends Omit<CosetEnumerationOptions, 'modified'> {
  /** 'relator_based' (HLT, the default) or 'coset_table_based' (Felsch). */
  strategy?: CosetStrategy;
}

/**
 * The finitely presented group with the
 * generators of a free group and these relators.
 * @see SymPy `sympy.combinatorics.fp_groups.FpGroup`
 * @example
 * ```ts
 * import { FpGroup, freeGroup } from '@symjs/symjs';
 *
 * const [F, x, y] = freeGroup('x, y');
 * const G = new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(4)]);
 * String(G.order()); // => 24
 * ```
 */
export class FpGroup {
  /**
   * Indicates whether the object represents a group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_group`
   */
  readonly isGroup = true;
  /**
   * Indicates whether the group is given by a finite presentation.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_FpGroup`
   */
  readonly isFpGroup = true;
  /**
   * Indicates whether the group acts by permutations.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_PermutationGroup`
   */
  readonly isPermutationGroup = false;
  /**
   * The free group on the generators.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.free_group`
   */
  readonly freeGroup: FreeGroup;
  /**
   * The words imposed as defining relations.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.relators`
   */
  readonly relators: FreeGroupElement[];
  /**
   * The generators in their defining order.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup._generators`
   */
  readonly generators: readonly FreeGroupElement[];
  /** The cached table for enumeration of the trivial subgroup. @internal */
  cosetTableCache: CosetTable | undefined;
  #isStandardized = false;
  #order: Expr | undefined;
  #rewritingSystem: RewritingSystem | undefined;
  #permIsomorphism: GroupHomomorphism | undefined;

  /**
   * Constructs a `FpGroup`.
   * @param frGroup - The free group on the presentation generators.
   * @param relators - The words imposed as relations.
   */
  constructor(frGroup: FreeGroup, relators: readonly FreeGroupElement[] = []) {
    this.freeGroup = frGroup;
    this.relators = [...relators];
    this.generators = frGroup.generators;
  }

  /**
   * Gets the rewriting system.
   * @returns The rewriting system.
   * @internal
   */
  get rewritingSystem(): RewritingSystem {
    return (this.#rewritingSystem ??= new RewritingSystem(this));
  }

  /**
   * Complete the rewriting system (Knuth-Bendix).
   * @returns Whether the resulting rewriting system is confluent.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.make_confluent`
   */
  makeConfluent(): boolean {
    return this.rewritingSystem.makeConfluent();
  }

  /**
   * The normal form of a word under the rewriting system.
   * @param word - The word in the presentation generators.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.reduce`
   */
  reduce(word: FreeGroupElement): FreeGroupElement {
    return this.rewritingSystem.reduce(word);
  }

  /**
   * Tests whether two words represent the same group element.
   * @param word1 - The first group word.
   * @param word2 - The second group word.
   * @returns The equality decision, or `'unknown'` when reduction cannot decide it.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.equals`
   */
  equals(word1: FreeGroupElement, word2: FreeGroupElement): boolean | 'unknown' {
    if (this.reduce(word1.mul(word2.inverse())).equals(this.identity)) return true;
    if (this.rewritingSystem.isConfluent) return false;
    return 'unknown';
  }

  /**
   * Gets the identity of the free group.
   * @returns The identity of the free group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.identity`
   */
  get identity(): FreeGroupElement {
    return this.freeGroup.identity;
  }

  /**
   * Tests whether a word belongs to the underlying free group.
   * @param g - The element whose group membership is being tested.
   * @returns Whether the value is a word on this presentation’s generators.
   */
  contains(g: unknown): boolean {
    return this.freeGroup.contains(g);
  }

  /**
   * The subgroup generated by gens as
   * a finitely presented group (by the Reidemeister-Schreier method); with
   * `homomorphism`, also the injection into this group.
   * @param gens - The group generators.
   * @param C - The coset table of the subgroup.
   * @param homomorphism - Whether to track the images of subgroup generators in the parent group.
   * @returns The subgroup generated by gens as a finitely presented group (by the Reidemeister-Schreier method).
   * @throws RangeError when a generator is not a free group element or a supplied generator does not belong to the group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.subgroup`
   */
  subgroup(gens: readonly FreeGroupElement[], C?: CosetTable, homomorphism?: false): FpGroup;
  subgroup(gens: readonly FreeGroupElement[], C: CosetTable | undefined, homomorphism: true): [FpGroup, GroupHomomorphism];
  subgroup(gens: readonly FreeGroupElement[], C?: CosetTable, homomorphism = false): FpGroup | [FpGroup, GroupHomomorphism] {
    if (!gens.every((g) => g instanceof FreeGroupElement)) throw new RangeError('Generators must be `FreeGroupElement`s');
    if (!gens.every((g) => g.group === this.freeGroup)) throw new RangeError('Given generators are not members of the group');
    const pres = reidemeisterPresentationFull(this, gens, C, homomorphism);
    const g = pres.generators.length ? new FpGroup(at(pres.generators, 0).group, pres.relators) : new FpGroup(new FreeGroup(''), []);
    if (homomorphism) return [g, homomorphismOf(g, this, g.generators, defined(pres.images, 'images'), false)];
    return g;
  }

  /**
   * Returns the (compressed) coset table of H.
   * @param H - The subgroup or second group in the operation.
   * @param opts - The settings described by {@link FpCosetOptions}.
   * @returns The (compressed) coset table of H.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.coset_enumeration`
   * @example
   * ```ts
   * import { FpGroup, freeGroup } from '@symjs/symjs';
   *
   * const [F, x] = freeGroup('x');
   * const G = new FpGroup(F, [x.pow(3)]);
   * G.cosetEnumeration([x]).n; // => 1
   * ```
   */
  cosetEnumeration(H: readonly FreeGroupElement[], opts: FpCosetOptions = {}): CosetTable {
    const { strategy = 'relator_based', maxCosets, ...rest } = opts;
    const max = maxCosets !== undefined && maxCosets !== 0 ? maxCosets : CosetTable.cosetTableMaxLimit;
    const C = strategy === 'relator_based' ? cosetEnumerationR(this, H, { ...rest, maxCosets: max }) : cosetEnumerationC(this, H, { ...rest, maxCosets: max });
    if (C.isComplete()) C.compress();
    return C;
  }

  /**
   * Standardize the stored coset table of the trivial subgroup.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.standardize_coset_table`
   */
  standardizeCosetTable(): void {
    defined(this.cosetTableCache, 'coset table').standardize();
    this.#isStandardized = true;
  }

  /**
   * Returns the standardized coset table of H (of the trivial subgroup for an empty H).
   * @param H - The subgroup or second group in the operation.
   * @param opts - The settings described by {@link FpCosetOptions}.
   * @returns The standardized coset table of H (of the trivial subgroup for an empty H).
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.coset_table`
   */
  cosetTable(H: readonly FreeGroupElement[], opts: FpCosetOptions = {}): CosetRow[] {
    if (!H.length) {
      this.cosetTableCache ??= this.cosetEnumeration([], opts);
      if (!this.#isStandardized) this.standardizeCosetTable();
      return this.cosetTableCache.table;
    }
    const C = this.cosetEnumeration(H, opts);
    C.standardize();
    return C.table;
  }

  /**
   * The order of the group (oo for an infinite group).
   * @param _strategy - The strategy used for coset enumeration.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.order`
   */
  order(_strategy: CosetStrategy = 'relator_based'): Expr {
    if (this.#order !== undefined) return this.#order;
    if (this.cosetTableCache !== undefined) this.#order = Rational.of(this.cosetTableCache.table.length);
    else if (this.relators.length === 0) this.#order = this.freeGroup.order();
    // one generator: the relators are powers of it
    else if (this.generators.length === 1) this.#order = Rational.of(this.relators.map((r) => r.exponentSum(at(this.generators, 0))).reduce(gcd, 0));
    else if (this.#isInfinite()) this.#order = S.Infinity;
    else {
      // SymPy falls back to index([]), which calls order() again
      const [gens, C] = this.#finiteIndexSubgroup();
      this.#order = Rational.of(C.table.length).mul(this.subgroup(gens, C).order());
    }
    return this.#order;
  }

  /** SymPy _is_infinite: true when the group is infinite by a simple test (a generator not in any relator, or a zero invariant factor of the abelianization). */
  #isInfinite(): boolean {
    const used = new Set(this.relators.flatMap((r) => r.syllables.map(([g]) => g)));
    if (this.generators.some((_g, i) => !used.has(i))) return true;
    const m = Matrix.of(this.relators.map((rel) => this.generators.map((g) => Rational.of(rel.exponentSum(g)))));
    return invariantFactors(m).some((f) => f instanceof Rational && f.p === 0n);
  }

  #finiteIndexSubgroup(): [FreeGroupElement[], CosetTable] {
    const gen = this.mostFrequentGenerator();
    const rels = [...this.generators, ...this.relators];
    let s: FreeGroupElement[];
    if (this.generators.length === 2) s = [gen, ...this.generators.filter((g) => !g.equals(gen))];
    else {
      let rand = this.freeGroup.identity;
      let i = 0;
      while ((hasWord(rels, rand) || hasWord(rels, rand.inverse()) || rand.isIdentity) && i < 10) {
        rand = this.random();
        i++;
      }
      s = [gen, rand, ...this.generators.filter((g) => !g.equals(gen))];
    }
    const mid = Math.floor((s.length + 1) / 2);
    const half1 = s.slice(0, mid);
    const half2 = s.slice(mid);
    let draft1: CosetTable | undefined;
    let draft2: CosetTable | undefined;
    let m = 200;
    let C: CosetTable | undefined;
    let half: FreeGroupElement[] = [];
    while (!C && m / 2 < CosetTable.cosetTableMaxLimit) {
      m = Math.min(m, CosetTable.cosetTableMaxLimit);
      draft1 = this.cosetEnumeration(half1, { maxCosets: m, draft: draft1, incomplete: true });
      if (draft1.isComplete()) {
        C = draft1;
        half = half1;
      } else {
        draft2 = this.cosetEnumeration(half2, { maxCosets: m, draft: draft2, incomplete: true });
        if (draft2.isComplete()) {
          C = draft2;
          half = half2;
        }
      }
      if (!C) m *= 2;
    }
    if (!C) throw new NotImplementedError(`no subgroup of index at most ${CosetTable.cosetTableMaxLimit} found to compute the order`);
    C.compress();
    return [half, C];
  }

  /**
   * The generator occurring most often in the relators.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.most_frequent_generator`
   */
  mostFrequentGenerator(): FreeGroupElement {
    const freqs = this.generators.map((g) => this.relators.reduce((t, r) => t + r.generatorCount(g), 0));
    return at(this.generators, freqs.indexOf(Math.max(...freqs)));
  }

  /**
   * A random word of length 2 or 3.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.random`
   */
  random(): FreeGroupElement {
    let r = this.freeGroup.identity;
    const n = Number(rng.randint(2n, 3n));
    for (let i = 0; i < n; i++) {
      const g = at(this.generators, Number(rng.randbelow(BigInt(this.generators.length))));
      r = r.mul(g.pow(rng.randbelow(2n) === 0n ? 1 : -1));
    }
    return r;
  }

  /**
   * The index of the subgroup generated by H (the order for an empty H).
   * @param H - The subgroup or second group in the operation.
   * @param strategy - The strategy used for coset enumeration.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.index`
   */
  index(H: readonly FreeGroupElement[], strategy: CosetStrategy = 'relator_based'): Expr {
    if (!H.length) return this.order();
    return Rational.of(this.cosetEnumeration(H, { strategy }).table.length);
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    if (this.freeGroup.rank > 30) return `<fp group with ${this.freeGroup.rank} generators>`;
    return `<fp group on the generators ${tupleStr(this.generators)}>`;
  }

  /**
   * Returns an isomorphic permutation group (the action on the cosets of the trivial subgroup) and the isomorphism.
   * @returns An isomorphic permutation group (the action on the cosets of the trivial subgroup) and the isomorphism.
   * @throws NotImplementedError when the group is infinite.
   * @internal
   */
  toPermGroup(): [PermutationGroupNode, GroupHomomorphism] {
    if (this.order() === S.Infinity) throw new NotImplementedError('Permutation presentation of infinite groups is not implemented');
    if (this.#permIsomorphism) {
      const T = this.#permIsomorphism;
      return [cast(T.image(), PermutationGroupNode, 'permutation group'), T];
    }
    const C = this.cosetTable([]);
    const gens = this.generators;
    const images = gens.map((_g, k) => new Permutation(C.map((row) => defined(at(row, 2 * k), 'coset table entry'))));
    const P = new PermutationGroupNode(images);
    const T = homomorphismOf(this, P, gens, images, false);
    this.#permIsomorphism = T;
    return [P, T];
  }

  #invertGroup(G: PermutationGroupNode): FreeGroupElement[] {
    const T = this.toPermGroup()[1];
    return G.generators.map((g) => wordOf(T.invert(g)));
  }

  #permGroup(f: (P: PermutationGroupNode) => PermutationGroupNode): FreeGroupElement[] {
    return this.#invertGroup(f(this.toPermGroup()[0]));
  }

  #permSeries(f: (P: PermutationGroupNode) => PermutationGroupNode[]): FreeGroupElement[][] {
    return f(this.toPermGroup()[0]).map((G) => this.#invertGroup(G));
  }

  /**
   * The derived series, each term as a list of generators.
   * @returns The successive derived subgroups, starting with this group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.derived_series`
   */
  derivedSeries(): FreeGroupElement[][] {
    return this.#permSeries((P) => P.derivedSeries());
  }

  /**
   * Return the list of lists containing the generators of the subgroups in the lower central series of `self`.
   * @returns The successive terms obtained by taking commutators with the full group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.lower_central_series`
   */
  lowerCentralSeries(): FreeGroupElement[][] {
    return this.#permSeries((P) => P.lowerCentralSeries());
  }

  /**
   * Generators of the center.
   * @returns The resulting group elements.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.center`
   */
  center(): FreeGroupElement[] {
    return this.#permGroup((P) => P.center());
  }

  /**
   * Generators of the derived subgroup.
   * @returns The resulting group elements.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.derived_subgroup`
   */
  derivedSubgroup(): FreeGroupElement[] {
    return this.#permGroup((P) => P.derivedSubgroup());
  }

  #perms(other: FreeGroupElement | readonly FreeGroupElement[]): Permutation[] {
    const T = this.toPermGroup()[1];
    return (other instanceof FreeGroupElement ? [other] : [...other]).map((w) => cast2Permutation(T.apply(w)));
  }

  /**
   * Generators of the centralizer of a word (or of a list of words).
   * @param other - The value to combine with or compare against.
   * @returns The resulting group elements.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.centralizer`
   */
  centralizer(other: FreeGroupElement | readonly FreeGroupElement[]): FreeGroupElement[] {
    const o = this.#perms(other);
    return this.#permGroup((P) => P.centralizer(o));
  }

  /**
   * Generators of the normal closure of a word (or of a list of words).
   * @param other - The value to combine with or compare against.
   * @returns The resulting group elements.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.normal_closure`
   */
  normalClosure(other: FreeGroupElement | readonly FreeGroupElement[]): FreeGroupElement[] {
    const o = this.#perms(other);
    return this.#permGroup((P) => P.normalClosure(o));
  }

  /**
   * Check if `self` is abelian.
   * @returns Whether the object is abelian.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_abelian`
   */
  get isAbelian(): boolean {
    return this.toPermGroup()[0].isAbelian;
  }

  /**
   * Check if `self` is nilpotent.
   * @returns Whether the object is nilpotent.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_nilpotent`
   */
  get isNilpotent(): boolean {
    return this.toPermGroup()[0].isNilpotent;
  }

  /**
   * Indicates whether the group has a terminating derived series.
   * @returns Whether the object is solvable.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_solvable`
   */
  get isSolvable(): boolean {
    return this.toPermGroup()[0].isSolvable;
  }

  /**
   * Gets the elements as words.
   * @returns The elements as words.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.elements`
   */
  get elements(): FreeGroupElement[] {
    const [P, T] = this.toPermGroup();
    return P.elements.map((g) => wordOf(T.invert(g)));
  }

  /** The permutation group of a finite group; the message for an infinite one. */
  #finitePerm(message: string): PermutationGroupNode {
    if (this.order() === S.Infinity) throw new NotImplementedError(message);
    return this.toPermGroup()[0];
  }

  /**
   * Return `True` if group is Cyclic.
   * @returns Whether the object is cyclic.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.is_cyclic`
   */
  get isCyclic(): boolean {
    if (this.generators.length <= 1) return true;
    return this.#finitePerm('Check for infinite Cyclic group is not implemented').isCyclic;
  }

  /**
   * Return Abelian Invariants of a group.
   * @returns Abelian Invariants of a group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.abelian_invariants`
   */
  abelianInvariants(): bigint[] {
    return this.#finitePerm('abelian invariants is not implementedfor infinite group').abelianInvariants();
  }

  /**
   * Return subnormal series of maximum length for a group.
   * @returns Subnormal series of maximum length for a group.
   * @see SymPy `sympy.combinatorics.fp_groups.FpGroup.composition_series`
   */
  compositionSeries(): PermutationGroupNode[] {
    return this.#finitePerm('composition series is not implementedfor infinite group').compositionSeries();
  }
}

const wordOf = (e: GroupElement): FreeGroupElement => cast(e, FreeGroupElement, 'word');
const cast2Permutation = (e: GroupElement): Permutation => cast(e, Permutation, 'permutation');

/**
 * Constructs a finitely presented group from a free group and its relators.
 * @param frGroup - The free group on the presentation generators.
 * @param relators - The words imposed as relations.
 * @returns The group followed by its generators.
 * @see SymPy `sympy.combinatorics.fp_groups.fp_group`
 */
export function fpGroup(frGroup: FreeGroup, relators: readonly FreeGroupElement[] = []): [FpGroup, ...FreeGroupElement[]] {
  const G = new FpGroup(frGroup, relators);
  return [G, ...G.generators];
}

/**
 * Constructs a finitely presented group and collects its generators in a separate array.
 * @param frGroup - The free group on the presentation generators.
 * @param relators - The words imposed as relations.
 * @returns The group and its array of generators.
 * @see SymPy `sympy.combinatorics.fp_groups.xfp_group`
 */
export function xfpGroup(frGroup: FreeGroup, relators: readonly FreeGroupElement[] = []): [FpGroup, FreeGroupElement[]] {
  const G = new FpGroup(frGroup, relators);
  return [G, [...G.generators]];
}

/**
 * Constructs a finitely presented group whose generators are accessible through `generators`.
 * @param frGroup - The free group on the presentation generators.
 * @param relators - The words imposed as relations.
 * @returns The presented group.
 * @see SymPy `sympy.combinatorics.fp_groups.vfp_group`
 */
export function vfpGroup(frGroup: FreeGroup | FreeGroupSymbols, relators: readonly FreeGroupElement[] = []): FpGroup {
  return new FpGroup(frGroup instanceof FreeGroup ? frGroup : new FreeGroup(frGroup), relators);
}

/**
 * The Stallings graph of a subgroup of a free group: the loops of the
 * generators at vertex 0, folded until no vertex has two edges with the same
 * letter. A word is in the subgroup exactly when it reads a closed path at 0.
 */
function stallingsGraph(gens: readonly FreeGroupElement[]): Map<number, number>[] {
  const edges: Map<number, number>[] = [new Map()];
  const parent: number[] = [0];
  const find = (v: number): number => {
    let r = v;
    while (at(parent, r) !== r) r = at(parent, r);
    return r;
  };
  const pending: [number, number][] = [];
  const addEdge = (u: number, c: number, v: number): void => {
    const e = at(edges, u);
    const t = e.get(c);
    if (t === undefined) e.set(c, v);
    else if (find(t) !== find(v)) pending.push([t, v]);
  };
  const newVertex = (): number => {
    edges.push(new Map());
    parent.push(parent.length);
    return edges.length - 1;
  };
  for (const g of gens) {
    const ls = g.letters;
    let u = 0;
    ls.forEach((c, i) => {
      const v = i === ls.length - 1 ? 0 : newVertex();
      addEdge(u, c, v);
      addEdge(v, -c, u);
      u = v;
    });
  }
  // fold: merge the targets of equal letters, moving the edges of the merged vertex
  while (pending.length) {
    const [p, q] = defined(pending.pop(), 'fold');
    const a = find(p);
    const b = find(q);
    if (a === b) continue;
    const [keep, gone] = a < b ? [a, b] : [b, a];
    parent[gone] = keep;
    for (const [c, t] of at(edges, gone)) addEdge(keep, c, t);
    at(edges, gone).clear();
  }
  return edges.map((e, v) => (find(v) === v ? new Map([...e].map(([c, t]) => [c, find(t)])) : new Map<number, number>()));
}

/**
 * Represents the subgroup generated by words in a free or finitely presented group. The `normal` flag takes their normal closure.
 * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup`
 */
export class FpSubgroup {
  /**
   * The ambient group containing the subgroup.
   * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup.parent`
   */
  readonly parent: FpGroup | FreeGroup;
  /**
   * The generators in their defining order.
   * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup.generators`
   */
  readonly generators: FreeGroupElement[];
  /**
   * Whether the generators are taken to generate a normal subgroup.
   * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup.normal`
   */
  readonly normal: boolean;
  #graph: Map<number, number>[] | undefined;
  /**
   * The coset table of the subgroup, once computed.
   * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup.C`
   */
  C: CosetTable | undefined;

  /**
   * Constructs a `FpSubgroup`.
   * @param G - The ambient group.
   * @param gens - The group generators.
   * @param normal - Whether the generators define a normal subgroup.
   */
  constructor(G: FpGroup | FreeGroup, gens: readonly FreeGroupElement[], normal = false) {
    this.parent = G;
    this.generators = uniqueWords(gens.filter((g) => !g.equals(G.identity)));
    this.normal = normal;
  }

  /**
   * Tests membership in the subgroup generated by the specified words.
   * @param gIn - The element whose group membership is being tested.
   * @returns The membership decision, or `'unknown'` for an undecided normal-closure membership test.
   */
  contains(gIn: FreeGroupElement): boolean | 'unknown' {
    if (this.parent instanceof FreeGroup) {
      if (this.normal) {
        // the normal closure: g is in it exactly when g is the identity of the quotient group
        const Q = new FpGroup(this.parent, this.generators);
        // 'unknown' when the completion of the rewriting system stops at its maximum number of rules
        let e = Q.equals(gIn, this.parent.identity);
        if (e === 'unknown') {
          Q.makeConfluent();
          e = Q.equals(gIn, this.parent.identity);
        }
        return e;
      }
      const graph = (this.#graph ??= stallingsGraph(this.generators));
      let v = 0;
      for (const c of gIn.letters) {
        const next = graph[v]?.get(c);
        if (next === undefined) return false;
        v = next;
      }
      return v === 0;
    }
    const C = (this.C ??= this.parent.cosetEnumeration(this.generators));
    let i = 0;
    for (const c of gIn.letters) i = defined(at(at(C.table, i), 2 * (Math.abs(c) - 1) + (c < 0 ? 1 : 0)), 'coset table entry');
    return i === 0;
  }

  /**
   * The order of the subgroup.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup.order`
   */
  order(): Expr {
    if (!this.generators.length) return S.One;
    if (this.parent instanceof FreeGroup) return S.Infinity;
    const C = (this.C ??= this.parent.cosetEnumeration(this.generators));
    return this.parent.order().div(Rational.of(C.table.length));
  }

  /**
   * Returns the subgroup as a finitely presented group (a free group for a subgroup of a free group).
   * @returns The subgroup as a finitely presented group (a free group for a subgroup of a free group).
   * @see SymPy `sympy.combinatorics.fp_groups.FpSubgroup.to_FpGroup`
   */
  toFpGroup(): FpGroup | FreeGroup {
    if (this.parent instanceof FreeGroup) return defined(freeGroup(this.generators.map((_g, i) => `x_${i}`).join(', '))[0], 'free group');
    // SymPy calls parent.subgroup(C=self.C), without the generators
    return this.parent.subgroup(this.generators, this.C);
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    if (this.generators.length > 30) return `<fp subgroup with ${this.generators.length} generators>`;
    return `<fp subgroup on the generators ${listStr(this.generators)}>`;
  }
}

/**
 * The coset tables of the subgroups of index at most N containing the words Y.
 * @param G - The ambient group.
 * @param N - The maximum subgroup index.
 * @param Y - Generators required to lie in the subgroup.
 * @returns One coset table per subgroup conjugacy class.
 * @see SymPy `sympy.combinatorics.fp_groups.low_index_subgroups`
 * @example
 * ```ts
 * import { FpGroup, freeGroup, lowIndexSubgroups, table } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * lowIndexSubgroups(G, 3).map(table => table.n); // => [1, 3]
 * ```
 */
export function lowIndexSubgroups(G: FpGroup, N: number, Y: readonly FreeGroupElement[] = []): CosetTable[] {
  const C = new CosetTable(G, []);
  const R = uniqueWords(G.relators);
  const lenShortRel = 5;
  const R2 = R.filter((rel) => rel.length > lenShortRel);
  const R1 = uniqueWords(R.filter((rel) => rel.length <= lenShortRel).map((rel) => rel.identityCyclicReduction()));
  const R1cList = conjugatesByLetter(C.A, R1);
  const S: CosetTable[] = [];
  descendantSubgroups(S, C, R1cList, at(C.A, 0), R2, N, Y);
  return S;
}

const colOf = (x: FreeGroupElement): number => {
  if (x.length !== 1) throw new RangeError(`${String(x)} is not a letter`);
  const c = at(x.letters, 0);
  return 2 * (Math.abs(c) - 1) + (c < 0 ? 1 : 0);
};

/**
 * Enumerates descendant coset tables in the low-index subgroup search.
 * @param S - The accumulating list of subgroup tables.
 * @param C - The coset table of the subgroup.
 * @param R1cList - The short relator conjugates indexed by starting letter.
 * @param _x - The generator letter labeling the transition.
 * @param R2 - The relators checked on completion.
 * @param N - The maximum subgroup index.
 * @param Y - Generators required to lie in the subgroup.
 * @see SymPy `sympy.combinatorics.fp_groups.descendant_subgroups`
 */
export function descendantSubgroups(S: CosetTable[], C: CosetTable, R1cList: readonly FreeGroupElement[][], _x: FreeGroupElement, R2: readonly FreeGroupElement[], N: number, Y: readonly FreeGroupElement[]): void {
  if (C.isComplete()) {
    for (const w of R2) for (const alpha of C.omega) if (!C.scanCheck(alpha, w)) return;
    S.push(C);
    return;
  }
  let undefinedCoset = -1;
  let undefinedGen = -1;
  outer: for (let alpha = 0; alpha < C.table.length; alpha++) {
    for (let x = 0; x < C.A.length; x++) {
      if ((at(at(C.table, alpha), x)) === null) {
        undefinedCoset = alpha;
        undefinedGen = x;
        break outer;
      }
    }
  }
  const n = C.n;
  for (const beta of [...C.omega, n]) {
    if (beta < N && (beta === n || (at(at(C.table, beta), undefinedGen ^ 1)) === null)) tryDescendantCol(S, C, R1cList, R2, N, undefinedCoset, undefinedGen, beta, Y);
  }
}

function tryDescendantCol(S: CosetTable[], C: CosetTable, R1cList: readonly FreeGroupElement[][], R2: readonly FreeGroupElement[], N: number, alpha: number, x: number, beta: number, Y: readonly FreeGroupElement[]): void {
  const D = C.copy();
  if (beta === D.n && beta < N) {
    D.table.push(Array<null>(D.A.length).fill(null));
    D.p.push(beta);
  }
  at(D.table, alpha)[x] = beta;
  at(D.table, beta)[x ^ 1] = alpha;
  D.deductionStack.push([alpha, x]);
  if (!D.processDeductionsCheck(at(R1cList, x), at(R1cList, x ^ 1))) return;
  for (const w of Y) if (!D.scanCheck(0, w)) return;
  if (firstInClass(D, Y)) descendantSubgroups(S, D, R1cList, at(D.A, x), R2, N, Y);
}

/**
 * Tries a coset transition and searches the compatible descendant tables.
 * @param S - The accumulating list of subgroup tables.
 * @param C - The coset table of the subgroup.
 * @param R1cList - The short relator conjugates indexed by starting letter.
 * @param R2 - The relators checked on completion.
 * @param N - The maximum subgroup index.
 * @param alpha - The starting coset label.
 * @param x - The generator letter labeling the transition.
 * @param beta - The second coset label.
 * @param Y - Generators required to lie in the subgroup.
 * @see SymPy `sympy.combinatorics.fp_groups.try_descendant`
 */
export function tryDescendant(S: CosetTable[], C: CosetTable, R1cList: readonly FreeGroupElement[][], R2: readonly FreeGroupElement[], N: number, alpha: number, x: FreeGroupElement, beta: number, Y: readonly FreeGroupElement[]): void {
  tryDescendantCol(S, C, R1cList, R2, N, alpha, colOf(x), beta, Y);
}

/**
 * Tests whether a coset table is the canonical representative of its conjugacy class.
 * @param C - The coset table of the subgroup.
 * @param Y - Generators required to lie in the subgroup.
 * @returns Whether the table is first in its class.
 * @see SymPy `sympy.combinatorics.fp_groups.first_in_class`
 * @example
 * ```ts
 * import { CosetTable, FpGroup, firstInClass, freeGroup } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * firstInClass(new CosetTable(G, [])); // => True
 * ```
 */
export function firstInClass(C: CosetTable, Y: readonly FreeGroupElement[] = []): boolean {
  const n = C.n;
  let lamda = -1;
  const nu: (number | null)[] = Array<null>(n).fill(null);
  const mu: (number | null)[] = Array<null>(n).fill(null);
  let nextAlpha = false;
  for (let alpha = 1; alpha < n; alpha++) {
    for (let beta = 0; beta <= lamda; beta++) nu[defined(at(mu, beta), 'mu')] = null;
    for (const w of Y) {
      if (at(C.table, alpha)[colOf(w)] !== alpha) {
        nextAlpha = true;
        break;
      }
    }
    if (nextAlpha) {
      nextAlpha = false;
      continue;
    }
    mu[0] = alpha;
    nu[alpha] = 0;
    lamda = 0;
    for (let beta = 0; beta < n; beta++) {
      for (let x = 0; x < C.A.length; x++) {
        const gamma = at(at(C.table, beta), x);
        const m = at(mu, beta);
        const delta = m === null ? null : (at(at(C.table, m), x));
        if (gamma === null || delta === null) {
          nextAlpha = true;
          break;
        }
        let nd = at(nu, delta);
        if (nd === null) {
          lamda++;
          nu[delta] = lamda;
          mu[lamda] = delta;
          nd = lamda;
        }
        if (nd < gamma) return false;
        if (nd > gamma) {
          nextAlpha = true;
          break;
        }
      }
      if (nextAlpha) {
        nextAlpha = false;
        break;
      }
    }
  }
  return true;
}

/**
 * Simplifies a group presentation by eliminating redundant relators and optionally generators.
 * @param G - The ambient group.
 * @param changeGens - Whether simplification may eliminate generators.
 * @param gens - The group generators.
 * @param rels - The defining relators.
 * @returns The simplified group or the reduced generators and relators.
 * @throws TypeError when the supplied group is not finitely presented or the generators are supplied without relators.
 * @see SymPy `sympy.combinatorics.fp_groups.simplify_presentation`
 */
export function simplifyPresentation(G: FpGroup, changeGens?: boolean): FpGroup;
export function simplifyPresentation(gens: readonly FreeGroupElement[], rels: readonly FreeGroupElement[], changeGens?: boolean): [FreeGroupElement[], FreeGroupElement[]];
export function simplifyPresentation(groupOrGens: FpGroup | readonly FreeGroupElement[], relsOrChangeGens?: readonly FreeGroupElement[] | boolean, changeGensIn = false): FpGroup | [FreeGroupElement[], FreeGroupElement[]] {
  if (!Array.isArray(groupOrGens)) {
    if (!(groupOrGens instanceof FpGroup)) throw new TypeError('The argument must be an instance of FpGroup');
    const changeGens = typeof relsOrChangeGens === 'boolean' ? relsOrChangeGens : changeGensIn;
    const [gens, rels] = simplifyPresentation(groupOrGens.generators, groupOrGens.relators, changeGens);
    if (gens.length) return new FpGroup(at(gens, 0).group, rels);
    return new FpGroup(new FreeGroup([]), []);
  }
  if (!Array.isArray(relsOrChangeGens)) throw new TypeError('simplify_presentation: expected the relators');
  const changeGens = changeGensIn;
  let gens: FreeGroupElement[] = [...(groupOrGens as readonly FreeGroupElement[])];
  let rels: FreeGroupElement[] = [...(relsOrChangeGens as readonly FreeGroupElement[])];
  if (!gens.length) return [gens, rels];
  let identity = at(gens, 0).group.identity;
  let prevGens: FreeGroupElement[] = [];
  let prevRels: FreeGroupElement[] = [];
  while (!sameWordSet(prevRels, rels)) {
    prevRels = rels;
    while (changeGens && !sameWordSet(prevGens, gens)) {
      prevGens = gens;
      [gens, rels] = eliminationTechnique1(gens, rels, identity);
    }
    rels = simplifyRelators(rels);
  }
  if (changeGens) {
    const syms = gens.map((g) => at(g.arrayForm, 0)[0]);
    const F = new FreeGroup(syms);
    identity = F.identity;
    gens = [...F.generators];
    const subs = new Map(syms.map((s, i) => [s.key, at(gens, i)]));
    rels = rels.map((r) => r.arrayForm.reduce((rel, [sym, p]) => rel.mul(defined(subs.get(sym.key), 'generator').pow(p)), identity));
  }
  return [gens, rels];
}

/** SymPy _simplify_relators(rels): relators with the one-syllable ones combined, reduced and sorted. */
function simplifyRelators(relsIn: readonly FreeGroupElement[]): FreeGroupElement[] {
  let rels = [...relsIn];
  if (!rels.length) return [];
  const identity = at(rels, 0).group.identity;
  const exps = new Map<string, [FreeGroupElement, FreeGroupElement]>();
  for (let i = 0; i < rels.length; i++) {
    const rel = at(rels, i);
    if (rel.numberSyllables() === 1) {
      let g = rel.getItem(0);
      let exp = Math.abs(at(rel.syllables, 0)[1]);
      if (at(rel.syllables, 0)[1] < 0) {
        rels[i] = rel.inverse();
        g = g.inverse();
      }
      const prev = exps.get(g.key);
      if (prev) exp = gcd(exp, at(prev[1].syllables, 0)[1]);
      exps.set(g.key, [g, g.pow(exp)]);
    }
  }
  const oneSyllableWords = [...exps.values()].map(([, w]) => w);
  for (let i = 0; i < rels.length; i++) {
    let rel = at(rels, i);
    if (hasWord(oneSyllableWords, rel)) continue;
    rel = rel.eliminateWords(oneSyllableWords, true);
    for (const g of rel.containsGenerators()) {
      const e = exps.get(g.key);
      if (e) {
        const exp = at(e[1].syllables, 0)[1];
        const maxExp = Math.floor((exp + 1) / 2);
        rel = rel.eliminateWord(g.pow(maxExp), g.pow(maxExp - exp), true);
        rel = rel.eliminateWord(g.pow(-maxExp), g.pow(-(maxExp - exp)), true);
      }
    }
    rels[i] = rel;
  }
  rels = rels.map((r) => r.identityCyclicReduction());
  rels.push(...oneSyllableWords);
  rels = sortWords(uniqueWords(rels));
  return rels.filter((r) => !r.equals(identity));
}

/**
 * Remove the generators a relator expresses in the others.
 * @param gensIn - The group generators.
 * @param relsIn - The defining relators.
 * @param identity - The identity word of the free group.
 * @returns The surviving generators and rewritten relators.
 * @see SymPy `sympy.combinatorics.fp_groups.elimination_technique_1`
 */
export function eliminationTechnique1(gensIn: readonly FreeGroupElement[], relsIn: readonly FreeGroupElement[], identity: FreeGroupElement): [FreeGroupElement[], FreeGroupElement[]] {
  let rels = sortWords([...relsIn]);
  let gens = [...gensIn];
  const redundantGens = new Map<FreeGroupElement, FreeGroupElement>();
  const redundantKeys = new Set<string>();
  const redundantRels: FreeGroupElement[] = [];
  const usedGens = new Set<string>();
  for (const rel of rels) {
    const contained = [...rel.containsGenerators()];
    if (contained.some((g) => redundantKeys.has(g.key))) continue;
    contained.sort((a, b) => FreeGroupElement.compare(b, a));
    for (const gen of contained) {
      if (rel.generatorCount(gen) === 1 && !usedGens.has(gen.key)) {
        const k = rel.exponentSum(gen);
        const genIndex = rel.index(gen.pow(k));
        const bk = rel.subword(genIndex + 1, rel.length);
        const fw = rel.subword(0, genIndex);
        const chi = bk.mul(fw);
        redundantGens.set(gen, chi.pow(-k));
        redundantKeys.add(gen.key);
        for (const g of chi.containsGenerators()) usedGens.add(g.key);
        redundantRels.push(rel);
        break;
      }
    }
  }
  rels = rels.filter((r) => !hasWord(redundantRels, r));
  rels = uniqueWords(rels.map((r) => r.eliminateWords(redundantGens, true).identityCyclicReduction())).filter((r) => !r.equals(identity));
  gens = gens.filter((g) => !redundantKeys.has(g.key));
  return [gens, rels];
}

/**
 * Labels the transitions of a standardized coset table with Schreier generators.
 * @param C - The coset table of the subgroup.
 * @param homomorphism - Whether to track the images of subgroup generators in the parent group.
 * @see SymPy `sympy.combinatorics.fp_groups.define_schreier_generators`
 */
export function defineSchreierGenerators(C: CosetTable, homomorphism = false): void {
  const y: string[] = [];
  let gamma = 1;
  const f = C.fpGroup;
  const tau = new Map<number, FreeGroupElement>([[0, f.identity]]);
  const genElems = new Map<string, FreeGroupElement>();
  const n = C.n;
  const P: (FreeGroupElement | string | null)[][] = Array.from({ length: n }, () => Array<null>(C.A.length).fill(null));
  for (const alpha of C.omega) {
    for (let x = 0; x < C.A.length; x++) {
      const beta = defined(at(at(C.table, alpha), x), 'coset table entry');
      const letter = at(C.A, x);
      if (beta === gamma) {
        at(P, alpha)[x] = '<identity>';
        at(P, beta)[x ^ 1] = '<identity>';
        gamma++;
        if (homomorphism) tau.set(beta, defined(tau.get(alpha), 'tau').mul(letter));
      } else if (x % 2 === 0 && at(P, alpha)[x] === null) {
        const name = `${String(letter)}_${alpha}`;
        y.push(name);
        at(P, alpha)[x] = name;
        if (homomorphism) genElems.set(name, defined(tau.get(alpha), 'tau').mul(letter).mul(defined(tau.get(beta), 'tau').inverse()));
      }
    }
  }
  const F = new FreeGroup(y.join(', '));
  const schreierGens = [...F.generators];
  C.schreier = { freeGroup: F, generators: schreierGens, ...(homomorphism ? { genElements: genElems } : {}) };
  const out: (FreeGroupElement | null)[][] = P.map((row) => row.map((e) => (typeof e === 'string' ? null : e)));
  P.forEach((row, i) =>
    row.forEach((e, j) => {
      if (e === '<identity>') at(out, i)[j] = F.identity;
      else if (typeof e === 'string') {
        const r = at(schreierGens, y.indexOf(e));
        at(out, i)[j] = r;
        const beta = defined(at(at(C.table, i), j), 'coset table entry');
        at(out, beta)[j + 1] = r.inverse();
      }
    }),
  );
  C.P = out;
}

/**
 * Rewrites the defining relations in terms of the subgroup’s Schreier generators.
 * @param C - The coset table of the subgroup.
 * @see SymPy `sympy.combinatorics.fp_groups.reidemeister_relators`
 */
export function reidemeisterRelators(C: CosetTable): void {
  const R = C.fpGroup.relators;
  let rels: FreeGroupElement[] = [];
  for (const word of R) for (let coset = 0; coset < C.n; coset++) rels.push(reidemeisterRewrite(C, coset, word));
  const order1 = uniqueWords(rels.filter((r) => r.length === 1));
  rels = rels.filter((r) => !hasWord(order1, r)).map((w) => w.eliminateWords(order1, true));
  C.schreier.generators = defined(C.schreier.generators, 'Schreier generators').filter((g) => !(hasWord(order1, g) || hasWord(order1, g.inverse())));
  let i = 0;
  while (i < rels.length) {
    const w = at(rels, i);
    let j = i + 1;
    while (j < rels.length) {
      if (w.isCyclicConjugate(at(rels, j))) rels.splice(j, 1);
      else j++;
    }
    i++;
  }
  C.schreier.relators = rels;
}

/**
 * The word w read from coset alpha, in the Schreier generators.
 * @param C - The coset table of the subgroup.
 * @param alphaIn - The starting coset label.
 * @param w - The group word to scan or rewrite.
 * @returns The resulting group word.
 * @see SymPy `sympy.combinatorics.fp_groups.rewrite`
 * @example
 * ```ts
 * import { FpGroup, cosetEnumerationR, defineSchreierGenerators, freeGroup, reidemeisterRewrite } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * const C = cosetEnumerationR(G, [x]);
 * defineSchreierGenerators(C);
 * String(reidemeisterRewrite(C, 0, x)); // => x_0
 * ```
 */
export function reidemeisterRewrite(C: CosetTable, alphaIn: number, w: FreeGroupElement): FreeGroupElement {
  let alpha = alphaIn;
  let v = defined(C.schreier.freeGroup, 'Schreier free group').identity;
  for (const c of w.letters) {
    const x = 2 * (Math.abs(c) - 1) + (c < 0 ? 1 : 0);
    v = v.mul(defined(at(at(C.P, alpha), x), 'P entry'));
    alpha = defined(at(at(C.table, alpha), x), 'coset table entry');
  }
  return v;
}

/**
 * Eliminate Schreier generators that occur once in a relator.
 * @param C - The coset table of the subgroup.
 * @returns The reduced Schreier generators and defining relators.
 * @see SymPy `sympy.combinatorics.fp_groups.elimination_technique_2`
 * @example
 * ```ts
 * import { FpGroup, cosetEnumerationR, defineSchreierGenerators, eliminationTechnique2, freeGroup, reidemeisterRelators } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * const C = cosetEnumerationR(G, [x]);
 * defineSchreierGenerators(C);
 * reidemeisterRelators(C);
 * eliminationTechnique2(C)[0].map(String); // => [x_0]
 * ```
 */
export function eliminationTechnique2(C: CosetTable): [FreeGroupElement[], FreeGroupElement[]] {
  let rels = sortWords([...defined(C.schreier.relators, 'Reidemeister relators')]).reverse();
  const gens = [...defined(C.schreier.generators, 'Schreier generators')];
  for (let i = gens.length - 1; i >= 0; i--) {
    const rel = at(rels, i);
    for (let j = gens.length - 1; j >= 0; j--) {
      const gen = at(gens, j);
      if (rel.generatorCount(gen) === 1) {
        const k = rel.exponentSum(gen);
        const genIndex = rel.index(gen.pow(k));
        const bk = rel.subword(genIndex + 1, rel.length);
        const fw = rel.subword(0, genIndex);
        const repBy = bk.mul(fw).pow(-k);
        rels.splice(i, 1);
        gens.splice(j, 1);
        rels = rels.map((r) => r.eliminateWord(gen, repBy));
        break;
      }
    }
  }
  C.schreier.relators = rels;
  C.schreier.generators = gens;
  return [gens, rels];
}

function reidemeisterPresentationFull(fpGrp: FpGroup, H: readonly FreeGroupElement[], CIn?: CosetTable, homomorphism = false): { generators: FreeGroupElement[]; relators: FreeGroupElement[]; images?: FreeGroupElement[] } {
  const C = CIn ?? cosetEnumerationR(fpGrp, H);
  C.compress();
  C.standardize();
  defineSchreierGenerators(C, homomorphism);
  reidemeisterRelators(C);
  const [gens, rels] = simplifyPresentation(defined(C.schreier.generators, 'Schreier generators'), defined(C.schreier.relators, 'Reidemeister relators'), true);
  C.schreierGenerators = gens;
  C.reidemeisterRelators = rels;
  if (homomorphism) {
    const elems = defined(C.schreier.genElements, 'Schreier generator elements');
    return { generators: gens, relators: rels, images: gens.map((g) => defined(elems.get(String(g)), 'Schreier generator')) };
  }
  return { generators: gens, relators: rels };
}

/**
 * The
 * presentation of the subgroup generated by H, [generators, relators]
 * (with `homomorphism`, also the generators' images in fp_grp).
 * @param fpGrp - The finitely presented ambient group.
 * @param H - The subgroup or second group in the operation.
 * @param C - The coset table of the subgroup.
 * @param homomorphism - Whether to track the images of subgroup generators in the parent group.
 * @returns The subgroup generators and relators, optionally followed by their images.
 * @see SymPy `sympy.combinatorics.fp_groups.reidemeister_presentation`
 * @example
 * ```ts
 * import { FpGroup, freeGroup, reidemeisterPresentation } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * reidemeisterPresentation(G, [x])[0].map(String); // => [x_0]
 * ```
 */
export function reidemeisterPresentation(fpGrp: FpGroup, H: readonly FreeGroupElement[], C?: CosetTable, homomorphism?: false): [FreeGroupElement[], FreeGroupElement[]];
export function reidemeisterPresentation(fpGrp: FpGroup, H: readonly FreeGroupElement[], C: CosetTable | undefined, homomorphism: true): [FreeGroupElement[], FreeGroupElement[], FreeGroupElement[]];
export function reidemeisterPresentation(fpGrp: FpGroup, H: readonly FreeGroupElement[], C?: CosetTable, homomorphism = false): [FreeGroupElement[], FreeGroupElement[]] | [FreeGroupElement[], FreeGroupElement[], FreeGroupElement[]] {
  const r = reidemeisterPresentationFull(fpGrp, H, C, homomorphism);
  return homomorphism ? [r.generators, r.relators, defined(r.images, 'images')] : [r.generators, r.relators];
}

// ---- group homomorphisms ------------------------------------------------------------------

/** An element of a permutation group or of a finitely presented or free group. */
export type GroupElement = Permutation | FreeGroupElement;
/** The groups homomorphisms are defined between. */
export type HomomorphismGroup = PermutationGroupNode | FpGroup | FreeGroup;

const isElementList = (v: GroupElement | readonly GroupElement[]): v is readonly GroupElement[] => Array.isArray(v);
const isElementMap = (v: ReadonlyMap<GroupElement, GroupElement> | readonly (readonly [GroupElement, GroupElement])[]): v is ReadonlyMap<GroupElement, GroupElement> => v instanceof Map;
const elementKey = (e: GroupElement): string => (e instanceof Permutation ? `p:${e.key}` : `w:${e.key}`);
/** @internal The product of two elements of the same kind of group. */
export function gmul(a: GroupElement, b: GroupElement): GroupElement {
  return a instanceof Permutation ? a.mul(cast2Permutation(b)) : a.mul(wordOf(b));
}
/** @internal An integer power of an element. */
export function gpow(a: GroupElement, n: number): GroupElement {
  return a instanceof Permutation ? a.pow(n) : a.pow(n);
}
/** @internal The inverse of an element. */
export const ginv = (a: GroupElement): GroupElement => a.inverse();
const gequals = (a: GroupElement, b: GroupElement): boolean => elementKey(a) === elementKey(b);
const groupIdentity = (G: HomomorphismGroup): GroupElement => G.identity;
const groupContains = (G: HomomorphismGroup, g: unknown): boolean => (G instanceof PermutationGroupNode ? G.contains(g) : G.contains(g));
/** The order of a group as an integer, or undefined when it is infinite. */
function finiteOrder(G: HomomorphismGroup | FpSubgroup): bigint | undefined {
  const o = G.order();
  if (typeof o === 'bigint') return o;
  return o === S.Infinity ? undefined : BigInt(String(o));
}

/** Elements keyed by value (a Python dict of group elements). */
class ElementMap<V> {
  readonly #m = new Map<string, [GroupElement, V]>();
  get(k: GroupElement): V | undefined {
    return this.#m.get(elementKey(k))?.[1];
  }
  has(k: GroupElement): boolean {
    return this.#m.has(elementKey(k));
  }
  set(k: GroupElement, v: V): void {
    this.#m.set(elementKey(k), [k, v]);
  }
  entries(): [GroupElement, V][] {
    return [...this.#m.values()];
  }
}

/**
 * The homomorphism
 * between groups given by the images of the domain's generators.
 * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism`
 * @example
 * ```ts
 * import { GroupHomomorphism, Perm, PermutationGroup } from '@symjs/symjs';
 * new GroupHomomorphism(PermutationGroup([new Perm([1, 2, 0]), new Perm([2, 1, 0])]), PermutationGroup([new Perm([1, 2, 0]), new Perm([2, 1, 0])]), [[new Perm([1, 2, 0]), new Perm([1, 2, 0])], [new Perm([2, 1, 0]), new Perm([2, 1, 0])]]).isIsomorphism(); // => True
 * ```
 */
export class GroupHomomorphism {
  /**
   * The source group of the homomorphism.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.domain`
   */
  readonly domain: HomomorphismGroup;
  /**
   * The target group of the homomorphism.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.codomain`
   */
  readonly codomain: HomomorphismGroup;
  /** The image of each domain generator under the homomorphism. @internal */
  readonly imageMap: ElementMap<GroupElement>;
  #inverses: ElementMap<GroupElement> | undefined;
  /** The previously computed kernel of the homomorphism. @internal */
  kernelCache: PermutationGroupNode | FpSubgroup | undefined;
  #image: PermutationGroupNode | FpSubgroup | undefined;

  /**
   * Constructs a `GroupHomomorphism`.
   * @param domain - The source group.
   * @param codomain - The target group.
   * @param images - The images of the generators, in matching order.
   */
  constructor(domain: HomomorphismGroup, codomain: HomomorphismGroup, images: ReadonlyMap<GroupElement, GroupElement> | readonly (readonly [GroupElement, GroupElement])[]) {
    this.domain = domain;
    this.codomain = codomain;
    this.imageMap = new ElementMap();
    for (const [k, v] of isElementMap(images) ? [...images] : images) this.imageMap.set(k, v);
  }

  /**
   * Gets the image of each generator.
   * @returns The image of each generator.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.images`
   */
  get images(): Map<GroupElement, GroupElement> {
    return new Map(this.imageMap.entries());
  }

  #invs(): ElementMap<GroupElement> {
    const image = this.image();
    const inverses = new ElementMap<GroupElement>();
    for (const [k, v] of this.imageMap.entries()) if (!(inverses.has(v) || v.isIdentity)) inverses.set(v, k);
    if (image instanceof PermutationGroupNode) {
      for (const g of image.strongGens) {
        if (inverses.has(g) || g.isIdentity) continue;
        let w = groupIdentity(this.domain);
        const parts = [...image.strongGensSlpOf(g)].reverse();
        for (const s of parts) w = inverses.has(s) ? gmul(w, defined(inverses.get(s), 'inverse')) : gmul(w, ginv(defined(inverses.get(s.inverse()), 'inverse')));
        inverses.set(g, w);
      }
    }
    // for a finitely presented codomain the generators of the image are the generators' images, already inverted
    return inverses;
  }

  /**
   * A preimage of an element of the image (or of each element of a list).
   * @param g - The element whose group membership is being tested.
   * @returns The resulting group elements.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.invert`
   */
  invert(g: GroupElement): GroupElement;
  invert(g: readonly GroupElement[]): GroupElement[];
  invert(gIn: GroupElement | readonly GroupElement[]): GroupElement | GroupElement[] {
    if (isElementList(gIn)) return gIn.map((e) => this.invert(e));
    let g = gIn;
    if (this.codomain instanceof FpGroup && g instanceof FreeGroupElement) g = this.codomain.reduce(g);
    const inverses = (this.#inverses ??= this.#invs());
    const image = this.image();
    let w = groupIdentity(this.domain);
    const gens: GroupElement[] = image instanceof PermutationGroupNode ? image.generatorProduct(cast2Permutation(g)).reverse() : wordOf(g).letterFormElm;
    for (const s of gens) {
      w = inverses.has(s) ? gmul(w, defined(inverses.get(s), 'inverse')) : gmul(w, ginv(defined(inverses.get(s.inverse()), 'inverse')));
    }
    return w;
  }

  /**
   * Returns the kernel (a permutation group or an FpSubgroup).
   * @returns The kernel (a permutation group or an FpSubgroup).
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.kernel`
   */
  kernel(): PermutationGroupNode | FpSubgroup {
    return (this.kernelCache ??= this.#computeKernel());
  }

  #computeKernel(): PermutationGroupNode | FpSubgroup {
    const G = this.domain;
    if (G instanceof FreeGroup) throw new NotImplementedError('Kernel computation is not implemented for infinite groups');
    const GOrder = finiteOrder(G);
    if (GOrder === undefined) throw new NotImplementedError('Kernel computation is not implemented for infinite groups');
    const gens: GroupElement[] = [];
    const make = (): PermutationGroupNode | FpSubgroup => (G instanceof PermutationGroupNode ? new PermutationGroupNode(gens.length ? gens.map(cast2Permutation) : [G.identity]) : new FpSubgroup(G, gens.map(wordOf), true));
    let K = make();
    const i = defined(finiteOrder(this.image()), 'image order');
    while (defined(finiteOrder(K), 'kernel order') * i !== GOrder) {
      const r: GroupElement = G.random();
      const k = gmul(r, ginv(this.invert(this.apply(r))));
      const inK = K instanceof PermutationGroupNode ? K.contains(k) : K.contains(wordOf(k));
      if (inK !== true) {
        gens.push(k);
        K = make();
      }
    }
    return K;
  }

  /**
   * Returns the image (a permutation group or an FpSubgroup).
   * @returns The image (a permutation group or an FpSubgroup).
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.image`
   */
  image(): PermutationGroupNode | FpSubgroup {
    if (this.#image === undefined) {
      const values = new ElementMap<GroupElement>();
      for (const [, v] of this.imageMap.entries()) values.set(v, v);
      const vs = values.entries().map(([v]) => v);
      const C = this.codomain;
      if (C instanceof PermutationGroupNode) this.#image = C.subgroup(vs.map(cast2Permutation));
      else this.#image = new FpSubgroup(C, vs.map(wordOf));
    }
    return this.#image;
  }

  /**
   * The image of an element (or of each element of a list).
   * @param elem - The domain element to map.
   * @returns The resulting group elements.
   * @throws RangeError when the element lies outside the domain.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism._apply`
   */
  apply(elem: GroupElement): GroupElement;
  apply(elem: readonly GroupElement[]): GroupElement[];
  apply(elem: GroupElement | readonly GroupElement[]): GroupElement | GroupElement[] {
    if (isElementList(elem)) return elem.map((x) => this.apply(x));
    const e = elem;
    if (!groupContains(this.domain, e)) throw new RangeError('The supplied element does not belong to the domain');
    if (e.isIdentity) return groupIdentity(this.codomain);
    let value = groupIdentity(this.codomain);
    if (this.domain instanceof PermutationGroupNode) {
      for (const g of this.domain.generatorProduct(cast2Permutation(e), true)) {
        const im = this.imageMap.get(g);
        value = im !== undefined ? gmul(im, value) : gmul(ginv(defined(this.imageMap.get(g.inverse()), 'image')), value);
      }
    } else {
      const w = wordOf(e);
      for (const [gi, p] of w.syllables) value = gmul(value, gpow(defined(this.imageMap.get(at(w.group.generators, gi)), 'image'), p));
    }
    return value;
  }

  /**
   * Whether the kernel is trivial.
   * @returns Whether the object is injective.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.is_injective`
   */
  isInjective(): boolean {
    return finiteOrder(this.kernel()) === 1n;
  }

  /**
   * Whether the image is the codomain ('unknown' when both are infinite).
   * @returns Whether every codomain element has a preimage, or `'unknown'` if undecidable.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.is_surjective`
   */
  isSurjective(): boolean | 'unknown' {
    const im = finiteOrder(this.image());
    const oth = finiteOrder(this.codomain);
    if (im === undefined && oth === undefined) return 'unknown';
    return im === oth;
  }

  /**
   * Check if `self` is an isomorphism.
   * @returns Whether the object is isomorphism.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.is_isomorphism`
   */
  isIsomorphism(): boolean {
    return this.isInjective() && this.isSurjective() === true;
  }

  /**
   * Whether the image is trivial.
   * @returns Whether the object is trivial.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.is_trivial`
   */
  isTrivial(): boolean {
    return finiteOrder(this.image()) === 1n;
  }

  /**
   * Returns the composite self∘other.
   * @param other - The value to combine with or compare against.
   * @returns The composite self∘other.
   * @throws RangeError when the preceding map has image outside the domain.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.compose`
   */
  compose(other: GroupHomomorphism): GroupHomomorphism {
    const im = other.image();
    if (!(im instanceof PermutationGroupNode) || !(this.domain instanceof PermutationGroupNode) || !im.isSubgroup(this.domain)) throw new RangeError('The image of `other` must be a subgroup of the domain of `self`');
    return new GroupHomomorphism(other.domain, this.codomain, other.imageMap.entries().map(([g]) => [g, this.apply(other.apply(g))] as const));
  }

  /**
   * Returns the restriction to a subgroup.
   * @param H - The subgroup or second group in the operation.
   * @returns The restriction to a subgroup.
   * @throws RangeError when the supplied subgroup is outside the domain.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.restrict_to`
   */
  restrictTo(H: PermutationGroupNode): GroupHomomorphism {
    if (!(H instanceof PermutationGroupNode) || !(this.domain instanceof PermutationGroupNode) || !H.isSubgroup(this.domain)) throw new RangeError('Given H is not a subgroup of the domain');
    return new GroupHomomorphism(H, this.codomain, H.generators.map((g) => [g, this.apply(g)] as const));
  }

  /**
   * The preimage of a subgroup of the image.
   * @param H - The subgroup or second group in the operation.
   * @returns The resulting permutation group.
   * @throws RangeError when the supplied subgroup is outside the image.
   * @see SymPy `sympy.combinatorics.homomorphisms.GroupHomomorphism.invert_subgroup`
   */
  invertSubgroup(H: PermutationGroupNode): PermutationGroupNode {
    const image = this.image();
    if (!(image instanceof PermutationGroupNode) || !H.isSubgroup(image)) throw new RangeError('Given H is not a subgroup of the image');
    const gens: Permutation[] = [];
    let P = new PermutationGroupNode([image.identity]);
    const kernel = this.kernel();
    for (const h of H.generators) {
      const hi = cast2Permutation(this.invert(h));
      if (!P.contains(hi)) {
        gens.push(hi);
        P = new PermutationGroupNode(gens);
      }
      for (const k of kernel.generators) {
        const kh = gmul(k, hi);
        if (!P.contains(kh)) {
          gens.push(cast2Permutation(kh));
          P = new PermutationGroupNode(gens);
        }
      }
    }
    return P;
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return `GroupHomomorphism(${String(this.domain)}, ${String(this.codomain)})`;
  }
}

/**
 * Constructs the group homomorphism that sends the specified generators to their images and all
 * remaining generators to the identity. By default, it checks that the images satisfy the
 * domain's relators.
 *
 * @see SymPy `sympy.combinatorics.homomorphisms.homomorphism`
 */
export function homomorphismOf(domain: HomomorphismGroup, codomain: HomomorphismGroup, gensIn: readonly GroupElement[], imagesIn: readonly GroupElement[] = [], check = true): GroupHomomorphism {
  if (!(domain instanceof PermutationGroupNode || domain instanceof FpGroup || domain instanceof FreeGroup)) throw new TypeError('The domain must be a group');
  if (!(codomain instanceof PermutationGroupNode || codomain instanceof FpGroup || codomain instanceof FreeGroup)) throw new TypeError('The codomain must be a group');
  const generators: readonly GroupElement[] = domain.generators;
  if (!gensIn.every((g) => generators.some((h) => gequals(g, h)))) throw new RangeError("The supplied generators must be a subset of the domain's generators");
  if (!imagesIn.every((g) => groupContains(codomain, g))) throw new RangeError('The images must be elements of the codomain');
  if (imagesIn.length && imagesIn.length !== gensIn.length) throw new RangeError('The number of images must be equal to the number of generators');
  const gens = [...gensIn];
  const images = [...imagesIn];
  while (images.length < generators.length) images.push(groupIdentity(codomain));
  for (const g of generators) if (!gens.some((h) => gequals(g, h))) gens.push(g);
  const pairs = gens.map((g, i) => [g, at(images, i)] as const);
  const map = new ElementMap<GroupElement>();
  for (const [g, v] of pairs) map.set(g, v);
  if (check && !checkHomomorphism(domain, codomain, map)) throw new RangeError('The given images do not define a homomorphism');
  return new GroupHomomorphism(domain, codomain, map.entries());
}

/** Checks whether the generator images satisfy the relators of the domain's presentation. */
export function checkHomomorphism(domain: HomomorphismGroup, codomain: HomomorphismGroup, images: ElementMap<GroupElement> | ReadonlyMap<GroupElement, GroupElement>): boolean {
  const map = images instanceof ElementMap ? images : (() => {
    const m = new ElementMap<GroupElement>();
    for (const [k, v] of images) m.set(k, v);
    return m;
  })();
  const pres = domain instanceof PermutationGroupNode ? domain.presentation() : domain;
  const rels = pres instanceof FreeGroup ? [] : pres.relators;
  const identity = groupIdentity(codomain);
  const domainGens: readonly GroupElement[] = domain.generators;
  const image = (r: FreeGroupElement): GroupElement => r.syllables.reduce((w, [g, p]) => gmul(w, gpow(defined(map.get(at(domainGens, g)), 'image'), p)), identity);
  for (const r of rels) {
    let s: boolean | 'unknown';
    if (codomain instanceof FpGroup) {
      s = codomain.equals(wordOf(image(r)), wordOf(identity));
      if (s === 'unknown') {
        codomain.makeConfluent();
        s = codomain.equals(wordOf(image(r)), wordOf(identity));
        if (s === 'unknown') throw new RangeError("Can't determine if the images define a homomorphism. Try increasing the maximum number of rewriting rules (group._rewriting_system.set_max(new_value); the current value is stored in group._rewriting_system.maxeqns)");
      }
    } else s = image(r).isIdentity;
    if (s !== true) return false;
  }
  return true;
}
