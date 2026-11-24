// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/pc_groups.py and
// PermutationGroup.polycyclic_group of perm_groups.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.pc_groups: polycyclic groups (a
 * polycyclic generating sequence with its series and relative orders) and
 * the collector, which brings words in the polycyclic generators into their
 * collected normal form.
 */

import { at, cast, defined } from '../core/guard';
import type { Expr } from '../core/nodes';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import { isprime } from '../ntheory/primetest';
import { FreeGroup, FreeGroupElement } from './freegroups';
import { PermutationGroupNode } from './permgroups';
import type { Permutation } from './permutations';

/** A value of the pc presentation: the collected word, or the empty tuple () for the identity (as SymPy prints it). */
export type PcRelatorValue = FreeGroupElement | readonly [];

/**
 * A polycyclic group given by a polycyclic generating sequence.
 * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup`
 */
export class PolycyclicGroup {
  /**
   * Indicates whether the object represents a group.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.is_group`
   */
  readonly isGroup = true;
  /**
   * Indicates whether the group has a terminating derived series.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.is_solvable`
   */
  readonly isSolvable = true;
  /**
   * The polycyclic generating sequence.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.pcgs`
   */
  readonly pcgs: Permutation[];
  /**
   * The subnormal series associated with the generating sequence.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.pc_series`
   */
  readonly pcSeries: PermutationGroupNode[];
  /**
   * The orders of the generators in successive quotients.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.relative_order`
   */
  readonly relativeOrder: bigint[];
  /**
   * The collector for words in the polycyclic generators.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.collector`
   */
  readonly collector: Collector;

  /**
   * Constructs a `PolycyclicGroup`.
   * @param pcSequence - The polycyclic generating sequence.
   * @param pcSeries - The corresponding subnormal series.
   * @param relativeOrder - The generator orders modulo the next subgroup.
   * @param collector - The collector for words in the polycyclic generators.
   */
  constructor(pcSequence: readonly Permutation[], pcSeries: readonly PermutationGroupNode[], relativeOrder: readonly (bigint | number)[], collector?: Collector) {
    this.pcgs = [...pcSequence];
    this.pcSeries = [...pcSeries];
    this.relativeOrder = relativeOrder.map(BigInt);
    this.collector = collector ?? new Collector(this.pcgs, this.pcSeries, this.relativeOrder);
  }

  /**
   * Whether every relative order is prime.
   * @returns Whether the object is prime order.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.is_prime_order`
   */
  isPrimeOrder(): boolean {
    return this.relativeOrder.every((o) => isprime(o));
  }

  /**
   * Returns the length of the polycyclic sequence.
   * @returns The length of the polycyclic sequence.
   * @see SymPy `sympy.combinatorics.pc_groups.PolycyclicGroup.length`
   */
  length(): number {
    return this.pcgs.length;
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return `PolycyclicGroup(${this.pcgs.length})`;
  }
}

/** a/b modulo m (b invertible modulo m), in 0 .. m - 1. */
function modQuotient(a: number, b: number, m: number): number {
  const r = (v: number): number => ((v % m) + m) % m;
  let inv = 1;
  while (r(b * inv) !== 1 % m) inv++;
  return r(a * inv);
}

const isWord = (v: PcRelatorValue): v is FreeGroupElement => !Array.isArray(v);

/** A syllable of a collector word: a symbol and its exponent. */
export type PcSyllable = [Expr, number];

/**
 * The collector of a polycyclic group, on the free group
 * x0, x1, ... of its polycyclic generators.
 * @see SymPy `sympy.combinatorics.pc_groups.Collector`
 * @example
 * ```ts
 * import { Collector, Perm, PermutationGroup } from '@symjs/symjs';
 * new Collector([new Perm([1, 0, 2]), new Perm([2, 0, 1])], [PermutationGroup([new Perm([1, 0, 2]), new Perm([2, 0, 1]), new Perm([1, 2, 0])]), PermutationGroup([new Perm([2, 0, 1])]), PermutationGroup([new Perm([0, 1, 2])])], [2, 3]).depth(new Perm([1, 2, 0])); // => 2
 * ```
 */
export class Collector {
  /**
   * The polycyclic generating sequence.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.pcgs`
   */
  readonly pcgs: Permutation[];
  /**
   * The subnormal series associated with the generating sequence.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.pc_series`
   */
  readonly pcSeries: PermutationGroupNode[];
  /**
   * The orders of the generators in successive quotients.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.relative_order`
   */
  readonly relativeOrder: bigint[];
  /**
   * The free group on the generators.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.free_group`
   */
  readonly freeGroup: FreeGroup;
  /** SymPy index: the position of each symbol of the free group (by symbol key). */
  readonly #index: Map<string, number>;
  /** The pc presentation, keyed by the relator's key. @internal */
  presentationMap = new Map<string, [FreeGroupElement, PcRelatorValue]>();

  /**
   * Constructs a `Collector`.
   * @param pcgs - The polycyclic generating sequence.
   * @param pcSeries - The corresponding subnormal series.
   * @param relativeOrder - The generator orders modulo the next subgroup.
   * @param freeGroup - The free group containing the words.
   */
  constructor(pcgs: readonly Permutation[], pcSeries: readonly PermutationGroupNode[], relativeOrder: readonly (bigint | number)[], freeGroup?: FreeGroup) {
    this.pcgs = [...pcgs];
    this.pcSeries = [...pcSeries];
    this.relativeOrder = relativeOrder.map(BigInt);
    this.freeGroup = freeGroup ?? new FreeGroup(`x:${pcgs.length}`);
    this.#index = new Map(this.freeGroup.symbols.map((s, i) => [s.key, i]));
    this.presentationMap = this.#pcRelators();
  }

  /**
   * Gets the position of each symbol of the free group.
   * @returns The position of each symbol of the free group.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.index`
   */
  get index(): Map<Expr, number> {
    return new Map(this.freeGroup.symbols.map((s, i) => [s, i]));
  }

  /**
   * Gets the power and conjugate relators and their collected values.
   * @returns The power and conjugate relators and their collected values.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.pc_presentation`
   */
  get pcPresentation(): Map<FreeGroupElement, PcRelatorValue> {
    return new Map(this.presentationMap.values());
  }

  #idx(s: Expr): number {
    return defined(this.#index.get(s.key), 'pc generator');
  }

  #re(i: number): number {
    return Number(at(this.relativeOrder, i));
  }

  /**
   * The leftmost minimal subword
   * that is not collected (a power out of range or two generators out of
   * order), as syllables; NoMatch when the word is collected.
   * @param word - The group word to examine.
   * @returns The leftmost minimal subword that is not collected (a power out of range or two generators out of order).
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.minimal_uncollected_subword`
   */
  minimalUncollectedSubword(word: FreeGroupElement): PcSyllable[] | NoMatchResult {
    if (word.isIdentity) return NoMatch;
    const array = word.arrayForm;
    for (const [s1, e1] of array) {
      const re = this.#re(this.#idx(s1));
      if (re && (e1 < 0 || e1 > re - 1)) return [[s1, e1]];
    }
    for (let i = 0; i < array.length - 1; i++) {
      const [s1, e1] = at(array, i);
      const [s2] = at(array, i + 1);
      // a negative exponent was found above (every relative order is positive)
      if (this.#idx(s1) > this.#idx(s2)) return [[s1, e1], [s2, 1]];
    }
    return NoMatch;
  }

  /**
   * Returns the power relators and the conjugate relators, separately.
   * @returns The power relators and the conjugate relators, separately.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.relations`
   */
  relations(): [Map<FreeGroupElement, PcRelatorValue>, Map<FreeGroupElement, PcRelatorValue>] {
    const power = new Map<FreeGroupElement, PcRelatorValue>();
    const conjugate = new Map<FreeGroupElement, PcRelatorValue>();
    for (const [k, v] of this.presentationMap.values()) (k.syllables.length === 1 ? power : conjugate).set(k, v);
    return [power, conjugate];
  }

  /**
   * Returns the start and end of the first occurrence of w in word ((-1, -1) when absent).
   * @param word - The group word to examine.
   * @param w - The group word to scan or rewrite.
   * @returns The start and end of the first occurrence of w in word ((-1, -1) when absent).
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.subword_index`
   */
  subwordIndex(word: FreeGroupElement, w: FreeGroupElement): [number, number] {
    for (let i = 0; i < word.length - w.length + 1; i++) if (word.subword(i, i + w.length).equals(w)) return [i, i + w.length];
    return [-1, -1];
  }

  /**
   * Returns the value of the conjugate relator x_j**-1*x_i*x_j for the subword x_i*x_j.
   * @param w - The group word to scan or rewrite.
   * @returns The value of the conjugate relator x_j**-1*x_i*x_j for the subword x_i*x_j.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.map_relation`
   */
  mapRelation(w: FreeGroupElement): PcRelatorValue {
    const array = w.arrayForm;
    const s1 = at(array, 0)[0];
    const s2 = at(array, 1)[0];
    const key = this.freeGroup.dtype([[s2, -1], [s1, 1], [s2, 1]]);
    return defined(this.presentationMap.get(key.key), 'conjugate relator')[1];
  }

  /**
   * The collected form x0**e0*x1**e1*... of a word.
   * @param wordIn - The group word to examine.
   * @returns The collected form x0**e0*x1**e1*.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.collected_word`
   */
  collectedWord(wordIn: FreeGroupElement): FreeGroupElement {
    const F = this.freeGroup;
    let word = wordIn;
    for (;;) {
      const w = this.minimalUncollectedSubword(word);
      if (isNoMatch(w)) break;
      // w is a subword of word
      const [low, high] = this.subwordIndex(word, F.dtype(w));
      const [s1, e1] = at(w, 0);
      if (w.length === 1) {
        const re = this.#re(this.#idx(s1));
        const q = Math.floor(e1 / re);
        const r = e1 - q * re;
        const key = F.dtype([[s1, re]]);
        const pres = defined(this.presentationMap.get(key.key), 'power relator')[1];
        let replacement: FreeGroupElement | undefined;
        if (isWord(pres)) {
          const [sym, exp] = at(pres.arrayForm, 0);
          replacement = F.dtype([[s1, r], [sym, q * exp]]);
        } else if (r !== 0) replacement = F.dtype([[s1, r]]);
        word = word.eliminateWord(F.dtype(w), replacement);
      }
      if (w.length === 2) {
        const g2 = F.dtype([[at(w, 1)[0], 1]]);
        // a conjugate of a generator is never the identity
        const rel = cast(this.mapRelation(F.dtype(w)), FreeGroupElement, 'conjugate relator');
        const replacement = g2.mul(rel.pow(e1));
        word = word.substitutedWord(low, high, replacement);
      }
    }
    return word;
  }

  /**
   * Returns the pc presentation (power and conjugate relators with their collected values).
   * @returns The pc presentation (power and conjugate relators with their collected values).
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.pc_relators`
   */
  pcRelators(): Map<FreeGroupElement, PcRelatorValue> {
    return new Map(this.#pcRelators().values());
  }

  #pcRelators(): Map<string, [FreeGroupElement, PcRelatorValue]> {
    const F = this.freeGroup;
    const pcRelators = new Map<string, [FreeGroupElement, PcRelatorValue]>();
    const permToFree = new Map<string, FreeGroupElement>();
    this.pcgs.forEach((gen, i) => {
      const s = at(F.generators, i);
      permToFree.set(gen.inverse().key, s.inverse());
      permToFree.set(gen.key, s);
    });
    const free = (g: Permutation): FreeGroupElement => defined(permToFree.get(g.key), 'pc generator');
    const pcgs = [...this.pcgs].reverse();
    const series = [...this.pcSeries].reverse();
    const relOrder = [...this.relativeOrder].reverse();
    const collected: Permutation[] = [];
    const wordOf = (G: PermutationGroupNode, g: Permutation): FreeGroupElement => {
      const l = G.generatorProduct(g, true).reverse();
      return this.collectedWord(l.reduce((w, h) => w.mul(free(h)), F.identity));
    };
    pcgs.forEach((gen, i) => {
      const re = Number(at(relOrder, i));
      const relation = free(gen).pow(re);
      const G = at(series, i);
      let word = wordOf(G, gen.pow(re));
      pcRelators.set(relation.key, [relation, word.isIdentity ? [] : word]);
      this.presentationMap = pcRelators;
      collected.push(gen);
      if (collected.length > 1) {
        const conj = at(collected, collected.length - 1);
        const conjugator = free(conj);
        for (let j = 0; j < collected.length - 1; j++) {
          const conjugated = free(at(collected, j));
          const rel = conjugator.inverse().mul(conjugated).mul(conjugator);
          word = wordOf(G, conj.inverse().mul(at(collected, j)).mul(conj));
          // a conjugate of a generator is never the identity
          pcRelators.set(rel.key, [rel, word]);
          this.presentationMap = pcRelators;
        }
      }
    });
    return pcRelators;
  }

  /**
   * Returns the exponents of the collected word of a group element.
   * @param element - The group element to express in the generating sequence.
   * @returns The exponents of the collected word of a group element.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.exponent_vector`
   */
  exponentVector(element: Permutation): number[] {
    const F = this.freeGroup;
    let G = new PermutationGroupNode([]);
    for (const g of this.pcgs) G = new PermutationGroupNode([g, ...G.generators]);
    const gens = G.generatorProduct(element, true).reverse();
    const permToFree = new Map<string, FreeGroupElement>();
    this.pcgs.forEach((g, i) => {
      const sym = at(F.generators, i);
      permToFree.set(g.inverse().key, sym.inverse());
      permToFree.set(g.key, sym);
    });
    const w = gens.reduce((acc, g) => acc.mul(defined(permToFree.get(g.key), 'pc generator')), F.identity);
    const word = this.collectedWord(w);
    const v = Array<number>(F.rank).fill(0);
    for (const [s, e] of word.arrayForm) v[this.#idx(s)] = e;
    return v;
  }

  /**
   * Finds the one-based position of the leading exponent in the polycyclic sequence.
   * @param element - The group element to express in the generating sequence.
   * @returns The one-based position of the leading exponent in the polycyclic sequence.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.depth`
   */
  depth(element: Permutation): number {
    const v = this.exponentVector(element);
    const i = v.findIndex((x) => x !== 0);
    return i < 0 ? this.pcgs.length + 1 : i + 1;
  }

  /**
   * Finds the exponent of the first generator with a nonzero exponent.
   * @param element - The group element to express in the generating sequence.
   * @returns The leading nonzero exponent, or `NoMatch` for the identity.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.leading_exponent`
   */
  leadingExponent(element: Permutation): number | NoMatchResult {
    const v = this.exponentVector(element);
    const d = this.depth(element);
    return d !== this.pcgs.length + 1 ? at(v, d - 1) : NoMatch;
  }

  /** The leading exponent of an element other than the identity. */
  #lead(element: Permutation): number {
    return at(this.exponentVector(element), this.depth(element) - 1);
  }

  #sift(z: readonly (Permutation | 1)[], g: Permutation): Permutation {
    let h = g;
    let d = this.depth(h);
    for (;;) {
      const k = z[d - 1];
      // SymPy stops at depth < len(pcgs), which skips the last generator of the sequence
      if (!(d <= this.pcgs.length) || k === undefined || k === 1) break;
      // SymPy divides the leading exponents as floats; the quotient is taken modulo the relative order
      const re = this.#re(d - 1);
      h = k.pow(-modQuotient(this.#lead(h), this.#lead(k), re)).mul(h);
      d = this.depth(h);
    }
    return h;
  }

  /**
   * Computes an induced polycyclic generating sequence for the subgroup.
   * @param gensIn - The group generators.
   * @returns An induced polycyclic generating sequence for the subgroup.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.induced_pcgs`
   */
  inducedPcgs(gensIn: readonly Permutation[]): Permutation[] {
    const z: (Permutation | 1)[] = Array<1>(this.pcgs.length).fill(1);
    const G = [...gensIn];
    while (G.length) {
      const g = defined(G.shift(), 'generator');
      const h = this.#sift(z, g);
      const d = this.depth(h);
      // depth len(pcgs) + 1 is the identity (SymPy's d < len(pcgs) also drops the last generator)
      if (d <= this.pcgs.length) {
        for (const gen of z) if (gen !== 1) G.push(h.inverse().mul(gen.inverse()).mul(h).mul(gen));
        z[d - 1] = h;
      }
    }
    return z.filter((gen): gen is Permutation => gen !== 1);
  }

  /**
   * Expresses a group element in the supplied induced polycyclic generating sequence.
   * @param ipcgs - The induced polycyclic generating sequence of the subgroup.
   * @param g - The group element on which to operate.
   * @returns The exponents in the induced sequence, or `false` if the element is outside the subgroup.
   * @see SymPy `sympy.combinatorics.pc_groups.Collector.constructive_membership_test`
   */
  constructiveMembershipTest(ipcgs: readonly Permutation[], g: Permutation): number[] | false {
    const e = Array<number>(ipcgs.length).fill(0);
    let h = g;
    let d = this.depth(h);
    ipcgs.forEach((gen, i) => {
      while (this.depth(gen) === d) {
        // SymPy multiplies the leading exponents; the quotient modulo the relative order is meant
        const f = modQuotient(this.#lead(h), this.#lead(gen), this.#re(d - 1));
        h = gen.pow(-f).mul(h);
        e[i] = f;
        d = this.depth(h);
      }
    });
    return h.isIdentity ? e : false;
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return `Collector(${String(this.freeGroup)})`;
  }
}

/** SymPy PermutationGroup.polycyclic_group(): a solvable permutation group as a PolycyclicGroup. */
export function polycyclicGroupOf(G: PermutationGroupNode): PolycyclicGroup {
  if (!G.isPolycyclic) throw new RangeError('The group must be solvable');
  const der = G.derivedSeries();
  const pcSeries: PermutationGroupNode[] = [at(der, der.length - 1)];
  const pcSequence: Permutation[] = [];
  const relativeOrder: bigint[] = [];
  der.reverse();
  for (let i = 0; i < der.length - 1; i++) {
    let H = at(der, i);
    for (const g of at(der, i + 1).generators) {
      if (!H.contains(g)) {
        H = new PermutationGroupNode([g, ...H.generators]);
        pcSeries.unshift(H);
        pcSequence.unshift(g);
        relativeOrder.unshift(at(pcSeries, 0).order() / at(pcSeries, 1).order());
      }
    }
  }
  return new PolycyclicGroup(pcSequence, pcSeries, relativeOrder);
}
