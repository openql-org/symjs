// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/util.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.combinatorics.util: helpers for bases and strong
 * generating sets (_base_ordering, _distribute_gens_by_base, _strip, ...).
 */

import { at, getOrThrow } from '../core/guard';
import { isprime } from '../ntheory/primetest';
import type { Permutation } from './permutations';
import { afInvert, afNew, afRmul } from './permutations';

/** A transversal: the coset representative u with base^u = point, for each orbit point. */
export type Transversal = Map<number, Permutation>;

/** Whether the list holds a permutation equal to p (Python `p in list`). */
export const includesPerm = (list: readonly Permutation[], p: Permutation): boolean => list.some((q) => q.key === p.key);

const sameArray = (a: readonly number[], b: readonly number[]): boolean => a.length === b.length && a.every((x, i) => x === b[i]);

/** SymPy _base_ordering(base, degree): the position of each point when the base comes first. */
export function baseOrdering(base: readonly number[], degree: number): number[] {
  const ordering = new Array<number>(degree).fill(0);
  base.forEach((b, i) => (ordering[b] = i));
  let current = base.length;
  for (let i = 0; i < degree; i++) if (!base.includes(i)) ordering[i] = current++;
  return ordering;
}

/** SymPy _check_cycles_alt_sym(perm): whether perm has a cycle of prime length p with n/2 < p < n-2. */
export function checkCyclesAltSym(perm: Permutation): boolean {
  const n = perm.size;
  const af = perm.arrayForm;
  const half = Math.floor(n / 2);
  let totalLen = 0;
  const used = new Set<number>();
  for (let i = 0; i < half; i++) {
    if (used.has(i) || i >= half - totalLen) continue;
    let currentLen = 1;
    used.add(i);
    let j = i;
    while (at(af, j) !== i) {
      currentLen++;
      j = at(af, j);
      used.add(j);
    }
    totalLen += currentLen;
    if (currentLen > half && currentLen < n - 2 && isprime(currentLen)) return true;
  }
  return false;
}

/** SymPy _distribute_gens_by_base(base, gens): the strong generators of each basic stabilizer. */
export function distributeGensByBase(base: readonly number[], gens: readonly Permutation[]): Permutation[][] {
  const baseLen = base.length;
  const degree = at(gens, 0).size;
  const stabs: Permutation[][] = Array.from({ length: baseLen }, () => []);
  let maxStabIndex = 0;
  for (const gen of gens) {
    const af = gen.arrayForm;
    let j = 0;
    while (j < baseLen - 1 && af[at(base, j)] === base[j]) j++;
    if (j > maxStabIndex) maxStabIndex = j;
    for (let k = 0; k <= j; k++) at(stabs, k).push(gen);
  }
  for (let i = maxStabIndex + 1; i < baseLen; i++) at(stabs, i).push(afNew(Array.from({ length: degree }, (_, k) => k)));
  return stabs;
}

/**
 * SymPy _orbit_transversal(degree, generators, alpha, pairs=True, slp=True):
 * the orbit points with their representatives (in breadth-first order) and
 * the straight-line programs (generator indices) that give them.
 */
export function orbitTransversalPairs(degree: number, generators: readonly Permutation[], alpha: number): { tr: [number, number[]][]; slp: Map<number, number[]> } {
  const tr: [number, number[]][] = [[alpha, Array.from({ length: degree }, (_, i) => i)]];
  const slp = new Map<number, number[]>([[alpha, []]]);
  const used = new Array<boolean>(degree).fill(false);
  used[alpha] = true;
  const gens = generators.map((g) => g.arrayForm);
  for (let k = 0; k < tr.length; k++) {
    const [x, px] = at(tr, k);
    const pxSlp = getOrThrow(slp, x);
    for (const gen of gens) {
      const temp = at(gen, x);
      if (!used[temp]) {
        // SymPy records gens.index(gen): the first generator equal to gen
        slp.set(temp, [gens.findIndex((g) => sameArray(g, gen)), ...pxSlp]);
        tr.push([temp, afRmul(gen, px)]);
        used[temp] = true;
      }
    }
  }
  return { tr, slp };
}

/** SymPy _orbits_transversals_from_bsgs(base, strong_gens_distr): the basic orbits and transversals. */
export function orbitsTransversalsFromBsgs(base: readonly number[], strongGensDistr: readonly (readonly Permutation[])[]): { basicOrbits: number[][]; transversals: Transversal[]; slps: Map<number, number[]>[] } {
  const degree = at(at(strongGensDistr, 0), 0).size;
  const basicOrbits: number[][] = [];
  const transversals: Transversal[] = [];
  const slps: Map<number, number[]>[] = [];
  base.forEach((b, i) => {
    const { tr, slp } = orbitTransversalPairs(degree, at(strongGensDistr, i), b);
    transversals.push(new Map(tr.map(([x, y]) => [x, afNew(y)])));
    slps.push(slp);
    basicOrbits.push(tr.map(([x]) => x));
  });
  return { basicOrbits, transversals, slps };
}

/** SymPy _handle_precomputed_bsgs: the transversals, basic orbits and distributed generators of a BSGS. */
export function handlePrecomputedBsgs(base: readonly number[], strongGens: readonly Permutation[], transversalsIn?: readonly Transversal[], basicOrbitsIn?: readonly number[][], strongGensDistrIn?: readonly Permutation[][]): { transversals: Transversal[]; basicOrbits: number[][]; strongGensDistr: Permutation[][] } {
  const strongGensDistr = strongGensDistrIn ? strongGensDistrIn.map((x) => [...x]) : distributeGensByBase(base, strongGens);
  if (transversalsIn === undefined) {
    const { basicOrbits, transversals } = orbitsTransversalsFromBsgs(base, strongGensDistr);
    return { transversals, basicOrbits: basicOrbitsIn ? basicOrbitsIn.map((o) => [...o]) : basicOrbits, strongGensDistr };
  }
  const basicOrbits = basicOrbitsIn ? basicOrbitsIn.map((o) => [...o]) : transversalsIn.map((t) => [...t.keys()]);
  return { transversals: [...transversalsIn], basicOrbits, strongGensDistr };
}

/** The orbit of alpha under the generators, in breadth-first order (SymPy _orbit for one point, as a list). */
export function orbitList(degree: number, generators: readonly Permutation[], alpha: number): number[] {
  const gens = generators.map((g) => g.arrayForm);
  const orb = [alpha];
  const used = new Array<boolean>(degree).fill(false);
  used[alpha] = true;
  for (let k = 0; k < orb.length; k++) {
    const b = at(orb, k);
    for (const gen of gens) {
      const temp = at(gen, b);
      if (!used[temp]) {
        orb.push(temp);
        used[temp] = true;
      }
    }
  }
  return orb;
}

const sameSet = (a: readonly number[], b: readonly number[]): boolean => a.length === b.length && new Set([...a, ...b]).size === a.length;

/** SymPy _remove_gens(base, strong_gens): a strong generating set without redundant generators. */
export function removeGens(base: readonly number[], strongGens: readonly Permutation[], basicOrbitsIn?: readonly number[][], strongGensDistrIn?: readonly Permutation[][]): Permutation[] {
  const degree = at(strongGens, 0).size;
  const strongGensDistr = strongGensDistrIn ? strongGensDistrIn.map((x) => [...x]) : distributeGensByBase(base, strongGens);
  const basicOrbits = basicOrbitsIn ?? base.map((b, i) => orbitList(degree, at(strongGensDistr, i), b));
  strongGensDistr.push([]);
  const res = [...strongGens];
  const removeFrom = (list: Permutation[], g: Permutation): void => {
    list.splice(list.findIndex((q) => q.key === g.key), 1);
  };
  for (let i = base.length - 1; i >= 0; i--) {
    const gensCopy = [...at(strongGensDistr, i)];
    for (const gen of at(strongGensDistr, i)) {
      if (includesPerm(at(strongGensDistr, i + 1), gen)) continue;
      const tempGens = [...gensCopy];
      removeFrom(tempGens, gen);
      if (tempGens.length === 0) continue;
      if (sameSet(orbitList(degree, tempGens, at(base, i)), at(basicOrbits, i))) {
        removeFrom(gensCopy, gen);
        removeFrom(res, gen);
      }
    }
  }
  return res;
}

/** SymPy _strip(g, base, orbits, transversals): the residue of sifting g and the level where it stopped. */
export function strip(g: Permutation, base: readonly number[], orbits: readonly (readonly number[])[], transversals: readonly Transversal[]): [Permutation, number] {
  let h = g.arrayForm;
  for (let i = 0; i < base.length; i++) {
    const beta = at(h, at(base, i));
    if (beta === base[i]) continue;
    if (!at(orbits, i).includes(beta)) return [afNew(h), i + 1];
    h = afRmul(afInvert(getOrThrow(at(transversals, i), beta).arrayForm), h);
  }
  return [afNew(h), base.length + 1];
}

/**
 * SymPy _strip_af(h, base, orbits, transversals, j, slp, slps) on array
 * forms, starting after level j; the residue is false when it becomes the
 * identity at a transversal element. The straight-line program is tracked
 * as in SymPy: entries [level, index] or [level, [index]] for an inverse.
 */
export function stripAf(hIn: number[], base: readonly number[], orbits: readonly (readonly number[])[], transversals: readonly (ReadonlyMap<number, number[]>)[], j: number, slpIn: SlpEntry[], slps: readonly (ReadonlyMap<number, number[]>)[]): [number[] | false, number, SlpEntry[]] {
  let h = hIn;
  let slp = slpIn;
  for (let i = j + 1; i < base.length; i++) {
    const beta = at(h, at(base, i));
    if (beta === base[i]) continue;
    if (!at(orbits, i).includes(beta)) return [h, i + 1, slp];
    const u = getOrThrow(at(transversals, i), beta);
    if (sameArray(h, u)) return [false, base.length + 1, slp];
    h = afRmul(afInvert(u), h);
    const uSlp = [...getOrThrow(at(slps, i), beta)].reverse().map((g): SlpEntry => [i, [g]]);
    slp = [...uSlp, ...slp];
  }
  return [h, base.length + 1, slp];
}

/** A straight-line program step: generator `index` of basic stabilizer `level`, or its inverse ([index]). */
export type SlpEntry = [number, number | [number]];

/** SymPy _strong_gens_from_distr(strong_gens_distr): the strong generators of the first two levels, in order. */
export function strongGensFromDistr(strongGensDistr: readonly (readonly Permutation[])[]): Permutation[] {
  const result = [...at(strongGensDistr, 0)];
  if (strongGensDistr.length === 1) return result;
  for (const gen of at(strongGensDistr, 1)) if (!includesPerm(result, gen)) result.push(gen);
  return result;
}

