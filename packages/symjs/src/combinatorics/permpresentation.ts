// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/perm_groups.py:
// PermutationGroup.presentation, strong_presentation, _verify and
// _block_verify), Copyright (c) 2006-2023 SymPy Development Team, BSD
// 3-Clause License.

/**
 * @file Finite presentations of permutation groups (SymPy
 * PermutationGroup.presentation and strong_presentation), which use the
 * finitely presented groups, coset tables and homomorphisms; registered on
 * PermutationGroup by the combinatorics entry.
 */

import { at, cast, defined } from '../core/guard';
import { CosetTable } from './cosettable';
import type { GroupElement, GroupHomomorphism } from './fpgroups';
import { FpGroup, homomorphismOf, simplifyPresentation } from './fpgroups';
import { FreeGroup, FreeGroupElement, uniqueWords } from './freegroups';
import { PermutationGroupNode } from './permgroups';
import { Permutation } from './permutations';

const word = (e: GroupElement): FreeGroupElement => cast(e, FreeGroupElement, 'word');
const perm = (e: GroupElement): Permutation => cast(e, Permutation, 'permutation');
const sameSet = (a: ReadonlySet<number>, b: ReadonlySet<number>): boolean => a.size === b.size && [...a].every((x) => b.has(x));

/**
 * Computes a finite presentation from the permutation group's generators and their relations.
 *
 * @see SymPy `sympy.combinatorics.perm_groups.PermutationGroup.presentation`
 */
export function presentationOf(G: PermutationGroupNode, _eliminateGens = true): FpGroup {
  if (G.fpPresentation) return G.fpPresentation;
  const gens = G.generators;
  const lenG = gens.length;
  if (lenG === 1) {
    const order = Number(at(gens, 0).order().toString());
    // SymPy returns the free group of rank 0 for the trivial group
    if (order === 1) return new FpGroup(new FreeGroup([]), []);
    const F = new FreeGroup('x');
    return new FpGroup(F, [at(F.generators, 0).pow(order)]);
  }
  const halfGens = G.order() > 20n ? gens.slice(0, Math.floor((lenG + 1) / 2)) : [];
  const H = new PermutationGroupNode(halfGens.length ? [...halfGens] : []);
  const Hp = presentationOf(H);
  const lenH = Hp.generators.length;
  const C = G.cosetTable(H);
  const n = C.length;
  const F = new FreeGroup(gens.map((_g, i) => `x_${i}`).join(', '));
  const R = homomorphismOf(Hp, F, Hp.generators, F.generators.slice(0, lenH), false);
  const rels = Hp.relators.map((r) => word(R.apply(r)));
  let Gp = new FpGroup(F, rels);
  const T = homomorphismOf(Gp, G, Gp.generators, gens);
  let Cp = new CosetTable(Gp, []);
  Cp.table = Array.from({ length: n }, () => Array<null>(2 * lenG).fill(null));
  const transversal: (FreeGroupElement | undefined)[] = Array<undefined>(n).fill(undefined);
  transversal[0] = Gp.identity;
  for (let i = 0; i < 2 * lenH; i++) at(Cp.table, 0)[i] = 0;
  const letter = (x: number): FreeGroupElement => at(Gp.generators, Math.floor(x / 2)).pow(x % 2 ? -1 : 1);
  let gamma = 1;
  outer: for (let alpha = 0; alpha < n; alpha++) {
    for (let x = 0; x < 2 * lenG; x++) {
      const beta = at(at(C, alpha), x);
      if (beta === gamma) {
        transversal[beta] = defined(transversal[alpha], 'transversal').mul(letter(x));
        at(Cp.table, alpha)[x] = beta;
        at(Cp.table, beta)[x + (x % 2 ? -1 : 1)] = alpha;
        gamma++;
        if (gamma === n) break outer;
      }
    }
  }
  Cp.p = Array.from({ length: n }, (_, i) => i);
  let beta = 0;
  let x = 0;
  while (!Cp.isComplete()) {
    while (at(Cp.table, beta)[x] === at(at(C, beta), x)) {
      x = (x + 1) % (2 * lenG);
      if (x === 0) beta = (beta + 1) % n;
    }
    let newRel = defined(transversal[beta], 'transversal').mul(letter(x)).mul(defined(transversal[at(at(C, beta), x)], 'transversal').inverse());
    const p = perm(T.apply(newRel));
    let nxt = Gp.identity;
    for (const s of H.generatorProduct(p, true)) nxt = nxt.mul(word(T.invert(s)).inverse());
    newRel = newRel.mul(nxt);
    // SymPy _factor_group_by_rels: the relators as a set (here the new one first)
    Gp = new FpGroup(Gp.freeGroup, uniqueWords([newRel, ...Gp.relators]));
    Cp.scanAndFill(0, newRel);
    Cp = Gp.cosetEnumeration([], { strategy: 'coset_table_based', draft: Cp, maxCosets: n, incomplete: true });
  }
  G.fpPresentation = simplifyPresentation(Gp);
  return G.fpPresentation;
}

/**
 * SymPy PermutationGroup._verify(K, phi, z, alpha): relators for this group
 * H = <K, z> from those of K. (SymPy's failure branch catches a ValueError
 * of generator_product that it does not raise.)
 */
function verify(H: PermutationGroupNode, K: PermutationGroupNode, phi: GroupHomomorphism, z: Permutation, alpha: number): FreeGroupElement[] {
  const orbit = H.orbit(alpha);
  const zi = z.inverse();
  const beta = zi.call(alpha);
  const Kbeta = K.stabilizer(beta);
  const gammas = [alpha, beta];
  const orbitTuples = new Map<string, number[]>();
  for (const o of orbit) {
    const t = [...Kbeta.orbit(o)].sort((a, b) => a - b);
    orbitTuples.set(t.join(','), t);
  }
  for (const orb of orbitTuples.values()) if (!gammas.includes(at(orb, 0))) gammas.push(at(orb, 0));
  const betas = [alpha, beta];
  const inv = (g: Permutation): FreeGroupElement => word(phi.invert(g));
  const transversal = new Map<number, FreeGroupElement>([
    [alpha, inv(H.identity)],
    [beta, inv(zi)],
  ]);
  for (const [s, g] of K.orbitTransversal(beta, true)) if (!transversal.has(s)) transversal.set(s, defined(transversal.get(beta), 'transversal').mul(inv(g)));
  let union = new Set([...K.orbit(alpha), ...K.orbit(beta)]);
  while (union.size < orbit.size) {
    for (const gamma of gammas.filter((g) => union.has(g))) {
      const r = z.call(gamma);
      if (!union.has(r)) {
        betas.push(r);
        transversal.set(r, defined(transversal.get(gamma), 'transversal').mul(inv(z)));
        for (const [s, g] of K.orbitTransversal(r, true)) if (!transversal.has(s)) transversal.set(s, defined(transversal.get(r), 'transversal').mul(inv(g)));
        union = new Set([...union, ...K.orbit(r)]);
        break;
      }
    }
  }
  const rels: FreeGroupElement[] = [];
  const addRel = (rel: FreeGroupElement): void => {
    if (!rels.some((r) => r.equals(rel))) rels.push(rel);
  };
  const reduceInK = (relIn: FreeGroupElement): FreeGroupElement => {
    let rel = relIn;
    const p = perm(phi.apply(rel));
    for (const g of K.generatorProduct(p, true)) rel = rel.mul(inv(g).inverse());
    return rel;
  };
  for (const b of betas) {
    const tb = defined(transversal.get(b), 'transversal');
    for (const y of K.stabilizer(b).generators) {
      let newRel = tb;
      for (const g of [...K.generatorProduct(y, true)].reverse()) newRel = newRel.mul(inv(g));
      addRel(reduceInK(newRel.mul(tb.inverse())));
    }
  }
  for (const gamma of gammas) {
    const newRel = defined(transversal.get(gamma), 'transversal').mul(inv(z)).mul(defined(transversal.get(z.call(gamma)), 'transversal').inverse());
    addRel(reduceInK(newRel));
  }
  return rels;
}

/**
 * Computes a presentation on the permutation group's strong generators, named `x_0`, `x_1`, and
 * so on.
 *
 * @see SymPy `sympy.combinatorics.perm_groups.PermutationGroup.strong_presentation`
 */
export function strongPresentationOf(G: PermutationGroupNode): FpGroup {
  const strongGens = G.strongGens;
  const stabs = G.basicStabilizers;
  const base = G.base;
  const F = new FreeGroup(strongGens.map((_g, i) => `x_${i}`).join(', '));
  const phi = homomorphismOf(F, G, F.generators, strongGens);
  let H = new PermutationGroupNode([G.identity]);
  let rels: FreeGroupElement[] = [];
  let intermediateGens: Permutation[] = [];
  let newRels: FreeGroupElement[] = [];
  const inv = (g: Permutation): FreeGroupElement => word(phi.invert(g));
  while (stabs.length) {
    const alpha = defined(base.pop(), 'base point');
    let K = H;
    H = defined(stabs.pop(), 'stabilizer');
    const newGens = H.generators.filter((g) => !K.contains(g));
    if (K.order() === 1n) {
      const z = defined(newGens.pop(), 'generator');
      // SymPy takes F.generators[-1]**order, the last strong generator, which need not be z
      rels = [inv(z).pow(Number(z.order().toString()))];
      intermediateGens = [z];
      K = new PermutationGroupNode(intermediateGens);
    }
    while (newGens.length) {
      const z = defined(newGens.pop(), 'generator');
      intermediateGens = [z, ...intermediateGens];
      const Ks = new PermutationGroupNode(intermediateGens);
      const orbit = Ks.orbit(alpha);
      const orbitK = K.orbit(alpha);
      if (sameSet(orbitK, orbit)) {
        // K contains the stabilizer of alpha below this level, so equal orbits make K = <K, z>: z is
        // in K (SymPy's branch for z outside K, through an orbit representative, is not reached)
        let rel = inv(z);
        for (const g of K.generatorProduct(z, true)) rel = rel.mul(inv(g).inverse());
        newRels = [rel];
      } else if (orbitK.size === 1) {
        newRels = verify(Ks, K, phi, z, alpha);
      } else {
        // SymPy verifies a block system here (_block_verify) and builds an action on the points and
        // the blocks; that construction raises IndexError unless the group is transitive on all
        // points, and without a block system it keeps the previous relators. A presentation on the
        // strong generators by the coset-table method of presentation() is used instead.
        return presentationOf(new PermutationGroupNode([...strongGens]));
      }
      for (const n of newRels) if (!rels.some((r) => r.equals(n))) rels.push(n);
      K = Ks;
    }
  }
  return simplifyPresentation(new FpGroup(F, rels));
}
