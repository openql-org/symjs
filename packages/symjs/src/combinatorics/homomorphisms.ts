// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/homomorphisms.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.homomorphisms: group homomorphisms
 * (GroupHomomorphism and homomorphism live in fpgroups.ts, which they share
 * with the finitely presented groups), the homomorphisms of a permutation
 * group given by its action on an orbit or on a block system, and the
 * isomorphism test of finite groups.
 */

import { NotImplementedError } from '../core/errors';
import { at } from '../core/guard';
import { S } from '../core/nodes';
import { igcd } from '../core/numberutils';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { factorint } from '../ntheory/factor';
import type { GroupElement } from './fpgroups';
import type { FreeGroup } from './freegroups';
import { FpGroup, GroupHomomorphism, checkHomomorphism, homomorphismOf, simplifyPresentation } from './fpgroups';
import { SymmetricGroup } from './namedgroups';
import { PermutationGroupNode } from './permgroups';
import { Permutation } from './permutations';


/**
 * Defines a group homomorphism by assigning an image to each generator.
 * @param domain - The source group.
 * @param codomain - The target group.
 * @param gens - The group generators.
 * @param images - The images of the generators, in matching order.
 * @param check - Whether to verify that the images respect the relations.
 * @returns The map determined by the generator images.
 * @see SymPy `sympy.combinatorics.homomorphisms.homomorphism`
 */
export function groupHomomorphism(domain: PermutationGroupNode | FpGroup | FreeGroup, codomain: PermutationGroupNode | FpGroup | FreeGroup, gens: readonly GroupElement[], images: readonly GroupElement[] = [], check = true): GroupHomomorphism {
  return homomorphismOf(domain, codomain, gens, images, check);
}

/**
 * The action of a permutation group on an invariant set omega, into the symmetric group on omega.
 * @param group - The ambient group.
 * @param omegaIn - The invariant set on which the group acts.
 * @returns The induced homomorphism into the permutations of the invariant set.
 * @see SymPy `sympy.combinatorics.homomorphisms.orbit_homomorphism`
 */
export function orbitHomomorphism(group: PermutationGroupNode, omegaIn: Iterable<number>): GroupHomomorphism {
  const omega = [...omegaIn];
  const codomain = SymmetricGroup(omega.length);
  const identity = codomain.identity;
  const images = group.generators.map((g) => [g, identity.mul(new Permutation(omega.map((o) => omega.indexOf(g.call(o)))))] as const);
  group.schreierSimsFromBase(omega);
  const H = new GroupHomomorphism(group, codomain, images);
  const stabs = group.basicStabilizers;
  H.kernelCache = stabs.length > omega.length ? at(stabs, omega.length) : new PermutationGroupNode([group.identity]);
  return H;
}

/**
 * The action of a permutation group
 * on a block system (blocks[i] the representative of the block of i), into
 * the symmetric group on the blocks.
 * @param group - The ambient group.
 * @param blocks - The blocks in placement order.
 * @returns The homomorphism induced on the blocks.
 * @see SymPy `sympy.combinatorics.homomorphisms.block_homomorphism`
 */
export function blockHomomorphism(group: PermutationGroupNode, blocks: readonly number[]): GroupHomomorphism {
  const n = blocks.length;
  let m = 0;
  const p: number[] = [];
  const b: number[] = Array<number>(n).fill(0);
  for (let i = 0; i < n; i++) {
    if (at(blocks, i) === i) {
      p.push(i);
      b[i] = m;
      m++;
    }
  }
  for (let i = 0; i < n; i++) b[i] = at(b, at(blocks, i));
  const codomain = SymmetricGroup(m);
  const images = group.generators.map((g) => [g, new Permutation(Array.from({ length: m }, (_, i) => at(b, g.call(at(p, i)))))] as const);
  return new GroupHomomorphism(group, codomain, images);
}

/** All arrangements of k elements of a list (Python itertools.permutations). */
function* arrangements<T>(items: readonly T[], k: number): Generator<T[]> {
  const n = items.length;
  if (k > n) return;
  const idx = Array.from({ length: n }, (_, i) => i);
  const cycles = Array.from({ length: k }, (_, i) => n - i);
  yield idx.slice(0, k).map((i) => at(items, i));
  for (;;) {
    let i = k - 1;
    for (; i >= 0; i--) {
      cycles[i] = at(cycles, i) - 1;
      if (at(cycles, i) === 0) {
        idx.push(...idx.splice(i, 1));
        cycles[i] = n - i;
      } else {
        const j = at(cycles, i);
        [idx[i], idx[n - j]] = [at(idx, n - j), at(idx, i)];
        yield idx.slice(0, k).map((t) => at(items, t));
        break;
      }
    }
    if (i < 0) return;
  }
}

/** Euler's totient of a positive integer. */
function totient(n: bigint): bigint {
  let t = n;
  for (const [p] of factorint(n)) t = (t / p) * (p - 1n);
  return t;
}

/** The result of group_isomorphism: [true, an isomorphism] or [false, NoMatch] (SymPy (False, None)). */
export type IsomorphismResult = [true, GroupHomomorphism] | [false, NoMatchResult];

/**
 * Tests two finite groups for isomorphism and optionally constructs an isomorphism.
 * @param G - The ambient group.
 * @param H - The subgroup or second group in the operation.
 * @param isomorphism - Whether to construct a map when the groups are isomorphic.
 * @returns The existence test and, if requested, the map or `NoMatch`.
 * @throws TypeError when the supplied group has an unsupported representation.
 * @throws NotImplementedError when the group is infinite.
 * @see SymPy `sympy.combinatorics.homomorphisms.group_isomorphism`
 * @example
 * ```ts
 * import { CyclicGroup, DihedralGroup, groupIsomorphism } from '@symjs/symjs';
 * groupIsomorphism(DihedralGroup(8), CyclicGroup(8), false); // => False
 * ```
 */
export function groupIsomorphism(G: PermutationGroupNode | FpGroup, H: PermutationGroupNode | FpGroup, isomorphism?: true): IsomorphismResult;
export function groupIsomorphism(G: PermutationGroupNode | FpGroup, H: PermutationGroupNode | FpGroup, isomorphism: false): boolean;
export function groupIsomorphism(GIn: PermutationGroupNode | FpGroup, HIn: PermutationGroupNode | FpGroup, isomorphism = true): IsomorphismResult | boolean {
  if (!(GIn instanceof PermutationGroupNode || GIn instanceof FpGroup)) throw new TypeError('The group must be a PermutationGroup or an FpGroup');
  if (!(HIn instanceof PermutationGroupNode || HIn instanceof FpGroup)) throw new TypeError('The group must be a PermutationGroup or an FpGroup');
  let G = GIn;
  let H = HIn;
  if (G instanceof FpGroup && H instanceof FpGroup) {
    const Gs = simplifyPresentation(G);
    const Hs = simplifyPresentation(H);
    G = Gs;
    H = Hs;
    // SymPy compares the generators (relators.sort() is None on both sides)
    if (Gs.generators.length === Hs.generators.length && Gs.generators.every((g, i) => g.equals(at(Hs.generators, i)))) {
      if (!isomorphism) return true;
      return [true, homomorphismOf(Gs, Hs, Gs.generators, Hs.generators)];
    }
  }
  const order = (X: PermutationGroupNode | FpGroup): bigint | undefined => {
    const o = X.order();
    if (typeof o === 'bigint') return o;
    if (o === S.Infinity) return undefined;
    return BigInt(o.toString());
  };
  const gOrder = order(G);
  const hOrder = order(H);
  if (gOrder === undefined) throw new NotImplementedError('Isomorphism methods are not implemented for infinite groups.');
  let Hp: PermutationGroupNode;
  let hIsomorphism: GroupHomomorphism | undefined;
  if (H instanceof FpGroup) {
    if (hOrder === undefined) throw new NotImplementedError('Isomorphism methods are not implemented for infinite groups.');
    [Hp, hIsomorphism] = H.toPermGroup();
  } else Hp = H;
  if (gOrder !== hOrder || G.isAbelian !== H.isAbelian) return isomorphism ? [false, NoMatch] : false;
  if (!isomorphism && igcd(gOrder, totient(gOrder)) === 1n) return true;
  const gens: GroupElement[] = [...G.generators];
  const tried = new Set<string>();
  for (const candidates of [Hp.generators, Hp.elements]) {
    for (const subset of arrangements(candidates, gens.length)) {
      const id = subset.map((p) => p.key).join(' ');
      if (tried.has(id)) continue;
      tried.add(id);
      const images: GroupElement[] = [...subset];
      const map = new Map<GroupElement, GroupElement>(gens.map((g, i) => [g, at(images, i)]));
      if (checkHomomorphism(G, Hp, map)) {
        const ims = hIsomorphism ? hIsomorphism.invert(images) : images;
        const T = homomorphismOf(G, H, G.generators, ims, false);
        if (T.isIsomorphism()) return isomorphism ? [true, T] : true;
      }
    }
  }
  return isomorphism ? [false, NoMatch] : false;
}

/**
 * Whether two finite groups are isomorphic.
 * @param G - The ambient group.
 * @param H - The subgroup or second group in the operation.
 * @returns Whether the object is isomorphic.
 * @see SymPy `sympy.combinatorics.homomorphisms.is_isomorphic`
 * @example
 * ```ts
 * import { Perm, PermutationGroup, isIsomorphic } from '@symjs/symjs';
 * isIsomorphic(PermutationGroup([new Perm([4, 5, 6, 7, 0, 1, 2, 3])]), PermutationGroup([new Perm([1, 0])])); // => True
 * ```
 */
export function isIsomorphic(G: PermutationGroupNode | FpGroup, H: PermutationGroupNode | FpGroup): boolean {
  return groupIsomorphism(G, H, false);
}
