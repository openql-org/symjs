// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy 1.14 combinatorics/tensor_can.py (and the helpers it uses from
// combinatorics/perm_groups.py, combinatorics/util.py and combinatorics/testutil.py), BSD-3-Clause; see LICENSE.

/**
 * @file Butler–Portugal tensor canonicalization (SymPy sympy.combinatorics.tensor_can).
 *
 * SymPy keeps this module in sympy.combinatorics; it is ported here, next to
 * the abstract tensors that are its only user, and works on array forms
 * (`number[]`) of permutations. A permutation of a tensor of `n` indices has
 * size `n + 2`: the last two points carry the sign.
 */

import { at, defined, last } from '../core/guard';

/** A permutation in array form. */
export type Af = number[];

/** SymPy _af_rmul(a, b): the product a*b in array form ([a[i] for i in b]). */
export function afRmul(a: readonly number[], b: readonly number[]): Af {
  return b.map((i) => at(a, i));
}

/** SymPy _af_invert. */
export function afInvert(a: readonly number[]): Af {
  const inv: Af = Array.from({ length: a.length }, () => 0);
  a.forEach((v, i) => {
    inv[v] = i;
  });
  return inv;
}

const range = (n: number, start = 0): number[] => Array.from({ length: n - start }, (_, i) => i + start);
const sameAf = (a: readonly number[], b: readonly number[]): boolean => a.length === b.length && a.every((v, i) => v === b[i]);
const isIdentity = (a: readonly number[]): boolean => a.every((v, i) => v === i);

/** Python list comparison of integer lists: negative when a < b. */
export function compareLists(a: readonly number[], b: readonly number[]): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) if (at(a, i) !== at(b, i)) return at(a, i) - at(b, i);
  return a.length - b.length;
}

/** SymPy _orbit(degree, generators, alpha): the orbit of a point. */
function orbit(gens: readonly Af[], alpha: number): Set<number> {
  const orb = [alpha];
  const used = new Set(orb);
  for (let k = 0; k < orb.length; k++) {
    for (const gen of gens) {
      const temp = at(gen, at(orb, k));
      if (!used.has(temp)) {
        orb.push(temp);
        used.add(temp);
      }
    }
  }
  return used;
}

/** SymPy _orbit_transversal(degree, generators, alpha, pairs=True, af=True): (point, transversal element) in BFS order. */
function orbitTransversal(degree: number, gens: readonly Af[], alpha: number): [number, Af][] {
  const tr: [number, Af][] = [[alpha, range(degree)]];
  const used = new Set([alpha]);
  for (let k = 0; k < tr.length; k++) {
    const [x, px] = at(tr, k);
    for (const gen of gens) {
      const temp = at(gen, x);
      if (!used.has(temp)) {
        tr.push([temp, afRmul(gen, px)]);
        used.add(temp);
      }
    }
  }
  return tr;
}

/** SymPy _distribute_gens_by_base: the generators of each basic stabilizer. */
function distributeGensByBase(base: readonly number[], gens: readonly Af[]): Af[][] {
  const baseLen = base.length;
  const degree = at(gens, 0).length;
  const stabs: Af[][] = base.map(() => []);
  let maxStabIndex = 0;
  for (const gen of gens) {
    let j = 0;
    while (j < baseLen - 1 && at(gen, at(base, j)) === at(base, j)) j++;
    if (j > maxStabIndex) maxStabIndex = j;
    for (let k = 0; k <= j; k++) at(stabs, k).push(gen);
  }
  for (let i = maxStabIndex + 1; i < baseLen; i++) at(stabs, i).push(range(degree));
  return stabs;
}

/** SymPy get_transversals(base, gens): the basic transversals of a BSGS (point -> array form, in BFS order). */
export function getTransversals(base: readonly number[], gens: readonly Af[]): Map<number, Af>[] {
  if (!base.length) return [];
  const stabs = distributeGensByBase(base, gens);
  const degree = at(at(stabs, 0), 0).length;
  return base.map((b, i) => new Map(orbitTransversal(degree, at(stabs, i), b)));
}

/** SymPy _strip_af (without straight-line programs): the sifted element and its level, or false when it sifts to the identity. */
function stripAf(h0: Af, base: readonly number[], orbits: readonly Set<number>[], transversals: readonly Map<number, Af>[], j: number): [Af, number] | false {
  let h = h0;
  const baseLen = base.length;
  for (let i = j + 1; i < baseLen; i++) {
    const beta = at(h, at(base, i));
    if (beta === at(base, i)) continue;
    if (!at(orbits, i).has(beta)) return [h, i + 1];
    const u = defined(at(transversals, i).get(beta));
    if (sameAf(h, u)) return false;
    h = afRmul(afInvert(u), h);
  }
  return [h, baseLen + 1];
}

/** SymPy PermutationGroup.schreier_sims_incremental(base, gens): a base and a strong generating set. */
export function schreierSimsIncremental(gens: readonly Af[], baseIn: readonly number[] = []): [number[], Af[]] {
  const degree = at(gens, 0).length;
  if (gens.length === 1 && isIdentity(at(gens, 0))) return [[...baseIn], [...gens]];
  const base = [...baseIn];
  const gensX = gens.filter((g) => !isIdentity(g));
  // make sure no generator fixes all base points
  for (const gen of gensX) {
    if (base.every((x) => at(gen, x) === x)) base.push(range(degree).findIndex((p) => at(gen, p) !== p));
  }
  const distr = distributeGensByBase(base, gensX);
  const newGens: Af[] = [];
  const transversals: Map<number, Af>[] = [];
  const orbs: Set<number>[] = [];
  const update = (l: number): void => {
    transversals[l] = new Map(orbitTransversal(degree, at(distr, l), at(base, l)));
    orbs[l] = new Set(at(transversals, l).keys());
  };
  for (let l = 0; l < base.length; l++) update(l);
  let i = base.length - 1;
  while (i >= 0) {
    let restart = false;
    const db = new Map<number, Af>();
    search: for (const [beta, uBeta] of [...at(transversals, i)]) {
      for (const gen of at(distr, i)) {
        const gb = at(gen, beta);
        const u1 = defined(at(transversals, i).get(gb));
        const g1 = afRmul(gen, uBeta);
        if (sameAf(g1, u1)) continue;
        let u1Inv = db.get(gb);
        if (!u1Inv) {
          u1Inv = afInvert(u1);
          db.set(gb, u1Inv);
        }
        const stripped = stripAf(afRmul(u1Inv, g1), base, orbs, transversals, i);
        if (stripped === false) continue;
        const [h, j] = stripped;
        if (j > base.length) {
          // h fixes all base points
          let moved = 0;
          while (at(h, moved) === moved) moved++;
          base.push(moved);
          distr.push([]);
        }
        newGens.push(h);
        for (let l = i + 1; l < j; l++) {
          at(distr, l).push(h);
          update(l);
        }
        i = j - 1;
        restart = true;
        break search;
      }
    }
    if (!restart) i--;
  }
  return [base, [...gensX, ...newGens]];
}

/** SymPy PermutationGroup.pointwise_stabilizer(points): generators of the stabilizer. */
function pointwiseStabilizer(gens: readonly Af[], points: readonly number[]): Af[] {
  const [, strong] = schreierSimsIncremental(gens, points);
  const stab = strong.filter((g) => points.every((p) => at(g, p) === p));
  return stab.length ? stab : [range(at(gens, 0).length)];
}

/** SymPy _is_minimal_bsgs: the base is the lexicographically smallest one. */
function isMinimalBsgs(base: readonly number[], gens: readonly Af[]): boolean {
  const base1: number[] = [];
  let sgs1 = [...gens];
  for (let i = 0; i < at(gens, 0).length; i++) {
    if (!sgs1.every((h) => at(h, i) === i)) {
      base1.push(i);
      sgs1 = sgs1.filter((h) => at(h, i) === i);
    }
  }
  return sameAf(base1, base);
}



/** SymPy dummy_sgs(dummies, sym, n): the strong generating set of the dummy-index group. */
export function dummySgs(dummies: readonly number[], sym: 0 | 1 | null, n: number): Af[] {
  if (dummies.length > n) throw new RangeError('List too large');
  const res: Af[] = [];
  // exchange of contravariant and covariant indices
  if (sym !== null) {
    for (let k = 0; k < dummies.length; k += 2) {
      const j = at(dummies, k);
      const a = range(n + 2);
      if (sym === 1) [a[n], a[n + 1]] = [n + 1, n];
      [a[j], a[j + 1]] = [at(a, j + 1), at(a, j)];
      res.push(a);
    }
  }
  // rename dummy indices
  for (let k = 0; k < dummies.length - 3; k += 2) {
    const j = at(dummies, k);
    const a = range(n + 2);
    a.splice(j, 4, j + 2, j + 3, j, j + 1);
    res.push(a);
  }
  return res;
}

/** SymPy _min_dummies: each dummy index replaced by the smallest dummy of its type. */
function minDummies(dummies: readonly number[][], indices: readonly number[]): number[] {
  const m = dummies.map((dx) => (dx.length ? Math.min(...dx) : -1));
  return indices.map((i) => {
    const j = dummies.findIndex((dx) => dx.includes(i));
    return j < 0 ? i : at(m, j);
  });
}

/** SymPy _dumx_remove: the pair of p0 removed from the dummy lists. */
function dumxRemove(dumx: number[][], p0: number): void {
  for (const dx of dumx) {
    const k = dx.indexOf(p0);
    if (k < 0) continue;
    const paired = k % 2 === 0 ? at(dx, k + 1) : at(dx, k - 1);
    dx.splice(dx.indexOf(p0), 1);
    dx.splice(dx.indexOf(paired), 1);
  }
}

/** SymPy transversal2coset: the coset representatives of each slot (the identity for slots not in the base). */
function transversal2coset(size: number, base: readonly number[], transversal: readonly Map<number, Af>[]): Af[][] {
  const a: Af[][] = [];
  let j = 0;
  for (let i = 0; i < size; i++) {
    if (base.includes(i)) a.push([...at(transversal, j++).values()].sort(compareLists));
    else a.push([range(size)]);
  }
  let k = a.length - 1;
  while (at(a, k).length === 1 && isIdentity(at(at(a, k), 0))) k--;
  return a.slice(0, k + 1);
}

/**
 * SymPy double_coset_can_rep(dummies, sym, b_S, sgens, S_transversals, g):
 * the canonical representative of the double coset D*g*S, or 0 when the
 * tensor vanishes.
 */
export function doubleCosetCanRep(dummies: readonly number[][], sym: readonly (0 | 1 | null)[], bSIn: readonly number[], sgens: readonly Af[], sTransversals: readonly Map<number, Af>[], g: Af): Af | 0 {
  const size = g.length;
  const numDummies = size - 2;
  const indices = range(numDummies);
  const allMetricsWithSym = sym.every((s) => s !== null);
  const numTypes = sym.length;
  const dumx = dummies.map((d) => [...d]);
  const bS = [...bSIn];
  let sgensx = sgens.map((h) => [...h]);
  const sCosets = bS.length ? transversal2coset(size, bS, sTransversals) : [];
  const dummyGens = (): Af[] => range(numTypes).flatMap((i) => dummySgs(at(dumx, i), at(sym, i), numDummies));
  let dsgsx = dummyGens();
  const idn = range(size);
  // TAB = list of entries (s, d, h) where h = d*g*s
  let TAB: [Af, Af, Af][] = [[idn, idn, g]];
  for (let b = 0; b < size - 2; b++) {
    const testb = bS.includes(b) && sgensx.length > 0;
    const deltab = testb ? [...orbit(sgensx, b)].sort((x, y) => x - y) : [b];
    // p1 = min(IMAGES) = min(Union D_p*h*deltab for h in TAB)
    const md = allMetricsWithSym ? minDummies(dumx, indices) : range(numDummies).map((ii) => Math.min(...orbit(dsgsx, ii)));
    const minImage = (h: Af): number => Math.min(...deltab.map((x) => at(md, at(h, x))));
    const pI = Math.min(...TAB.map(([, , h]) => minImage(h)));
    const dxtrav = dsgsx.length ? orbitTransversal(size, dsgsx, pI).map(([, x]) => afInvert(x)) : undefined;
    // the orbit of p_i
    let deltap = [pI];
    for (let ii = 0; ii < numTypes; ii++) {
      const dx = at(dumx, ii);
      if (dx.includes(pI)) {
        deltap = at(sym, ii) !== null ? dx : dx.filter((_, k) => k % 2 === dx.indexOf(pI) % 2);
        break;
      }
    }
    const TAB1: [Af, Af, Af][] = [];
    while (TAB.length) {
      const [s, d, h] = defined(TAB.pop());
      if (minImage(h) !== pI) continue;
      const deltab1 = deltab.filter((x) => at(md, at(h, x)) === pI);
      // NEXT = s*deltab1 intersection (d*g)**-1*deltap
      const dg = afRmul(d, g);
      const dginv = afInvert(dg);
      const sdeltab = deltab1.map((x) => at(s, x));
      const gdeltap = deltap.map((x) => at(dginv, x));
      for (const j of sdeltab.filter((x) => gdeltap.includes(x))) {
        // solve s1*b = j with s1 = s*sx for some element sx of the stabilizer of ..., base[i-1]
        // (j is in the basic orbit of b, so a coset representative exists)
        const s1 = testb ? defined(at(sCosets, b).find((hh) => at(s, at(hh, b)) === j), 'a coset representative').map((ix) => at(s, ix)) : s;
        // solve d1*g*j = p_i with d1 = dx*d for some element dx of the stabilizer of ..., p_{i-1}
        // (d*g*j is in the orbit of p_i under the dummy group; without dummy generators it is p_i)
        const d1 = dxtrav ? defined(dxtrav.find((hh) => at(hh, at(dg, j)) === pI), 'a dummy transversal element') : idn;
        const d2 = d.map((ix) => at(d1, ix));
        const h1 = s1.map((ix) => at(d2, at(g, ix)));
        TAB1.push([s1, d2, h1]);
      }
    }
    // if TAB contains equal permutations, keep only one of them;
    // if TAB contains equal permutations up to the sign, return 0
    TAB1.sort((x, y) => compareLists(x[2], y[2]));
    let prev: Af = Array.from({ length: size }, () => 0);
    TAB = [];
    while (TAB1.length) {
      const entry = defined(TAB1.pop());
      const h = entry[2];
      if (sameAf(h.slice(0, -2), prev.slice(0, -2))) {
        if (last(h) !== last(prev)) return 0;
      } else TAB.push(entry);
      prev = h;
    }
    // stabilize the SGS
    sgensx = sgensx.filter((h) => at(h, b) === b);
    const k = bS.indexOf(b);
    if (k >= 0) bS.splice(k, 1);
    dumxRemove(dumx, pI);
    dsgsx = dummyGens();
  }
  return at(at(TAB, 0), 2);
}

/** SymPy canonical_free(base, gens, g, num_free): the minimal tensor under slot symmetries with free indices only. */
export function canonicalFree(base: readonly number[], gens: readonly Af[], g: Af, numFree: number): Af {
  if (!base.length) return [...g];
  const size = g.length;
  let h = g;
  for (const transv of getTransversals(base, gens)) {
    let hI: number[] = Array.from({ length: numFree }, () => size);
    let s: Af | undefined;
    for (const sk of transv.values()) {
      const h1 = afRmul(h, sk);
      const hi = range(numFree).map((ix) => h1.indexOf(ix));
      if (compareLists(hi, hI) < 0) {
        hI = hi;
        s = sk;
      }
    }
    if (s) h = afRmul(h, s);
  }
  return h;
}

/** SymPy perm_af_direct_product(gens1, gens2, signed=True). */
function permAfDirectProduct(gens1: readonly Af[], gens2: readonly Af[]): Af[] {
  const n1 = at(gens1, 0).length - 2;
  const n2 = at(gens2, 0).length - 2;
  const start = range(n1);
  const end = range(n1 + n2, n1);
  return [
    ...gens1.map((gen) => [...gen.slice(0, -2), ...end, at(gen, gen.length - 2) + n2, last(gen) + n2]),
    ...gens2.map((gen) => [...start, ...gen.map((x) => x + n1)]),
  ];
}

/** SymPy bsgs_direct_product(base1, gens1, base2, gens2, signed=True): the BSGS of the direct product. */
export function bsgsDirectProduct(base1: readonly number[], gens1: readonly Af[], base2: readonly number[], gens2: readonly Af[]): [number[], Af[]] {
  const n1 = at(gens1, 0).length - 2;
  const base = [...base1, ...base2.map((x) => x + n1)];
  const gens = permAfDirectProduct(gens1, gens2).filter((h) => !isIdentity(h));
  return [base, gens.length ? gens : [range(n1 + at(gens2, 0).length)]];
}

/** SymPy get_symmetric_group_sgs(n, antisym): the minimal BSGS of the (anti)symmetric group of n slots. */
export function getSymmetricGroupSgs(n: number, antisym = false): [number[], Af[]] {
  if (n === 1) return [[], [range(3)]];
  const gens = range(n - 1).map((i) => {
    const a = range(n + 2);
    [a[i], a[i + 1]] = [i + 1, i];
    if (antisym) [a[n], a[n + 1]] = [n + 1, n];
    return a;
  });
  return [range(n - 1), gens];
}

/** SymPy riemann_bsgs: the BSGS of the Riemann tensor symmetry. */
export const riemannBsgs = (): [number[], Af[]] => [
  [0, 2],
  [
    [1, 0, 2, 3, 5, 4],
    [0, 1, 3, 2, 5, 4],
    [2, 3, 0, 1, 4, 5],
  ],
];

/** The slot symmetry of `n` copies of one component tensor: (base, generators, free slots of each copy, commutation sign). */
type TensorGens = [number[], Af[], number[][], 0 | 1 | null];

/** SymPy tensor_gens(base, gens, list_free_indices, sym): the BSGS of n equal tensors. */
function tensorGens(base: readonly number[], gens: readonly Af[], listFreeIndices: readonly number[][], sym: 0 | 1 | null): [number, number[], Af[]] {
  const getBsgs = (freeIndices: readonly number[]): [number[], Af[]] => {
    if (!freeIndices.length) return [[...base], [...gens]];
    return schreierSimsIncremental(pointwiseStabilizer(gens, freeIndices));
  };
  // if not base there is no slot symmetry for the component tensors;
  // with fewer than two copies without fixed indices there is no commutation symmetry
  if (!base.length && listFreeIndices.filter((f) => !f.length).length < 2) {
    const size = listFreeIndices.length * (at(gens, 0).length - 2) + 2;
    return [size, [], [range(size)]];
  }
  const noFree: number[][] = [];
  let size = at(gens, 0).length;
  const idAf = range(size);
  const numIndices = size - 2;
  if (!at(listFreeIndices, 0).length) noFree.push(range(numIndices));
  let [resBase, resGens] = getBsgs(at(listFreeIndices, 0));
  for (let i = 1; i < listFreeIndices.length; i++) {
    const [base1, gens1] = getBsgs(at(listFreeIndices, i));
    [resBase, resGens] = bsgsDirectProduct(resBase, resGens, base1, gens1);
    if (!at(listFreeIndices, i).length) noFree.push(range(size - 2 + numIndices, size - 2));
    size += numIndices;
  }
  const nr = size - 2;
  resGens = resGens.filter((h) => !sameAf(h, idAf));
  // if sym there are no commuting tensors stop here
  if (sym === null || !noFree.length) return [size, resBase, resGens.length ? resGens : [idAf]];
  // the slot symmetry group is S = P*C, where C is the group to (anti)commute the component tensors with no free indices
  const baseComm: number[] = [];
  for (let i = 0; i < noFree.length - 1; i++) {
    const ind1 = at(noFree, i);
    const ind2 = at(noFree, i + 1);
    const a = [...range(at(ind1, 0)), ...ind2, ...ind1, ...range(nr, last(ind2) + 1)];
    baseComm.push(at(ind1, 0));
    a.push(...(sym === 0 ? [nr, nr + 1] : [nr + 1, nr]));
    resGens.push(a);
  }
  resBase = [...resBase];
  for (const i of baseComm) if (!resBase.includes(i)) resBase.push(i);
  resBase.sort((x, y) => x - y);
  return [size, resBase, resGens];
}

/** SymPy gens_products(*v): the BSGS of the product of the component tensors. */
function gensProducts(v: readonly TensorGens[]): [number, number[], Af[]] {
  let [, resBase, resGens] = tensorGens(...at(v, 0));
  for (let i = 1; i < v.length; i++) {
    const [, base, gens] = tensorGens(...at(v, i));
    [resBase, resGens] = bsgsDirectProduct(resBase, resGens, base, gens);
  }
  const resSize = at(resGens, 0).length;
  const nonId = resGens.filter((h) => !isIdentity(h));
  return [resSize, resBase, nonId.length ? nonId : [range(resSize)]];
}

/** SymPy _get_map_slots. */
function getMapSlots(size: number, fixedSlots: readonly number[]): number[] {
  const res = range(size);
  let pos = 0;
  for (let i = 0; i < size; i++) {
    if (fixedSlots.includes(i)) continue;
    res[i] = pos++;
  }
  return res;
}

/** SymPy _lift_sgens. */
function liftSgens(size: number, fixedSlots: readonly number[], free: readonly number[], s: Af): Af {
  const a: Af = [];
  let j = 0;
  let k = 0;
  const fd = fixedSlots.map((slot, i): [number, number] => [slot, at(free, i)]).sort((x, y) => x[0] - y[0]).map(([, y]) => y);
  for (let i = 0; i < size; i++) {
    if (fixedSlots.includes(i)) a.push(at(fd, k++));
    else a.push(at(s, j++) + free.length);
  }
  return a;
}

/** All elements of the group generated by `gens` (array forms). */
function generate(gens: readonly Af[]): Af[] {
  const id = range(at(gens, 0).length);
  const seen = new Map([[id.join(','), id]]);
  const queue = [id];
  for (let k = 0; k < queue.length; k++) {
    for (const gen of gens) {
      const p = afRmul(at(queue, k), gen);
      const key = p.join(',');
      if (!seen.has(key)) {
        seen.set(key, p);
        queue.push(p);
      }
    }
  }
  return queue;
}

/** SymPy canonicalize_naive: the canonical form by enumerating the double coset (used when no minimal BSGS is found). */
function canonicalizeNaive(g: Af, dummies: readonly number[][], sym: readonly (0 | 1 | null)[], v: readonly [number[], Af[], number, 0 | 1 | null][]): Af | 0 {
  const [size, , sgens] = gensProducts(v.map(([b, gs, n, s]): TensorGens => [b, gs, Array.from({ length: n }, () => []), s]));
  const dgens = sym.flatMap((s, i) => dummySgs(at(dummies, i), s, size - 2));
  const dlist = generate(dgens.length ? dgens : [range(size)]);
  const st = new Map<string, Af>();
  for (const s of generate(sgens)) {
    const h = afRmul(g, s);
    for (const d of dlist) {
      const q = afRmul(d, h);
      st.set(q.join(','), q);
    }
  }
  const a = [...st.values()].sort(compareLists);
  let prev: Af = Array.from({ length: size }, () => 0);
  for (const h of a) {
    if (sameAf(h.slice(0, -2), prev.slice(0, -2)) && last(h) !== last(prev)) return 0;
    prev = h;
  }
  return at(a, 0);
}

/**
 * SymPy canonicalize(g, dummies, msym, *v): the canonical form of the tensor
 * `g` (an array form of size n + 2) with the dummy index pairs `dummies` of
 * each index type (metric symmetry `msym`: 0 symmetric, 1 antisymmetric,
 * null none) and the components `v` = [(base, generators, count, commutation)],
 * or 0 when the tensor vanishes.
 */
export function canonicalize(g: Af, dummies: readonly number[][], msym: readonly (0 | 1 | null)[], ...v: [number[], Af[], number, 0 | 1 | null][]): Af | 0 {
  if (dummies.length !== msym.length) throw new RangeError('dummies and msym must have the same number of elements');
  const size = g.length;
  const v1: TensorGens[] = [];
  for (const [baseI, gensI, nI, symI] of v) {
    // the BSGS must be minimal for double_coset_can_rep; otherwise compute one, or use the naive algorithm
    let bsgs: [number[], Af[]] = [baseI, gensI];
    if (!isMinimalBsgs(baseI, gensI)) {
      // SymPy get_minimal_bsgs; when Schreier–Sims gives no minimal base, the naive algorithm (with that base)
      bsgs = schreierSimsIncremental(gensI);
      if (!isMinimalBsgs(...bsgs)) return canonicalizeNaive(g, dummies, msym, v.map(([, gs, n, s]) => [schreierSimsIncremental(gs)[0], gs, n, s]));
    }
    v1.push([bsgs[0], bsgs[1], Array.from({ length: nI }, () => []), symI]);
  }
  const flatDummies = dummies.flat();
  if (flatDummies.length && !sameAf(flatDummies, range(last(flatDummies) + 1, at(flatDummies, 0)))) throw new RangeError('dummies is not valid');
  // slot symmetry of the tensor
  const [size1, sbase, sgens] = gensProducts(v1);
  if (size !== size1) throw new RangeError(`g has size ${size}, generators have size ${size1}`);
  const free = range(size - 2).filter((i) => !flatDummies.includes(i));
  const numFree = free.length;
  // g1 minimal tensor under slot symmetry
  const g1 = canonicalFree(sbase, sgens, g, numFree);
  if (!flatDummies.length) return g1;
  const sign = last(g1) === size - 1 ? 0 : 1;
  // the free indices are kept fixed: the slots of each component occupied by free indices
  let start = 0;
  v.forEach(([, gensI, nI], i) => {
    const lenTens = at(gensI, 0).length - 2;
    const freeI: number[][] = [];
    for (let j = 0; j < nI; j++) {
      const h = g1.slice(start, start + lenTens);
      freeI.push(free.filter((k) => h.includes(k)).map((k) => h.indexOf(k)));
      start += lenTens;
    }
    at(v1, i)[2] = freeI;
  });
  // BSGS of the tensor with fixed free indices
  const [size2, sbase2, sgens2] = gensProducts(v1);
  // reduce the permutations getting rid of the free indices
  const posFree = range(numFree).map((x) => g1.indexOf(x));
  const sizeRed = size2 - numFree;
  const g1Red = g1.filter((x) => flatDummies.includes(x)).map((x) => x - numFree);
  g1Red.push(...(sign ? [sizeRed - 1, sizeRed - 2] : [sizeRed - 2, sizeRed - 1]));
  const mapSlots = getMapSlots(size2, posFree);
  const sbaseRed = sbase2.filter((i) => !posFree.includes(i)).map((i) => at(mapSlots, i));
  const sgensRed = sgens2.map((y) => y.filter((i) => !posFree.includes(i)).map((i) => at(mapSlots, i)));
  const dummiesRed = dummies.map((y) => y.map((x) => x - numFree));
  const transvRed = getTransversals(sbaseRed, sgensRed);
  const g2 = doubleCosetCanRep(dummiesRed, msym, sbaseRed, sgensRed, transvRed, g1Red);
  if (g2 === 0) return 0;
  // lift to the case with the free indices
  return liftSgens(size2, posFree, free, g2);
}
