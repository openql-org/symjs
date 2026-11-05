// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 combinatorics.perm_groups (the larger replayed table is in
// permgroups.sympy.test.ts).
import { describe, expect, it } from 'vitest';
import { Sym, latex, str } from '../../src';
import { AlternatingGroup, Coset, Cycle, CyclicGroup, DihedralGroup, Permutation, PermutationGroup, SymmetricGroup, SymmetricPermutationGroup } from '../../src/combinatorics';
import { NoMatch } from '../../src/core/truth';
import { seed } from '../../src/ntheory/random';

const P = (...a: number[]): Permutation => new Permutation(...a);
const af = (g: Permutation): number[] => g.arrayForm;
const gens = (G: PermutationGroup): number[][] => G.generators.map(af);
const pg = (...ps: Permutation[]): PermutationGroup => PermutationGroup(...ps);

describe('construction and printing', () => {
  it('resizes, removes repeats and identities as SymPy', () => {
    expect(gens(PermutationGroup(new Cycle(0, 1), P(2)))).toEqual([[1, 0, 2]]);
    expect(gens(PermutationGroup([P(0, 1), P(2)], { degree: 4 }))).toEqual([[1, 0, 2, 3]]);
    expect(gens(PermutationGroup([P(0, 1), P(0, 1)], { dups: false }))).toEqual([[1, 0], [1, 0]]);
    expect(gens(PermutationGroup([]))).toEqual([[]]);
    expect(gens(PermutationGroup())).toEqual([[]]);
    expect(PermutationGroup().degree).toBe(0);
    const G = pg(P(0, 1, 2), P(0, 1));
    expect(str(G)).toBe('PermutationGroup([\n    (0 1 2),\n    (2)(0 1)])');
    expect(latex(pg(P(0, 1, 2)))).toBe('\\operatorname{PermutationGroup}\\left(\\left( 0\\; 1\\; 2\\right)\\right)');
    expect(G.withArgs(G.args).key).toBe(G.key);
    expect(G.length).toBe(2);
    expect(G.getItem(1).equals(P(2).mul(P(0, 1)))).toBe(true);
    expect(G.copy().key).toBe(G.key);
  });
  it('compares groups by the elements they generate', () => {
    const G = pg(P(0, 1, 2), P(0, 1));
    expect(G.equals(P(0, 1))).toBe(false);
    expect(G.equals(pg(P(0, 1), P(0, 1, 2)))).toBe(true);
    expect(G.equals(pg(P(0, 1, 2)))).toBe(false);
    expect(pg(P(0, 1, 2)).equals(G)).toBe(false);
    expect(G.equals(pg(P(1, 2), P(0, 2, 1)))).toBe(true);
  });
  it('forms cosets and direct products', () => {
    const G = pg(P(0, 1, 2), P(0, 1));
    expect(str(G.mul(P(1, 2)))).toBe('Coset((1 2), PermutationGroup([\n    (0 1 2),\n    (2)(0 1)]), SymmetricPermutationGroup(3), +)');
    const D = G.mul(CyclicGroup(2));
    expect(D instanceof Coset ? [] : gens(D)).toEqual([[1, 2, 0, 3, 4], [1, 0, 2, 3, 4], [0, 1, 2, 4, 3]]);
  });
});

describe('Schreier-Sims', () => {
  it('handles the trivial group', () => {
    const T = pg(P(2));
    T.schreierSims();
    expect(T.basicStabilizers).toEqual([]);
    expect([...T.generateSchreierSims()].map(af)).toEqual([[0, 1, 2]]);
    expect([T.base, T.order(), T.abelianInvariants()]).toEqual([[], 1n, []]);
    expect(T.schreierSimsIncremental()).toEqual([[], T.generators]);
  });
  it('swaps base points', () => {
    const S5 = SymmetricGroup(5);
    seed(3);
    const [b, s] = S5.baseswap(S5.base, S5.strongGens, 1, true);
    expect([b, s.map(af)]).toEqual([[0, 3, 1, 2], [[1, 2, 3, 4, 0], [1, 0, 2, 3, 4], [0, 4, 1, 2, 3], [0, 1, 2, 4, 3], [0, 1, 4, 3, 2], [0, 2, 1, 3, 4]]]);
    const [b2, s2] = S5.baseswap(S5.base, S5.strongGens, 2);
    expect([b2, s2.map(af)]).toEqual([[0, 1, 2, 3], [[1, 2, 3, 4, 0], [1, 0, 2, 3, 4], [0, 4, 1, 2, 3], [0, 1, 2, 4, 3], [0, 1, 4, 3, 2]]]);
    const A5 = AlternatingGroup(5);
    const [b3, s3] = A5.baseswap(A5.base, A5.strongGens, 0);
    expect([b3, s3.map(af)]).toEqual([[2, 0, 1], [[1, 2, 0, 3, 4], [1, 2, 3, 4, 0], [0, 1, 3, 4, 2], [0, 3, 2, 4, 1], [1, 3, 2, 0, 4]]]);
  });
  it('factors elements over the transversals', () => {
    const D = DihedralGroup(6);
    expect(D.cosetFactor(new Cycle(0, 1, 2, 3, 4, 5)).map(af)).toEqual([[1, 2, 3, 4, 5, 0], [0, 1, 2, 3, 4, 5]]);
    expect(D.cosetFactor([1, 2, 3, 4, 5, 0], true)).toEqual([1, 1]);
    expect(D.cosetFactor([1, 0, 2, 3, 4, 5])).toEqual([]);
    expect(D.cosetFactor([0, 2, 1, 3, 4, 5])).toEqual([]);
    expect(() => D.cosetFactor([1, 0])).toThrow('same size');
    expect([D.contains(3), D.contains(P(0, 1)), D.contains(P(1, 5)), D.contains(P(0, 1), false), D.contains(P(5).mul(P(0, 1)))]).toEqual([false, false, false, false, false]);
    expect(D.contains(P(1, 2, 3, 4, 5, 0).resize(6))).toBe(true);
    expect(pg(P(0, 1, 2)).contains(P(0, 1, 2).resize(2 + 1))).toBe(true);
    expect(pg(P(0, 1, 2)).contains(P(1, 2), false)).toBe(false);
    expect(pg(P(0, 1, 2)).contains(new Permutation([1, 2, 0]).resize(3), false)).toBe(true);
    expect(pg(P(0, 1, 2, 3)).contains(new Permutation([1, 0]), false)).toBe(false);
    expect(pg(P(0, 1), P(2, 3)).contains(new Permutation([1, 0]), false)).toBe(true);
  });
  it('writes elements as products of generators', () => {
    const D = DihedralGroup(6);
    expect([P(0, 5, 4, 3, 2, 1), P(0, 2, 4).mul(P(1, 3, 5)), P(5)].map((g) => D.generatorProduct(g).map(af))).toEqual([[[5, 0, 1, 2, 3, 4]], [[1, 2, 3, 4, 5, 0], [1, 2, 3, 4, 5, 0]], []]);
    const S5 = SymmetricGroup(5);
    expect(S5.generatorProduct(P(4, 3, 2, 1, 0), true).map(af)).toEqual([[4, 0, 1, 2, 3]]);
    const g = P(1, 2, 3, 4);
    expect(S5.generatorProduct(g, true).reduce((a, b) => b.mul(a), P(4)).equals(g)).toBe(true);
  });
  it('ranks and unranks, NoMatch outside the group', () => {
    const D = DihedralGroup(6);
    expect([D.cosetRank(P(0, 1).mul(P(2, 5))), D.cosetUnrank(-1), D.cosetUnrank(12), D.index(pg(P(0, 1).mul(P(2, 5))))]).toEqual([NoMatch, NoMatch, NoMatch, NoMatch]);
  });
});

describe('random elements', () => {
  it('draws from the shared generator as SymPy', () => {
    const D = DihedralGroup(6);
    seed(4);
    expect(af(D.randomStab(2))).toEqual([0, 1, 2, 3, 4, 5]);
    expect(af(D.makePerm([1, 1, 0]))).toEqual([1, 2, 3, 4, 5, 0]);
    expect(() => D.makePerm([1], [0])).toThrow('seed should be None');
    expect(() => D.makePerm(3, [0])).toThrow('too short');
    expect(af(D.makePerm(2, [5, 1, 9, 0]))).toEqual([4, 3, 2, 1, 0, 5]);
  });
});

describe('orbits and stabilizers', () => {
  it('computes orbits and transversals', () => {
    const D = DihedralGroup(6);
    expect(D.orbitTransversal(1)).toHaveLength(6);
    expect(D.orbitTransversal(1, true).map(([k, v]) => [k, af(v)])).toEqual([[1, [0, 1, 2, 3, 4, 5]], [2, [1, 2, 3, 4, 5, 0]], [4, [5, 4, 3, 2, 1, 0]], [3, [2, 3, 4, 5, 0, 1]], [5, [0, 5, 4, 3, 2, 1]], [0, [1, 0, 5, 4, 3, 2]]]);
    expect([...D.orbit([2], 'tuples')].sort((a, b) => Number(a) - Number(b))).toEqual([0, 1, 2, 3, 4, 5]);
    expect(() => D.orbit(6)).toThrow('outside');
    expect(() => D.stabilizer(-1)).toThrow('outside');
    expect(() => D.schreierVector(0.5)).toThrow('outside');
    expect(() => D.pointwiseStabilizer([7])).toThrow('outside');
    expect(D.pointwiseStabilizer([]).order()).toBe(12n);
    expect(pg(P(0, 1, 2)).pointwiseStabilizer([0]).order()).toBe(1n);
    expect([pg(P(0, 1), P(2, 3)).isTransitive(false), pg(P(0, 1).mul(P(2, 3))).isTransitive(false), pg(P(3)).isTransitive(false), pg(P(0, 1)).isTransitive(false)]).toEqual([false, false, false, true]);
    const C = CyclicGroup(4);
    expect([C.transitivityDegree, C.transitivityDegree]).toEqual([1, 1]);
  });
  it('finds blocks', () => {
    expect([pg(new Permutation([0])).maxDiv, DihedralGroup(7).maxDiv, SymmetricGroup(9).maxDiv]).toEqual([1, 1, 3]);
    const NT = pg(P(0, 1), P(2, 3));
    expect([NT.minimalBlock([0, 2]), NT.isPrimitive(), NT.minimalBlocks(), NT.isPrimitive(false)]).toEqual([false, false, false, false]);
    expect(DihedralGroup(6).minimalBlock([0, 1, 2, 3])).toEqual([0, 0, 0, 0, 0, 0]);
    const S5 = SymmetricGroup(5);
    expect([S5.isPrimitive(false), S5.isPrimitive(false), CyclicGroup(7).isPrimitive(false), CyclicGroup(7).minimalBlocks(false)]).toEqual([true, true, true, [[0, 0, 0, 0, 0, 0, 0]]]);
  });
});

describe('properties', () => {
  it('recognizes elementary abelian groups', () => {
    expect([pg(P(0, 1), P(2, 3)).isElementary(2), pg(P(0, 1, 2)).isElementary(2), SymmetricGroup(3).isElementary(2n)]).toEqual([true, false, false]);
  });
  it('recognizes symmetric and alternating groups', () => {
    seed(6);
    expect(pg(...SymmetricGroup(17).generators).isAltSym()).toBe(true);
    const NT8 = pg(P(0, 1, 2, 3), P(4, 5, 6, 7));
    expect([NT8.isAltSym(), NT8.isAltSym(), NT8.isSymmetric, NT8.isAlternating]).toEqual([false, false, false, false]);
    expect([pg(P(0, 1, 2, 3), P(4, 5, 6, 7, 8)).isSymmetric, pg(P(0, 1, 2, 3), P(4, 5, 6, 7, 8)).isAlternating]).toEqual([false, false]);
    seed(7);
    expect([pg(...SymmetricGroup(8).generators).isSymmetric, pg(...SymmetricGroup(8).generators).isAlternating, pg(...AlternatingGroup(8).generators).isAlternating, pg(...AlternatingGroup(8).generators).isSymmetric]).toEqual([true, false, true, false]);
    expect([pg(...DihedralGroup(8).generators).isSymmetric, pg(...DihedralGroup(8).generators).isAlternating]).toEqual([false, false]);
    expect([pg(...SymmetricGroup(5).generators).isAltSym(), pg(...AlternatingGroup(5).generators).isAltSym(), pg(...SymmetricGroup(5).generators).isAlternating, pg(...AlternatingGroup(5).generators).isSymmetric]).toEqual([true, true, false, false]);
    expect([SymmetricGroup(5).isAltSym(), AlternatingGroup(5).isAltSym(), pg(P(0, 1, 2), P(3, 4)).isAltSym()]).toEqual([true, true, false]);
    const S3 = pg(P(0, 1, 2), P(0, 1));
    expect([S3.isSymmetric, S3.isAltSym()]).toEqual([true, true]);
    // SymPy fails on the group of degree 0 (orbit(0) indexes an empty list); symjs answers
    expect([PermutationGroup().isTransitive(), PermutationGroup().isSymmetric, PermutationGroup().isAlternating]).toEqual([true, true, false]);
  });
  it('recognizes cyclic groups', () => {
    const groups = [pg(P(0, 1).mul(P(2, 3)), P(0, 2).mul(P(1, 3))), pg(P(0, 1, 2), P(3, 4)), pg(P(0, 1, 2, 3, 4).mul(P(5, 6, 7)), P(0, 1, 2, 3, 4)), pg(P(0, 1, 2), P(0, 1)), pg(P(0, 1), P(2, 3, 4, 5)), pg(P(0, 1, 2, 3), P(4, 5, 6, 7)), pg(P(0, 1), P(2, 3), P(0, 1).mul(P(2, 3))), SymmetricGroup(4)];
    expect(groups.map((g) => g.isCyclic)).toEqual([false, true, true, false, false, false, false, false]);
    const S3 = SymmetricGroup(3);
    expect([S3.isAbelian, pg(...S3.generators).isCyclic, S3.isCyclic, S3.isCyclic]).toEqual([false, false, false, false]);
    expect([pg(P(0, 1, 2), P(0, 2, 1)).isCyclic, pg(P(0, 1), P(2, 3, 4), P(5, 6, 7, 8, 9)).isCyclic]).toEqual([true, true]);
    const C6 = pg(P(0, 1, 2), P(3, 4));
    expect([C6.isAbelian, C6.isCyclic]).toEqual([true, true]);
  });
  it('recognizes dihedral groups', () => {
    const groups = [CyclicGroup(3), pg(P(0, 1)), pg(P(0, 1), P(2, 3)), pg(P(0, 1, 2, 3)), pg(P(0, 1).mul(P(2, 3)), P(0, 2).mul(P(1, 3))), pg(P(0, 1), P(2, 3), P(4, 5)), pg(P(0, 1), P(1, 2)), pg(P(0, 1, 2, 3, 4, 5), P(0, 5).mul(P(1, 4)).mul(P(2, 3))), pg(P(0, 5).mul(P(1, 4)).mul(P(2, 3)), P(0, 1, 2, 3, 4, 5)), pg(P(0, 1, 2), P(0, 1), P(3, 4)), SymmetricGroup(4), pg(P(0, 1, 2, 3, 4, 5, 6, 7), P(1, 7).mul(P(2, 6)).mul(P(3, 5)), P(0, 4).mul(P(1, 5)).mul(P(2, 6)).mul(P(3, 7))), AlternatingGroup(4), pg(P(0, 1, 2, 3).mul(P(4, 5, 6, 7)), P(0, 4, 2, 6).mul(P(1, 7, 3, 5)))];
    expect(groups.map((g) => g.isDihedral)).toEqual([false, true, true, false, true, false, true, true, true, true, false, true, false, false]);
    expect([pg(P(0, 1, 2, 3), P(0, 2)).isDihedral, pg(P(0, 1, 2), P(1, 2), P(0, 1)).isDihedral, pg(P(0, 1, 2, 3, 4, 5), P(1, 5).mul(P(2, 4)), P(0, 3).mul(P(1, 4)).mul(P(2, 5))).isDihedral, pg(P(0, 1).mul(P(2, 3)).mul(P(4, 5)), P(0, 2, 4).mul(P(1, 3, 5)), P(0, 3).mul(P(1, 4)).mul(P(2, 5))).isDihedral]).toEqual([true, true, true, false]);
    // the generalized dihedral group of C3 x C3: 9 involutions but no element of order 9
    const dih33 = pg(new Permutation([3, 4, 5, 6, 7, 8, 0, 1, 2]), new Permutation([1, 2, 0, 4, 5, 3, 7, 8, 6]), new Permutation([0, 2, 1, 6, 8, 7, 3, 5, 4]));
    expect([dih33.order(), dih33.isDihedral, pg(P(0, 1, 2)).isDihedral]).toEqual([18n, false, false]);
    const D = DihedralGroup(5);
    expect([D.isDihedral, pg(...D.generators).isDihedral, pg(...D.generators).isDihedral]).toEqual([true, true, true]);
  });
  it('tests subgroups and normality', () => {
    expect([pg(P(0, 1)).isSubgroup(SymmetricPermutationGroup(2)), pg(P(0, 1)).isSubgroup(SymmetricPermutationGroup(3)), pg(P(0, 1)).isSubgroup(SymmetricGroup(3)), pg(P(0, 1)).isSubgroup(SymmetricGroup(3), false), pg(P(0, 1, 2)).isSubgroup(pg(P(0, 1)))]).toEqual([true, false, false, true, false]);
    expect(pg(P(0, 1, 2, 3)).isSubgroup(pg(P(0, 1, 2)), false)).toBe(false);
    expect([pg(P(0, 1)).isNormal(SymmetricGroup(3)), pg(P(2)).isNormal(SymmetricGroup(3)), pg(P(1)).isNormal(SymmetricGroup(3), false), pg(P(0, 1, 2)).isNormal(SymmetricGroup(4), false), CyclicGroup(3).isNormal(SymmetricGroup(3))]).toEqual([false, true, true, false, true]);
    const K = pg(P(0, 1).mul(P(2, 3)), P(0, 2).mul(P(1, 3)));
    expect([K.isNormal(SymmetricGroup(4)), K.isAbelian, K.isNormal(SymmetricGroup(4))]).toEqual([true, true, true]);
    expect(pg(P(0, 1).mul(P(2, 3))).isNormal(pg(...SymmetricGroup(4).generators, P(4)), false)).toBe(false);
    expect(pg(P(0, 1, 2).mul(P(3, 4))).isNormal(pg(P(0, 1, 2), P(3, 4)), false)).toBe(true);
    expect(gens(SymmetricGroup(3).subgroup([P(0, 1, 2)]))).toEqual([[1, 2, 0]]);
    expect(() => CyclicGroup(3).subgroup([P(0, 1)])).toThrow('does not contain');
  });
  it('tests solvability', () => {
    expect([CyclicGroup(5).isSolvable, AlternatingGroup(5).isPolycyclic, pg(...AlternatingGroup(5).generators).isSolvable]).toEqual([true, false, false]);
    expect(pg(P(0, 1, 2, 3, 4)).isSolvable).toBe(true);
    expect(() => AlternatingGroup(5).compositionSeries()).toThrow('solvable');
  });
});

describe('subgroups by search, centralizers and cosets', () => {
  it('searches subgroups', () => {
    expect(SymmetricGroup(4).subgroupSearch((g) => g.isEven).order()).toBe(12n);
    const S5 = SymmetricGroup(5);
    expect(S5.subgroupSearch((g) => g.arrayForm[4] === 4, S5.base, undefined, [() => true, () => true, () => true, () => true]).order()).toBe(24n);
    expect(S5.subgroupSearch((g) => g.arrayForm[4] === 4, S5.base, S5.strongGens, undefined, pg(P(0, 1).resize(5))).order()).toBe(24n);
  });
  it('computes centralizers', () => {
    const S4 = SymmetricGroup(4);
    expect([S4.centralizer(pg(P(3))).order(), pg(P(3)).centralizer(S4).order(), SymmetricGroup(5).centralizer(P(0, 1, 2).mul(P(3, 4))).order(), SymmetricGroup(6).centralizer(P(0, 1, 2).mul(P(3, 4, 5))).order(), DihedralGroup(8).centralizer(P(0, 2, 4, 6).mul(P(1, 3, 5, 7))).order(), S4.centralizer([P(0, 1).mul(P(2, 3))]).order(), S4.centralizer(P(3).mul(P(0, 1))).order()]).toEqual([24n, 1n, 6n, 18n, 8n, 8n, 4n]);
  });
  it('builds coset transversals and tables', () => {
    const S3 = SymmetricGroup(3);
    expect(() => S3.cosetTransversal(pg(P(0, 1, 2, 3)))).toThrow('must be a subgroup');
    expect(() => S3.cosetTable(pg(P(0, 1, 2, 3)))).toThrow('must be a subgroup');
    expect(S3.cosetTransversal(pg(P(2))).map(af)).toEqual([[0, 1, 2], [1, 2, 0], [2, 0, 1], [0, 2, 1], [1, 0, 2], [2, 1, 0]]);
    expect(SymmetricGroup(4).cosetTransversal(pg(new Permutation([1, 0, 2, 3]))).map(af)).toEqual([[0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 1, 3, 2], [0, 2, 1, 3], [0, 3, 2, 1], [1, 2, 3, 0], [1, 3, 0, 2], [1, 2, 0, 3], [1, 3, 2, 0], [2, 3, 0, 1], [2, 3, 1, 0]]);
    expect([S3.cosetTransversal(SymmetricGroup(3)).map(af), DihedralGroup(4).cosetTransversal(CyclicGroup(4)).map(af)]).toEqual([[[0, 1, 2]], [[0, 1, 2, 3], [0, 3, 2, 1]]]);
    const V = pg(P(0, 1).mul(P(2, 3)), P(0, 2).mul(P(1, 3)));
    expect(SymmetricGroup(4).cosetTransversal(V).map(af)).toEqual([[0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 1, 3, 2], [0, 2, 1, 3], [0, 3, 2, 1]]);
    expect(SymmetricGroup(4).cosetTable(V)).toEqual([[1, 1, 2, 2], [0, 0, 3, 3], [4, 4, 0, 0], [5, 5, 1, 1], [2, 2, 5, 5], [3, 3, 4, 4]]);
    expect(SymmetricGroup(4).cosetTable(pg(P(1, 2, 3)))).toEqual([[1, 2, 1, 1], [3, 0, 0, 0], [0, 3, 4, 4], [2, 1, 5, 5], [6, 5, 2, 2], [4, 7, 3, 3], [7, 4, 7, 7], [5, 6, 6, 6]]);
    expect(DihedralGroup(4).cosetTable(pg(P(3)))).toEqual([[1, 2, 3, 3], [4, 0, 5, 5], [0, 4, 6, 6], [6, 5, 0, 0], [2, 1, 7, 7], [3, 7, 1, 1], [7, 3, 2, 2], [5, 6, 4, 4]]);
  });
});

describe('SymmetricPermutationGroup and Coset', () => {
  it('describes the symmetric group by its degree', () => {
    const G = SymmetricPermutationGroup(3);
    expect([str(G), G.degree, G.contains(P(0, 1, 2)), G.contains(P(0, 1)), G.order()]).toEqual(['SymmetricPermutationGroup(3)', 3, true, false, 6n]);
    expect(() => G.contains(1)).toThrow(TypeError);
    expect(G.withArgs(G.args).key).toBe(G.key);
    expect(SymmetricPermutationGroup(3n).key).toBe(G.key);
  });
  it('checks its arguments and lists its elements', () => {
    const c = new Coset(P(1, 2), pg(P(0, 2)));
    expect([str(c), c.isRightCoset, c.isLeftCoset, new Coset(P(1, 2), pg(P(0, 2)), undefined, new Sym('-')).isLeftCoset]).toEqual(['Coset((1 2), PermutationGroup([\n    (0 2)]), SymmetricPermutationGroup(3), +)', true, false, true]);
    expect(c.withArgs(c.args).key).toBe(c.key);
    const c2 = new Coset(P(1, 2), pg(P(0, 2)), SymmetricGroup(3));
    expect(c2.withArgs(c2.args).key).toBe(c2.key);
    expect(() => new Coset(P(1, 2), pg(P(0, 3)))).toThrow('should be matching');
    expect(() => new Coset(P(1, 2), pg(P(0, 3)), SymmetricGroup(3))).toThrow('must be a subgroup');
    expect(() => new Coset(P(0, 1, 2), pg(P(1, 2)), pg(P(1, 2)))).toThrow('must be an element');
    expect(() => new Coset(P(1, 2), pg(P(0, 2)), undefined, new Sym('*'))).toThrow("dir must be one of '+' or '-'");
    expect(new Coset(P(1, 2), pg(P(0, 2)), undefined, '-').asList().map(af)).toEqual([[0, 2, 1], [2, 0, 1]]);
  });
});
