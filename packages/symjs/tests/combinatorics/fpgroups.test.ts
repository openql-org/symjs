// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Finitely presented groups (after SymPy 1.14 test_fp_groups.py; expected values from SymPy, see
// tools/sympy-reference/generators/gen_fpgroups.py): subgroup presentations, orders, subgroups with their injections, the
// permutation group methods, simplification, low index subgroups, and the subgroups of free groups.
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { S } from '../../src';
import { NotImplementedError } from '../../src/core/errors';
import {
  CosetTable,
  FpGroup,
  FpSubgroup,
  FreeGroup,
  FreeGroupElement,
  cosetEnumerationR,
  defineSchreierGenerators,
  descendantSubgroups,
  eliminationTechnique1,
  eliminationTechnique2,
  firstInClass,
  fpGroup,
  freeGroup,
  lowIndexSubgroups,
  reidemeisterPresentation,
  reidemeisterRelators,
  reidemeisterRewrite,
  simplifyPresentation,
  tryDescendant,
  vfpGroup,
  xfpGroup,
} from '../../src/combinatorics';

const ref = JSON.parse(readFileSync(new URL('./fpgroups.references.json', import.meta.url), 'utf8'));
const [F, x, y] = freeGroup('x, y') as [FreeGroup, FreeGroupElement, FreeGroupElement];
const s = (v: unknown): string => String(v);
const tup = (ws: readonly unknown[]): string => (ws.length === 1 ? `(${s(ws[0])},)` : `(${ws.map(s).join(', ')})`);

describe('construction and printing', () => {
  it('fp_group, xfp_group, vfp_group', () => {
    const [G, gx, gy] = fpGroup(F, [x.pow(2)]);
    expect(s(G)).toBe('<fp group on the generators (x, y)>');
    expect([gx, gy].map(s)).toEqual(['x', 'y']);
    expect(xfpGroup(F)[1].map(s)).toEqual(['x', 'y']);
    expect(s(vfpGroup(F, [x]))).toBe('<fp group on the generators (x, y)>');
    expect(s(vfpGroup('u, v'))).toBe('<fp group on the generators (u, v)>');
    expect(s(new FpGroup(new FreeGroup('a:31')))).toBe('<fp group with 31 generators>');
    expect(G.contains(x)).toBe(true);
    expect(G.identity.isIdentity).toBe(true);
  });
});

describe('subgroup presentations', () => {
  it('SymPy test_subgroup_presentations', () => {
    const f = new FpGroup(F, [x.pow(3), y.pow(5), x.mul(y).pow(2)]);
    const H = [x.mul(y), x.inverse().mul(y.inverse()).mul(x).mul(y).mul(x)];
    const [g1, r1] = reidemeisterPresentation(f, H);
    expect(`(${tup(g1)}, ${tup(r1)})`).toBe('((y_1, y_2), (y_1**2, y_2**3, y_2*y_1*y_2*y_1*y_2*y_1))');
    const K = f.subgroup(H);
    expect([K.generators.map(s), K.relators.map(s)]).toEqual([g1.map(s), r1.map(s)]);
    const [g2, r2] = reidemeisterPresentation(new FpGroup(F, [x.pow(3), y.pow(3), x.mul(y).pow(3)]), [x.mul(y), x.mul(y.inverse())]);
    expect(`(${tup(g2)}, ${tup(r2)})`).toBe('((x_0, y_0), (x_0**3, y_0**3, x_0*y_0*x_0*y_0*x_0*y_0))');
    const [Fa, a, b, c] = freeGroup('a, b, c') as [FreeGroup, FreeGroupElement, FreeGroupElement, FreeGroupElement];
    const psl = new FpGroup(Fa, [a.pow(11), b.pow(5), c.pow(4), b.mul(c.pow(2)).pow(2), a.mul(b).mul(c).pow(3), a.pow(4).mul(c.pow(2)).pow(3), b.pow(2).mul(c.inverse()).mul(b.inverse()).mul(c), a.pow(4).mul(b.inverse()).mul(a.inverse()).mul(b)]);
    const [g3, r3] = reidemeisterPresentation(psl, [a, b, c.pow(2)]);
    expect(tup(g3)).toBe(ref.fp_extra.psl[0]);
    expect(r3.length).toBe(18);
    // the trivial subgroup of a trivial group
    expect(s(new FpGroup(F, [x, y]).subgroup([x]))).toBe('<fp group on the generators ()>');
  });
  it('the Reidemeister-Schreier steps', () => {
    const f = new FpGroup(F, [x.pow(3), y.pow(5), x.mul(y).pow(2)]);
    const C = cosetEnumerationR(f, [x.mul(y), x.inverse().mul(y.inverse()).mul(x).mul(y).mul(x)]);
    C.compress();
    C.standardize();
    defineSchreierGenerators(C);
    expect(s(reidemeisterRewrite(C, 0, x.mul(y).pow(6)))).toBe('y_1**6');
    reidemeisterRelators(C);
    const [gens, rels] = eliminationTechnique2(C);
    expect(`(${`[${gens.map(s).join(', ')}]`}, ${`[${rels.map(s).join(', ')}]`})`).toBe('([y_1, y_2], [y_2**-3, y_2*y_1*y_2*y_1*y_2*y_1, y_1**2])');
    const [g4, r4] = eliminationTechnique1([x, y], [x.pow(3).mul(y), y.pow(2)], F.identity);
    expect([g4.map(s), r4.map(s)]).toEqual([['x'], ['x**-6']]);
  });
});

describe('orders', () => {
  it('SymPy test_order', () => {
    expect(s(new FpGroup(F, [x.pow(4), y.pow(2), x.mul(y).mul(x.inverse()).mul(y)]).order())).toBe(ref.fp_extra.order_d4);
    expect(new FpGroup(F, [x.mul(y).mul(x.inverse()).mul(y.inverse()), y.pow(2)]).order()).toBe(S.Infinity);
    const [Fa, a, b, c] = freeGroup('a, b, c') as [FreeGroup, FreeGroupElement, FreeGroupElement, FreeGroupElement];
    const f = new FpGroup(Fa, [a.pow(250), b.pow(2), c.mul(b).mul(c.inverse()).mul(b), c.pow(4), c.inverse().mul(a.inverse()).mul(c).mul(a), a.inverse().mul(b.inverse()).mul(a).mul(b)]);
    expect(s(f.order())).toBe(ref.fp_extra.order_2000);
    expect(f.order()).toBe(f.order());
    expect(new FpGroup(new FreeGroup('x'), []).order()).toBe(S.Infinity);
    expect(new FpGroup(new FreeGroup(''), []).order()).toBe(S.One);
    const [Z, z] = freeGroup('z') as [FreeGroup, FreeGroupElement];
    expect(s(new FpGroup(Z, [z.pow(6), z.pow(4)]).order())).toBe(ref.fp_extra.order_cyclic);
    // the order from the stored coset table of the trivial subgroup
    const g = new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(3)]);
    g.cosetTable([]);
    expect(s(g.order())).toBe('12');
    expect(s(g.index([x]))).toBe('6');
    expect(g.cosetTable([]).length).toBe(12);
    expect(g.cosetTable([x], { strategy: 'coset_table_based' }).length).toBe(6);
    expect(g.mostFrequentGenerator().equals(y)).toBe(true);
    expect(g.random().group).toBe(F);
    expect(() => new FpGroup(F, [x.pow(2)]).toPermGroup()).toThrow(NotImplementedError);
  });
});

describe('subgroups and the permutation group methods', () => {
  it('SymPy test_fp_subgroup', () => {
    const f = new FpGroup(F, [x.pow(4), y.pow(2), x.mul(y).mul(x.inverse()).mul(y)]);
    const S1 = new FpSubgroup(f, [x.mul(y)]);
    expect(S1.contains(x.mul(y).pow(-3))).toBe(true);
    const [K, T] = f.subgroup([x.mul(y)], undefined, true);
    expect(s(K)).toBe(ref.fp_extra.K);
    expect(tup(K.relators)).toBe(ref.fp_extra.K_rels);
    expect(`[${T.apply([...K.generators]).map(s).join(', ')}]`).toBe(ref.fp_extra.T_gens);
    expect(T.isInjective()).toBe(true);
    expect(s(T.image().order())).toBe(s(S1.order()));
    const S2 = new FpSubgroup(f, [x.inverse().mul(y).mul(x)]);
    expect(S2.contains(x.inverse().mul(y.pow(4)).mul(x))).toBe(true);
    expect(S2.contains(x.inverse().mul(y.pow(4)).mul(x.pow(2)))).toBe(false);
    const [K2, T2] = f.subgroup([x.inverse().mul(y).mul(x)], undefined, true);
    expect(s(T2.apply(K2.generators[0]!.pow(3)))).toBe(ref.fp_extra.T2_cube);
    expect(s(new FpSubgroup(f, []).order())).toBe('1');
    expect(s(S2.toFpGroup())).toBe('<fp group on the generators (y_0,)>');
    expect(s(new FpSubgroup(f, Array.from({ length: 31 }, (_v, i) => x.pow(i + 1))))).toBe('<fp subgroup with 31 generators>');
  });
  it('SymPy test_permutation_methods, test_cyclic and test_abelian_invariants', () => {
    const D8 = new FpGroup(F, [x.pow(2), y.pow(8), x.mul(y).mul(x.inverse()).mul(y)]);
    expect(D8.toPermGroup()[1].isIsomorphism()).toBe(true);
    expect(`[${D8.center().map(s).join(', ')}]`).toBe(ref.fp_extra.center_d8);
    const D4 = new FpGroup(F, [x.pow(2), y.pow(4), x.mul(y).mul(x.inverse()).mul(y)]);
    const N = new FpSubgroup(D4, D4.normalClosure([x]));
    expect(N.contains(x)).toBe(true);
    expect(N.contains(y.inverse().mul(x).mul(y))).toBe(true);
    expect(D4.normalClosure(x).length).toBe(ref.fp_extra.normal_closure_d4);
    expect(D4.centralizer(x).length).toBe(ref.fp_extra.centralizer_d4);
    expect(D4.centralizer([x]).length).toBe(ref.fp_extra.centralizer_d4);
    const Z = new FpGroup(F, [x.mul(y).mul(x.inverse()).mul(y.inverse()), y.pow(5), x.pow(4)]);
    expect(Z.isAbelian).toBe(true);
    expect(Z.isSolvable).toBe(true);
    expect(new FpGroup(F, [x.pow(3), y.pow(2), x.mul(y).pow(5)]).isSolvable).toBe(false);
    const A4 = new FpGroup(F, [x.pow(3), y.pow(2), x.mul(y).pow(3)]);
    expect(A4.derivedSeries().length).toBe(3);
    expect(s(new FpSubgroup(A4, A4.derivedSubgroup()).order())).toBe('4');
    expect(A4.derivedSubgroup().length).toBe(ref.fp_extra.derived_a4);
    expect(A4.lowerCentralSeries().map((t) => t.length)).toEqual(ref.fp_extra.lcs_a4);
    expect(A4.compositionSeries().length).toBe(ref.fp_extra.composition_a4);
    expect(new FpGroup(F, [x.mul(y), x.inverse().mul(y.inverse()).mul(x).mul(y).mul(x)]).isCyclic).toBe(true);
    expect(new FpGroup(F, [x.mul(y), x.mul(y.inverse())]).isCyclic).toBe(true);
    expect(new FpGroup(F, [x.pow(4), y.pow(2), x.mul(y).mul(x.inverse()).mul(y)]).isCyclic).toBe(false);
    expect(new FpGroup(new FreeGroup('x'), [new FreeGroup('x').generators[0]!.pow(5)]).isCyclic).toBe(true);
    expect(new FpGroup(F, [x.mul(y), x.inverse().mul(y.inverse()).mul(x).mul(y).mul(x)]).abelianInvariants()).toEqual([]);
    expect(new FpGroup(F, [x.mul(y), x.mul(y.inverse())]).abelianInvariants()).toEqual([2n]);
    expect(new FpGroup(F, [x.pow(4), y.pow(2), x.mul(y).mul(x.inverse()).mul(y)]).abelianInvariants()).toEqual([2n, 4n]);
    const inf = new FpGroup(F, [x.pow(2)]);
    expect(() => inf.isCyclic).toThrow(NotImplementedError);
    expect(() => inf.abelianInvariants()).toThrow(NotImplementedError);
    expect(() => inf.compositionSeries()).toThrow(NotImplementedError);
  });
});

describe('simplification', () => {
  it('SymPy test_simplify_presentation', () => {
    const G = simplifyPresentation(new FpGroup(new FreeGroup([]), []));
    expect(G.generators.length).toBe(0);
    expect(G.relators.length).toBe(0);
    expect(simplifyPresentation(new FpGroup(F, [x.pow(2), x.pow(5), y.pow(3)])).relators.map(s)).toEqual(ref.fp_extra.simplify_x);
    expect(simplifyPresentation(new FpGroup(F, [x.pow(2), x.pow(5), y.pow(3)]), true).generators.map(s)).toEqual(ref.fp_extra.simplify_change);
    expect(simplifyPresentation([], [])).toEqual([[], []]);
    expect(simplifyPresentation([x], [], true).map((l) => l.map(s))).toEqual([['x'], []]);
    expect(() => simplifyPresentation(1 as never)).toThrow(TypeError);
    expect(() => simplifyPresentation([x], true as never)).toThrow(TypeError);
    expect(simplifyPresentation([x, y], [x.pow(-3), x.pow(6), y.mul(x).mul(y.inverse()).mul(x.pow(4))])[1].map(s)).toEqual(['x**3', 'y*x*y**-1*x']);
  });
});

describe('low index subgroups', () => {
  it('SymPy test_low_index_subgroups', () => {
    const f = new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(7)]);
    expect(lowIndexSubgroups(f, 15).map((c) => c.table)).toEqual(ref.low_index.N15);
    expect(lowIndexSubgroups(f, 10, [x]).map((c) => c.table)).toEqual(ref.low_index.N10x);
  });
  it('the search steps', () => {
    const f = new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(4)]);
    const C = new CosetTable(f, []);
    const R1 = C.conjugates(f.relators);
    const S1: CosetTable[] = [];
    tryDescendant(S1, C, R1, [], 2, 0, x, 0, []);
    expect(S1.length).toBeGreaterThan(0);
    const S2: CosetTable[] = [];
    descendantSubgroups(S2, C, R1, x, [x.mul(y).pow(4)], 3, [y]);
    expect(S2.map((c) => c.table)).toEqual([[[0, 0, 0, 0]], [[1, 1, 0, 0], [0, 0, 1, 1]]]);
    const D = new CosetTable(f, []);
    D.table = [[1, 1, 0, 0], [0, 0, 1, 1]];
    D.p = [0, 1];
    expect(firstInClass(D)).toBe(true);
    expect(firstInClass(D, [y])).toBe(true);
    D.table = [[0, 0, 1, 1], [1, 1, null, 0]];
    expect(firstInClass(D)).toBe(true);
    expect(() => firstInClass(D, [x.mul(y)])).toThrow(RangeError);
  });
});

describe('subgroups of free groups (Stallings foldings; SymPy can raise or loop)', () => {
  it('membership', () => {
    const H = new FpSubgroup(F, [x.pow(2).mul(y), y.pow(3)]);
    expect(H.contains(x.pow(2).mul(y).pow(-2))).toBe(true);
    expect(H.contains(y.pow(3).mul(x.pow(2)).mul(y))).toBe(true);
    expect(H.contains(y)).toBe(false);
    expect(H.contains(x.pow(2))).toBe(false);
    expect(H.contains(F.identity)).toBe(true);
    expect(H.contains(x.pow(2).mul(y.pow(4)))).toBe(true);
    // folding of a generator against another
    const K = new FpSubgroup(F, [x.mul(y).mul(x.inverse()), x.mul(y.pow(2)).mul(x.inverse()), y.mul(x).mul(y)]);
    expect(K.contains(x.mul(y).mul(x.inverse()))).toBe(true);
    expect(K.contains(y.mul(x).mul(y).mul(x.mul(y).mul(x.inverse())))).toBe(true);
    expect(K.contains(x)).toBe(false);
    expect(K.order()).toBe(S.Infinity);
    expect(s(K.toFpGroup())).toBe('<free group on the generators (x_0, x_1, x_2)>');
    expect(s(new FpSubgroup(F, [x.mul(x.inverse())]).order())).toBe('1');
  });
  it('the normal closure (the word problem of the quotient)', () => {
    const N = new FpSubgroup(F, [x.pow(2), y.pow(2), x.mul(y).pow(2)], true);
    expect(N.contains(x.mul(y).mul(x.inverse()).mul(y.inverse()))).toBe(true);
    expect(N.contains(x)).toBe(false);
    const M = new FpSubgroup(F, [x.mul(y).mul(x.inverse()).mul(y.inverse())], true);
    expect(M.contains(y.mul(x).mul(y.inverse()).mul(x.inverse()))).toBe(true);
  });
});

describe('more paths', () => {
  it('equality, subgroups, coset tables and orders', () => {
    const G = new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(4)]);
    expect(G.equals(x, y)).toBe('unknown');
    expect(G.equals(x, x.inverse())).toBe(true);
    G.makeConfluent();
    expect(G.equals(x, y)).toBe(false);
    expect(() => G.subgroup([1 as never])).toThrow(RangeError);
    expect(() => G.subgroup([new FreeGroup('u').generators[0]!])).toThrow(RangeError);
    expect(G.cosetTable([])).toBe(G.cosetTable([]));
    expect(s(G.index([]))).toBe('24');
    // the second half of the generators gives the subgroup of finite index
    const H = new FpGroup(F, [x.pow(2), y.pow(300), x.mul(y).mul(x.inverse()).mul(y.inverse()), x.pow(400)]);
    expect(H.mostFrequentGenerator().equals(x)).toBe(true);
    expect(s(H.order())).toBe('600');
    const [Fa, a, b] = freeGroup('a, b') as [FreeGroup, FreeGroupElement, FreeGroupElement];
    const cox = new FpGroup(Fa, [a.pow(6), b.pow(6), a.mul(b).pow(2), a.pow(2).mul(b.pow(2)).pow(2), a.pow(3).mul(b.pow(3)).pow(5)]);
    const limit = CosetTable.cosetTableMaxLimit;
    CosetTable.cosetTableMaxLimit = 150;
    try {
      expect(() => cox.order()).toThrow(NotImplementedError);
    } finally {
      CosetTable.cosetTableMaxLimit = limit;
    }
    const f = new FpGroup(F, [x.pow(3), y.pow(5), x.mul(y).pow(2)]);
    const [g, r, im] = reidemeisterPresentation(f, [x.mul(y), x.inverse().mul(y.inverse()).mul(x).mul(y).mul(x)], undefined, true);
    expect([g.map(s), r.length, im.map(s)]).toEqual([['y_1', 'y_2'], 3, ['x*y', 'x**-1*y**2*x**-1']]);
  });
  it('folding, normal closures and first_in_class', () => {
    expect(new FpSubgroup(F, [x.pow(2)]).contains(y)).toBe(false);
    expect(new FpSubgroup(F, [x.pow(2), x.pow(3)]).contains(x)).toBe(true);
    const K = new FpSubgroup(F, [x.mul(y).mul(x.inverse()), x.mul(y.pow(2)).mul(x.inverse()), y.pow(3), x.mul(y.pow(5)).mul(x.inverse()).mul(y.inverse())]);
    expect(K.contains(y)).toBe(true);
    expect(K.contains(x.mul(y).mul(x.inverse()).mul(y))).toBe(true);
    expect(K.contains(x)).toBe(false);
    const L = new FpSubgroup(F, [y.mul(x).mul(y.inverse()), y.mul(x.pow(2)).mul(y.inverse()), x.mul(y).mul(x), x.pow(2).mul(y).mul(x.pow(2))]);
    expect(L.contains(x.mul(y).mul(x).mul(y.mul(x).mul(y.inverse())))).toBe(true);
    const N = new FpSubgroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(4)], true);
    expect(N.contains(x)).toBe(false);
    expect(N.contains(x.mul(y).pow(-4))).toBe(true);
    const D = new CosetTable(new FpGroup(F, []), []);
    D.table = [[0, 0, 0, 0], [1, 1, 1, 1]];
    D.p = [0, 1];
    expect(firstInClass(D)).toBe(true);
    expect(firstInClass(D, [y.inverse()])).toBe(true);
  });
});

