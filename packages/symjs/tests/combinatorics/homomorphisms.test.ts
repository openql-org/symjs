// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Group homomorphisms and isomorphisms (after SymPy 1.14 test_homomorphisms.py), and the
// homomorphisms of a permutation group on an orbit and on a block system.
import { describe, expect, it } from 'vitest';
import { NotImplementedError } from '../../src/core/errors';
import { NoMatch } from '../../src/core/truth';
import {
  AbelianGroup,
  AlternatingGroup,
  CyclicGroup,
  DihedralGroup,
  FpGroup,
  FpSubgroup,
  FreeGroup,
  FreeGroupElement,
  GroupHomomorphism,
  Permutation,
  PermutationGroup,
  SymmetricGroup,
  blockHomomorphism,
  freeGroup,
  groupHomomorphism,
  groupIsomorphism,
  isIsomorphic,
  orbitHomomorphism,
} from '../../src/combinatorics';

const [F, a, b] = freeGroup('a, b') as [FreeGroup, FreeGroupElement, FreeGroupElement];

describe('homomorphisms', () => {
  it('FpGroup -> PermutationGroup', () => {
    const G = new FpGroup(F, [a.pow(3), b.pow(3), a.mul(b).pow(2)]);
    const c = new Permutation(3).call(0, 1, 2);
    const d = new Permutation(3).call(1, 2, 3);
    const T = groupHomomorphism(G, AlternatingGroup(4), [a, b], [c, d]);
    expect(T.apply(a.mul(b.pow(2)).mul(a.inverse())).equals(c.mul(d.pow(2)).mul(c.inverse()))).toBe(true);
    expect(T.isIsomorphism()).toBe(true);
    const p = new Permutation(3).call(0, 2, 3);
    expect(T.apply(T.invert(p)).equals(p)).toBe(true);
    expect(T.invert([p, c]).length).toBe(2);
    expect(T.apply([a, b]).length).toBe(2);
    expect(String(T)).toBe('GroupHomomorphism(<fp group on the generators (a, b)>, PermutationGroup([\n    (3)(0 1 2),\n    (1 2 3)]))');
    const U = groupHomomorphism(G, AlternatingGroup(4), G.generators);
    expect(U.isTrivial()).toBe(true);
    expect(U.kernel().order()).toEqual(G.order());
    expect(() => U.apply(new FreeGroup('u').generators[0]!)).toThrow(RangeError);
  });
  it('FpGroup on one generator -> PermutationGroup', () => {
    const [E, e] = freeGroup('e') as [FreeGroup, FreeGroupElement];
    const G = new FpGroup(E, [e.pow(8)]);
    const P = new PermutationGroup([new Permutation(0, 1, 2, 3), new Permutation(0, 2)]);
    const T = groupHomomorphism(G, P, [e], [new Permutation(0, 1, 2, 3)]);
    expect(T.image().order()).toBe(4n);
    const q = new Permutation(0, 2).call(1, 3);
    expect(T.apply(T.invert(q)).equals(q)).toBe(true);
    expect(T.isSurjective()).toBe(false);
    expect(String(T.kernel().order())).toBe('2');
    const V = groupHomomorphism(E, AlternatingGroup(4), E.generators, [new Permutation(3).call(0, 1, 2)]);
    expect(String(V.invert(new Permutation(3).call(0, 1, 2).pow(2)))).toBe('e**-1');
    expect(() => V.kernel()).toThrow(NotImplementedError);
  });
  it('FreeGroup -> FreeGroup and FpGroup', () => {
    const [E, e] = freeGroup('e') as [FreeGroup, FreeGroupElement];
    const T = groupHomomorphism(F, E, [a], [e]);
    expect(T.apply(a.pow(-2).mul(b.pow(4)).mul(a.pow(2))).isIdentity).toBe(true);
    expect(T.isSurjective()).toBe('unknown');
    const G = new FpGroup(F, [a.mul(b).mul(a.inverse()).mul(b.inverse())]);
    const U = groupHomomorphism(F, G, F.generators, G.generators);
    expect(String(U.invert(a.inverse().mul(b.inverse()).mul(a.pow(2))))).toBe('a*b**-1');
    expect(U.image()).toBeInstanceOf(FpSubgroup);
  });
  it('PermutationGroup -> PermutationGroup, composition and restriction', () => {
    const D = DihedralGroup(8);
    const p = new Permutation(0, 1, 2, 3, 4, 5, 6, 7);
    const P = new PermutationGroup(p);
    const T = groupHomomorphism(P, D, [p], [p]);
    expect(T.isInjective()).toBe(true);
    expect(T.isIsomorphism()).toBe(false);
    expect(T.invert(p.pow(3)).equals(p.pow(3))).toBe(true);
    const T2 = groupHomomorphism(F, P, [a], P.generators);
    const C = T.compose(T2);
    expect(C.domain).toBe(F);
    expect(C.codomain).toBe(D);
    expect(C.apply(a.mul(b)).equals(p)).toBe(true);
    expect(() => T2.compose(T)).toThrow(RangeError);
    const D3 = DihedralGroup(3);
    const I = groupHomomorphism(D3, D3, D3.generators, D3.generators);
    expect(I.isIsomorphism()).toBe(true);
    const H = new PermutationGroup([D3.generators[0]!]);
    const R = I.restrictTo(H);
    expect(R.domain).toBe(H);
    expect(() => I.restrictTo(DihedralGroup(4))).toThrow(RangeError);
    expect(I.invertSubgroup(H).order()).toBe(3n);
    expect(() => I.invertSubgroup(DihedralGroup(4))).toThrow(RangeError);
    const S3 = SymmetricGroup(3);
    const sign = groupHomomorphism(S3, CyclicGroup(2), S3.generators, S3.generators.map((g) => (g.isEven ? new Permutation(1) : new Permutation(0, 1))));
    expect(sign.kernel().order()).toBe(3n);
    expect(sign.invertSubgroup(CyclicGroup(2)).order()).toBe(6n);
    expect(new GroupHomomorphism(S3, S3, new Map([[S3.generators[0]!, S3.generators[0]!]])).images.size).toBe(1);
  });
  it('checks', () => {
    const x = new Permutation(1, 2, 3, 4);
    const y = new Permutation(1, 3);
    const G = new PermutationGroup([x, y]);
    expect(() => groupHomomorphism(G, G, [x], [x])).toThrow(RangeError);
    expect(() => groupHomomorphism(G, G, [new Permutation(0, 1)], [x])).toThrow(RangeError);
    expect(() => groupHomomorphism(G, G, [x, y], [new Permutation(0, 9)])).toThrow(RangeError);
    expect(() => groupHomomorphism(G, G, [x, y], [x])).toThrow(RangeError);
    expect(() => groupHomomorphism(1 as never, G, [])).toThrow(TypeError);
    expect(() => groupHomomorphism(G, 1 as never, [])).toThrow(TypeError);
    // an FpGroup codomain whose word problem needs the completion of its rewriting system
    const Q = new FpGroup(F, [a.pow(2), b.pow(2), a.mul(b).pow(3)]);
    expect(groupHomomorphism(SymmetricGroup(3), Q, SymmetricGroup(3).generators, [a.mul(b), a]).codomain).toBe(Q);
    expect(() => groupHomomorphism(SymmetricGroup(3), Q, SymmetricGroup(3).generators, [a, a])).toThrow(RangeError);
  });
});

describe('isomorphisms', () => {
  it('finitely presented groups', () => {
    expect(isIsomorphic(new FpGroup(F, [a.pow(2), b.pow(3), a.mul(b).pow(2)]), new FpGroup(F, [b.pow(3), a.pow(2), a.mul(b).pow(2)]))).toBe(true);
    const H = new FpGroup(F, [a.pow(3), b.pow(3), a.mul(b).pow(2)]);
    const [E, c, d] = freeGroup('c, d') as [FreeGroup, FreeGroupElement, FreeGroupElement];
    const G = new FpGroup(E, [c.pow(3), d.pow(3), c.mul(d).pow(2)]);
    const r = groupIsomorphism(G, H);
    expect(r[0]).toBe(true);
    if (r[0]) expect(String(r[1].apply(c.pow(3).mul(d.pow(2))))).toBe('a**3*b**2');
    expect(groupIsomorphism(G, AlternatingGroup(4), false)).toBe(true);
    const s = groupIsomorphism(G, AlternatingGroup(4));
    expect(s[0]).toBe(true);
    if (s[0]) expect(s[1].isIsomorphism()).toBe(true);
    const t = groupIsomorphism(AlternatingGroup(4), G);
    expect(t[0] && t[1].isIsomorphism()).toBe(true);
    expect(() => groupIsomorphism(new FpGroup(F, [a.pow(2)]), AlternatingGroup(4))).toThrow(NotImplementedError);
    expect(() => groupIsomorphism(AlternatingGroup(4), new FpGroup(F, [a.pow(2)]))).toThrow(NotImplementedError);
    expect(isIsomorphic(new FpGroup(F, [a, b.pow(5)]), CyclicGroup(5))).toBe(true);
  });
  it('permutation groups', () => {
    expect(isIsomorphic(DihedralGroup(8), new PermutationGroup(new Permutation(0, 1, 2, 3, 4, 5, 6, 7)))).toBe(false);
    expect(isIsomorphic(CyclicGroup(5), CyclicGroup(7))).toBe(false);
    expect(groupIsomorphism(DihedralGroup(4), CyclicGroup(8))).toEqual([false, NoMatch]);
    expect(groupIsomorphism(CyclicGroup(4), DihedralGroup(2))).toEqual([false, NoMatch]);
    // C6 generated by elements of orders 2 and 3: SymPy, mapping onto generators only, misses the isomorphism
    const C6 = new PermutationGroup([new Permutation(0, 2, 4).call(1, 3, 5), new Permutation(0, 3).call(1, 4).call(2, 5)]);
    expect(isIsomorphic(CyclicGroup(6), C6)).toBe(true);
    const u = groupIsomorphism(CyclicGroup(6), C6);
    expect(u[0] && u[1].isIsomorphism()).toBe(true);
    expect(isIsomorphic(SymmetricGroup(3), DihedralGroup(3))).toBe(true);
    expect(isIsomorphic(CyclicGroup(15), CyclicGroup(15))).toBe(true);
    expect(() => groupIsomorphism(1 as never, CyclicGroup(2))).toThrow(TypeError);
    expect(() => groupIsomorphism(CyclicGroup(2), 1 as never)).toThrow(TypeError);
  });
});

describe('orbit and block homomorphisms', () => {
  it('the action on an orbit', () => {
    const G = new PermutationGroup([new Permutation(0, 1, 2), new Permutation(3, 4)]);
    const T = orbitHomomorphism(G, [0, 1, 2]);
    expect(T.image().order()).toBe(3n);
    expect(T.kernel().order()).toBe(2n);
    const U = orbitHomomorphism(SymmetricGroup(3), [0, 1, 2]);
    expect(U.kernel().order()).toBe(1n);
  });
  it('the action on a block system', () => {
    const D = DihedralGroup(4);
    const blocks = D.minimalBlock([0, 2]);
    if (blocks === false) throw new Error('no block');
    const T = blockHomomorphism(D, blocks);
    expect(T.image().order()).toBe(2n);
    expect(T.kernel().order()).toBe(4n);
  });
});

describe('more paths', () => {
  it('kernels, preimages and checks', () => {
    const inf = new FpGroup(F, [a.pow(2)]);
    expect(() => groupHomomorphism(inf, CyclicGroup(2), [a, b], [new Permutation(0, 1), new Permutation(1)]).kernel()).toThrow(NotImplementedError);
    const C4 = CyclicGroup(4);
    const g = C4.generators[0]!;
    const I = groupHomomorphism(C4, C4, [g], [g]);
    expect(I.invertSubgroup(new PermutationGroup([g, g.pow(2)])).order()).toBe(4n);
    expect(() => groupHomomorphism(C4, C4, [g], [new Permutation(0, 9)])).toThrow(RangeError);
    expect(() => groupHomomorphism(C4, C4, [g], [g, g])).toThrow(RangeError);
    // the word problem of the codomain needs its rewriting system completed
    const S4 = new FpGroup(F, [a.pow(2), b.pow(3), a.mul(b).pow(4)]);
    const [E, e] = freeGroup('e') as [FreeGroup, FreeGroupElement];
    expect(groupHomomorphism(new FpGroup(E, [e.pow(4)]), S4, [e], [b.mul(a)]).codomain).toBe(S4);
    const T4 = new FpGroup(F, [a.pow(2), b.pow(3), a.mul(b).pow(4)]);
    // decided after completing the rewriting system: a^3 = a is not 1
    expect(() => groupHomomorphism(new FpGroup(E, [e.pow(3)]), new FpGroup(F, [a.pow(2), b.pow(3), a.mul(b).pow(4)]), [e], [a])).toThrow(/do not define/);
    T4.rewritingSystem.setMax(2);
    // a^3 = a is not decided by the initial rules, and the completion stops at two rules
    expect(() => groupHomomorphism(new FpGroup(E, [e.pow(3)]), T4, [e], [a])).toThrow(/Can't determine/);
  });
  it('more generators than the other group has', () => {
    const r = groupIsomorphism(AbelianGroup(2, 3), CyclicGroup(6));
    expect(r[0] && r[1].isIsomorphism()).toBe(true);
  });
  it('isomorphic presentations', () => {
    const G = new FpGroup(F, [a.pow(2), b.pow(3), a.mul(b).pow(2)]);
    const H = new FpGroup(F, [a.pow(2), b.pow(3), a.mul(b).pow(2)]);
    expect(groupIsomorphism(G, H, false)).toBe(true);
    const r = groupIsomorphism(G, H);
    expect(r[0]).toBe(true);
  });
});

