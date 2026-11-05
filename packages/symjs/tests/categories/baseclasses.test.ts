// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Adapted from SymPy 1.14 categories/tests/test_baseclasses.py (BSD-3-Clause).
import { describe, expect, it } from 'vitest';
import type { MorphismProperties } from '../../src/categories';
import { Category, CategoryClass, CompositeMorphism, Diagram, IdentityMorphism, Morphism, NamedMorphism, SymObject, categoryObject } from '../../src/categories';
import { Dict, Tuple, Sym, symbol, latex } from '../../src/core';
import { EmptySet, FiniteSet, Reals } from '../../src/sets';
import { CompositeMorphismNode } from '../../src/categories/baseclasses';
const A = new SymObject('A'), B = new SymObject('B'), C = new SymObject('C'), D = new SymObject('D');
const f = NamedMorphism(A, B, 'f'), g = NamedMorphism(B, C, 'g'), h = NamedMorphism(C, D, 'h');
const set = (...xs: Parameters<typeof FiniteSet.of>): ReturnType<typeof FiniteSet.of> => FiniteSet.of(...xs);

describe('category objects and morphisms', () => {
  it('keeps object identity distinct from ordinary symbols and prints SymPy forms', () => {
    expect(categoryObject('A').equals(A)).toBe(true);
    expect(A.equals(symbol('A'))).toBe(false);
    expect(A.toString()).toBe('Object("A")');
    expect(A.sortClass).toBe('Object');
    expect(latex(A)).toBe('A');
    expect(new SymObject('A', { real: true }).equals(A)).toBe(false);
    expect(f.domain).toBe(A); expect(f.codomain).toBe(B); expect(f.name).toBe('f');
    expect(f.equals(NamedMorphism(A, B, 'f'))).toBe(true);
    expect(f.equals(NamedMorphism(A, B, 'g'))).toBe(false);
    expect(f.equals(NamedMorphism(A, C, 'f'))).toBe(false);
    expect(f.toString()).toBe('NamedMorphism(Object("A"), Object("B"), "f")');
    expect(latex(f)).toBe('f:A\\rightarrow B');
    expect(f.isScalar).toBe(false); expect(f.isCommutative).toBe(false);
  });
  it('respects identities, order and associativity', () => {
    const ia = IdentityMorphism(A), ib = IdentityMorphism(B);
    expect(ia.codomain).toBe(A); expect(ia.domain).toBe(A);
    expect(ia.equals(ib)).toBe(false);
    expect(f.mul(ia).equals(f)).toBe(true); expect(ib.mul(f).equals(f)).toBe(true);
    expect(ia.mul(ia).equals(ia)).toBe(true);
    expect(CompositeMorphism(ia)).toBe(ia);
    expect(CompositeMorphism(f)).toBe(f);
    const k = g.compose(f);
    expect(k.domain).toBe(A); expect(k.codomain).toBe(C);
    expect(k.equals(CompositeMorphism(f, g))).toBe(true);
    expect(k.equals(CompositeMorphism([f, g]))).toBe(true);
    expect(k.equals(g.mul(f))).toBe(true);
    expect(CompositeMorphism(k).equals(k)).toBe(true);
    expect(h.mul(k).equals(h.mul(g).mul(f))).toBe(true);
    expect(h.mul(k).equals(CompositeMorphism(f, g, h))).toBe(true);
    expect(k.toString()).toBe('CompositeMorphism((NamedMorphism(Object("A"), Object("B"), "f"), NamedMorphism(Object("B"), Object("C"), "g")))');
    expect(latex(k)).toBe('g\\circ f:A\\rightarrow C');
    expect(latex(ia)).toBe('id:A\\rightarrow A');
    expect(ia.toString()).toBe('IdentityMorphism(Object("A"))');
    const composite = k as CompositeMorphismNode;
    expect(composite.components).toEqual([f, g]);
    expect(composite.flatten('u').equals(NamedMorphism(A, C, 'u'))).toBe(true);
  });
  it('rebuilds morphisms through expression traversal', () => {
    expect(f.withArgs([B, C]).equals(NamedMorphism(B, C, 'f'))).toBe(true);
    expect(IdentityMorphism(A).withArgs([C]).equals(IdentityMorphism(C))).toBe(true);
    const composite = new CompositeMorphismNode([f, g]);
    expect(composite.withArgs([Tuple(g, h)]).equals(h.compose(g))).toBe(true);
  });
  it('rejects invalid compositions and abstract construction', () => {
    expect(() => f.compose(g)).toThrow('Uncomposable');
    expect(() => f.mul(1)).toThrow('morphism');
    expect(() => NamedMorphism(A, B, '')).toThrow('Empty morphism');
    expect(() => CompositeMorphism()).toThrow('at least one');
    expect(() => Reflect.construct(Morphism, ['Morphism', [A, B]])).toThrow('Cannot instantiate');
  });
});

describe('diagrams', () => {
  it('adds identities and composites and uses structural keys', () => {
    const d = Diagram([f, g]);
    expect(d.objects.equals(set(A, B, C))).toBe(true);
    expect(d.premises.containsKey(g.compose(f))).toBe(true);
    expect(d.hom(A, C)[0].equals(set(g.compose(f)))).toBe(true);
    expect(d.hom(A, C)[1].equals(EmptySet)).toBe(true);
    expect(d.hom(A, A)[0].equals(set(IdentityMorphism(A)))).toBe(true);
    expect(d.hom(B, B)[0].equals(set(IdentityMorphism(B)))).toBe(true);
    expect(Diagram([f, f]).equals(Diagram([f]))).toBe(true);
    expect(Diagram([IdentityMorphism(A), f]).equals(Diagram([f]))).toBe(true);
    const compositeOnly = Diagram([g.compose(f)]);
    expect(compositeOnly.premises.containsKey(f)).toBe(true);
    expect(compositeOnly.premises.containsKey(g)).toBe(true);
    expect(Diagram([g, f]).hom(A, C)[0].equals(set(g.compose(f)))).toBe(true);
  });
  it('intersects properties along a composite and unions repeated properties', () => {
    const d = Diagram(new Map<Morphism, MorphismProperties>([[f, ['unique', 'isomorphism']], [g, 'unique']]));
    expect(d.premises.get(g.compose(f)).equals(set(new Sym('unique')))).toBe(true);
    const repeated = Diagram(new Map([[f, 'unique'], [NamedMorphism(A, B, 'f'), 'isomorphism']]));
    expect(repeated.premises.get(f).equals(set(new Sym('unique'), new Sym('isomorphism')))).toBe(true);
    const dictionary = Diagram(Dict([[f, set(new Sym('unique'))], [g, new Sym('unique')]]));
    expect(dictionary.premises.get(g.compose(f)).equals(set(new Sym('unique')))).toBe(true);
    expect(Diagram(new Map([[f, set(new Sym('unique'))]])).premises.get(f).equals(set(new Sym('unique')))).toBe(true);
    expect(() => Diagram(new Map([[IdentityMorphism(A), 'unique']]))).toThrow('cannot have properties');
  });
  it('keeps conclusions separate and rejects their new objects', () => {
    const d = Diagram([f, g], new Map([[g.compose(f), 'unique']]));
    expect(d.conclusions.equals(Dict([[g.compose(f), set(new Sym('unique'))]]))).toBe(true);
    expect(d.hom(A, C).every((s) => s.equals(set(g.compose(f))))).toBe(true);
    expect(Diagram([f, g], [g.compose(f)]).hom(A, C).every((s) => s.equals(set(g.compose(f))))).toBe(true);
    expect(Diagram([f], [g]).conclusions.size).toBe(0);
    expect(Diagram([f], [h]).conclusions.size).toBe(0);
    expect(Diagram([f, g], [f, g]).conclusions.containsKey(g.compose(f))).toBe(true);
  });
  it('handles empty diagrams and prints them', () => {
    const d = Diagram();
    expect(d.premises.size).toBe(0); expect(d.conclusions.size).toBe(0);
    expect(d.objects.equals(EmptySet)).toBe(true);
    expect(d.toString()).toBe('Diagram({}, {}, EmptySet)');
    expect(latex(d)).toBe(latex(Dict([])));
    expect(Diagram([f]).withArgs([Dict([[g, EmptySet]]), Dict([])]).equals(Diagram([g]))).toBe(true);
  });
  it('compares and restricts subdiagrams including properties', () => {
    const d = Diagram([f, g], new Map([[f, 'unique'], [g.compose(f), 'veryunique']]));
    const small = Diagram([f], new Map([[f, 'unique']]));
    expect(d.isSubdiagram(small)).toBe(true); expect(small.isSubdiagram(d)).toBe(false);
    expect(d.isSubdiagram(Diagram([f, g], new Map([[g.compose(f), 'different']])))).toBe(false);
    expect(d.subdiagramFromObjects(set(A, B)).equals(small)).toBe(true);
    expect(d.subdiagramFromObjects(EmptySet).equals(Diagram())).toBe(true);
    expect(() => d.subdiagramFromObjects(set(D))).toThrow('belong');
    expect(() => d.subdiagramFromObjects(Reals)).toThrow('finite');
    expect(Diagram(new Map([[f, 'a']])).isSubdiagram(Diagram(new Map([[f, 'b']])))).toBe(false);
  });
});

it('stores category objects and asserted commutative diagrams without inventing hom sets', () => {
  const d = Diagram([f, g]);
  const k = Category('K', d.objects, [d]);
  expect(k.name).toBe('K'); expect(k.objects.objects.equals(d.objects)).toBe(true);
  expect(k.commutativeDiagrams.equals(set(d))).toBe(true);
  expect(k.objects.isProper).toBe(false);
  expect(k.objects.withArgs([set(A)]).equals(new CategoryClass(set(A)))).toBe(true);
  expect(k.withArgs([new CategoryClass(set(A)), EmptySet]).equals(Category('K', set(A)))).toBe(true);
  expect(k.toString()).toBe('Category("K")'); expect(latex(k)).toBe('\\mathbf{K}');
  expect(Category('K').commutativeDiagrams.equals(EmptySet)).toBe(true);
  expect(Category('K').equals(k)).toBe(false);
  expect(() => Category('')).toThrow('empty name');
  expect(() => k.hom(A, B)).toThrow('not implemented');
  expect(() => k.allMorphisms()).toThrow('not implemented');
});

it('accepts symbolic property labels without string coercion', () => {
  const a = new SymObject('A'), b = new SymObject('B'), f = NamedMorphism(a, b, 'f');
  const property = new Sym('monic');
  const d = Diagram(new Map([[f, [property]]]));
  expect(d.premises.get(f).equals(set(property))).toBe(true);
});
