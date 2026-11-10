// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// References from SymPy 1.14.0 (scripts/gen_fpgroups.py): words of a free group, finitely presented
// groups (orders, coset tables by both strategies, coset representatives, Reidemeister-Schreier and
// simplified presentations, low index subgroups, rewriting systems), subgroups, homomorphisms,
// presentations of permutation groups and polycyclic collectors.
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { Sym } from '../../src';
import {
  AlternatingGroup,
  Collector,
  CyclicGroup,
  DihedralGroup,
  FpGroup,
  FpSubgroup,
  FreeGroupElement,
  Permutation,
  PermutationGroup,
  SymmetricGroup,
  cosetEnumerationC,
  cosetEnumerationR,
  freeGroup,
  groupHomomorphism,
  groupIsomorphism,
  lowIndexSubgroups,
  modifiedCosetEnumerationR,
  reidemeisterPresentation,
  simplifyPresentation,
} from '../../src/combinatorics';

type Af = [string, number][];
const ref = JSON.parse(readFileSync(new URL('./fpgroups.references.json', import.meta.url), 'utf8'));
const [F, x, y] = freeGroup('x, y') as [ReturnType<typeof freeGroup>[0], FreeGroupElement, FreeGroupElement];
const word = (a: Af): FreeGroupElement => F.dtype(a.map(([s, e]) => [new Sym(s), e]));
const WORDS: FreeGroupElement[] = ref.words.map((w: { w: Af }) => word(w.w));
const s = (v: unknown): string => String(v);

describe('words of a free group', () => {
  (ref.words as Record<string, any>[]).forEach((r, i) => it(`word ${i}`, () => {
    const w = WORDS[i]!;
    expect(s(w)).toBe(r.str);
    expect(s(w.inverse())).toBe(r.inverse);
    expect(w.length).toBe(r.len);
    expect(s(w.cyclicReduction())).toBe(r.cyclic_reduction);
    expect(s(w.cyclicReduction(true)[1])).toBe(r.removed);
    expect(s(w.identityCyclicReduction())).toBe(r.identity_cyclic_reduction);
    expect(w.isCyclicallyReduced()).toBe(r.is_cyclically_reduced);
    expect([...w.cyclicConjugates()].map(s).sort()).toEqual(r.cyclic_conjugates);
    expect(w.exponentSum(x)).toBe(r.exponent_sum_x);
    expect(w.exponentSum(y.inverse())).toBe(r.exponent_sum_yi);
    expect(w.generatorCount(y)).toBe(r.generator_count_y);
    expect(s(w.eliminateWord(x, y.pow(2), true))).toBe(r.eliminate_x);
    expect(s(w.eliminateWords([x.mul(y)], true))).toBe(r.eliminate_xy);
    expect(s(w.eliminateWord(x.inverse(), y, false, false))).toBe(r.eliminate_noinv);
    expect(s(w.subword(1, Math.min(3, w.length)))).toBe(r.subword_1_3);
    expect(s(w.cyclicSubword(1, w.length + 3))).toBe(r.cyclic_subword);
    expect(w.powerOf(x)).toBe(r.power_of_x);
    expect(w.powerOf(x.mul(y))).toBe(r.power_of_xy);
    expect(w.letterForm.map(s)).toEqual(r.letters);
    expect(WORDS.map((v) => w.lt(v))).toEqual(r.lt);
    expect(WORDS.map((v) => w.isCyclicConjugate(v))).toEqual(r.cyclic_conjugate);
    expect(WORDS.map((v) => w.isDependent(v))).toEqual(r.dependent);
    expect(w.extRep.map(s)).toEqual(r.ext_rep);
  }));
});

describe('finitely presented groups', () => {
  for (const [name, r] of Object.entries<Record<string, any>>(ref.groups)) {
    it(name, () => {
      const G = new FpGroup(F, r.rels.map(word));
      expect(s(G)).toBe(r.str);
      expect(s(G.order())).toBe(r.order);
      if (!r.table) return;
      expect(G.cosetTable([])).toEqual(r.table);
      for (const c of r.cosets) {
        const H = c.H.map(word);
        const C = cosetEnumerationR(G, H);
        C.compress();
        C.standardize();
        expect(C.table).toEqual(c.r);
        const D = cosetEnumerationC(G, H);
        D.compress();
        D.standardize();
        expect(D.table).toEqual(c.c);
        expect(s(G.index(H))).toBe(c.index);
        expect(C.table.map((_r, i) => s(C.cosetRepresentative(i)))).toEqual(c.reps);
      }
      const [g, rels] = reidemeisterPresentation(G, [x]);
      expect([`[${g.map(s).join(', ')}]`, `[${rels.map(s).join(', ')}]`]).toEqual(r.reidemeister);
      expect(lowIndexSubgroups(G, 4).map((c) => c.table)).toEqual(r.low_index);
      expect(`[${simplifyPresentation(G).relators.map(s).join(', ')}]`).toBe(r.simplified);
      expect(G.isAbelian).toBe(r.abelian);
      expect(G.isSolvable).toBe(r.solvable);
      expect(G.isNilpotent).toBe(r.nilpotent);
      expect(G.isCyclic).toBe(r.cyclic);
      expect(`[${G.abelianInvariants().join(', ')}]`).toBe(r.invariants);
      expect(G.elements.length).toBe(r.elements);
      expect(G.derivedSeries().map((t) => t.length)).toEqual(r.derived);
      expect(G.center().length).toBe(r.center);
      G.makeConfluent();
      expect(WORDS.map((w) => s(G.reduce(w)))).toEqual(r.reduce);
      expect(WORDS.map((w) => G.equals(w, x))).toEqual(r.equals);
      expect(WORDS.map((w) => s(G.rewritingSystem.reduceUsingAutomaton(w)))).toEqual(r.automaton);
      expect(G.rewritingSystem.isConfluent).toBe(r.confluent);
    });
  }
});

describe('subgroups and homomorphisms', () => {
  it('a subgroup of a finitely presented group', () => {
    const fp = new FpGroup(F, ref.groups.S4.rels.map(word));
    const K = new FpSubgroup(fp, [x.mul(y)]);
    expect(WORDS.map((w) => K.contains(w))).toEqual(ref.subgroups.fp_contains);
    expect(s(K.order())).toBe(ref.subgroups.fp_order);
    expect(s(K)).toBe(ref.subgroups.str);
    const M = modifiedCosetEnumerationR(fp, [x.mul(y)]);
    M.compress();
    M.standardize();
    expect(M.table).toEqual(ref.subgroups.modified);
  });
  it('a homomorphism onto S4', () => {
    const h = ref.homomorphisms;
    const fp = new FpGroup(F, ref.groups.S4.rels.map(word));
    const T = groupHomomorphism(fp, SymmetricGroup(4), [x, y], [new Permutation(3).call(0, 1), new Permutation(1, 2, 3)]);
    expect(s(T.kernel().order())).toBe(h.kernel);
    expect(s(T.image().order())).toBe(h.image);
    expect(T.isInjective()).toBe(h.injective);
    expect(T.isSurjective()).toBe(h.surjective);
    expect(WORDS.map((w) => s(T.apply(w)))).toEqual(h.apply);
    expect(WORDS.map((w) => s(T.apply(T.invert(T.apply(w)))))).toEqual(h.invert);
    expect(s(new FpGroup(F, ref.groups.S3.rels.map(word)).toPermGroup()[0].order())).toBe(h.perm_order);
    expect(groupIsomorphism(DihedralGroup(3), SymmetricGroup(3), false)).toBe(h.iso_d3_s3);
    expect(groupIsomorphism(CyclicGroup(4), DihedralGroup(2), false)).toBe(h.iso_c4_d2);
    expect(groupIsomorphism(new FpGroup(F, ref.groups.S3.rels.map(word)), SymmetricGroup(3), false)).toBe(h.iso_fp);
  });
});

describe('presentations of permutation groups', () => {
  const groups: Record<string, PermutationGroup> = { D4: DihedralGroup(4), S4: SymmetricGroup(4), A4: AlternatingGroup(4), C6: CyclicGroup(6), D6: DihedralGroup(6) };
  for (const [name, r] of Object.entries<Record<string, any>>(ref.presentations)) {
    it(name, () => {
      const G = groups[name]!;
      const p = G.presentation();
      expect(s(G.order())).toBe(r.order);
      expect(s(p.order())).toBe(r.presentation);
      expect(p.generators.length).toBe(r.gens);
      expect(s(G.strongPresentation().order())).toBe(r.strong);
    });
  }
});

describe('polycyclic collectors', () => {
  const groups: Record<string, PermutationGroup> = { S4: SymmetricGroup(4), D4: DihedralGroup(4), C6: CyclicGroup(6) };
  for (const [name, r] of Object.entries<Record<string, any>>(ref.pc)) {
    it(name, () => {
      const pcgs = r.pcgs.map((a: number[]) => new Permutation(a));
      const series = r.series.map((gs: number[][]) => new PermutationGroup(gs.map((a) => new Permutation(a))));
      const C = new Collector(pcgs, series, r.relative_order);
      expect([...C.pcPresentation].map(([k, v]) => `${s(k)}: ${Array.isArray(v) ? '()' : s(v)}`).sort()).toEqual(r.presentation);
      const cmp = (a: number[], b: number[]): number => { const i = a.findIndex((v, k) => v !== b[k]); return i < 0 ? 0 : a[i]! - b[i]!; };
      const els = groups[name]!.elements.sort((a, b) => cmp(a.arrayForm, b.arrayForm));
      expect(els.map((g) => C.exponentVector(g))).toEqual(r.vectors);
      expect(els.map((g) => C.depth(g))).toEqual(r.depths);
      // SymPy returns [] (r.induced is 0): its depth bound d < len(pcgs) drops the last generator
      expect(r.induced).toBe(0);
      expect(C.inducedPcgs([pcgs[pcgs.length - 1]]).map(String)).toEqual([String(pcgs[pcgs.length - 1])]);
    });
  }
});
