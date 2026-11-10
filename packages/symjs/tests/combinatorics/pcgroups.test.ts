// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Polycyclic groups and collectors (after SymPy 1.14 test_pc_groups.py): the pc presentation holds in
// the group, exponent vectors rebuild the generators and induced pcgs give upper triangular exponents.
import { describe, expect, it } from 'vitest';
import { NoMatch } from '../../src/core/truth';
import { AbelianGroup, AlternatingGroup, Collector, DihedralGroup, FreeGroup, FreeGroupElement, Permutation, PermutationGroup, PolycyclicGroup, SymmetricGroup } from '../../src/combinatorics';

const GROUPS: [string, PermutationGroup][] = [
  ['S3', SymmetricGroup(3)],
  ['S4', SymmetricGroup(4)],
  ['A4', AlternatingGroup(4)],
  ['D4', DihedralGroup(4)],
  ['D9', DihedralGroup(9)],
  ['D10', DihedralGroup(10)],
];
const evalWord = (pcgs: Permutation[], F: FreeGroup, af: [unknown, number][]): Permutation =>
  af.reduce((p, [s, e]) => p.mul(pcgs[F.symbols.findIndex((t) => t === s || String(t) === String(s))]!.pow(e)), new Permutation());

describe('polycyclic groups', () => {
  for (const [name, G] of GROUPS) {
    it(`${name}: the pc presentation, exponent vectors and induced pcgs`, () => {
      const pc = G.polycyclicGroup();
      const C = pc.collector;
      const F = C.freeGroup;
      expect(pc.length()).toBe(pc.pcgs.length);
      expect(pc.isPrimeOrder()).toBe(pc.relativeOrder.every((o) => [2n, 3n, 5n, 7n].includes(o)));
      expect(pc.relativeOrder.reduce((a, b) => a * b, 1n)).toBe(G.order());
      for (const [k, v] of C.pcPresentation) {
        const lhs = evalWord(pc.pcgs, F, k.arrayForm);
        if (v instanceof FreeGroupElement) expect(lhs.equals(evalWord(pc.pcgs, F, v.arrayForm))).toBe(true);
        else expect(lhs.isIdentity).toBe(true);
      }
      for (const gen of G.generators) {
        const exp = C.exponentVector(gen);
        const g = exp.reduce((p, e, i) => (e ? p.mul(pc.pcgs[i]!.pow(e)) : p), new Permutation());
        expect(g.equals(gen)).toBe(true);
      }
      const ipcgs = C.inducedPcgs([...G.generators]);
      const m = ipcgs.map((g) => C.exponentVector(g));
      m.forEach((row, i) => row.slice(0, i).forEach((v) => expect(v).toBe(0)));
      expect(C.constructiveMembershipTest(ipcgs, G.generators[0]!)).not.toBe(false);
      const [power, conjugate] = C.relations();
      expect(power.size + conjugate.size).toBe(C.pcPresentation.size);
      expect(C.pcRelators().size).toBe(C.pcPresentation.size);
    });
  }
  it('the collector methods (SymPy docstring examples)', () => {
    const G = SymmetricGroup(4);
    const pc = G.polycyclicGroup();
    const C = pc.collector;
    const F = C.freeGroup;
    const [x0, x1, x2, x3] = F.generators;
    expect(String(pc)).toBe('PolycyclicGroup(4)');
    expect(String(C)).toBe('Collector(<free group on the generators (x0, x1, x2, x3)>)');
    expect([...C.index.values()]).toEqual([0, 1, 2, 3]);
    const word = x2!.pow(2).mul(x1!.pow(7));
    expect(C.minimalUncollectedSubword(word)).toEqual([[F.symbols[2], 2]]);
    expect(C.minimalUncollectedSubword(x1!.mul(x0!))).toEqual([[F.symbols[1], 1], [F.symbols[0], 1]]);
    expect(C.minimalUncollectedSubword(x1!.mul(x0!.inverse()))).toEqual([[F.symbols[0], -1]]);
    expect(C.minimalUncollectedSubword(x0!.mul(x1!))).toBe(NoMatch);
    expect(C.minimalUncollectedSubword(F.identity)).toBe(NoMatch);
    expect(C.subwordIndex(x2!.pow(2).mul(x1!.pow(7)), x2!.pow(2).mul(x1!))).toEqual([0, 3]);
    expect(C.subwordIndex(x1!, x2!)).toEqual([-1, -1]);
    expect(String(C.collectedWord(x3!.mul(x2!).mul(x1!).mul(x0!)))).toMatch(/^x0/);
    expect(String(C.collectedWord(x3!.inverse().mul(x2!.pow(-2)).mul(x1!.inverse())))).not.toContain('**-');
    expect(C.depth(G.identity)).toBe(5);
    expect(C.leadingExponent(G.identity)).toBe(NoMatch);
    expect(C.leadingExponent(pc.pcgs[1]!)).toBe(1);
    expect(C.constructiveMembershipTest([pc.pcgs[3]!], pc.pcgs[0]!)).toBe(false);
    const again = new PolycyclicGroup(pc.pcgs, pc.pcSeries, pc.relativeOrder, C);
    expect(again.collector).toBe(C);
    expect(new Collector(pc.pcgs, pc.pcSeries, pc.relativeOrder, F).freeGroup).toBe(F);
  });
  it('collecting in an abelian group (trivial conjugate relators)', () => {
    const pc = AbelianGroup(2, 3).polycyclicGroup();
    const C = pc.collector;
    const [x0, x1] = C.freeGroup.generators;
    expect(String(C.collectedWord(x1!.mul(x0!)))).toBe(String(x0!.mul(x1!)));
  });
  it('a group that is not solvable', () => {
    expect(() => SymmetricGroup(5).polycyclicGroup()).toThrow(RangeError);
  });
});
