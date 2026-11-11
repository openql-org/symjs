// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import {
  AlternatingGroup, CyclicGroup, SymmetricGroup, isIsomorphic, permutationRepr,
  S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups,
  TransitiveSubgroup, findTransitiveSubgroupsOfS6, fourGroup, M20, S3InS6, PGL2F5,
} from '../../src';
import type { PermutationGroupNode } from '../../src/combinatorics/permgroups';

it('names the transitive subgroups through degree six like SymPy enumerations', () => {
  const orders = [[1], [2], [3, 6], [4, 4, 8, 12, 24], [5, 10, 20, 60, 120], [6, 6, 12, 12, 18, 24, 24, 24, 36, 36, 48, 60, 72, 120, 360, 720]];
  [S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups].forEach((groups, n) => {
    [...groups].forEach((name: TransitiveSubgroup, i) => {
      const group = name.getPermGroup();
      expect(Number(group.order())).toBe(orders[n]?.[i]);
      expect(group.isTransitive()).toBe(true);
      expect(group.degree).toBe(n + 1);
      expect(name.degree).toBe(n + 1);
      expect(String(name)).toBe(`S${n + 1}TransitiveSubgroups.${name.name}`);
    });
  });
  expect(S6TransitiveSubgroups.S4p.repr()).toBe("<S6TransitiveSubgroups.S4p: 'S4+'>");
  expect(S6TransitiveSubgroups.A4xC2.value).toBe('A4 x C2');
  expect(S4TransitiveSubgroups.V).toBe(S4TransitiveSubgroups.V);
});

it('constructs the Klein four-group and M20 (SymPy test_four_group, test_M20)', () => {
  const G = fourGroup();
  expect(G.isSubgroup(AlternatingGroup(4))).toBe(true);
  expect(G.isCyclic).toBe(false);
  expect(String(G)).toBe('PermutationGroup([\n    (0 1)(2 3),\n    (0 2)(1 3)])');
  const M = M20();
  expect(M.isSubgroup(SymmetricGroup(5))).toBe(true);
  expect(M.isSubgroup(AlternatingGroup(5))).toBe(false);
  expect([M.degree, Number(M.order()), M.isTransitive()]).toEqual([5, 20, true]);
  expect(S3InS6().isDihedral).toBe(true);
  expect(PGL2F5().isSolvable).toBe(false);
});

it('distinguishes all 16 transitive subgroups of S6 (SymPy test_S6_transitive_subgroups)', () => {
  const ts = S6TransitiveSubgroups;
  const A6 = AlternatingGroup(6);
  const cases: [S6TransitiveSubgroups, boolean, number, PermutationGroupNode | undefined, PermutationGroupNode | undefined][] = [
    [ts.C6, false, 6, CyclicGroup(6), undefined], [ts.S3, false, 6, SymmetricGroup(3), undefined],
    [ts.D6, false, 12, undefined, undefined], [ts.A4, true, 12, undefined, undefined],
    [ts.G18, false, 18, undefined, undefined], [ts.A4xC2, false, 24, undefined, SymmetricGroup(4)],
    [ts.S4m, false, 24, SymmetricGroup(4), undefined], [ts.S4p, true, 24, undefined, undefined],
    [ts.G36m, false, 36, undefined, undefined], [ts.G36p, true, 36, undefined, undefined],
    [ts.S4xC2, false, 48, undefined, undefined], [ts.PSL2F5, true, 60, undefined, undefined],
    [ts.G72, false, 72, undefined, undefined], [ts.PGL2F5, false, 120, undefined, undefined],
    [ts.A6, true, 360, undefined, undefined], [ts.S6, false, 720, undefined, undefined],
  ];
  for (const [name, alt, order, isom, notIsom] of cases) {
    const G = name.getPermGroup();
    expect([G.isTransitive(), G.degree, G.isSubgroup(A6), Number(G.order())]).toEqual([true, 6, alt, order]);
    if (isom) expect(isIsomorphic(G, isom)).toBe(true);
    if (notIsom) expect(isIsomorphic(G, notIsom)).toBe(false);
  }
});

it('searches S6 for generators of the transitive subgroups', () => {
  const lines: string[] = [];
  const all = findTransitiveSubgroupsOfS6(...S6TransitiveSubgroups, { printReport: (t) => lines.push(t) });
  expect([...all.keys()].length).toBe(16);
  for (const [name, G] of all) {
    expect(Number(G.order())).toBe(Number(name.getPermGroup().order()));
    expect(G.isTransitive()).toBe(true);
  }
  expect(all.get(S6TransitiveSubgroups.S4p)?.isSubgroup(AlternatingGroup(6))).toBe(true);
  expect(lines[0]).toMatch(/^=+\nS6TransitiveSubgroups\.A4:\n\[Permutation/);
  expect(lines[0]).toContain(permutationRepr(all.get(S6TransitiveSubgroups.A4)!.generators[0]!));
  const some = findTransitiveSubgroupsOfS6(S6TransitiveSubgroups.A4xC2, S6TransitiveSubgroups.S4xC2);
  expect([...some.keys()].map(String)).toEqual(['S6TransitiveSubgroups.A4', 'S6TransitiveSubgroups.S4m', 'S6TransitiveSubgroups.A4xC2', 'S6TransitiveSubgroups.S4xC2']);
  expect(findTransitiveSubgroupsOfS6().size).toBe(0);
}, 600_000);
