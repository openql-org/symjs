// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups } from '../../src';
it('constructs all transitive subgroups through degree six', () => {
  const orders = [[1], [2], [3,6], [4,4,8,12,24], [5,10,20,60,120], [6,6,12,12,18,24,24,24,36,36,48,60,72,120,360,720]];
  [S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups].forEach((groups, n) => {
    Object.values(groups).forEach((name, i) => {
      const group = name.getPermGroup();
      expect(Number(group.order())).toBe(orders[n]?.[i]);
      expect(group.isTransitive()).toBe(true);
      expect(String(name)).toBe(`S${n+1}TransitiveSubgroups.${name.name}`);
    });
  });
});
