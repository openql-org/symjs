// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/group_constructs.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.combinatorics.group_constructs: DirectProduct.
 */

import { afNew } from './permutations';
import { PermutationGroupNode } from './permgroups';

/** SymPy DirectProduct(*groups): the direct product, each group acting on its own block of points. */
export function DirectProduct(...groups: PermutationGroupNode[]): PermutationGroupNode {
  const totalDegree = groups.reduce((s, g) => s + g.degree, 0);
  const gens: number[][] = [];
  let offset = 0;
  for (const group of groups) {
    for (const g of group.generators) {
      const a = Array.from({ length: totalDegree }, (_, i) => i);
      g.arrayForm.forEach((x, i) => (a[offset + i] = x + offset));
      gens.push(a);
    }
    offset += group.degree;
  }
  const uniq = [...new Map(gens.map((a) => [a.join(','), a] as const)).values()];
  return new PermutationGroupNode(uniq.map(afNew), { dups: false });
}
