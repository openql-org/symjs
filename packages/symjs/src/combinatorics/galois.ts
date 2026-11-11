// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/galois.py, BSD-3-Clause; see LICENSE.

import { defined } from '../core/guard';
import { Permutation } from './permutations';
import { PermutationGroup } from './permgroups';
import type { PermutationGroupNode } from './permgroups';
import data from './galoisdata';

/** A named transitive subgroup, with its faithful action on n points. */
export class TransitiveSubgroup {
  constructor(readonly degree: number, readonly name: string, readonly value: string, private readonly generators: readonly (readonly number[])[]) {}
  getPermGroup(): PermutationGroupNode { return PermutationGroup(this.generators.map((p) => new Permutation(p))); }
  toString(): string { return `S${this.degree}TransitiveSubgroups.${this.name}`; }
}
function group(degree: number, name: string): TransitiveSubgroup {
  const entry = defined(data.find((g) => g.degree === degree && g.name === name));
  return new TransitiveSubgroup(degree, name, entry.value, entry.generators);
}

export const S1TransitiveSubgroups = Object.freeze({
  S1: group(1, 'S1'),
});

export const S2TransitiveSubgroups = Object.freeze({
  S2: group(2, 'S2'),
});

export const S3TransitiveSubgroups = Object.freeze({
  A3: group(3, 'A3'),
  S3: group(3, 'S3'),
});

export const S4TransitiveSubgroups = Object.freeze({
  C4: group(4, 'C4'),
  V: group(4, 'V'),
  D4: group(4, 'D4'),
  A4: group(4, 'A4'),
  S4: group(4, 'S4'),
});

export const S5TransitiveSubgroups = Object.freeze({
  C5: group(5, 'C5'),
  D5: group(5, 'D5'),
  M20: group(5, 'M20'),
  A5: group(5, 'A5'),
  S5: group(5, 'S5'),
});

export const S6TransitiveSubgroups = Object.freeze({
  C6: group(6, 'C6'),
  S3: group(6, 'S3'),
  D6: group(6, 'D6'),
  A4: group(6, 'A4'),
  G18: group(6, 'G18'),
  A4xC2: group(6, 'A4xC2'),
  S4m: group(6, 'S4m'),
  S4p: group(6, 'S4p'),
  G36m: group(6, 'G36m'),
  G36p: group(6, 'G36p'),
  S4xC2: group(6, 'S4xC2'),
  PSL2F5: group(6, 'PSL2F5'),
  G72: group(6, 'G72'),
  PGL2F5: group(6, 'PGL2F5'),
  A6: group(6, 'A6'),
  S6: group(6, 'S6'),
});
