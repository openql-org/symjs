// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { LatticeOp, symbol } from '../../src';

it('flattens lattice operands and removes identities and duplicates', () => {
  const join = LatticeOp('join', 1, 0);
  expect(join().equals(1)).toBe(true);
  expect(join(0, 2).equals(0)).toBe(true);
  expect(join(1, 2, 2).equals(2)).toBe(true);
  const x = symbol('x');
  const flat = join(2, 3, x);
  expect(join(join(2, x), 3).equals(flat)).toBe(true);
  expect(join(x, 3, 2).equals(flat)).toBe(true);
  expect(flat.subs(x, 0).equals(0)).toBe(true);
  expect([...join.makeArgs(flat)].map(String).sort()).toEqual(['2', '3', 'x']);
  expect([...join.makeArgs(0)].map(String)).toEqual(['0']);
  expect(LatticeOp('join', 1, 0)(2, 3, x).equals(flat)).toBe(true);
  expect(LatticeOp('join', 0, 1)(2, 3, x).equals(flat)).toBe(false);
  const other = LatticeOp('other', 0, 1);
  expect(join.makeArgs(other(2, 3)).size).toBe(1);
  expect(join(other(2, 3), 4).args).toHaveLength(2);
});
