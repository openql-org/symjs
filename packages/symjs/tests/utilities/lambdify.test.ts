// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { lambdastr, Sym } from '../../src';
const x = new Sym('x'), y = new Sym('y'), z = new Sym('z');
it('prints Python lambdas with scalars, lists, and nested arguments', () => {
  expect(lambdastr(x, x.pow(2))).toBe('lambda x: (x**2)');
  expect(lambdastr([x, y, z], [z, y, x])).toBe('lambda x,y,z: ([z, y, x])');
  expect(lambdastr([x, [y, z]], x.add(y))).toBe('lambda _0,_1: (lambda x,y,z: (x + y))(_0,_1[0],_1[1])');
  expect(lambdastr('x', [1, [x]])).toBe('lambda x: ([1, [x]])');
  expect(lambdastr([], 1)).toBe('lambda : (1)');
});
