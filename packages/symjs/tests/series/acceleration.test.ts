// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Sym, Sum, add, mul, pow, richardson, shanks, simplify, S } from '../../src';
const k = new Sym('k'), a = new Sym('a'), b = new Sym('b');
it('matches exact SymPy 1.14 Richardson extrapolations', () => {
  expect(String(richardson(add(1, pow(k, -1), pow(k, -2)), k, 3, 2))).toBe('1');
  expect(richardson(pow(k, -1), k, Number.MAX_SAFE_INTEGER, 2).equals(0)).toBe(true);
  expect(simplify(richardson(add(a, mul(b, pow(k, -1))), k, 3, 2)).equals(a)).toBe(true);
  expect(String(richardson(pow(add(1, pow(k, -1)), k), k, 3, 2))).toBe('16249/6000');
  expect(richardson(k, k, 3, 0).equals(3)).toBe(true);
  const j = new Sym('j');
  expect(richardson(Sum(j, [j, 1, k]), k, 1, 0).equals(1)).toBe(true);
});
it('matches exact SymPy 1.14 recursive Shanks transformations', () => {
  const A = add(1, pow(k, -1), pow(k, -2));
  expect(String(shanks(A, k, 3))).toBe('1091/900');
  expect(String(shanks(A, k, 3, 2))).toBe('1887492401/1714339800');
  expect(String(shanks(pow(add(1, pow(k, -1)), k), k, 3, 2))).toBe('42753330490480787/16258052578272120');
  expect(simplify(shanks(add(a, mul(b, pow(2, mul(-1, k)))), k, 3)).equals(a)).toBe(true);
  expect(shanks(k, k, 3, 0).equals(3)).toBe(true);
  expect(shanks(1, k, 3)).toBe(S.NaN);
});
it('rejects invalid sequence indices', () => {
  for (const bad of [-1, 1.5, Infinity]) {
    expect(() => richardson(k, k, bad, 1)).toThrow(RangeError);
    expect(() => richardson(k, k, 1, bad)).toThrow(RangeError);
    expect(() => shanks(k, k, bad)).toThrow(RangeError);
    expect(() => shanks(k, k, 1, bad)).toThrow(RangeError);
  }
});

it('reports a missing calculus evaluation hook explicitly', async () => {
  const { impl } = await import('../../src/core/nodes');
  const original = { ...impl };
  try {
    delete impl.doit;
    expect(() => richardson(k, k, 1, 0)).toThrow('calculus entry must be loaded');
  } finally {
    Object.assign(impl, original);
  }
});
