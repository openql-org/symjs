// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { unchanged, cos, pi, Piecewise, Sym, S, Gt, SymFunction, Basic } from '../../src';
it('recognizes unevaluated construction and normalized piecewise pairs', () => {
  const x = new Sym('x');
  expect(unchanged(cos, 1)).toBe(true);
  expect(unchanged(cos, pi)).toBe(false);
  expect(unchanged(Piecewise, [x, Gt(x, 1)] as const, [0, true] as const)).toBe(true);
  expect(unchanged(Basic, 1n)).toBe(true);
  const f = SymFunction('f');
  expect(unchanged(f, 2)).toBe(true);
  const changed = Object.defineProperty(() => f(S.One), 'name', { value: 'f' });
  expect(unchanged(changed)).toBe(false);
  const different = Object.defineProperty((_a: unknown) => f(S.One), 'name', { value: 'f' });
  expect(unchanged(different, 2)).toBe(false);
  expect(unchanged(different, '1')).toBe(false);
  const rawPiecewise = Object.defineProperty((_pair: readonly [number, boolean]) => new Piecewise([S.One, S.false]), 'name', { value: 'Piecewise' });
  expect(unchanged(rawPiecewise, [1, false] as const)).toBe(true);
});
