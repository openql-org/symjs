// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { QQ, QQ_I, ZZ, ZZ_I, dmpAlgInject, dmpToDict, sqrt } from '../../src';
it('injects extension coefficients before the existing polynomial generators', () => {
  const K = QQ.algebraicField(sqrt(2));
  const [f, level, domain] = dmpAlgInject([K.convert(sqrt(2)), K.zero, K.one], 0, K);
  expect(level).toBe(1); expect(domain).toBe(QQ);
  expect([...dmpToDict(f, level)].map(([m, c]) => [m, String(c)])).toEqual([[[0, 0], '1'], [[1, 2], '1']]);
  expect(dmpAlgInject([], 0, K)[0]).toEqual([[]]);
  const [g] = dmpAlgInject([[K.new([1, 1]), K.new(2)]], 1, K);
  expect([...dmpToDict(g, 2)].length).toBe(3);
});
it('handles Gaussian integer and rational domains, including purely real coefficients', () => {
  for (const K of [ZZ_I, QQ_I]) {
    const [f, u, domain] = dmpAlgInject([K.new(2, 3), K.new(0, 1), K.new(4)], 0, K);
    expect(domain).toBe(K.dom);
    expect([...dmpToDict(f, u)].map(([m, c]) => [m, String(c)])).toEqual([[[0, 0], '4'], [[0, 2], '2'], [[1, 1], '1'], [[1, 2], '3']]);
  }
  expect(() => dmpAlgInject([1], 0, ZZ)).toThrow('algebraic or Gaussian');
});
