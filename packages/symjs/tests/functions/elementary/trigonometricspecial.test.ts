// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/elementary/trigonometricspecial.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';

describe('Fermat prime helpers', () => {
  it('migcdex', () => {
    expect(sj.migcdex()).toEqual([[], 0n]);
    expect(sj.migcdex(4)).toEqual([[1n], 4n]);
    expect(sj.migcdex(4, 6)).toEqual([[-1n, 1n], 2n]);
    expect(sj.migcdex(6, 10, 15)).toEqual([[1n, 1n, -1n], 1n]);
  });
  it('ipartfrac and fermat_coords', () => {
    expect(sj.ipartfrac()).toEqual([]);
    expect(sj.ipartfrac(3, 5)).toEqual([-1n, 2n]);
    expect(sj.ipartfrac(3, 5, 17)).toEqual([1n, 56n, -196n]);
    expect(sj.fermatCoords(15)).toEqual([3, 5]);
    expect(sj.fermatCoords(255)).toEqual([3, 5, 17]);
    expect(sj.fermatCoords(30)).toBe(sj.NoMatch);
    expect(sj.fermatCoords(9)).toBe(sj.NoMatch);
    expect(sj.fermatCoords(1)).toBe(sj.NoMatch);
  });
});

it('ports the lazy Fermat-prime radical table from SymPy 1.14', async () => {
  const { cos3, cos5, cos17, cos257, cosTable, toComplex } = await import('../../../src');
  const table = cosTable();
  expect([...table.keys()]).toEqual([3, 5, 17, 257]);
  expect([...table.values()]).toEqual([cos3, cos5, cos17, cos257]);
  for (const [n, cosine] of table) {
    const e = cosine();
    expect(toComplex(e).re).toBeCloseTo(Math.cos(Math.PI / n), 13);
    expect(e.has(sj.pi)).toBe(false);
  }
});
