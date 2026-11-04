// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/graycode.ts (SymPy sympy/combinatorics/graycode.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { GrayCode, binToGray, getSubsetFromBitstring, grayToBin, graycodeSubsets, randomBitstring } from '../../src';

describe('GrayCode', () => {
  it('generates the code', () => {
    const a = new GrayCode(3);
    expect([...a.generateGray()]).toEqual(['000', '001', '011', '010', '110', '111', '101', '100']);
    expect([...a.generateGray({ start: '011' })]).toEqual(['011', '010', '110', '111', '101', '100']);
    expect([...a.generateGray({ rank: 4 })]).toEqual(['110', '111', '101', '100']);
    expect([String(a), a.n, a.selections]).toEqual(['GrayCode(3)', 3, 8n]);
    const out: string[] = [];
    for (const i of a.generateGray()) {
      if (i === '010') a.skip();
      out.push(i);
    }
    expect(out).toEqual(['000', '001', '011', '010', '111', '101', '100']);
  });

  it('ranks and unranks', () => {
    expect(new GrayCode(3, { start: '100' }).current).toBe('100');
    expect(new GrayCode(4, { rank: 4 }).current).toBe('0110');
    expect(new GrayCode(4, { rank: 4 }).rank).toBe(4n);
    expect(new GrayCode(3, { start: '110' }).next().current).toBe('111');
    expect(new GrayCode(3, { start: '110' }).next(-1).current).toBe('010');
    expect(new GrayCode(3, { start: '100' }).rank).toBe(7n);
    expect(new GrayCode(3, { rank: 7 }).current).toBe('100');
    expect(new GrayCode(5, { rank: 3n }).current).toBe('00010');
    expect(GrayCode.unrank(5, 3)).toBe('00010');
    expect(new GrayCode(3, { rank: -1 }).current).toBe('100');
    expect(new GrayCode(3, { start: '' }).current).toBe('000');
  });

  it('rejects invalid codes', () => {
    expect(() => new GrayCode(0)).toThrow('Gray code dimension must be a positive integer, not 0');
    expect(() => new GrayCode(2, { start: '101' })).toThrow('Gray code start has length 3 but should not be greater than 2');
    expect(() => [...new GrayCode(2).generateGray({ start: '101' })]).toThrow('Gray code start has length 3 but should not be greater than 2');
  });
});

describe('Gray code helpers', () => {
  it('converts and selects subsets', () => {
    expect(grayToBin('100')).toBe('111');
    expect(binToGray('111')).toBe('100');
    expect(binToGray('101')).toBe('111');
    expect(getSubsetFromBitstring(['a', 'b', 'c', 'd'], '0011')).toEqual(['c', 'd']);
    expect(getSubsetFromBitstring(['c', 'a', 'c', 'c'], '1100')).toEqual(['c', 'a']);
    expect(() => getSubsetFromBitstring([1], '10')).toThrow('The sizes of the lists are not equal');
    expect([...graycodeSubsets(['a', 'b', 'c'])]).toEqual([[], ['c'], ['b', 'c'], ['b'], ['a', 'b'], ['a', 'b', 'c'], ['a', 'c'], ['a']]);
    expect(randomBitstring(5)).toMatch(/^[01]{5}$/);
  });
});
