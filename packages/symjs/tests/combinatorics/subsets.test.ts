// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/subsets.ts (SymPy sympy/combinatorics/subsets.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational, Subset, ksubsets } from '../../src';

const abcd = ['a', 'b', 'c', 'd'];

describe('Subset', () => {
  it('has the subset, superset and sizes', () => {
    const a = new Subset(['c', 'd'], abcd);
    expect(a.subset).toEqual(['c', 'd']);
    expect(a.superset).toEqual(abcd);
    expect([a.size, a.supersetSize, a.cardinality]).toEqual([2, 4, 16n]);
    expect(String(a)).toBe('Subset([c, d], [a, b, c, d])');
    expect(a.equals(new Subset(['c', 'd'], abcd))).toBe(true);
    expect(a.equals(new Subset(['c'], abcd))).toBe(false);
    expect(a.equals(new Subset(['c', 'd'], [...abcd, 'e']))).toBe(false);
    expect(() => new Subset([1, 2, 3], [1, 2])).toThrow('Invalid arguments have been provided. The superset must be larger than the subset.');
    expect(() => new Subset([5], [1, 2])).toThrow('The superset provided is invalid as it does not contain the element 5');
  });

  it('steps in binary order', () => {
    const a = new Subset(['c', 'd'], abcd);
    expect(a.nextBinary().subset).toEqual(['b']);
    expect(a.prevBinary().subset).toEqual(['c']);
    expect(a.iterateBinary(-2).subset).toEqual(['d']);
    expect(new Subset(['a', 'b', 'c'], abcd).iterateBinary(2n).subset).toEqual([]);
    expect(new Subset(abcd, abcd).nextBinary().subset).toEqual([]);
    expect(new Subset([], abcd).prevBinary().subset).toEqual(abcd);
    expect([new Subset([], abcd).rankBinary, a.rankBinary]).toEqual([0n, 3n]);
  });

  it('steps in lexicographic order', () => {
    const a = new Subset(['c', 'd'], abcd);
    expect(a.nextLexicographic().subset).toEqual(['d']);
    expect(new Subset(['d'], abcd).nextLexicographic().subset).toEqual([]);
    expect(new Subset([], abcd).prevLexicographic().subset).toEqual(['d']);
    expect(a.prevLexicographic().subset).toEqual(['c']);
    const walk = (step: (s: Subset<string>) => Subset<string>): string[] => {
      const out: string[] = [];
      let s = new Subset<string>([], abcd);
      for (let i = 0; i < 17; i++) {
        out.push(s.subset.join(''));
        s = step(s);
      }
      return out;
    };
    expect(walk((s) => s.nextLexicographic())).toEqual(['', 'a', 'ab', 'abc', 'abcd', 'abd', 'ac', 'acd', 'ad', 'b', 'bc', 'bcd', 'bd', 'c', 'cd', 'd', '']);
    expect(walk((s) => s.prevLexicographic())).toEqual(['', 'd', 'cd', 'c', 'bd', 'bcd', 'bc', 'b', 'ad', 'acd', 'ac', 'abd', 'abcd', 'abc', 'ab', 'a', '']);
    expect([a.rankLexicographic, a.rankLexicographic, new Subset([2, 4, 5], [1, 2, 3, 4, 5, 6]).rankLexicographic]).toEqual([14n, 14n, 43n]);
  });

  it('steps in Gray code order', () => {
    const b = new Subset([1, 2, 3], [1, 2, 3, 4]);
    expect(b.iterateGraycode(3).subset).toEqual([1, 4]);
    expect(b.iterateGraycode(-2n).subset).toEqual([1, 2, 4]);
    expect(b.nextGray().subset).toEqual([1, 3]);
    expect(new Subset([2, 3, 4], [1, 2, 3, 4, 5]).prevGray().subset).toEqual([2, 3, 4, 5]);
    const a = new Subset(['c', 'd'], abcd);
    expect([a.rankGray, new Subset([2, 4, 5], [1, 2, 3, 4, 5, 6]).rankGray]).toEqual([2n, 27n]);
  });

  it('has the class methods', () => {
    expect(Subset.subsetFromBitlist(abcd, '0011').subset).toEqual(['c', 'd']);
    expect(() => Subset.subsetFromBitlist([1, 2], '1')).toThrow('The sizes of the lists are not equal');
    expect(Subset.bitlistFromSubset(['c', 'd'], abcd)).toBe('0011');
    expect(Subset.bitlistFromSubset(new Subset(['c', 'd'], abcd), abcd)).toBe('0011');
    expect(Subset.unrankBinary(4, abcd).subset).toEqual(['b']);
    expect(Subset.unrankGray(4, ['a', 'b', 'c']).subset).toEqual(['a', 'b']);
    expect(Subset.unrankGray(0n, ['a', 'b', 'c']).subset).toEqual([]);
    const superset = [1, 3, 2, 5, 4];
    expect(Subset.subsetIndices([3, 2, 1], superset)).toEqual([1, 2, 0]);
    expect(Subset.subsetIndices([1, 6], superset)).toEqual([]);
    expect(Subset.subsetIndices([], superset)).toEqual([]);
    // 3 == Integer(3) in Python
    expect(Subset.subsetIndices([Rational.of(3n)], superset)).toEqual([1]);
  });
});

describe('ksubsets', () => {
  it('lists the subsets of k elements', () => {
    expect([...ksubsets([1, 2, 3], 2)]).toEqual([
      [1, 2],
      [1, 3],
      [2, 3],
    ]);
    expect([...ksubsets([1, 2, 3, 4, 5], 2)].map((s) => s.join(''))).toEqual(['12', '13', '14', '15', '23', '24', '25', '34', '35', '45']);
    expect([...ksubsets([1, 2], 0)]).toEqual([[]]);
    expect([...ksubsets([1, 2], 3)]).toEqual([]);
  });
});
