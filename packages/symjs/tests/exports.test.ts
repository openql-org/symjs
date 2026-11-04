// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import * as root from '../src/index';
import { Matrix } from '../src/matrices';
import * as ntheory from '../src/ntheory';
import * as utilities from '../src/utilities';

const ENTRIES = ['index', 'core', 'special', 'simplify', 'polys', 'calculus', 'solvers', 'sets', 'matrices', 'logic', 'ntheory', 'combinatorics', 'utilities', 'tensor', 'printing', 'discrete', 'algebras', 'strategies', 'unify', 'holonomic', 'geometry'];

describe('one definition per exported name', () => {
  it('a name exported by several entry points is the same value in each', async () => {
    const seen = new Map<string, [string, unknown]>();
    const differing: string[] = [];
    for (const e of ENTRIES) {
      const m = (await import(`../src/${e}.ts`)) as Record<string, unknown>;
      for (const [k, v] of Object.entries(m)) {
        const prev = seen.get(k);
        if (prev && prev[1] !== v) differing.push(`${k} (${prev[0]}, ${e})`);
        else if (!prev) seen.set(k, [e, v]);
      }
    }
    expect(differing).toEqual([]);
  });

  it('isPalindromic takes an integer and base or a sequence and slice', () => {
    expect(ntheory.isPalindromic).toBe(utilities.isPalindromic);
    expect(utilities.isPalindromic(121)).toBe(true);
    expect(utilities.isPalindromic(-121n)).toBe(true);
    expect(utilities.isPalindromic(5, 2)).toBe(true);
    expect(utilities.isPalindromic(6, 2)).toBe(false);
    expect(utilities.isPalindromic('abcbb', 1)).toBe(false);
    expect(utilities.isPalindromic('abcbb', 1, -1)).toBe(true);
    expect(() => utilities.isPalindromic(5, 1)).toThrow(RangeError);
  });

  it('connectedComponents takes a graph or an adjacency matrix', () => {
    expect(root.connectedComponents).toBe(utilities.connectedComponents);
    expect(utilities.connectedComponents([[1, 2, 3], [[1, 2]]])).toEqual([[1, 2], [3]]);
    const A = Matrix.of([[1, 0, 1], [0, 1, 0], [1, 0, 1]]);
    expect(utilities.connectedComponents(A)).toEqual([[0, 2], [1]]);
    expect(utilities.stronglyConnectedComponents(A)).toEqual([[0, 2], [1]]);
  });

  it('SymPy names that are JavaScript globals are renamed (the old spellings are deprecated aliases)', () => {
    const lib = root as unknown as Record<string, unknown>;
    const renames: [string, string][] = [['Symbol', 'Sym'], ['Number', 'SymNumber'], ['Function', 'SymFunction'], ['Array', 'SymArray']];
    for (const [old, name] of renames) {
      expect(lib[name]).toBeDefined();
      expect(lib[old]).toBe(lib[name]);
    }
    expect(lib['Set']).toBeUndefined();
    expect(lib['SetExpr']).toBeDefined();
  });
});
