// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/orderings.ts: monomial orderings; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];

describe('monomial orderings', () => {
  it('give SymPy keys', () => {
    expect(sj.lex.key([1, 2, 3])).toEqual([1, 2, 3]);
    expect(sj.grlex.key([1, 2, 3])).toEqual([6, [1, 2, 3]]);
    expect(sj.grevlex.key([1, 2, 3])).toEqual([6, [-3, -2, -1]]);
    expect(sj.ilex.key([1, 2, 3])).toEqual([-1, -2, -3]);
    expect(sj.igrlex.key([1, 2, 3])).toEqual([-6, [-1, -2, -3]]);
    expect(sj.igrevlex.key([1, 2, 3])).toEqual([-6, [3, 2, 1]]);
    expect([sj.lex, sj.grlex, sj.grevlex, sj.ilex, sj.igrlex, sj.igrevlex].map(String)).toEqual(['lex', 'grlex', 'grevlex', 'ilex', 'igrlex', 'igrevlex']);
    expect([sj.lex.isGlobal, sj.ilex.isGlobal]).toEqual([true, false]);
    expect(new sj.InverseOrder(sj.lex).O).toBe(sj.lex);
  });

  it('sort monomials like sorted(..., key=monomial_key(...))', () => {
    const ms = [[1, 2], [2, 0], [0, 3]];
    const sortBy = (k: (m: readonly number[]) => sj.MonomialKey) => [...ms].sort((a, b) => sj.compareMonomialKeys(k(a), k(b)));
    expect(sortBy(sj.monomialKey('grevlex'))).toEqual([[2, 0], [0, 3], [1, 2]]);
    expect(sortBy(sj.monomialKey(sj.igrlex))).toEqual([[1, 2], [0, 3], [2, 0]]);
    expect(sortBy(sj.monomialKey())).toEqual([[0, 3], [1, 2], [2, 0]]);
    expect([...ms].sort((a, b) => sj.grlex.compare(a, b))).toEqual([[2, 0], [0, 3], [1, 2]]);
    expect(sj.compareMonomialKeys([1, [2]], [1, [2]])).toBe(0);
    expect(sj.compareMonomialKeys([1, 2], [1])).toBe(1);
  });

  it('key expressions by their degrees in the generators', () => {
    const k = sj.monomialKey('grlex', [x, y]);
    expect(k(sj.mul(x, sj.pow(y, 2)))).toEqual([3, [1, 2]]);
    const es = [sj.pow(x, 2), y, sj.mul(x, sj.pow(y, 2)), sj.S.One];
    expect(es.sort((a, b) => sj.compareMonomialKeys(k(a), k(b))).map(String)).toEqual(['1', 'y', 'x**2', 'x*y**2']);
  });

  it('rejects unknown orderings', () => {
    expect(() => sj.monomialKey('foo')).toThrow(RangeError);
  });
});
