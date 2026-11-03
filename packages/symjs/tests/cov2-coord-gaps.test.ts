// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * The last uncovered paths found by the full coverage run. Expected values
 * from SymPy 1.14 unless a comment says otherwise.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { factorInt } from '../src/core/numbers';
import { plTrue } from '../src/logic/inference';
import { minlex, multisetPartitions, multisetPermutations, permuteSigns } from '../src/utilities/iterables';
import { MutableDenseMatrix } from '../src/matrices/mutable';
import { toDM } from '../src/matrices';

const [x, y, a] = sj.symbols('x y a');
const R = (p: bigint, q = 1n): sj.Rational => sj.Rational.of(p, q);
const P = (s: string): sj.Expr => sj.parse(s, { symbols: { x, y, a } } as never);

describe('numeric radicals in a product', () => {
  it('an unevaluated integer power is multiplied out: Mul(Pow(2, 3, evaluate=False), x)', () => {
    expect(String(sj.mul(new sj.Pow(R(2n), R(3n)), x))).toBe('8*x');
  });
  it('bases sharing an exponent after the common factors are pulled out', () => {
    expect(String(P('6**(1/6)*10**(1/3)*7**(1/2)'))).toBe('sqrt(14)*3**(1/6)*5**(1/3)');
  });
  it('the same in one product: bases with equal exponents after the common factors are pulled out', () => {
    const third = R(1n, 3n);
    const r = sj.mul(sj.pow(6, R(1n, 6n)), sj.pow(10, third), sj.pow(7, R(1n, 2n)));
    expect(String(r)).toBe('sqrt(14)*3**(1/6)*5**(1/3)');
  });
  it('a common factor whose exponents add up to an integer', () => {
    expect(String(P('2**(1/3)*6**(2/3)'))).toBe('2*3**(2/3)');
    expect(String(P('2**(1/3)*6**(1/2)'))).toBe('2**(5/6)*sqrt(3)');
  });
});

describe('factorInt: a cofactor above the trial-division limit that is a perfect power', () => {
  it('65537**2', () => {
    expect([...factorInt(4295098369n)]).toEqual([[65537n, 2n]]);
  });
});

describe('match: a product pattern that leaves no factor for the wild', () => {
  it('(x*y).match(x*y*a_) = {a_: 1}', () => {
    const w = new sj.Wild('a');
    const m = sj.match(sj.mul(x, y), sj.mul(x, y, w));
    expect(m instanceof Map ? String(m.get(w)) : String(m)).toBe('1');
  });
  it('an expression containing the wild matches itself with no bindings: (a_*x).match(a_*x) = {}', () => {
    const w = new sj.Wild('a');
    const m = sj.match(sj.mul(w, x), sj.mul(w, x));
    expect(m instanceof Map ? m.size : String(m)).toBe(0);
  });
  it('a pattern whose factors are all exact leaves 1 to match the rest: (a_*x*y).match(a_*x) is None', () => {
    const w = new sj.Wild('a');
    expect(sj.match(sj.mul(w, x, y), sj.mul(w, x)) instanceof Map).toBe(false);
    expect(sj.match(sj.mul(w, x, 2), sj.mul(w, x)) instanceof Map).toBe(false);
  });
});

describe('plTrue', () => {
  const [A, B, C] = sj.symbols('A B C');
  it('a model value that is not a boolean is ignored: pl_true(A & B, {A: True, B: C}) is None', () => {
    expect(plTrue(sj.And(A, B), new Map<sj.Expr, sj.Expr>([[A, sj.S.true], [B, C]]))).toBe('unknown');
  });
  it('deep, false under all-true but satisfiable: pl_true(A & ~B, {A: True}, deep=True) is None', () => {
    expect(plTrue(sj.And(A, sj.Not(B)), new Map<sj.Expr, sj.Expr>([[A, sj.S.true]]), true)).toBe('unknown');
  });
});

describe('matrices', () => {
  it('DomainMatrix leaves out a zero row', () => {
    expect(String(toDM(sj.Matrix.of([[0, 0], [1, 2]])))).toBe('DomainMatrix({1: {0: 1, 1: 2}}, (2, 2), ZZ)');
  });
  it('linsolve outside a rational function field keeps the free unknown', () => {
    expect(String(sj.linsolve([P('x + sin(a)*y - 1')], [x, y]))).toBe('-y*sin(a) + 1,y');
  });
  it('MutableDenseMatrix.fromFunction', () => {
    const m = MutableDenseMatrix.fromFunction(2, 2, (i, j) => i + j);
    expect(m instanceof MutableDenseMatrix).toBe(true);
    expect(String(m)).toBe('Matrix([[0, 1], [1, 2]])');
  });
});

describe('iterables', () => {
  it('minlex undirected keeps the forward rotation when it is smaller', () => {
    expect(minlex('abc', { directed: false })).toBe('abc');
    expect(minlex([1, 2, 3], { directed: false })).toEqual([1, 2, 3]);
  });
  it('multiset_permutations with a size', () => {
    const j = (s: string, k?: number) => [...multisetPermutations(s.split(''), k)].map((p) => p.join(''));
    expect(j('aab', 1)).toEqual(['a', 'b']);
    expect(j('aabb', 2)).toEqual(['aa', 'ab', 'ba', 'bb']);
    expect(j('aaab', 3)).toEqual(['aaa', 'aab', 'aba', 'baa']);
    expect(j('aabb', 3)).toEqual(['aab', 'aba', 'abb', 'baa', 'bab', 'bba']);
    expect(j('aabb')).toEqual(['aabb', 'abab', 'abba', 'baab', 'baba', 'bbaa']);
  });
  it('multiset_partitions(0, m) for m < 1 has no partition (SymPy raises IndexError)', () => {
    expect([...multisetPartitions(0, -1)]).toEqual([]);
  });
  it('permute_signs of bigints keeps a zero', () => {
    expect([...permuteSigns([0n, 1n])]).toEqual([[0n, 1n], [0n, -1n]]);
    expect([...permuteSigns([R(0n), R(1n)])].map((t) => t.map(String))).toEqual([['0', '1'], ['0', '-1']]);
  });
});
