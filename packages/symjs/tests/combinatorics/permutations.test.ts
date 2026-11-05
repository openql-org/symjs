// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/permutations.ts.
// Permutation: construction, group operations, cycles and ranking. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { NoMatch, Rational, Sym, isNoMatch, latex, str, symbols } from '../../src';
import { NotImplementedError } from '../../src/core/errors';
import type { NoMatchResult } from '../../src/core/truth';
import {
  AppliedPermutation,
  Cycle,
  Perm,
  Permutation,
  afCommutesWith,
  afInvert,
  afParity,
  afPow,
  afRmul,
  afRmuln,
  permutationLatex,
  permutationRepr,
  permutationStr,
  type PermutationInput,
  type PermutationOptions,
} from '../../src/combinatorics';
import { xreplace } from '../../src/core/traverse';

function P(...cycle: (number | bigint)[]): Permutation;
function P(...args: [...cycle: (number | bigint)[], options: PermutationOptions]): Permutation;
function P(arg: PermutationInput, options?: PermutationOptions): Permutation;
function P(...a: unknown[]): Permutation {
  return new (Permutation as unknown as new (...x: unknown[]) => Permutation)(...a);
}
/** SymPy's printing with init_printing(perm_cyclic=False). */
const arr = (p: Permutation): string => permutationStr(p, { permCyclic: false });
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const ok = (p: Permutation | NoMatchResult): Permutation => {
  if (isNoMatch(p)) throw new RangeError('unexpected NoMatch');
  return p;
};
const matrixRows = (m: { rows: number; cols: number; data: readonly { toString(): string }[] }): number[][] =>
  range(m.rows).map((i) => range(m.cols).map((j) => Number(m.data[i * m.cols + j]!.toString())));

describe('array-form helpers', () => {
  it('_af_rmul', () => {
    const a = [1, 0, 2];
    const b = [0, 2, 1];
    expect(afRmul(a, b)).toEqual([1, 2, 0]);
    expect(range(3).map((i) => a[b[i]!])).toEqual([1, 2, 0]);
    const pa = P(a);
    const pb = P(b);
    expect([...pa.mul(pb)]).toEqual([2, 0, 1]);
    expect(range(3).map((i) => pb.call(pa.call(i)))).toEqual([2, 0, 1]);
  });
  it('_af_rmuln', () => {
    expect(afRmuln([1, 0, 2], [0, 2, 1])).toEqual([1, 2, 0]);
    const a = [1, 2, 0, 3, 4];
    const b = [0, 2, 1, 4, 3];
    const c = [4, 3, 2, 1, 0];
    const d = [1, 0, 3, 2, 4];
    expect(afRmuln(a, b, c)).toEqual(range(5).map((i) => a[b[c[i]!]!]!));
    expect(afRmuln(a, b, c, d, a, b, c, d, a)).toEqual(range(5).map((i) => a[b[c[d[a[b[c[d[a[i]!]!]!]!]!]!]!]!]!));
    expect(afRmuln(a)).toEqual(a);
    expect(() => afRmuln()).toThrow(RangeError);
  });
  it('_af_parity', () => {
    expect(afParity([0, 1, 2, 3])).toBe(0);
    expect(afParity([3, 2, 0, 1])).toBe(1);
  });
  it('_af_invert', () => {
    const A = [1, 2, 0, 3];
    expect(afInvert(A)).toEqual([2, 0, 1, 3]);
    expect(afRmul(afInvert(A), A)).toEqual([0, 1, 2, 3]);
  });
  it('_af_pow', () => {
    const p = P([2, 0, 3, 1]);
    expect(p.order().toString()).toBe('4');
    expect(afPow(p.arrayForm, 4)).toEqual([0, 1, 2, 3]);
    const q = P([3, 1, 5, 2, 4, 0, 7, 8, 6]);
    expect(afPow(q.arrayForm, 7)).toEqual([5, 1, 3, 0, 4, 2, 7, 8, 6]);
    expect(afPow(q.arrayForm, -3)).toEqual([3, 1, 5, 2, 4, 0, 6, 7, 8]);
    expect(afPow(q.arrayForm, 0)).toEqual(range(9));
  });
  it('_af_commutes_with', () => {
    expect(afCommutesWith([1, 2, 0], [0, 2, 1])).toBe(false);
  });
});

describe('Cycle', () => {
  it('class doctests', () => {
    expect(new Cycle(1, 2).call(2, 3).toString()).toBe('(1 3 2)');
    expect(new Cycle().call(1, 2).call(2, 3).toString()).toBe('(1 3 2)');
    const a = new Cycle(1, 2);
    expect(a.list()).toEqual([0, 2, 1]);
    expect([...a]).toEqual([0, 2, 1]);
    const b = new Cycle(2, 4).call(1, 2).call(3, 1, 4).call(1, 3);
    expect(b.list()).toEqual([0, 2, 1, 3, 4]);
    expect(b.list(b.size + 1)).toEqual([0, 2, 1, 3, 4, 5]);
    expect(b.list(-1)).toEqual([0, 2, 1]);
    expect(new Cycle(1, 4, 10).call(4, 5).toString()).toBe('(1 5 4 10)');
    expect(new Cycle(1, 2).call(4).call(5).call(10).toString()).toBe('(1 2)(10)');
    expect(new Perm(new Cycle(1, 2).call(3, 4).list()).transpositions()).toEqual([[1, 2], [3, 4]]);
    expect(new Cycle(1, 2).items()).toEqual([[1, 2], [2, 1]]);
  });
  it('__call__', () => {
    expect(new Cycle(1, 2).call(2, 3).toString()).toBe('(1 3 2)');
    const a = new Cycle(1, 2);
    expect(a.call(2, 3).toString()).toBe('(1 3 2)');
    expect(a.call(2, 3).call(4, 5).toString()).toBe('(1 3 2)(4 5)');
    expect(new Cycle(1, 2).call(P(2, 3)).toString()).toBe('(1 3 2)');
  });
  it('list', () => {
    const p = new Cycle(2, 3).call(4, 5);
    expect(p.list()).toEqual([0, 1, 3, 2, 5, 4]);
    expect(p.list(10)).toEqual([0, 1, 3, 2, 5, 4, 6, 7, 8, 9]);
    expect(new Cycle(2, 4).call(1, 2, 4).list(-1)).toEqual([0, 2, 1]);
    expect(() => new Cycle().list()).toThrow('must give size for empty Cycle');
    expect(new Cycle().list(3)).toEqual([0, 1, 2]);
  });
  it('repr, str and latex', () => {
    expect(new Cycle(1, 2).repr()).toBe('Cycle(1, 2)');
    expect(new Cycle(1, 2).toString()).toBe('(1 2)');
    expect(new Cycle(1, 2).items()).toEqual([[1, 2], [2, 1]]);
    expect(new Cycle(1, 2, 4).call(5, 6).toString()).toBe('(1 2 4)(5 6)');
    expect(new Cycle(1, 2, 6).toString()).toBe('(1 2 6)');
    expect(new Cycle().toString()).toBe('()');
    expect(new Cycle().repr()).toBe('Cycle()');
    expect(new Cycle(5).toString()).toBe('(5)');
    expect(new Cycle(5).repr()).toBe('Cycle(5)');
    expect(new Cycle(5).list()).toEqual([0, 1, 2, 3, 4, 5]);
    expect(new Cycle(1, 2).toLatex()).toBe('\\left( 1\\; 2\\right)');
    expect(new Cycle(1, 2).call(4).toLatex()).toBe('\\left( 1\\; 2\\right)\\left( 4\\right)');
    expect(new Cycle().toLatex()).toBe('\\left( \\right)');
  });
  it('construction and errors', () => {
    expect(() => new Cycle(1, -2)).toThrow('negative integers are not allowed in a cycle.');
    expect(() => new Cycle(1, 2, 1)).toThrow('All elements must be unique in a cycle.');
    expect(() => new Cycle(1.5)).toThrow(TypeError);
    const c = new Cycle(1, 2);
    const d = c.copy();
    expect(d.items()).toEqual(c.items());
    expect(new Cycle(c).toString()).toBe('(1 2)');
    expect(new Cycle(P([[0, 3], [1, 2]])).toString()).toBe('(0 3)(1 2)');
    expect(c.get(7)).toBe(7);
    expect(c.get(1)).toBe(2);
    expect(c.keys()).toEqual([1, 2]);
    expect(c.size).toBe(3);
    expect(new Cycle().size).toBe(0);
    expect(new Cycle().isEmpty).toBe(true);
  });
});

describe('Permutation class doctests', () => {
  it('array notation', () => {
    const p = P([0, 2, 1]);
    expect(arr(p)).toBe('Permutation([0, 2, 1])');
    expect(range(p.size).map((i) => p.call(i))).toEqual([0, 2, 1]);
    const q = P([2, 1, 0]);
    expect(range(3).map((i) => q.call(p.call(i)))).toEqual([2, 0, 1]);
    expect(range(3).map((i) => p.mul(q).call(i))).toEqual([2, 0, 1]);
    expect(range(p.size).map((i) => q.call(p.call(i)))).toEqual([2, 0, 1]);
    expect(range(p.size).map((i) => p.call(q.call(i)))).toEqual([1, 2, 0]);
  });
  it('disjoint cycle notation', () => {
    expect(P(1, 2, 3).equals(P(2, 3, 1)) && P(2, 3, 1).equals(P(3, 1, 2))).toBe(true);
    expect(P(1, 2).call(3, 5).equals(P([[1, 2], [3, 5]]))).toBe(true);
    const r = P(1, 2).call(1, 3).call(2, 3);
    expect(arr(r)).toBe('Permutation([0, 3, 2, 1])');
    expect(r.equals(P([[1, 2]]).mul(P([[1, 3]])).mul(P([[2, 3]])))).toBe(true);
    expect(P(1, 2).call(2, 3).equals(P([[1, 2], [2, 3]]))).toBe(true);
    expect(P(1, 2).call(2, 3).list()).toEqual([0, 3, 1, 2]);
    expect(P([[2, 3], [1, 2]]).list()).toEqual([0, 2, 3, 1]);
  });
  it('size by singleton or keyword', () => {
    expect(arr(P([[1, 2], [9]]))).toBe('Permutation([0, 2, 1], size=10)');
    expect(arr(P([[1, 2]], { size: 10 }))).toBe('Permutation([0, 2, 1], size=10)');
    expect(arr(P(1, 2, { size: 10 }))).toBe('Permutation([0, 2, 1], size=10)');
    expect(arr(P(9).call(1, 2))).toBe('Permutation([0, 2, 1], size=10)');
    expect(arr(P(5))).toBe('Permutation([], size=6)');
    expect(() => P(1, 2).call(3)).toThrow(TypeError);
    expect(arr(P(3).call(1, 2))).toBe('Permutation([0, 2, 1, 3])');
    expect(P(1, 2).call(3, 4).equals(P(3, 4).call(1, 2))).toBe(true);
  });
  it('equality and identity', () => {
    expect(P([1, 0, 2, 3]).equals(P([1, 0]))).toBe(false);
    const I = P([0, 1, 2, 3]);
    expect([P(3), P(range(4)), P([], { size: 4 }), P({ size: 4 })].every((p) => p.equals(I))).toBe(true);
    expect(I.equals(P([range(4)]))).toBe(false);
  });
  it('printing', () => {
    const p = P(1, 2).call(4, 5).call(3, 4);
    expect(arr(p)).toBe('Permutation([0, 2, 1, 4, 5, 3])');
    expect(p.toString()).toBe('(1 2)(3 4 5)');
    expect(p.arrayForm).toEqual([0, 2, 1, 4, 5, 3]);
    expect(p.cyclicForm).toEqual([[1, 2], [3, 4, 5]]);
    expect(P(p.cyclicForm).equals(p)).toBe(true);
    expect(arr(P([1, 0, 2, 3]))).toBe('Permutation([1, 0, 2, 3])');
    expect(arr(P([1, 0, 2, 3], { size: 20 }))).toBe('Permutation([1, 0], size=20)');
    expect(arr(P([1, 0, 2, 4, 3, 5, 6], { size: 20 }))).toBe('Permutation([1, 0, 2, 4, 3], size=20)');
    const q = P([1, 0, 2, 3]);
    expect(q.toString()).toBe('(3)(0 1)');
    expect(q.arrayForm).toEqual([1, 0, 2, 3]);
    expect(q.size).toBe(4);
  });
  it('other methods', () => {
    const q = P([5, 2, 3, 4, 1, 0]);
    expect(q.arrayForm[1]).toBe(2);
    expect(q.call(1)).toBe(2);
    expect(new Map(range(q.size).map((i) => [i, q.call(i)]))).toEqual(new Map([[0, 5], [1, 2], [2, 3], [3, 4], [4, 1], [5, 0]]));
    const p = P([1, 0, 2, 3]);
    expect(p.fullCyclicForm).toEqual([[0, 1], [2], [3]]);
    const t = P([[1, 2], [3, 4, 5]]).transpositions();
    expect(t).toEqual([[1, 2], [3, 5], [3, 4]]);
    const [t0, ...trest] = t.map((ti) => P([ti], { size: 6 }));
    expect(Permutation.rmul(t0!, ...trest).cyclicForm).toEqual([[1, 2], [3, 4, 5]]);
    expect(p.size).toBe(4);
    expect(p.cardinality).toBe(24n);
    expect(p.rank()).toBe(6n);
    expect(arr(p.add(1))).toBe('Permutation([1, 0, 3, 2])');
    const nl = ok(p.nextLex());
    expect(arr(nl)).toBe('Permutation([1, 0, 3, 2])');
    expect(nl.rank()).toBe(7n);
    expect(arr(Permutation.unrankLex(p.size, 7))).toBe('Permutation([1, 0, 3, 2])');
  });
  it('products and application to lists', () => {
    const p = P([1, 0, 2, 3]);
    const q = P([2, 3, 1, 0]);
    expect([...q.mul(p)]).toEqual([2, 3, 0, 1]);
    expect([...p.mul(q)]).toEqual([3, 2, 1, 0]);
    expect(range(p.size).map((i) => q.call(p.call(i)))).toEqual([3, 2, 1, 0]);
    expect(p.call(['zero', 'one', 'four', 'two'])).toEqual(['one', 'zero', 'four', 'two']);
    expect(p.call('zo42')).toEqual(['o', 'z', '4', '2']);
    expect(arr(Permutation.fromSequence('SymPy'))).toBe('Permutation([1, 3, 2, 0, 4])');
  });
  it('group containment examples (printing part)', () => {
    const p1 = P(new Cycle(2, 5, 3));
    const p2 = P(new Cycle(1, 2, 3));
    const a1 = P(new Cycle(1, 2, 3).list(6));
    const a2 = P(new Cycle(1, 2, 3).call(5));
    const a3 = P(new Cycle(1, 2, 3), { size: 6 });
    expect([p1, p2, a1, a2, a3].map(String)).toEqual(['(2 5 3)', '(1 2 3)', '(5)(1 2 3)', '(5)(1 2 3)', '(5)(1 2 3)']);
  });
});

describe('Permutation construction', () => {
  it('__new__ doctests', () => {
    expect(arr(P([0, 2, 1]))).toBe('Permutation([0, 2, 1])');
    expect(arr(P([[4, 5, 6], [0, 1]]))).toBe('Permutation([1, 0, 2, 3, 5, 6, 4])');
    expect(arr(P([[4, 5, 6], [0, 1], [19]]))).toBe('Permutation([1, 0, 2, 3, 5, 6, 4], size=20)');
    expect(() => P([2, 1])).toThrow('Integers 0 through 2 must be present.');
    const r = P([[1, 4], [3, 5, 2]], { size: 10 });
    expect(arr(r)).toBe('Permutation([0, 4, 3, 5, 1, 2], size=10)');
    expect(r.arrayForm).toEqual([0, 4, 3, 5, 1, 2, 6, 7, 8, 9]);
  });
  it('_af_new and copies', () => {
    expect(arr(P([2, 1, 3, 0]))).toBe('Permutation([2, 1, 3, 0])');
    const p = P([2, 1, 3, 0]);
    expect(p.copy().equals(p)).toBe(true);
    expect(P(p).equals(p)).toBe(true);
    expect(arr(P(p, { size: 6 }))).toBe('Permutation([2, 1, 3, 0, 4, 5])');
  });
  it('errors and edge cases', () => {
    expect(() => P([0, 0, 1])).toThrow('there were repeated elements.');
    expect(() => P([0, 2, 1], { size: 2 })).toThrow('max element should not exceed 1');
    expect(() => P(3, { size: 2 })).toThrow('size is too small when max is 3');
    expect(() => P([[1, 2], 3] as never)).toThrow(TypeError);
    expect(P(2, { size: 5 }).arrayForm).toEqual([0, 1, 2]);
    expect(P().size).toBe(0);
    expect(P([]).arrayForm).toEqual([]);
    expect(P([], { size: 3 }).arrayForm).toEqual([0, 1, 2]);
    expect(P(1n, 2n).arrayForm).toEqual([0, 2, 1]);
  });
  it('array_form', () => {
    expect(P([[2, 0], [3, 1]]).arrayForm).toEqual([2, 3, 0, 1]);
    expect(P([[2, 0, 3, 1]]).arrayForm).toEqual([3, 2, 0, 1]);
    expect(P([2, 0, 3, 1]).arrayForm).toEqual([2, 0, 3, 1]);
    expect(P([[1, 2], [4, 5]]).arrayForm).toEqual([0, 2, 1, 3, 5, 4]);
  });
  it('list', () => {
    const p = P(2, 3).call(4, 5);
    expect(p.list()).toEqual([0, 1, 3, 2, 5, 4]);
    expect(p.list(10)).toEqual([0, 1, 3, 2, 5, 4, 6, 7, 8, 9]);
    expect(P(2, 4).call(1, 2, 4).list(-1)).toEqual([0, 2, 1]);
    expect(P(3).list(-1)).toEqual([]);
    expect(P(3).list(4)).toEqual([]);
  });
  it('cyclic_form, full_cyclic_form, size, support', () => {
    expect(P([0, 3, 1, 2]).cyclicForm).toEqual([[1, 3, 2]]);
    expect(P([1, 0, 2, 4, 3, 5]).cyclicForm).toEqual([[0, 1], [3, 4]]);
    expect(P([0, 2, 1]).fullCyclicForm).toEqual([[0], [1, 2]]);
    expect(P([[3, 2], [0, 1]]).size).toBe(4);
    const p = P([[3, 2], [0, 1], [4]]);
    expect(p.arrayForm).toEqual([1, 0, 3, 2, 4]);
    expect(p.support()).toEqual([0, 1, 2, 3]);
  });
});

describe('Permutation arithmetic', () => {
  it('__add__', () => {
    const I = P([0, 1, 2, 3]);
    const a = P([2, 1, 3, 0]);
    expect(I.add(a.rank()).equals(a)).toBe(true);
    expect(I.sub(1).equals(P([3, 2, 1, 0]))).toBe(true);
  });
  it('rmul', () => {
    const a = P([1, 0, 2]);
    const b = P([0, 2, 1]);
    expect([...Permutation.rmul(a, b)]).toEqual([1, 2, 0]);
    expect(range(3).map((i) => a.call(b.call(i)))).toEqual([1, 2, 0]);
    expect([...a.mul(b)]).toEqual([2, 0, 1]);
    expect(range(3).map((i) => b.call(a.call(i)))).toEqual([2, 0, 1]);
    expect(Permutation.rmul(a, [0, 2, 1]).equals(Permutation.rmul(a, b))).toBe(true);
    expect(Permutation.rmulWithAf(a, b).equals(Permutation.rmul(a, b))).toBe(true);
    expect(Permutation.rmulWithAf(a, b, a).equals(Permutation.rmul(a, b, a))).toBe(true);
  });
  it('__mul__', () => {
    const a = P([1, 0, 2]);
    const b = P([0, 2, 1]);
    expect([...a.mul(b)]).toEqual([2, 0, 1]);
    expect(range(3).map((i) => b.call(a.call(i)))).toEqual([2, 0, 1]);
    const al = [...a];
    const bl = [...b];
    expect(afRmul(al, bl)).toEqual([1, 2, 0]);
    expect(range(3).map((i) => al[bl[i]!])).toEqual([1, 2, 0]);
    expect(arr(b.mul(P([1, 0])))).toBe('Permutation([1, 2, 0])');
    expect(arr(P([1, 0]).mul(b))).toBe('Permutation([2, 0, 1])');
    // [0, 1]*a and [[0, 1]]*a coerce the list on the left
    expect(arr(P([0, 1]).mul(a))).toBe('Permutation([1, 0, 2])');
    expect(arr(P([[0, 1]]).mul(a))).toBe('Permutation([0, 1, 2])');
    expect(new Cycle(1, 2).call(2, 3).toString()).toBe('(1 3 2)');
    expect(arr(P([1, 0]).mul(P([])))).toBe('Permutation([1, 0])');
    expect(() => a.mul(2)).toThrow(TypeError);
  });
  it('mul_inv', () => {
    const a = P([1, 2, 0, 3]);
    const b = P([3, 0, 2, 1]);
    // other*~self in SymPy's product convention
    expect(a.mulInv(b).toString()).toBe('(0 3)(1 2)');
    expect(a.mulInv(b).equals(b.mul(a.inverse()))).toBe(true);
    expect(a.inverse().mul(b).toString()).toBe('(0 2)(1 3)');
  });
  it('commutes_with', () => {
    const a = P([1, 4, 3, 0, 2, 5]);
    expect(a.commutesWith(P([0, 1, 2, 3, 4, 5]))).toBe(true);
    expect(a.commutesWith(P([2, 3, 5, 4, 1, 0]))).toBe(false);
    expect(P([1, 0]).commutesWith(P([0, 1, 2]))).toBe(true);
  });
  it('__pow__', () => {
    const p = P([2, 0, 3, 1]);
    expect(p.order().toString()).toBe('4');
    expect(arr(p.pow(4))).toBe('Permutation([0, 1, 2, 3])');
    expect(arr(p.pow(-1))).toBe(arr(p.inverse()));
    expect(p.pow(5n).equals(p)).toBe(true);
    expect(() => p.pow(p)).toThrow(NotImplementedError);
  });
  it('__rxor__ (i^p)', () => {
    const p = P(1, 2, 9);
    expect(p.call(2)).toBe(9);
  });
  it('__xor__ (conjugation)', () => {
    let p = P(1, 2, 9);
    const q = P(6, 9, 8);
    expect(p.mul(q).equals(q.mul(p))).toBe(false);
    const c = p.xor(q);
    expect(c.equals(q.inverse().mul(p).mul(q)) && p.equals(q.mul(c).mul(q.inverse()))).toBe(true);
    const r = P(9).call(4, 6, 8);
    expect(q.xor(p).xor(r).equals(q.xor(p.mul(r)))).toBe(true);
    expect(range(p.size).every((i) => p.call(i) === p.arrayForm[i])).toBe(true);
    // q^r*p^r parses as (q^(r*p))^r in Python
    expect(q.xor(r.mul(p)).xor(r).toString()).toBe('(9)(1 6 4)');
    expect(q.xor(r.mul(p)).xor(r).equals(P(9).call(1, 6, 4))).toBe(true);
    expect(q.xor(p).xor(r).toString()).toBe('(9)(1 4 8)');
    expect(q.xor(p.xor(r)).toString()).toBe('(9)(1 8 6)');
    expect(r.inverse().mul(p).mul(r).equals(r.mul(p).mul(r.inverse()))).toBe(true);
    p = P(1, 2, 9).call(5, 6);
    expect(r.inverse().mul(p).mul(r).equals(r.mul(p).mul(r.inverse()))).toBe(false);
    expect(p.xor(r.inverse()).equals(r.mul(p).mul(r.inverse()))).toBe(true);
    expect(() => P(1, 2).xor(P(3))).toThrow('The permutations must be of equal size.');
  });
  it('transpositions', () => {
    const p = P([[1, 2, 3], [0, 4, 5, 6, 7]]);
    const t = p.transpositions();
    expect(t).toEqual([[0, 7], [0, 6], [0, 5], [0, 4], [1, 3], [1, 2]]);
    expect(t.map((c) => `(${c.join(', ')})`).join('')).toBe('(0, 7)(0, 6)(0, 5)(0, 4)(1, 3)(1, 2)');
    const [t0, ...trest] = t.map((ti) => P([ti], { size: p.size }));
    expect(Permutation.rmul(t0!, ...trest).equals(p)).toBe(true);
  });
  it('from_sequence', () => {
    const p = Permutation.fromSequence('SymPy');
    expect(p.toString()).toBe('(4)(0 1 3)');
    expect(p.call(Array.from('SymPy').sort())).toEqual(['S', 'y', 'm', 'P', 'y']);
    expect(Permutation.fromSequence('SymPy', (x: string) => x.toLowerCase()).toString()).toBe('(4)(0 2)(1 3)');
    expect(Permutation.fromSequence([3, 1, 2]).arrayForm).toEqual([2, 0, 1]);
  });
  it('__invert__', () => {
    const p = P([[2, 0], [3, 1]]);
    expect(arr(p.inverse())).toBe('Permutation([2, 3, 0, 1])');
    expect(p.inverse().equals(p.pow(-1))).toBe(true);
    const I = P([0, 1, 2, 3]);
    expect(p.mul(p.inverse()).equals(p.inverse().mul(p)) && p.mul(p.inverse()).equals(I)).toBe(true);
  });
  it('__iter__', () => {
    expect([...P(range(3))]).toEqual([0, 1, 2]);
  });
  it('__call__', () => {
    const p = P([[2, 0], [3, 1]]);
    expect(p.arrayForm).toEqual([2, 3, 0, 1]);
    expect(range(4).map((i) => p.call(i))).toEqual([2, 3, 0, 1]);
    const x = new Sym('x');
    const out = p.call([x, 1, 0, x.pow(2)]);
    expect(out.map(String)).toEqual(['0', 'x**2', 'x', '1']);
    expect(() => p.call(-1)).toThrow(TypeError);
    expect(() => p.call([1, 2])).toThrow(TypeError);
  });
  it('atoms', () => {
    expect(P([0, 1, 2, 3, 4, 5]).atoms()).toEqual(new Set([0, 1, 2, 3, 4, 5]));
    expect(P([[0, 1], [2, 3], [4, 5]]).atoms()).toEqual(new Set([0, 1, 2, 3, 4, 5]));
  });
  it('commutator', () => {
    let p = P([0, 2, 3, 1]);
    const x = P([2, 0, 3, 1]);
    const c = p.commutator(x);
    expect(arr(c)).toBe('Permutation([2, 1, 3, 0])');
    expect(c.equals(x.inverse().mul(p.inverse()).mul(x).mul(p))).toBe(true);
    const I = P(3);
    const ps = range(6).map((i) => I.add(i));
    for (const pi of ps) {
      for (const pj of ps) {
        const cc = pi.commutator(pj);
        if (pi.mul(pj).equals(pj.mul(pi))) expect(cc.equals(I)).toBe(true);
        else expect(cc.equals(I)).toBe(false);
      }
    }
    p = P(1, 2);
    expect(() => p.commutator(P(4))).toThrow('The permutations must be of equal size.');
  });
});

describe('Permutation ranking', () => {
  it('next_lex', () => {
    let p = P([2, 3, 1, 0]);
    expect(p.rank()).toBe(17n);
    p = ok(p.nextLex());
    expect(p.rank()).toBe(18n);
    expect(P([3, 2, 1, 0]).nextLex()).toBe(NoMatch);
    expect(P([0]).nextLex()).toBe(NoMatch);
  });
  it('unrank_nonlex, rank_nonlex, next_nonlex', () => {
    expect(arr(Permutation.unrankNonlex(4, 5))).toBe('Permutation([2, 0, 3, 1])');
    expect(arr(Permutation.unrankNonlex(4, -1))).toBe('Permutation([0, 1, 2, 3])');
    expect(P([0, 1, 2, 3]).rankNonlex()).toBe(23n);
    let p = P([2, 0, 3, 1]);
    expect(p.rankNonlex()).toBe(5n);
    p = ok(p.nextNonlex());
    expect(arr(p)).toBe('Permutation([3, 0, 1, 2])');
    expect(p.rankNonlex()).toBe(6n);
    expect(P([0, 1, 2, 3]).nextNonlex()).toBe(NoMatch);
    expect(P([]).rankNonlex()).toBe(0n);
    expect(P([2, 0, 3, 1]).rankNonlex(afInvert([2, 0, 3, 1]))).toBe(5n);
    for (let r = 0; r < 24; r++) expect(Permutation.unrankNonlex(4, r).rankNonlex()).toBe(BigInt(r));
  });
  it('rank and cardinality', () => {
    expect(P([0, 1, 2, 3]).rank()).toBe(0n);
    expect(P([3, 2, 1, 0]).rank()).toBe(23n);
    expect(P([0, 1, 2, 3]).cardinality).toBe(24n);
    expect(P([]).rank()).toBe(0n);
    // beyond 2**53
    const big = P(range(25).reverse());
    expect(big.rank()).toBe(15511210043330985983999999n);
    expect(big.cardinality).toBe(15511210043330985984000000n);
    expect(Permutation.unrankLex(25, big.rank()).equals(big)).toBe(true);
  });
  it('unrank_lex', () => {
    const a = Permutation.unrankLex(5, 10);
    expect(a.rank()).toBe(10n);
    expect(arr(a)).toBe('Permutation([0, 2, 4, 1, 3])');
  });
  it('rank_trotterjohnson, unrank_trotterjohnson, next_trotterjohnson', () => {
    expect(P([0, 1, 2, 3]).rankTrotterjohnson()).toBe(0n);
    expect(P([0, 2, 1, 3]).rankTrotterjohnson()).toBe(7n);
    expect(P([1, 0]).rankTrotterjohnson()).toBe(1n);
    expect(arr(Permutation.unrankTrotterjohnson(5, 10))).toBe('Permutation([0, 3, 1, 2, 4])');
    let p = P([3, 0, 2, 1]);
    expect(p.rankTrotterjohnson()).toBe(4n);
    p = ok(p.nextTrotterjohnson());
    expect(arr(p)).toBe('Permutation([0, 3, 2, 1])');
    expect(p.rankTrotterjohnson()).toBe(5n);
    for (let r = 0; r < 24; r++) {
      const q = Permutation.unrankTrotterjohnson(4, r);
      expect(q.rankTrotterjohnson()).toBe(BigInt(r));
      const nx = q.nextTrotterjohnson();
      if (r === 23) expect(nx).toBe(NoMatch);
      else expect(ok(nx).rankTrotterjohnson()).toBe(BigInt(r + 1));
    }
    expect(P([0]).nextTrotterjohnson()).toBe(NoMatch);
  });
  it('inversion_vector and from_inversion_vector', () => {
    expect(P([4, 8, 0, 7, 1, 5, 3, 6, 2]).inversionVector()).toEqual([4, 7, 0, 5, 0, 2, 1, 1]);
    expect(P([3, 2, 1, 0]).inversionVector()).toEqual([3, 2, 1]);
    const lines: string[] = [];
    let p: Permutation | NoMatchResult = P(2);
    while (!isNoMatch(p)) {
      lines.push(`${str(p)} [${p.inversionVector().join(', ')}] ${p.rank()}`);
      p = p.nextLex();
    }
    expect(lines).toEqual(['(2) [0, 0] 0', '(1 2) [0, 1] 1', '(2)(0 1) [1, 0] 2', '(0 1 2) [1, 1] 3', '(0 2 1) [2, 0] 4', '(0 2) [2, 1] 5']);
    expect(arr(Permutation.fromInversionVector([3, 2, 1, 0, 0]))).toBe('Permutation([3, 2, 1, 0, 4, 5])');
    expect(() => Permutation.fromInversionVector([3, 3])).toThrow('The inversion vector is not valid.');
    expect(Permutation.fromInversionVector([-1, 0]).arrayForm).toEqual([2, 0, 1]);
    expect(P([]).inversionVector()).toEqual([]);
  });
});

describe('Permutation properties', () => {
  it('parity, is_even, is_odd, signature', () => {
    expect(P([0, 1, 2, 3]).parity()).toBe(0);
    expect(P([3, 2, 0, 1]).parity()).toBe(1);
    expect(P([0, 1, 2, 3]).isEven).toBe(true);
    expect(P([3, 2, 1, 0]).isEven).toBe(true);
    expect(P([0, 1, 2, 3]).isOdd).toBe(false);
    expect(P([3, 2, 0, 1]).isOdd).toBe(true);
    const p = P([0, 1, 2]);
    expect(p.inversions()).toBe(0);
    expect(p.signature()).toBe(1);
    const q = P([0, 2, 1]);
    expect(q.inversions()).toBe(1);
    expect(q.signature()).toBe(-1);
  });
  it('is_Singleton, is_Empty, is_Identity', () => {
    expect(P([0]).isSingleton).toBe(true);
    expect(P([0, 1]).isSingleton).toBe(false);
    expect(P([]).isEmpty).toBe(true);
    expect(P([0]).isEmpty).toBe(false);
    expect(P([]).isIdentity).toBe(true);
    expect(P([[0], [1], [2]]).isIdentity).toBe(true);
    expect(P([0, 1, 2]).isIdentity).toBe(true);
    expect(P([0, 2, 1]).isIdentity).toBe(false);
  });
  it('ascents, descents, max, min', () => {
    expect(P([4, 0, 1, 3, 2]).ascents()).toEqual([1, 2]);
    expect(P([4, 0, 1, 3, 2]).descents()).toEqual([0, 3]);
    expect(P([1, 0, 2, 3, 4]).max()).toBe(1);
    expect(P([0, 1, 4, 3, 2]).min()).toBe(2);
    expect(P([]).max()).toBe(0);
    expect(P([]).min()).toBe(0);
    expect(() => P([0, 1]).max()).toThrow(RangeError);
    expect(() => P([0, 1]).min()).toThrow(RangeError);
  });
  it('inversions', () => {
    expect(P([0, 1, 2, 3, 4, 5]).inversions()).toBe(0);
    expect(P([3, 2, 1, 0]).inversions()).toBe(6);
    // the merge-sort branch (n >= 130)
    const a = range(300).map((i) => (i * 37) % 300).map((v, i) => (i % 2 === 0 ? v : v));
    const perm = P(Permutation.fromSequence(a).inverse());
    const af = perm.arrayForm;
    let brute = 0;
    for (let i = 0; i < af.length; i++) for (let j = i + 1; j < af.length; j++) if (af[i]! > af[j]!) brute++;
    expect(perm.inversions()).toBe(brute);
    expect(P(range(200).reverse()).inversions()).toBe(19900);
    expect(P(range(131)).inversions()).toBe(0);
  });
  it('order, length, cycle_structure, cycles, index, runs', () => {
    const p = P([3, 1, 5, 2, 4, 0]);
    expect(p.order().toString()).toBe('4');
    expect(arr(p.pow(Number(p.order().p)))).toBe('Permutation([], size=6)');
    expect(p.pow(p.order()).isIdentity).toBe(true);
    expect(P([]).order().toString()).toBe('1');
    expect(P([0, 3, 2, 1]).length()).toBe(2);
    expect(P([[0, 1], [2, 3]]).length()).toBe(4);
    expect(P(3).cycleStructure).toEqual(new Map([[1, 4]]));
    expect(P(0, 4, 3).call(1, 2).call(5, 6).cycleStructure).toEqual(new Map([[2, 2], [3, 1]]));
    expect(P([]).cycleStructure).toEqual(new Map());
    expect(P([0, 1, 2]).cycles).toBe(3);
    expect(P([0, 1, 2]).fullCyclicForm).toEqual([[0], [1], [2]]);
    expect(P(0, 1).call(2, 3).cycles).toBe(2);
    expect(P([3, 0, 2, 1, 4]).index()).toBe(2);
    expect(P([2, 5, 7, 3, 6, 0, 1, 4, 8]).runs()).toEqual([[2, 5, 7], [3, 6], [0, 1, 4, 8]]);
    expect(P([1, 3, 2, 0]).runs()).toEqual([[1, 3], [2], [0]]);
    expect(P([]).runs()).toEqual([]);
  });
});

describe('Permutation matrices and distances', () => {
  it('get_precedence_matrix', () => {
    const p = Permutation.josephus(3, 6, 1);
    expect(arr(p)).toBe('Permutation([2, 5, 3, 1, 4, 0])');
    expect(matrixRows(p.getPrecedenceMatrix())).toEqual([
      [0, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0],
      [1, 1, 0, 1, 1, 1],
      [1, 1, 0, 0, 1, 0],
      [1, 0, 0, 0, 0, 0],
      [1, 1, 0, 1, 1, 0],
    ]);
  });
  it('get_precedence_distance', () => {
    const p = P([2, 0, 4, 3, 1]);
    const q = P([3, 1, 2, 4, 0]);
    expect(p.getPrecedenceDistance(q)).toBe(7);
    expect(q.getPrecedenceDistance(p)).toBe(7);
    expect(() => p.getPrecedenceDistance(P(2))).toThrow(RangeError);
  });
  it('get_adjacency_matrix', () => {
    const p = Permutation.josephus(3, 6, 1);
    expect(matrixRows(p.getAdjacencyMatrix())).toEqual([
      [0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0],
      [0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 0],
    ]);
    const q = P([0, 1, 2, 3]);
    expect(matrixRows(q.getAdjacencyMatrix())).toEqual([
      [0, 1, 0, 0],
      [0, 0, 1, 0],
      [0, 0, 0, 1],
      [0, 0, 0, 0],
    ]);
  });
  it('get_adjacency_distance and get_positional_distance', () => {
    const p = P([0, 3, 1, 2, 4]);
    const q = Permutation.josephus(4, 5, 2);
    expect(p.getAdjacencyDistance(q)).toBe(3);
    const r = P([0, 2, 1, 4, 3]);
    expect(p.getAdjacencyDistance(r)).toBe(4);
    const r2 = P([3, 1, 4, 0, 2]);
    expect(p.getPositionalDistance(q)).toBe(12);
    expect(p.getPositionalDistance(r2)).toBe(12);
    expect(() => p.getAdjacencyDistance(P(2))).toThrow(RangeError);
    expect(() => p.getPositionalDistance(P(2))).toThrow(RangeError);
  });
  it('josephus', () => {
    expect(Permutation.josephus(3, 6, 2).arrayForm).toEqual([2, 5, 3, 1, 4, 0]);
    expect(Permutation.josephus(4, 5, 2).arrayForm).toEqual([3, 2, 4, 0, 1]);
  });
});

describe('random and resize', () => {
  it('random', () => {
    const p = Permutation.random(2);
    expect(p.equals(P([1, 0])) || p.equals(P([0, 1]))).toBe(true);
    const a = Permutation.random(10, { seed: 42 });
    expect(a.equals(Permutation.random(10, { seed: 42 }))).toBe(true);
    expect([...a].sort((u, v) => u - v)).toEqual(range(10));
    expect(Permutation.random(4, { prng: () => 0 }).arrayForm).toEqual([1, 2, 3, 0]);
  });
  it('resize', () => {
    let p = P(0, 1, 2);
    p = p.resize(5);
    expect(p.toString()).toBe('(4)(0 1 2)');
    p = p.resize(4);
    expect(p.toString()).toBe('(3)(0 1 2)');
    expect(() => p.resize(2)).toThrow('The permutation cannot be resized to 2 because the cycle (0, 1, 2) may break.');
    expect(P(5).resize(3).toString()).toBe('(2)');
    expect(P(1, 2, { size: 10 }).resize(3).toString()).toBe('(1 2)');
    expect(p.resize(4)).toBe(p);
  });
});

describe('printing', () => {
  it('str (perm_cyclic=True, the default)', () => {
    expect(P(1, 2).toString()).toBe('(1 2)');
    expect(str(P(3))).toBe('(3)');
    expect(str(P([]))).toBe('()');
    expect(str(P([1, 0, 2, 3]))).toBe('(3)(0 1)');
    expect(P(1, 2).call(3, 4).toString()).toBe('(1 2)(3 4)');
    expect(P([1, 0]).mul(P([0, 1, 2])).toString()).toBe('(2)(0 1)');
  });
  it('str (perm_cyclic=False)', () => {
    expect(arr(P([0, 1, 2]))).toBe('Permutation([0, 1, 2])');
    expect(arr(P([]))).toBe('Permutation([])');
    expect(arr(P(5))).toBe('Permutation([], size=6)');
  });
  it('srepr', () => {
    expect(permutationRepr(P(1, 2))).toBe('Permutation(1, 2)');
    expect(permutationRepr(P([1, 0, 2, 3]))).toBe('Permutation(3)(0, 1)');
    expect(permutationRepr(P(1, 2).call(3, 4))).toBe('Permutation(1, 2)(3, 4)');
    expect(permutationRepr(P([]))).toBe('Permutation()');
    expect(permutationRepr(P([1, 0, 2, 3]), { permCyclic: false })).toBe('Permutation([1, 0, 2, 3])');
  });
  it('latex', () => {
    expect(latex(P(1, 2))).toBe('\\left( 1\\; 2\\right)');
    expect(latex(P([1, 0, 2, 3]))).toBe('\\left( 0\\; 1\\right)\\left( 3\\right)');
    expect(latex(P([]))).toBe('\\left( \\right)');
    expect(latex(P(1, 2, { size: 5 }))).toBe('\\left( 1\\; 2\\right)\\left( 4\\right)');
    expect(permutationLatex(P(1, 2), { permCyclic: false })).toBe('\\begin{pmatrix} 0 & 1 & 2 \\\\ 0 & 2 & 1 \\end{pmatrix}');
    expect(permutationLatex(P([]), { permCyclic: false })).toBe('\\left( \\right)');
  });
});

describe('AppliedPermutation and apply', () => {
  const [x] = symbols('x');
  it('doctest', () => {
    const p = P(0, 1, 2);
    const ap = p.apply(x!);
    expect(ap).toBeInstanceOf(AppliedPermutation);
    expect(ap.toString()).toBe('AppliedPermutation((0 1 2), x)');
    expect(ap.subs(x!, 1).toString()).toBe('2');
  });
  it('apply', () => {
    const p = P(1, 2);
    expect(p.apply(1).toString()).toBe('2');
    expect(p.apply(x!).toString()).toBe('AppliedPermutation((1 2), x)');
    expect(latex(p.apply(x!))).toBe('\\sigma_{\\left( 1\\; 2\\right)}(x)');
    expect(() => p.apply(Rational.of(1, 2))).toThrow('1/2 should be an integer.');
    expect(() => p.apply(3)).toThrow(NotImplementedError);
    expect(() => p.apply(-1)).toThrow(NotImplementedError);
    expect(() => p.apply(new Sym('n', { negative: true }))).toThrow(NotImplementedError);
    expect(AppliedPermutation.of(p, 1).toString()).toBe('2');
    expect(AppliedPermutation.of(p, 1, { evaluate: false }).toString()).toBe('AppliedPermutation((1 2), 1)');
  });
  it('expression behaviour', () => {
    const p = P(1, 2);
    expect(p.freeSymbols().size).toBe(0);
    expect(p.isAtom).toBe(true);
    expect(p.subs(x!, 1)).toBe(p);
    expect(p.key).toBe(P([0, 2, 1]).key);
    expect(p.key).not.toBe(P([0, 2, 1, 3]).key);
    expect(() => p.neg()).toThrow(TypeError);
    expect(() => p.div(2)).toThrow(TypeError);
    expect(Perm).toBe(Permutation);
  });
});

// Coverage of combinatorics/permutations.ts; expected values are those of SymPy 1.14
// (sympy.combinatorics.Permutation).

describe('Permutation', () => {
  it('integer arguments given as Integers and bigints', () => {
    expect(new Permutation(sj.sympify(3)).arrayForm).toEqual([0, 1, 2, 3]);
    // SymPy: TypeError 'Rational' object cannot be interpreted as an integer
    expect(() => new Permutation(Rational.of(1n, 2n))).toThrow(TypeError);
    // SymPy would build a list of 2**60 elements
    expect(() => new Permutation(2n ** 60n)).toThrow('value 1152921504606846976 is too large');
    // options without a size
    expect(new Permutation([1, 0], {}).arrayForm).toEqual([1, 0]);
  });

  it('subtraction below rank 0 wraps around', () => {
    expect(new Permutation([0, 1, 2]).sub(1).arrayForm).toEqual([2, 1, 0]);
  });

  it('powers with a non-integer exponent', () => {
    // SymPy truncates the exponent with int(): p**2.5 and p**Rational(1, 2) are p**2 and p**0;
    // symjs rejects them
    const p = new Permutation([1, 0, 2]);
    expect(() => p.pow(2.5)).toThrow(TypeError);
    expect(() => p.pow(Rational.of(1n, 2n))).toThrow(TypeError);
    expect(p.pow(sj.sympify(2)).arrayForm).toEqual([0, 1, 2]);
  });

  it('from_sequence with strings, lists and big keys', () => {
    expect(Permutation.fromSequence('aab').arrayForm).toEqual([0, 1, 2]);
    expect(Permutation.fromSequence('bab').arrayForm).toEqual([1, 0, 2]);
    expect(Permutation.fromSequence([[1, 2], [1], [0, 5], [1, 2]]).arrayForm).toEqual([2, 1, 0, 3]);
    expect(Permutation.fromSequence([3, 1, 2], (x) => -BigInt(x) * 10n ** 20n).arrayForm).toEqual([0, 2, 1]);
    expect(Permutation.fromSequence([3n, 1, 2]).arrayForm).toEqual([2, 0, 1]);
    // SymPy: TypeError '<' not supported between instances of 'str' and 'int'
    expect(() => Permutation.fromSequence<unknown>([1, 'a'])).toThrow(TypeError);
  });

  it('unrank_trotterjohnson', () => {
    expect([0, 1, 2, 3, 4, 5].map((r) => Permutation.unrankTrotterjohnson(3, r).arrayForm)).toEqual([
      [0, 1, 2],
      [0, 2, 1],
      [2, 0, 1],
      [2, 1, 0],
      [1, 2, 0],
      [1, 0, 2],
    ]);
    expect(Permutation.unrankTrotterjohnson(4, 5).arrayForm).toEqual([0, 3, 2, 1]);
    // SymPy gives [0, 0, 2] and [0, 2, 0] (not permutations) for the ranks -1 and 7, and IndexError for -5
    expect(() => Permutation.unrankTrotterjohnson(3, -1)).toThrow('rank must be in [0, 6), got -1');
    expect(() => Permutation.unrankTrotterjohnson(3, 7)).toThrow(RangeError);
  });

  it('_af_rmul with Python indexing', () => {
    expect(afRmul([0, 1, 2], [-1, 0, 1])).toEqual([2, 0, 1]);
    // SymPy: IndexError list index out of range
    expect(() => afRmul([0, 1], [2, 0])).toThrow('list index out of range');
  });

  it('rebuilding', () => {
    const p = new Permutation([1, 0, 2]);
    // a Permutation has no expression arguments: rebuilding gives itself
    expect(p.withArgs([])).toBe(p);
    const [x, y] = sj.symbols('x y');
    const a = AppliedPermutation.of(p, x);
    expect(String(xreplace(a, new Map([[x, sj.sympify(1)]])))).toBe('0');
    // SymPy: ValueError y must be a Permutation instance
    expect(() => xreplace(a, new Map([[p, y]]))).toThrow(TypeError);
  });
});

describe('Basic methods (SymPy Permutation is an Atom)', () => {
  const p = new sj.Permutation([1, 0, 2]);
  const q = new sj.Permutation([0, 2, 1]);
  const r = new sj.Permutation([1, 0]);
  const x = new Sym('x');
  it('match SymPy for the structural methods', () => {
    const [c, e] = p.asContentPrimitive({ radical: true });
    expect([str(c), str(e)]).toEqual(['1', '(2)(0 1)']);
    expect(p.asDummy()).toBe(p);
    expect(sj.Permutation.classKey()).toEqual([2, 0, 'Permutation']);
    expect(p.sortKey()).toEqual([[2, 0, 'Permutation'], [1, ['(2)(0 1)']], [[1, 0, 'Number'], [0, []], [], 1], 1]);
    // SymPy: p.compare(q) = 1, q.compare(p) = -1, p.compare(Permutation([1, 0])) = 1, p.compare(x) = 1
    expect([p.compare(q), q.compare(p), p.compare(p), p.compare(r), r.compare(p), p.compare(x), p.compare(sj.Tuple(1))]).toEqual([1, -1, 0, 1, -1, 1, -1]);
    expect(p.couldExtractMinusSign()).toBe(false);
    expect([p.count(p), p.count(q), p.countOps(), str(p.countOps({ visual: true }) as sj.Expr)]).toEqual([1, 0, 0, '0']);
    expect(p.doit()).toBe(p);
    expect([p.dummyEq(p), p.dummyEq(q)]).toEqual([true, false]);
    expect(p.find(p).map(str)).toEqual(['(2)(0 1)']);
    expect(p.find(() => true).map(str)).toEqual(['(2)(0 1)']);
    // SymPy: Permutation.fromiter([1, 0, 2]) is Permutation(1, 0, 2), the cycle (0 2 1)
    expect(str(sj.Permutation.fromiter([1, 0, 2]))).toBe('(0 2 1)');
    expect([p.hasFree(x), p.hasFree(p), p.hasXfree([x]), p.hasXfree(new Set([p]))]).toEqual([false, true, false, true]);
    // SymPy: TypeError unsupported operand type(s) for /: 'Permutation' and 'Permutation'
    expect(() => p.isHypergeometric(x)).toThrow(TypeError);
    expect([p.isSame(p), p.isSame(q)]).toEqual([true, false]);
  });
  it('match SymPy for matching, calling and replacing', () => {
    expect(p.match(p)).toEqual(new Map());
    expect(p.match(q)).toBe(NoMatch);
    const a = new sj.Wild('a');
    expect([...(p.match(a) as Map<Sym, sj.Expr>)].map(([k, v]) => [str(k), str(v)])).toEqual([['a_', '(2)(0 1)']]);
    expect([p.matches(p), p.matches(q), p.matches(a)]).toEqual([new Map(), NoMatch, NoMatch]);
    expect([p.rcall(1), str(p.rcall() as sj.Expr), str(p.rcall(1, 2) as sj.Expr)]).toEqual([0, '(2)(0 1)', '(0 2 1)']);
    expect(str(p.refine())).toBe('(2)(0 1)');
    // SymPy p.replace(p, q) raises TypeError (Permutation.atoms takes no query); the replacement is q
    expect(str(p.replace(p, q))).toBe('(1 2)');
    expect(str(p.xreplace(new Map([[p, q]])))).toBe('(1 2)');
  });
});
