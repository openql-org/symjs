// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/unify/core.ts (SymPy sympy/unify/core.py).
// Cases from sympy/unify/tests/test_unify.py and the doctests; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Compound, CondVariable, TermMap, Variable, allcombinations, index, partition, termEquals, termKey, unify as coreUnify } from '../../src/unify/core';
import type { Term } from '../../src/unify/core';

const [a, b, c] = ['a', 'b', 'c'];
const [w, x, y, z] = ['w', 'x', 'y', 'z'].map((v) => new Variable(v));
const C = (op: string, args: readonly Term[]) => new Compound(op, args);

const isAssociative = (t: Term): boolean => t instanceof Compound && ['Add', 'Mul', 'CAdd', 'CMul'].includes(String(t.op));
const isCommutative = (t: Term): boolean => t instanceof Compound && ['CAdd', 'CMul'].includes(String(t.op));
const unify = (p: Term, q: Term, s: ReadonlyMap<Term, Term> = new Map()) => [...coreUnify(p, q, s, { isAssociative, isCommutative })];

/** A substitution as comparable pairs. */
const pairs = (m: ReadonlyMap<Term, Term>): string[] => [...m].map(([k, v]) => `${termKey(k)}=${termKey(v)}`).sort();
const subst = (...ps: [Term, Term][]): string[] => pairs(new Map(ps));
const all = (ms: ReadonlyMap<Term, Term>[]): string[][] => ms.map(pairs);

describe('unification of terms', () => {
  it('basic', () => {
    expect(all(unify(a, x))).toEqual([subst([x, a])]);
    expect(unify(a, x, new Map([[x, 10]]))).toEqual([]);
    expect(all(unify(1, x))).toEqual([subst([x, 1])]);
    expect(all(unify(a, a))).toEqual([subst()]);
    expect(all(unify([w, x], [y, z]))).toEqual([subst([w, y], [x, z])]);
    expect(all(unify(x, [a, b]))).toEqual([subst([x, [a, b]])]);
    expect(unify([a, b], [x, x])).toEqual([]);
    expect(unify([y, z], [x, x])).not.toEqual([]);
    expect(all(unify([a, [b, c]], [a, [x, y]]))).toEqual([subst([x, b], [y, c])]);
    // the occur check
    expect(unify(x, [a, x])).toEqual([]);
    expect(unify(x, C('Add', [a, x]))).toEqual([]);
    // sequences of different lengths
    expect(unify([a, b], [a])).toEqual([]);
  });

  it('ops', () => {
    expect(all(unify(C('Add', [a, b, c]), C('Add', [a, x, y])))).toEqual([subst([x, b], [y, c])]);
    expect(all(unify(C('Add', [C('Mul', [1, 2]), b, c]), C('Add', [x, y, c])))).toEqual([subst([x, C('Mul', [1, 2])], [y, b])]);
    // a non-associative operator matches argument by argument
    expect(all(unify(C('F', [a, b]), C('F', [x, y])))).toEqual([subst([x, a], [y, b])]);
    expect(unify(C('F', [a, b]), C('F', [x]))).toEqual([]);
    expect(unify(C('F', [a]), C('G', [x]))).toEqual([]);
  });

  it('associative', () => {
    const c1 = C('Add', [1, 2, 3]);
    const c2 = C('Add', [x, y]);
    expect(all(unify(c1, c2))).toEqual([subst([x, 1], [y, C('Add', [2, 3])]), subst([x, C('Add', [1, 2])], [y, 3])]);
  });

  it('commutative', () => {
    const c1 = C('CAdd', [1, 2, 3]);
    const c2 = C('CAdd', [x, y]);
    const result = all(unify(c1, c2));
    expect(result).toContainEqual(subst([x, 1], [y, C('CAdd', [2, 3])]));
    expect(result).toContainEqual(subst([x, 2], [y, C('CAdd', [1, 3])]));
  });

  it('allcombinations', () => {
    const key = ([p, q]: [number[][], number[][]]) => JSON.stringify([p, q]);
    expect(new Set([...allcombinations([1, 2], [1, 2], 'commutative')].map(key))).toEqual(
      new Set([
        [
          [[1], [2]],
          [[1], [2]],
        ],
        [
          [[1], [2]],
          [[2], [1]],
        ],
      ].map((v) => JSON.stringify(v))),
    );
    // doctests
    expect([...allcombinations([1, 2, 3], [5, 6], 'associative')]).toEqual([
      [[[1], [2, 3]], [[5], [6]]],
      [[[1, 2], [3]], [[5], [6]]],
    ]);
    const comm = [...allcombinations([1, 2, 3], [5, 6], 'commutative')];
    expect(comm.length).toBe(12);
    expect(comm.map((p) => p[0])).toEqual([
      [[1], [2, 3]],
      [[1, 2], [3]],
      [[1], [3, 2]],
      [[1, 3], [2]],
      [[2], [1, 3]],
      [[2, 1], [3]],
      [[2], [3, 1]],
      [[2, 3], [1]],
      [[3], [1, 2]],
      [[3, 1], [2]],
      [[3], [2, 1]],
      [[3, 2], [1]],
    ]);
    // the shorter sequence first
    expect([...allcombinations([5, 6], [1, 2, 3], 'associative')][0]).toEqual([[[5], [6]], [[1], [2, 3]]]);
  });

  it('commutativity', () => {
    const c1 = new Compound('CAdd', [a, b]);
    const c2 = new Compound('CAdd', [x, y]);
    expect(isCommutative(c1) && isCommutative(c2)).toBe(true);
    expect(unify(c1, c2).length).toBe(2);
  });

  it('CondVariable', () => {
    const expr = C('CAdd', [1, 2]);
    const xv = new Variable('x');
    const yv = new CondVariable('y', (v) => (v as number) % 2 === 0);
    expect(all(unify(expr, C('CAdd', [xv, yv])))).toEqual([subst([xv, 1], [yv, 2])]);
    const zv = new CondVariable('z', (v) => (v as number) > 3);
    expect(unify(expr, C('CAdd', [zv, yv]))).toEqual([]);
  });

  it('default substitution', () => {
    expect(all([coreUnify(new Variable('x'), 'foo').next().value as TermMap])).toEqual([subst([new Variable('x'), 'foo'])]);
    // without fns no operator is associative
    expect(all([...coreUnify(C('Add', [1, 2, 3]), C('Add', [x, y, z]))])).toEqual([subst([x, 1], [y, 2], [z, 3])]);
    expect([...coreUnify(C('Add', [1, 2, 3]), C('Add', [x, y]))]).toEqual([]);
    // associative without commutativity
    expect(all([...coreUnify(C('Add', [1, 2, 3]), C('Add', [x, y]), null, { isAssociative })])).toEqual([subst([x, 1], [y, C('Add', [2, 3])]), subst([x, C('Add', [1, 2])], [y, 3])]);
    expect(all(unify([], []))).toEqual([subst()]);
  });

  it('partition and index', () => {
    expect(partition([10, 20, 30, 40], [[0, 1, 2], [3]])).toEqual([[10, 20, 30], [40]]);
    expect(index([10, 20, 30], [1, 2, 0])).toEqual([20, 30, 10]);
  });
});

describe('terms', () => {
  it('print like SymPy', () => {
    expect(String(C('Add', ['x', 'y']))).toBe('Add[x, y]');
    expect(String(new Variable('a'))).toBe('Variable(a)');
    expect(String(new CondVariable('a', () => true))).toBe('CondVariable(a)');
  });

  it('compare by value', () => {
    const valid = (): boolean => true;
    expect(new Compound('Add', ['x', 'y']).equals(C('Add', ['x', 'y']))).toBe(true);
    expect(new Compound('Add', ['x', 'y']).equals(C('Add', ['y', 'x']))).toBe(false);
    expect(new Variable('a').equals(new Variable('a'))).toBe(true);
    expect(new CondVariable('a', valid).equals(new CondVariable('a', valid))).toBe(true);
    expect(new CondVariable('a', valid).equals(new CondVariable('a', () => true))).toBe(false);
    expect(termEquals({ unifyKey: 'k' }, { unifyKey: 'k' })).toBe(true);
    expect(termEquals([1, 'a'], [1, 'a'])).toBe(true);
  });

  it('TermMap keys compare by value', () => {
    const m = new TermMap([[new Variable('a'), 1]]);
    expect(m.get(new Variable('a'))).toBe(1);
    expect(m.get(new Variable('b'))).toBeUndefined();
    m.set(new Variable('a'), 2);
    expect(m.size).toBe(1);
    expect(m.get(new Variable('a'))).toBe(2);
    expect(m.has(new Variable('a'))).toBe(true);
    expect(m.delete(new Variable('b'))).toBe(false);
    expect(m.delete(new Variable('a'))).toBe(true);
    expect(m.size).toBe(0);
    m.set('k', 1);
    m.clear();
    expect(m.has('k')).toBe(false);
    expect(new TermMap().size).toBe(0);
  });
});
