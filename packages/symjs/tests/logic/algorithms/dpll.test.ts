// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/algorithms/dpll.ts.
// The recursive DPLL algorithm and its helpers. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import type { Expr } from '../../../src';
import {
  dpll,
  dpllIntRepr,
  dpllSatisfiable,
  findPureSymbol,
  findPureSymbolIntRepr,
  findUnitClause,
  findUnitClauseIntRepr,
  plTrueIntRepr,
  unitPropagate,
  unitPropagateIntRepr,
} from '../../../src/logic';

const [A, B, C, D] = sj.symbols('A B C D') as [Expr, Expr, Expr, Expr];
const { And, Or, Not } = sj;
/** A model as a sorted "name: value" list. */
const show = (m: ReadonlyMap<Expr, boolean> | false): string =>
  m === false
    ? 'False'
    : [...m]
        .map(([k, v]) => `${sj.str(k)}: ${v ? 'True' : 'False'}`)
        .sort()
        .join(', ');
const showInt = (m: ReadonlyMap<number, boolean> | false): string =>
  m === false
    ? 'False'
    : [...m]
        .sort((a, b) => a[0] - b[0])
        .map(([k, v]) => `${k}: ${v ? 'True' : 'False'}`)
        .join(', ');

describe('dpll', () => {
  it('dpll_satisfiable', () => {
    expect(show(dpllSatisfiable(And(A, Not(B))))).toBe('A: True, B: False');
    expect(dpllSatisfiable(And(A, Not(A)))).toBe(false);
    expect(show(dpllSatisfiable(And(Or(A, B), Or(Not(A), C), Or(Not(C), Not(B)))))).toBe('A: True, B: False, C: True');
    expect(show(dpllSatisfiable(A))).toBe('A: True');
    expect(dpllSatisfiable(false)).toBe(false);
    expect(dpllSatisfiable(And(sj.Implies(A, B), A, Not(B)))).toBe(false);
    const all = [...dpllSatisfiable(Or(A, B), { allModels: true })];
    expect(all.length).toBe(3);
  });
  it('dpll in a partial model', () => {
    expect(dpll([A, B, D], [A, B], new Map([[D, false]]))).toBe(false);
    expect(show(dpll([Or(A, B), Or(Not(A), C), Not(C)], [A, B, C], new Map()))).toBe('A: False, B: True, C: False');
    expect(show(dpll([Or(A, B), Not(A)], [A, B], new Map()))).toBe('A: False, B: True');
    expect(show(dpll([Or(A, B, C), Or(Not(A), Not(B)), Or(Not(B), Not(C)), Or(Not(A), Not(C)), Or(A, Not(B))], [A, B, C], new Map()))).toBe('A: False, B: False, C: True');
    // branching on a symbol
    expect(show(dpll([Or(A, B), Or(Not(A), Not(B)), Or(A, Not(B), C)], [A, B, C], new Map()))).not.toBe('False');
    expect(() => dpll([Or(A, B), Or(Not(A), Not(B))], [], new Map())).toThrow(RangeError);
    // a negative pure symbol, a unit clause of a symbol outside the list, a failed first branch
    expect(show(dpll([Or(Not(A), B), Or(Not(A), C)], [A], new Map()))).toBe('A: False');
    expect(() => dpll([A], [], new Map())).toThrow(RangeError);
    expect(dpll([Or(A, B), Or(A, Not(B)), Or(Not(A), C), Or(Not(A), Not(C))], [B, C, A], new Map())).toBe(false);
  });
  it('dpll_int_repr', () => {
    expect(dpllIntRepr([new Set([1]), new Set([2]), new Set([3])], new Set([1, 2]), new Map([[3, false]]))).toBe(false);
    expect(showInt(dpllIntRepr([new Set([1, 2, 3]), new Set([-1, -2]), new Set([-2, -3]), new Set([-1, -3]), new Set([1, -2])], new Set([1, 2, 3]), new Map()))).toBe('1: True, 2: False, 3: False');
    expect(showInt(dpllIntRepr([new Set([1, 2]), new Set([-1, 2]), new Set([1, -2])], new Set([1, 2]), new Map()))).toBe('1: True, 2: True');
    expect(showInt(dpllIntRepr([new Set([1, 2]), new Set([-1, -2])], new Set([1, 2]), new Map()))).toBe('1: True, 2: False');
    expect(() => dpllIntRepr([new Set([1, 2]), new Set([-1, -2])], new Set(), new Map())).toThrow(RangeError);
    expect(showInt(dpllIntRepr([new Set([1, 2, 3]), new Set([-2, -3]), new Set([2, 3])], new Set([2, 3]), new Map([[1, true]])))).toBe('1: True, 2: True, 3: False');
    expect(showInt(dpllIntRepr([new Set([1, 2]), new Set([1, 3])], new Set([1, 2, 3]), new Map()))).toBe('1: True');
    expect(showInt(dpllIntRepr([new Set([-1, 2]), new Set([-1, -2])], new Set([1, 2]), new Map()))).toBe('1: False');
    expect(dpllIntRepr([new Set([1, 2]), new Set([1, -2]), new Set([-1, 3]), new Set([-1, -3])], new Set([1, 2, 3]), new Map())).toBe(false);
  });
  it('pl_true_int_repr', () => {
    expect(plTrueIntRepr(new Set([1, 2]), new Map([[1, false]]))).toBe('unknown');
    expect(plTrueIntRepr(new Set([1, 2]), new Map([[1, false], [2, false]]))).toBe(false);
    expect(plTrueIntRepr(new Set([-1, 2]), new Map([[1, false]]))).toBe(true);
    expect(plTrueIntRepr(new Set([1]))).toBe('unknown');
  });
  it('unit propagation', () => {
    expect(unitPropagate([Or(A, B), Or(D, Not(B)), B], B).map(sj.str)).toEqual(['D', 'B']);
    expect(unitPropagate([Or(A, B), Or(Not(B), D), A, Or(Not(D), B, C)], B).map(sj.str)).toEqual(['D', 'A']);
    expect(unitPropagateIntRepr([new Set([1, 2]), new Set([3, -2]), new Set([2])], 2).map((c) => [...c])).toEqual([[3]]);
  });
  it('pure symbols', () => {
    expect(findPureSymbol([A, B, D], [Or(A, Not(B)), Or(Not(B), Not(D)), Or(D, A)])).toEqual([A, true]);
    expect(findPureSymbol([A, B], [Or(A, B), Or(Not(A), B), Or(A, Not(B))])).toBe(sj.NoMatch);
    expect(findPureSymbolIntRepr(new Set([1, 2, 3]), [new Set([1, -2]), new Set([-2, -3]), new Set([3, 1])])).toEqual([1, true]);
    expect(findPureSymbolIntRepr(new Set([1, 2]), [new Set([1, 2]), new Set([-1, -2])])).toBe(sj.NoMatch);
    expect(findPureSymbolIntRepr(new Set([1, 2]), [new Set([-1, 2]), new Set([-2])])).toEqual([1, false]);
  });
  it('unit clauses', () => {
    expect(findUnitClause([Or(A, B, D), Or(B, Not(D)), Or(A, Not(B))], new Map([[A, true]]))).toEqual([B, false]);
    expect(findUnitClause([Or(A, B)], new Map())).toBe(sj.NoMatch);
    expect(findUnitClauseIntRepr([new Set([1, 2, 3]), new Set([2, -3]), new Set([1, -2])], new Map([[1, true]]))).toEqual([2, false]);
    expect(findUnitClauseIntRepr([new Set([1, 2])], new Map([[2, false]]))).toEqual([1, true]);
    expect(findUnitClauseIntRepr([new Set([1, 2])], new Map())).toBe(sj.NoMatch);
  });
});
