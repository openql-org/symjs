// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/inference.ts.
// satisfiable, entails and the other inference functions. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import type { Expr } from '../../src';
import * as L from '../../src/logic';
import { plTrue } from '../../src/logic/inference';
import * as boolalg from '../../src/logic/boolalg';
import { BoolOp } from '../../src/core/boolalg';

const s = (e: unknown): string => sj.str(e as Expr);
const syms = (names: string): Expr[] => sj.symbols(names) as Expr[];
const [x, y] = syms('x y z w') as [Expr, Expr, Expr, Expr];
const [A, B, C] = syms('A B C D') as [Expr, Expr, Expr, Expr];
const { And, Or, Not, Xor } = sj;
const T = sj.S.true;
/** SymPy dict printing: {k: v, ...} with keys in sort order. */
const dict = (m: ReadonlyMap<Expr, unknown> | false): string =>
  m === false
    ? 'False'
    : `{${sj
        .ordered([...m.keys()])
        .map((k) => `${s(k)}: ${(() => {
          const v = m.get(k);
          return typeof v === 'boolean' ? (v ? 'True' : 'False') : s(v);
        })()}`)
        .join(', ')}}`;

describe('inference', () => {
  it('literal_symbol', () => {
    expect(s(L.literalSymbol(A))).toBe('A');
    expect(s(L.literalSymbol(Not(A)))).toBe('A');
    expect(L.literalSymbol(true)).toBe(T);
    expect(() => L.literalSymbol(And(A, B))).toThrow(RangeError);
  });

  it('satisfiable', () => {
    expect(dict(L.satisfiable(And(A, Not(B))))).toBe('{A: True, B: False}');
    expect(L.satisfiable(And(A, Not(A)))).toBe(false);
    expect(dict(L.satisfiable(true))).toBe('{True: True}');
    expect(L.satisfiable(false)).toBe(false);
    expect(L.satisfiable(And(A, Not(A)), { allModels: true }).next().value).toBe(false);
    const models = L.satisfiable(And(L.Implies(A, B), B), { allModels: true });
    expect(dict(models.next().value as sj.ExprMap<boolean>)).toBe('{A: False, B: True}');
    expect(dict(models.next().value as sj.ExprMap<boolean>)).toBe('{A: True, B: True}');
    expect(models.next().done).toBe(true);
    const use = (ms: Iterable<sj.ExprMap<boolean> | false>): string[] => [...ms].map((m) => (m === false ? 'UNSAT' : dict(m)));
    expect(use(L.satisfiable(L.Implies(A, Not(A)), { allModels: true }))).toEqual(['{A: False}']);
    expect(use(L.satisfiable(Xor(A, A), { allModels: true }))).toEqual(['UNSAT']);
    expect(dict(L.satisfiable(sj.Lt(x, 1)))).toBe('{x < 1: True}');
  });

  it('satisfiable with minimal models', () => {
    const ms = [...L.satisfiable(Or(A, B, C), { allModels: true, minimal: true })].map((m) => dict(m));
    expect(ms.sort()).toEqual(['{A: False, B: False, C: True}', '{A: False, B: True, C: False}', '{A: True, B: False, C: False}']);
    expect(dict(L.satisfiable(Or(A, B), { minimal: true }))).toMatch(/^\{A: (True, B: False|False, B: True)\}$/);
    expect(dict(L.satisfiable(And(L.Implies(A, B), Or(A, C)), { minimal: true }))).toBe('{A: False, B: False, C: True}');
    expect(L.satisfiable(And(A, Not(A)), { minimal: true })).toBe(false);
  });

  it('valid and entails', () => {
    expect(L.valid(Or(A, Not(A)))).toBe(true);
    expect(L.valid(Or(A, B))).toBe(false);
    expect(L.entails(A, [L.Implies(A, B), L.Implies(B, C)])).toBe(false);
    expect(L.entails(C, [L.Implies(A, B), L.Implies(B, C), A])).toBe(true);
    expect(L.entails(L.Implies(A, B))).toBe(false);
    expect(L.entails(L.Implies(A, L.Implies(B, A)))).toBe(true);
  });

  it('pl_true', () => {
    expect(L.plTrue(And(A, B), new Map([[A, true], [B, true]]))).toBe(true);
    expect(L.plTrue(And(A, B), new Map([[A, false]]))).toBe(false);
    expect(L.plTrue(And(A, B), new Map([[A, true]]))).toBe('unknown');
    expect(L.plTrue(And(A, B), new Map([[A, true]]), true)).toBe('unknown');
    expect(L.plTrue(L.Implies(A, L.Implies(B, A)))).toBe('unknown');
    expect(L.plTrue(L.Implies(A, L.Implies(B, A)), new Map(), true)).toBe(true);
    expect(L.plTrue(And(A, Not(A)))).toBe('unknown');
    expect(L.plTrue(And(A, Not(A)), new Map(), true)).toBe(false);
    expect(L.plTrue(And(A, B, Or(Not(A), Not(B))), new Map([[A, true]]))).toBe('unknown');
    expect(L.plTrue(And(A, B, Or(Not(A), Not(B))), new Map([[A, true]]), true)).toBe(false);
    expect(L.plTrue(true)).toBe(true);
    expect(() => L.plTrue(sj.Lt(x, 1))).toThrow(RangeError);
  });

  it('PropKB', () => {
    const l = new L.PropKB();
    expect(l.clauses).toEqual([]);
    l.tell(Or(x, y));
    expect(l.clauses.map(s)).toEqual(['x | y']);
    l.tell(y);
    expect(l.clauses.map(s)).toEqual(['y', 'x | y']);
    const k = new L.PropKB();
    k.tell(And(x, Not(y)));
    expect(k.ask(x)).toBe(true);
    expect(k.ask(y)).toBe(false);
    const r = new L.PropKB(Or(x, y));
    expect(r.clauses.map(s)).toEqual(['x | y']);
    r.retract(Or(x, y));
    expect(r.clauses).toEqual([]);
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

// Coverage of logic/*.ts. Expected values are the str() of SymPy 1.14.

const [z] = sj.symbols('z');

const dictStr = (m: unknown): string =>
  m instanceof Map
    ? `{${[...m.entries()]
        .map(([k, v]) => `${String(k)}: ${v ? 'True' : 'False'}`)
        .sort()
        .join(', ')}}`
    : String(m);

describe('inference and dpll', () => {
  it('satisfiable of ITE (the logic gate and the core node of Piecewise)', () => {
    const all = [
      '{x: False, y: False, z: True}',
      '{x: False, y: True, z: True}',
      '{x: True, y: True, z: False}',
      '{x: True, y: True, z: True}',
    ];
    expect([...L.satisfiable(L.ITE(x, y, z), { allModels: true })].map(dictStr).sort()).toEqual(all);
    expect([...L.satisfiable(new BoolOp('ITE', [x, y, z]), { allModels: true })].map(dictStr).sort()).toEqual(all);
    expect(dictStr(L.satisfiable(L.ITE(x, y, z)))).toBe('{x: False, y: True, z: True}');
  });

  it('minimal model with every variable false', () => {
    expect(dictStr(L.satisfiable(boolalg.andFn(boolalg.notFn(x), boolalg.notFn(y)), { minimal: true }))).toBe('{x: False, y: False}');
  });
});

describe('inference of unevaluated gates', () => {
  it('satisfiable of Nand, Nor, Xnor', () => {
    const all = (e: sj.Expr): string[] => [...L.satisfiable(e, { allModels: true })].map(dictStr).sort();
    expect(all(L.Nand(x, y, { evaluate: false }))).toEqual(['{x: False, y: False}', '{x: False, y: True}', '{x: True, y: False}']);
    expect(all(L.Nor(x, y, { evaluate: false }))).toEqual(['{x: False, y: False}']);
    expect(all(L.Xnor(x, y, { evaluate: false }))).toEqual(['{x: False, y: False}', '{x: True, y: True}']);
  });
});
