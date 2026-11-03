// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of logic/*.ts. Expected values are the str() of SymPy 1.14.
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import * as L from '../src/logic';
import * as B from '../src/logic/boolalg';
import { Rel } from '../src/core/nodes';
import { BoolOp } from '../src/core/boolalg';
import { SATSolver } from '../src/logic/dpll';

const [x, y, z] = sj.symbols('x y z');
const s = (e: unknown): string => String(e);
const [w] = sj.symbols('w');
const eqT = (a: sj.Expr, b: sj.Expr): Rel => new Rel('Eq', a, b);
const neT = (a: sj.Expr, b: sj.Expr): Rel => new Rel('Ne', a, b);

describe('boolalg', () => {
  it('ITE with Eq/Ne of a binary symbol', () => {
    const T = sj.S.true;
    const F = sj.S.false;
    expect(s(L.ITE(eqT(x, T), x, z))).toBe('ITE(x, x, z)');
    expect(s(L.ITE(eqT(T, x), x, z))).toBe('ITE(x, x, z)');
    expect(s(L.ITE(eqT(x, F), x, z))).toBe('ITE(~x, x, z)');
    expect(s(L.ITE(eqT(F, x), x, z))).toBe('ITE(~x, x, z)');
    expect(s(L.ITE(neT(x, T), x, z))).toBe('ITE(~x, x, z)');
    expect(s(L.ITE(sj.Eq(x, y), x, z))).toBe('z');
    expect(s(L.ITE(sj.Ne(x, y), x, z))).toBe('x');
    expect(s(L.ITE(sj.Eq(x, y), x, y))).toBe('ITE(Eq(x, y), x, y)');
  });

  it('as_Boolean, Not of floats, canonical relations', () => {
    // SymPy as_Boolean(Symbol('p', positive=True)) is True; symjs has no zero=True symbols (SymPy gives False for them)
    expect(s(L.asBoolean(sj.symbol('p', { positive: true })))).toBe('True');
    expect(s(B.notFn(new sj.Float(2.5)))).toBe('False');
    expect(s(B.notFn(new sj.Float(0)))).toBe('True');
    expect(s(B.relCanonical(sj.Lt(x, sj.mul(-1, y)) as Rel))).toBe('x < -y');
    expect(s(B.relCanonical(sj.Lt(y, sj.mul(-1, x)) as Rel))).toBe('x < -y');
  });

  it('relations in And, Or, Xor, Equivalent, Implies', () => {
    // Or keeps the first of equal relations in the given order, And the first in sorted order
    expect(s(B.orFn(sj.Lt(x, 1), sj.Gt(1, x), y))).toBe('y | (x < 1)');
    expect(s(B.orFn(sj.Gt(1, x), sj.Lt(x, 1), y))).toBe('y | (1 > x)');
    expect(s(B.andFn(sj.Lt(x, 1), sj.Gt(1, x), y))).toBe('y & (1 > x)');
    expect(s(B.andFn(sj.Gt(1, x), sj.Lt(x, 1), y))).toBe('y & (1 > x)');
    // Or compares only its own arguments, not those of a nested Or
    expect(s(B.orFn(sj.Lt(x, 1), B.orFn(sj.Gt(1, x), y)))).toBe('y | (1 > x) | (x < 1)');
    expect(s(B.orFn(sj.Lt(x, 1), B.orFn(sj.Ge(x, 1), y)))).toBe('y | (x >= 1) | (x < 1)');
    expect(s(B.orFn(sj.Lt(x, 1), sj.Ge(x, 1)))).toBe('True');
    expect(s(B.xorFn([sj.Lt(x, 1), sj.Lt(y, 2)]))).toBe('(x < 1) ^ (y < 2)');
    expect(s(L.Equivalent(sj.Lt(x, 1), sj.Lt(y, 2)))).toBe('Equivalent(x < 1, y < 2)');
    expect(s(L.Implies(sj.Lt(x, 1), sj.Lt(y, 2)))).toBe('Implies(x < 1, y < 2)');
  });

  it('binary_symbols', () => {
    expect([...B.binarySymbols(eqT(sj.S.true, x)).values()].map(s)).toEqual(['x']);
    expect(B.binarySymbols(eqT(B.andFn(x, y), sj.S.true)).size).toBe(0);
    expect(B.binarySymbols(sj.S.true).size).toBe(0);
  });
});

const dict = (m: unknown): string =>
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
    expect([...L.satisfiable(L.ITE(x, y, z), { allModels: true })].map(dict).sort()).toEqual(all);
    expect([...L.satisfiable(new BoolOp('ITE', [x, y, z]), { allModels: true })].map(dict).sort()).toEqual(all);
    expect(dict(L.satisfiable(L.ITE(x, y, z)))).toBe('{x: False, y: True, z: True}');
  });

  it('minimal model with every variable false', () => {
    expect(dict(L.satisfiable(B.andFn(B.notFn(x), B.notFn(y)), { minimal: true }))).toBe('{x: False, y: False}');
  });

  it('SATSolver with an empty clause or without variables', () => {
    expect([...new SATSolver([[]], 1).findModels()]).toEqual([]);
    expect([...new SATSolver([[1, 2], []], 2).findModels()]).toEqual([]);
    expect([...new SATSolver([], 0).findModels()]).toEqual([[]]);
  });
});

describe('normal forms', () => {
  it('to_nnf', () => {
    expect(s(L.toNnf(B.andFn(x, B.notFn(B.orFn(x, y)))))).toBe('False');
    expect(s(L.toNnf(B.orFn(x, B.notFn(B.andFn(x, y)))))).toBe('True');
    expect(s(L.toNnf(new BoolOp('ITE', [x, y, z])))).toBe('(x | z) & (y | ~x)');
    expect(s(L.toNnf(L.ITE(x, y, z)))).toBe('(x | z) & (y | ~x)');
    expect(s(L.toNnf(B.notFn(L.ITE(x, y, z))))).toBe('(x | ~z) & (~x | ~y)');
    // unevaluated gates: the arguments in NNF, then the gate evaluated
    expect(s(L.toNnf(L.Nand(x, B.orFn(y, B.notFn(B.andFn(y, z))), { evaluate: false })))).toBe('~x');
    expect(s(L.toNnf(L.Nor(x, L.Implies(y, z), { evaluate: false })))).toBe('~(x | z | ~y)');
    // a relation that is not a literal is its own NNF (Boolean.to_nnf)
    expect(s(L.toNnf(B.andFn(x, sj.Gt(sj.add(x, sj.mul(y, z)), 1))))).toBe('x & (x + y*z > 1)');
    // SymPy: ValueError Illegal operator Nand / f / <class 'sympy.core.add.Add'> in expression
    expect(() => L.toNnf(B.notFn(L.Nand(x, y, { evaluate: false })))).toThrow('Illegal operator Nand in expression');
    const f = sj.SymFunction('f');
    expect(() => L.toNnf(B.notFn(f(sj.add(x, 1))))).toThrow('Illegal operator f in expression');
    expect(() => L.toNnf(B.notFn(sj.add(x, sj.mul(y, z))))).toThrow('Illegal operator Add in expression');
  });

  it('is_anf and to_anf', () => {
    expect(L.isAnf(B.xorFn([B.andFn(x, B.notFn(y)), z]))).toBe(false);
    expect(s(L.toAnf(B.andFn(x, B.orFn(y, z)), false))).toBe('x & (y | z)');
    expect(s(L.toAnf(B.orFn(x, y), false))).toBe('x ^ y ^ (x & y)');
    expect(s(L.toAnf(B.orFn(x, B.andFn(y, B.notFn(z))), false))).toBe('x ^ (y & ~z) ^ (x & y & ~z)');
    expect(s(L.toAnf(new BoolOp('ITE', [x, y, z])))).toBe('ITE(x, y, z)');
    // SymPy: AttributeError ('StrictLessThan' object has no attribute 'to_anf'); a relation is kept
    expect(s(L.toAnf(sj.Lt(sj.add(x, sj.mul(y, z)), 1)))).toBe('x + y*z < 1');
  });

  it('to_int_repr and integer_to_term', () => {
    expect(L.toIntRepr([B.orFn(B.notFn(x), y)], [x, y]).map((c) => [...c].sort((a, b) => a - b))).toEqual([[-1, 2]]);
    // SymPy: KeyError z
    expect(() => L.toIntRepr([B.orFn(x, z)], [x])).toThrow(RangeError);
    // SymPy ibin: ValueError (negative numbers are not allowed / `bits` must be >= 3)
    expect(() => L.integerToTerm(-1)).toThrow(RangeError);
    expect(() => L.integerToTerm(5, 2)).toThrow(RangeError);
  });
});

describe('minimization', () => {
  it('simplify_logic with constants among the predicates, deep=False', () => {
    expect(s(L.simplifyLogic(L.Nand(x, true, { evaluate: false })))).toBe('~x');
    expect(s(L.simplifyLogic(L.Nand(x, false, { evaluate: false })))).toBe('True');
    expect(s(L.simplifyLogic(L.Nand(x, 1, { evaluate: false })))).toBe('~x');
    expect(s(L.simplifyLogic(L.Nand(x, 0, { evaluate: false })))).toBe('True');
    expect(s(L.simplifyLogic(L.ITE(x, y, true, { evaluate: false })))).toBe('y | ~x');
    expect(s(L.simplifyLogic(L.Xnor(x, y, false, { evaluate: false })))).toBe('(x | ~y) & (y | ~x)');
    const r = B.orFn(y, sj.Eq(sj.sub(sj.mul(x, sj.add(x, 1)), sj.pow(x, 2)), 1));
    expect(s(L.simplifyLogic(r, { deep: false }))).toBe('y | Eq(-x**2 + x*(x + 1), 1)');
    expect(s(L.simplifyLogic(r))).toBe('y | Eq(x, 1)');
  });

  it('simplify_logic: a dontcare with too many variables is ignored', () => {
    const v = sj.symbols('v0:9');
    const dc = B.andFn(...v);
    // SymPy: simplify_logic((x & y) | (x & ~y), dontcare=And(v0, ..., v8)) is x
    expect(s(L.simplifyLogic(B.orFn(B.andFn(x, y), B.andFn(x, B.notFn(y))), { dontcare: dc }))).toBe('x');
    expect(s(L.simplifyLogic(B.orFn(x, y), { dontcare: B.andFn(y, ...v.slice(0, 7)) }))).toBe('x | y');
  });

  it('SOPform with a bad term', () => {
    expect(() => L.SOPform([x], ['a' as unknown as number])).toThrow(TypeError);
  });

  it('bool_map without a match', () => {
    // SymPy gives None or False
    expect(L.boolMap(B.orFn(x, y), B.orFn(x, y, z))).toBe(sj.NoMatch);
    expect(L.boolMap(B.orFn(B.andFn(x, y), z), B.orFn(B.andFn(x, B.notFn(y)), z))).toBe(sj.NoMatch);
    expect(L.boolMap(B.orFn(B.andFn(x, y), z), B.orFn(B.andFn(x, y), B.notFn(z)))).toBe(sj.NoMatch);
    expect(L.boolMap(B.orFn(x, y, B.notFn(z)), B.orFn(x, B.notFn(y), B.notFn(z)))).toBe(sj.NoMatch);
    // SymPy: NotImplementedError unexpected level of nesting
    expect(() => L.boolMap(B.orFn(B.andFn(x, sj.Gt(y, 1)), z), B.orFn(B.andFn(w, sj.Gt(y, 1)), z))).toThrow(sj.NotImplementedError);
    // SymPy: KeyError f(x)
    const f = sj.SymFunction('f');
    expect(() => L.boolMap(B.orFn(B.notFn(f(x)), y), B.orFn(B.notFn(f(z)), w))).toThrow(sj.NotImplementedError);
  });

  it('bool_map with symbols in terms of different shapes', () => {
    const [a, b, c, d] = sj.symbols('a b c d');
    const e1 = B.orFn(B.andFn(x, y), B.andFn(x, B.notFn(z), w));
    const e2 = B.orFn(B.andFn(a, b), B.andFn(a, B.notFn(c), d));
    const m = L.boolMap(e1, e2);
    if (sj.isNoMatch(m)) throw new Error('no match');
    expect(s(m[0])).toBe('x & (w | y) & (y | ~z)');
    expect([...m[1]].map(([k, v]) => `${s(k)}: ${s(v)}`).sort()).toEqual(['w: d', 'x: a', 'y: b', 'z: c']);
  });
});

describe('inference of unevaluated gates', () => {
  it('satisfiable of Nand, Nor, Xnor', () => {
    const all = (e: sj.Expr): string[] => [...L.satisfiable(e, { allModels: true })].map(dict).sort();
    expect(all(L.Nand(x, y, { evaluate: false }))).toEqual(['{x: False, y: False}', '{x: False, y: True}', '{x: True, y: False}']);
    expect(all(L.Nor(x, y, { evaluate: false }))).toEqual(['{x: False, y: False}']);
    expect(all(L.Xnor(x, y, { evaluate: false }))).toEqual(['{x: False, y: False}', '{x: True, y: True}']);
  });
});
