// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of small core modules: guard invariants, error classes, Basic, kinds, Indexed, Lambda,
// ExprMap, undefined functions and Subs. Expected values are SymPy 1.14's where SymPy has them.
import { inspect } from 'node:util';
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { at, cast, defined, expectType, getOrThrow, pair } from '../src/core/guard';
import { InvariantError } from '../src/core/errors';

const [x, y] = sj.symbols('x y');

describe('guard invariants', () => {
  it('throws InvariantError when a guarantee does not hold', () => {
    expect(at([1, 2], -1)).toBe(2);
    expect(() => at([1], 3)).toThrow(InvariantError);
    expect(() => defined(undefined, 'v')).toThrow(InvariantError);
    expect(() => defined(null)).toThrow(InvariantError);
    expect(getOrThrow(new Map([['a', undefined]]), 'a')).toBe(undefined);
    expect(() => getOrThrow(new Map<string, number>(), 'a')).toThrow(InvariantError);
    expect(() => cast(1, sj.Expr)).toThrow(InvariantError);
    expect(() => cast(1, sj.Expr, 'one')).toThrow('one is not a Expr');
    expect(() => expectType(1, (v): v is string => typeof v === 'string')).toThrow(InvariantError);
    expect(pair([1, 2, 3])).toEqual([1, 2]);
  });
});

describe('matrix error classes (SymPy sympy.matrices.exceptions)', () => {
  it('follows the SymPy hierarchy', () => {
    // SymPy: NonSquareMatrixError(ShapeError), ShapeError(ValueError, MatrixError), NonPositiveDefiniteMatrixError(ValueError, MatrixError)
    const e = new sj.NonSquareMatrixError();
    expect(e).toBeInstanceOf(sj.ShapeError);
    expect(e).toBeInstanceOf(sj.MatrixError);
    expect(new sj.ShapeError()).toBeInstanceOf(sj.MatrixError);
    expect(new sj.ShapeError().message).toBe('Matrices are not aligned');
    const p = new sj.NonPositiveDefiniteMatrixError();
    expect(p).toBeInstanceOf(sj.MatrixError);
    expect(p.message).toBe('Matrix must be positive-definite');
    expect(p.name).toBe('NonPositiveDefiniteMatrixError');
    expect(new sj.NonInvertibleMatrixError()).toBeInstanceOf(sj.MatrixError);
  });

  it('keeps an inverse of a Kronecker product of non-square factors unevaluated', () => {
    const A = sj.MatrixSymbol('A', 2, 3);
    const B = sj.MatrixSymbol('B', 3, 2);
    expect(String(sj.Inverse(sj.KroneckerProduct(A, B)))).toBe('(KroneckerProduct(A, B))**(-1)');
  });
});

describe('small core nodes', () => {
  it('rebuilds Basic and prints kinds', () => {
    // SymPy: Basic(x, y).xreplace({x: y}) = Basic(y, y)
    expect(String(sj.xreplace(sj.Basic(x, y), [[x, y]]))).toBe('Basic(y, y)');
    expect(inspect(sj.NumberKind)).toBe('NumberKind');
  });

  it('prints and differentiates indexed objects', () => {
    const A = new sj.IndexedBase('A');
    const i = sj.symbol('i');
    expect(String(A)).toBe('A');
    expect(String(new sj.IndexedBase(sj.symbol('B')))).toBe('B');
    expect(String(sj.diff(A.at(i), A.at(i)))).toBe('1');
  });

  it('prints Lambda and checks the number of arguments', () => {
    const f = sj.Lambda([x, y], sj.add(x, y));
    expect(sj.latex(f)).toBe('\\left( \\left( x, \\  y\\right) \\mapsto x + y \\right)');
    // SymPy raises BadArgumentsError (a TypeError)
    expect(() => f.call(1)).toThrow(TypeError);
  });

  it('keeps ExprMap keys structurally', () => {
    const m = new sj.ExprMap<number>();
    m.set(1, 1);
    m.set(x, 2);
    expect(m.get(1)).toBe(1);
    expect(m.delete(y)).toBe(false);
    expect(m.delete(x)).toBe(true);
    m.clear();
    expect(m.size).toBe(0);
    expect(m.has(1)).toBe(false);
  });

  it('creates undefined functions and Subs', () => {
    // SymPy: symbols('f g', cls=Function) = (f, g)
    expect(sj.functions('f g').map((f) => String(f(x)))).toEqual(['f(x)', 'g(x)']);
    expect(() => sj.SymFunction('1f')).toThrow(SyntaxError);
    // SymPy: Subs(x, [], []) = x; mismatched lengths raise ValueError
    expect(String(sj.Subs(x, [], []))).toBe('x');
    expect(() => sj.Subs(x, [x, y], [1])).toThrow(RangeError);
  });
});
