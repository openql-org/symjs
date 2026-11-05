// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference results from SymPy 1.14 (sympy/solvers/tests/test_simplex.py and the doctests of solvers/simplex.py).
import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src';
import { Matrix, NonlinearError, S, parseExpr } from '../../src';
import { InfeasibleLPError, UnboundedLPError, linprog, lpmax, lpmin, showLinprog } from '../../src/solvers/simplex';

const e = (src: string): Expr => parseExpr(src);
const c = (...src: string[]): Expr[] => src.map(e);
const sm = ([o, p]: [Expr, ReadonlyMap<Expr, Expr>]): string => `(${String(o)}, {${[...p].map(([k, v]) => `${String(k)}: ${String(v)}`).join(', ')}})`;
const sl = ([o, p]: [Expr, readonly Expr[]]): string => `(${String(o)}, [${p.map(String).join(', ')}])`;

describe('lpmin and lpmax', () => {
  it('solve the doctests', () => {
    expect(sm(lpmin(e('x'), c('x >= 1')))).toBe('(1, {x: 1})');
    expect(sm(lpmin(e('x'), c('x >= 0', 'x <= 3')))).toBe('(0, {x: 0})');
    expect(sm(lpmax(e('x'), c('x <= -1')))).toBe('(-1, {x: -1})');
    expect(sm(lpmin(e('x'), c('2*x - 3*y >= -1', 'Eq(x + 3*y, 2)', 'x <= 2*y')))).toBe('(1/3, {x: 1/3, y: 5/9})');
    expect(sm(lpmax(e('x'), c('2*x - 3*y >= -1', 'Eq(x + 3*y, 2)', 'x <= 2*y')))).toBe('(4/5, {x: 4/5, y: 2/5})');
  });

  it('solve the problems of test_lp', () => {
    expect(sm(lpmax(e('-x - y - 5*z'), c('y + 2*z <= 3', '-x - 3*z <= -2', '2*x + y + 7*z <= 5', 'x >= 0', 'y >= 0', 'z >= 0')))).toBe(
      '(-2, {x: 2, y: 0, z: 0})',
    );
    expect(sm(lpmax(e('-x - y - 5*z + 2'), c('x - y + 2*z <= -4', '-x + 2*y - 3*z <= 8', '2*x + y - 7*z <= 10', 'x >= 0', 'y >= 0', 'z >= 0')))).toBe(
      '(-2, {x: 0, y: 4, z: 0})',
    );
    expect(sm(lpmax(e('-x - y - 5*z'), c('x - y + 2.0*z <= -4', '-x + 2*y - 3.0*z <= 8', '2*x + y - 7*z <= 10', 'x >= 0', 'y >= 0', 'z >= 0')))).toBe(
      '(-4, {x: 0, y: 4, z: 0})',
    );
    // Ferguson, Section 4 Problem 1
    expect(
      sm(lpmax(e('x1 - 2*x2 - 3*x3 - x4'), c('x1 - x2 - 2*x3 - x4 <= 4', '2*x1 + x3 - 4*x4 <= 2', '-2*x1 + x2 + x4 <= 1', 'x1 >= 0', 'x2 >= 0', 'x3 >= 0', 'x4 >= 0'))),
    ).toBe('(4, {x1: 7, x2: 0, x3: 0, x4: 3})');
    expect(sm(lpmax(e('x'), c('Eq(x, y)', 'Eq(y, z)', 'z <= 3')))).toBe('(3, {x: 3, y: 3, z: 3})');
  });

  it('handle equalities, extra symbols and constant constraints', () => {
    expect(sm(lpmax(e('x - y'), c('x <= y + 2', 'x >= y + 2', 'x >= 0', 'y >= 0')))).toBe('(2, {x: 2, y: 0})');
    expect(sm(lpmax(e('x - y'), c('x <= y + 2', 'Eq(x, 2)')))).toBe('(2, {x: 2, y: 0})');
    expect(sm(lpmax(e('y'), c('Eq(y, 2)')))).toBe('(2, {y: 2})');
    expect(sm(lpmin(e('y'), c('x <= y + 2', 'x >= y + 2', 'y >= 0')))).toBe('(0, {x: 2, y: 0})');
    expect(sm(lpmax(e('y'), c('0 <= y + 2', '0 >= y + 2')))).toBe('(-2, {y: -2})');
    expect(sm(lpmin(e('x'), c('y >= 1', 'x >= y')))).toBe('(1, {x: 1, y: 1})');
    expect(sm(lpmin(e('x'), c('y >= 1', 'x >= y + z', 'x >= 0', 'z >= 0')))).toBe('(1, {x: 1, y: 1, z: 0})');
    expect(sm(lpmax(e('x'), [S.true, e('x <= 2')]))).toBe('(2, {x: 2})');
    // a univariate constraint that is not linear still gives an interval
    expect(sm(lpmin(e('x'), c('x**2 <= 1')))).toBe('(-1, {x: -1})');
  });

  it('report errors as SymPy', () => {
    expect(() => lpmax(e('-x - y - 5*z'), c('x - y + sqrt(2)*z <= -4'))).toThrow(TypeError);
    expect(() => lpmax(e('x'), c('x >= 0'))).toThrow(UnboundedLPError);
    expect(() => lpmax(e('x'), c('x >= 0', 'x <= -1'))).toThrow(InfeasibleLPError);
    expect(() => lpmax(e('x'), [S.false, e('x <= 2')])).toThrow(InfeasibleLPError);
    expect(() => lpmin(e('x + y'), c('x + y <= -1', 'x >= 0', 'y >= 0'))).toThrow('The constraint set is empty!');
    expect(() => lpmax(e('x'), c('x > 0'))).toThrow(TypeError);
    expect(() => lpmax(e('x'), c('Ne(x, 0)'))).toThrow(TypeError);
    expect(() => lpmax(e('x'), c('x <= oo'))).toThrow('only finite bounds are permitted');
    expect(() => lpmax(e('x'), c('x <= -oo*y'))).toThrow('only finite bounds are permitted');
    expect(() => lpmin(e('x*y'), c('x >= 0'))).toThrow(NonlinearError);
  });

  it('detects an oscillation without a solution (o1)', () => {
    expect(() =>
      lpmin(e('9*x2 - 8*x3 + 3*x4 + 6'), c('5*x2 - 2*x3 <= 0', '-x1 - 8*x2 + 9*x3 <= -3', '10*x1 - x2 + 9*x4 <= -4', 'x1 >= 0', 'x2 >= 0', 'x3 >= 0', 'x4 >= 0')),
    ).toThrow(InfeasibleLPError);
  });
});

describe('linprog', () => {
  it('solves the doctests', () => {
    expect(sl(linprog([1], undefined, undefined, undefined, undefined, [1, null]))).toBe('(1, [1])');
    expect(sl(linprog([1], [-1], [-1]))).toBe('(1, [1])');
    const ab = [Matrix.of([[-1, 5, 1, 4]]), Matrix.of([[-1, 5, 2, 5]]), Matrix.of([[5]]), Matrix.of([[0, 3, 0, 1], [-1, 0, 1, 2]]), Matrix.col(2, 1)] as const;
    expect(sl(linprog(...ab))).toBe('(9/2, [0, 1/2, 0, 1/2])');
    // o2: this system oscillates and ends in a valid solution
    expect(sl(linprog(...ab, [0, 1]))).toBe('(9/2, [0, 1/2, 0, 1/2])');
  });

  it('solves the problems of test_linprog', () => {
    const A = [[7, 4, -7], [3, -1, 10], [-1, 0, 0], [0, -1, 0], [0, 0, -1]];
    const b = [3, 6, 0, 0, 0];
    expect(sl(linprog([[1, 1, -2]], A, b))).toBe('(-6/5, [0, 0, 3/5])');
    expect(sl(linprog([[1, 1, -2]], A, b, [[-9, 1, 0]], [1]))).toBe('(-2/5, [0, 1, 7/10])');
    expect(sl(linprog([[1, 1, -2]], A, b, undefined, undefined, [[0, null], [0, null], [null, S.Half]]))).toBe('(-1, [0, 0, 1/2])');
    expect(sl(linprog([[1, 1, -2]], A, b, undefined, undefined, new Map([[2, [null, S.Half] as const]])))).toBe('(-1, [0, 0, 1/2])');
    expect(sl(linprog([[1]], [], [], undefined, undefined, [2, 3]))).toBe('(2, [2])');
    expect(sl(linprog([1], undefined, undefined, undefined, undefined, [2, 3]))).toBe('(2, [2])');
    expect(sl(linprog([1, -1], [[1, 1]], [2], undefined, undefined, new Map([[1, [null, null] as const]])))).toBe('(-2, [0, 2])');
    expect(sl(linprog([1, -1], [[1, 1]], [5], undefined, undefined, new Map([[1, [3, null] as const]])))).toBe('(-5, [0, 5])');
    expect(sl(linprog(Matrix.of([[1, 2]]), Matrix.of([[1, 1]]), Matrix.col(3)))).toBe('(0, [0, 0])');
  });

  it('interprets the bounds', () => {
    expect(sl(linprog([-1], [[1]], [5], undefined, undefined, [null, 3]))).toBe('(-3, [3])');
    expect(sl(linprog([1, 1], [[1, 1]], [5], undefined, undefined, [[0, null], [2, null]]))).toBe('(2, [0, 2])');
    expect(sl(linprog([1], [[1]], [5], undefined, undefined, new Map()))).toBe('(0, [0])');
    expect(sl(linprog([1], [[1]], [5], undefined, undefined, [0, null]))).toBe('(0, [0])');
    // SymPy fails here ("Cannot create a 1 x -2 matrix")
    expect(sl(linprog([1, 1], [[1, 1]], [5], undefined, undefined, [[0, null], [0, null]]))).toBe('(0, [0, 0])');
    expect(() => linprog([1], [[1]], [5], undefined, undefined, [[0, null, 1] as unknown as readonly [number, null]])).toThrow('unexpected bounds');
    expect(() => linprog([1], [[1]], [1], undefined, undefined, new Map([[3, [0, 1] as const]]))).toThrow(RangeError);
    expect(() => linprog([1], [[1]], [5], undefined, undefined, [e('sqrt(2)'), null] as const)).toThrow(TypeError);
  });

  it('rejects an oscillation that ends outside the feasible region', () => {
    // SymPy returns (3, [1]), which violates 2*x <= 0
    expect(() => linprog([3], [[2], [3], [-1]], [0, 1, -1])).toThrow(InfeasibleLPError);
  });

  it('reports errors as SymPy', () => {
    expect(() => linprog([1])).toThrow('must give A and B');
    expect(() => linprog([[1, 2], [3, 4]])).toThrow('C must be a single row.');
    expect(() => linprog([1], [], [1])).toThrow('A and b must both be given');
    expect(() => linprog([1], [[1]])).toThrow('A and b must both be given');
    expect(() => linprog([1, 2], [[1]], [1])).toThrow('number of columns in A and C must match');
    expect(() => linprog([1], [[1]], [1], [[1]])).toThrow('A_eq and b_eq must both be given');
    expect(() => linprog([1], [[1]], [1], undefined, [1])).toThrow('A_eq and b_eq must both be given');
  });
});

describe('showLinprog', () => {
  it('writes the problem in the variables x1, x2, ...', () => {
    const [f, cons] = showLinprog([1, 2], [[1, 1]], [3], [[1, -1]], [0], [[1, null], [null, 4]]);
    expect(String(f)).toBe('x1 + 2*x2');
    expect(cons.map(String)).toEqual(['x1 + x2 <= 3', 'Eq(x1 - x2, 0)', 'x1 >= 1', 'x2 <= 4']);
    expect(showLinprog([[3]]).map(String)).toEqual(['3*x1', '']);
    expect(() => showLinprog([[1, 2], [3, 4]])).toThrow('C must be a single row.');
    expect(() => showLinprog([1], [[1]])).toThrow('A and b must both be given');
  });
});
