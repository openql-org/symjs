// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/public.ts: the monotonicity wrappers; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { isDecreasing, isStrictlyDecreasing, isStrictlyIncreasing, oo, parse, symbols, Matrix, EmptySet, linsolveAugmented, solveLinearSystem } from '../../src';
import type { Expr, Sym } from '../../src';
import { interval } from '../../src/sets/sets';

const [x, y] = symbols('x y');

describe('monotonicity wrappers', () => {
  it('follow SymPy (None is unknown)', () => {
    const pos = interval(0, oo);
    const neg = interval(oo.neg(), 0);
    const unit = interval(0, 1);
    expect([parse('-x**3'), parse('x**2')].map((e) => isStrictlyIncreasing(e))).toEqual([false, false]);
    expect([isStrictlyIncreasing(parse('-x'), unit, x), isStrictlyIncreasing(parse('x**2'), neg)]).toEqual([false, false]);
    expect([parse('-x**3'), parse('x**2')].map((e) => isDecreasing(e))).toEqual([true, false]);
    expect([isDecreasing(parse('-x'), unit), isDecreasing(parse('x**2'), pos, x)]).toEqual([true, false]);
    expect([parse('x**3'), parse('x**2')].map((e) => isStrictlyDecreasing(e))).toEqual([false, false]);
    expect([isStrictlyDecreasing(parse('-x'), unit), isStrictlyDecreasing(parse('x**2'), pos, x)]).toEqual([true, false]);
  });
});

it('solves augmented systems through the public API', () => {
  expect(linsolveAugmented(Matrix.of([[1, 1, 2]]), [x, y]).toString()).toBe('2 - y,y');
  expect([...solveLinearSystem(Matrix.of([[1, 1, 2]]), [x, y]) as Map<Sym, Expr>].map(([k, v]) => `${k}:${v}`)).toEqual(['x:2 - y']);
  expect(solveLinearSystem(Matrix.of([[0, 0, 1]]), [x, y])).toBe(EmptySet);
  expect(() => linsolveAugmented(Matrix.of([[1, 2]]), [x, y])).toThrow('one more column');
});

import * as sj from '../../src';
it('extracts linear matrices without cancelling nonlinear structure', () => {
  expect(sj.linearEqToMatrix([sj.parseExpr('x + y*(3*x + 2)')], [x]).map(String)).toEqual(['Matrix([[3*y + 1]])', 'Matrix([[-2*y]])']);
  expect(sj.linearEqToMatrix([new sj.Rel('Eq', sj.add(x, 2), sj.S.One)], [x]).map(String)).toEqual(['Matrix([[1]])', 'Matrix([[-1]])']);
  expect(sj.linearEqToMatrix([], [x]).map((m) => [m.rows, m.cols])).toEqual([[0, 1], [0, 1]]);
  expect(() => sj.linearEqToMatrix([x], [])).toThrow(RangeError);
  expect(() => sj.linearEqToMatrix([x], [x, x])).toThrow(RangeError);
  expect(() => sj.linearEqToMatrix([sj.S.true], [x])).toThrow(TypeError);
  expect(() => sj.linearEqToMatrix([sj.Gt(x, 0)], [x])).toThrow(TypeError);
  expect(() => sj.linearEqToMatrix([new sj.Rel('Eq', sj.add(sj.pow(x, -1), x), sj.pow(x, -1))], [x])).toThrow(sj.NonlinearError);
  expect(() => sj.linearEqToMatrix([sj.parseExpr('(x+1)**3-x**3-3*x**2+7')], [x])).toThrow(sj.NonlinearError);
});

it('solves linear systems with expression unknowns and rejects ambiguous unknowns', () => {
  const f = sj.SymFunction('f')(x);
  expect(sj.linsolve([sj.add(f, -5)], [f]).toString()).toBe('5');
  expect(sj.linsolve([sj.add(x, y, -1)], [x, y]).toString()).toBe('1 - y,y');
  expect(sj.linsolve([x, sj.add(x, 1)], [x])).toBe(EmptySet);
  expect(() => sj.linsolve([x], [])).toThrow(RangeError);
  expect(() => sj.linsolve([x], [x, x])).toThrow(RangeError);
});

it('exposes periodicity, monotonicity and recurrence results through public wrappers', () => {
  const n = new sj.Sym('n', { integer: true });
  expect(String(sj.periodicity(sj.sin(x), x))).toBe('2*pi');
  expect(sj.periodicity(x, x)).toBe(sj.NoMatch);
  expect(sj.isIncreasing(x)).toBe(true);
  expect(sj.isIncreasing(x, sj.interval(0, 1), x)).toBe(true);
  expect(sj.isMonotonic(x)).toBe(true);
  expect(sj.isMonotonic(sj.pow(x, 2), sj.Reals, x)).toBe(false);
  for (const result of [sj.rsolvePoly([-1, 1], 1, n), sj.rsolvePoly([-1, 1], 1, n, 0), sj.rsolveRatio([-1, 1], 1, n), sj.rsolveHyper([-1, 1], 1, n)]) {
    expect(Array.isArray(result) && String(result[0])).toBe('C0 + n');
  }
});
