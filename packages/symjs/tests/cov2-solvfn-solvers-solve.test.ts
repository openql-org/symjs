// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { NotImplementedError, nonlinsolve, parse, solve, solveLinear, symbols } from '../src';

const [x, y] = symbols('x y');
const show = (r: readonly Expr[]): string => `[${r.map(String).join(', ')}]`;
const sol = (s: string) => show(solve(parse(s), x));

// expected values from SymPy 1.14 solve / nonlinsolve; comments mark where symjs differs
describe('solve', () => {
  it('a power of a function of x: its base is an n-th root', () => {
    expect(sol('sin(x)**2 - 1/4')).toBe('[-pi/6, pi/6, 5*pi/6, 7*pi/6]');
    expect(sol('sin(x)**(-2) - 4')).toBe('[-pi/6, pi/6, 5*pi/6, 7*pi/6]');
  });
  it('a power of a radical or a logarithm', () => {
    expect(sol('(sqrt(x) + 1)**2 - 4')).toBe('[1]');
    expect(sol('log(x)**3 - 8')).toBe('[exp(2), exp(-1 - sqrt(3)*I), exp(-1 + sqrt(3)*I)]');
  });
  it('radicals', () => {
    // the seventh root is solved through the substitution x + 1 = t**7 (SymPy: [127])
    expect(sol('(x + 1)**(1/7) - 2')).toBe('[127]');
    expect(sol('x**(1/61) - 2')).toBe('[2305843009213693952]');
    expect(sol('1/sqrt(x) - 2')).toBe('[1/4]');
    expect(sol('sqrt(x) + x**(-1/3)')).toBe('[]');
    // SymPy: [0]; a seventh root beside other terms is not squared away (degree limit)
    expect(() => sol('(x + 1)**(1/7) + x - 1')).toThrow(NotImplementedError);
    // the lcm 122 of the root indices is beyond the substitution limit (SymPy does not finish)
    expect(() => sol('x**(1/61) + sqrt(x) - 2')).toThrow(NotImplementedError);
  });
  it('Lambert W forms', () => {
    expect(sol('x*exp(x) - 1')).toBe('[LambertW(1)]');
    // the constant term vanishes: (x + 1)*exp(x) = 0
    expect(sol('x*exp(x) + exp(x)')).toBe('[-1]');
    // SymPy: [2*LambertW(-1/2), 2*LambertW(1/2)] (a square root of both sides first)
    expect(() => sol('x**2*exp(x) - 1')).toThrow(NotImplementedError);
    // SymPy: NotImplementedError as well
    expect(() => sol('x + exp(x**2)')).toThrow(NotImplementedError);
  });
  it('equations out of reach', () => {
    // SymPy: [exp(LambertW(log(2)))]
    expect(() => sol('x**x - 2')).toThrow(NotImplementedError);
    // SymPy: [] (no formula for a symbolic quintic)
    expect(() => sol('x**5 + y*x + 1')).toThrow(NotImplementedError);
    // 13 nested exponentials exceed the recursion depth (SymPy: a tower of 13 logarithms of -log(log(2)))
    let e = 'x';
    for (let i = 0; i < 13; i++) e = `exp(${e})`;
    expect(() => sol(`${e} - 2`)).toThrow(NotImplementedError);
  });
});

describe('nonlinsolve', () => {
  it('an equation solved with LambertW', () => {
    // SymPy: {(x, 1)}, which leaves x free although x*exp(x) = 1 fixes it; exp(W(1))*W(1) = 1
    expect(nonlinsolve([parse('x*exp(x) - y'), parse('y - 1')], [x, y]).map(show)).toEqual(['[LambertW(1), exp(LambertW(1))*LambertW(1)]']);
  });
  it('a single radical that is the whole equation', () => {
    expect(nonlinsolve([parse('sqrt(x)'), parse('y - 1')], [x, y]).map(show)).toEqual(['[0, 1]']);
  });
  it('a solution that cannot be evaluated is kept', () => {
    // SymPy: {(ConditionSet(x, Eq(sqrt(x) - g(1), 0), {g(1)**2}),)}
    expect(nonlinsolve([parse('sqrt(x) - g(1)')], [x]).map(show)).toEqual(['[g(1)**2]']);
  });
  it('unsupported systems', () => {
    // SymPy: {(-cos(y), y)}, which does not solve sin(x) + x*y = 0
    expect(() => nonlinsolve([parse('sin(x) + x*y'), parse('cos(y) + x')], [x, y])).toThrow(NotImplementedError);
  });
});

describe('solveLinear', () => {
  it('a derivative whose free symbols are the symbols but which does not change with them', () => {
    const pr = (r: readonly [Expr, Expr]) => `(${String(r[0])}, ${String(r[1])})`;
    expect(pr(solveLinear(parse('x*(sin(x)**2 + cos(x)**2 + sin(y)**2 + cos(y)**2) - 1'), { symbols: [x, y] }))).toBe(
      '(x*(sin(x)**2 + sin(y)**2 + cos(x)**2 + cos(y)**2) - 1, 1)',
    );
    expect(pr(solveLinear(parse('x*(sin(y)**2 + cos(y)**2) - 1'), { symbols: [x] }))).toBe('(0, 1)');
  });
});
