// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/defun.ts.
// User-defined functions (defineFunction). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { runInNewContext } from 'node:vm';
import { at } from '../../src/core/guard';
import * as sj from '../../src';
import {
  type Expr,
  NoMatch,
  SymFunction,
  arity,
  defineFunction,
  log,
  sin,
  diff,
  evalf,
  expand,
  implementedFunction,
  latex,
  mul,
  pow,
  rewrite,
  str,
  symbols,
} from '../../src';

const [x, y] = symbols('x y');

const g = SymFunction('g');
const s = (e: unknown): string => str(e as Expr);

describe('defineFunction', () => {
  it('validates names and arities and uses custom numeric and printing hooks', () => {
    expect(() => defineFunction('bad-name')).toThrow(SyntaxError);
    const f = defineFunction('custom', { nargs: [1, 2], latex: (args) => `F(${args.join(',')})`, evalf: (a) => a + 1 });
    expect(() => f()).toThrow(TypeError);
    expect(latex(f(x))).toBe('F(x)');
    const value = f(2);
    if (!(value instanceof sj.DefinedFunctionCall)) throw new TypeError('a defined function expected');
    expect(String(value.numericValue(15))).toBe('3.00000000000000');
  });
  it('constructs Taylor series from evaluation and partial derivatives', () => {
    const mysin = defineFunction('mysin', {
      nargs: 1,
      eval: (a) => a.equals(0) ? 0 : undefined,
      fdiff: (args) => sj.cos(at(args, 0)),
    });
    expect(String(sj.series(mysin(x), x, 0, 10))).toBe('x - x**3/6 + x**5/120 - x**7/5040 + x**9/362880 + O(x**10)');
    expect(String(sj.limit(sj.mul(mysin(x), sj.pow(x, -1)), x, 0))).toBe('1');
  });
  const myf = defineFunction('myf', { expand: { twice: () => undefined } });
  it('differentiates without fdiff like SymPy Function.fdiff', () => {
    expect(s(diff(myf(x), x))).toBe('Derivative(myf(x), x)');
    expect(s(diff(myf(x, y), x))).toBe('Derivative(myf(x, y), x)');
    expect(s(diff(myf(pow(x, 2)), x))).toBe('2*x*Subs(Derivative(myf(_xi_1), _xi_1), _xi_1, x**2)');
    expect(s(diff(myf(x, x), x))).toBe('Subs(Derivative(myf(_xi_1, x), _xi_1), _xi_1, x) + Subs(Derivative(myf(x, _xi_2), _xi_2), _xi_2, x)');
    expect(s(diff(myf(g(x)), x))).toBe('Derivative(g(x), x)*Derivative(myf(g(x)), g(x))');
    expect(s(diff(myf(mul(2, x), y), x))).toBe('2*Subs(Derivative(myf(_xi_1, y), _xi_1), _xi_1, 2*x)');
  });
  it('uses fdiff only for the arguments containing the variable', () => {
    const h = defineFunction('h', { fdiff: (_args, idx) => (idx === 0 ? y : x) });
    expect(s(diff(h(x, y), x))).toBe('y');
  });
  it('prints LaTeX, expands and evaluates by default', () => {
    expect(latex(myf(x))).toBe('\\operatorname{myf}{\\left(x \\right)}');
    expect(latex(defineFunction('h')(x, y))).toBe('h{\\left(x,y \\right)}');
    expect(s(expand(myf(x), { twice: true }))).toBe('myf(x)');
    // myf(x).rewrite(cos) -> myf(x)
    expect(s(rewrite(myf(x), 'cos'))).toBe('myf(x)');
    // no numeric implementation: the call stays (SymPy keeps myf(1); symjs evalf also evaluates the arguments)
    expect(s(evalf(myf(1)))).toBe('myf(1.0)');
    const inv = implementedFunction('inv', (t) => 1 / t);
    expect(s(evalf(inv(x)))).toBe('inv(x)');
    // a non-finite value is not a Float: the call stays
    expect(s(evalf(inv(0)))).toBe('inv(0)');
  });
});

describe('arity', () => {
  it('counts the parameters of a function (SymPy arity)', () => {
    expect(arity((a: number) => a)).toBe(1);
    expect(arity((a: number, b = 1) => a + b)).toEqual([1, 2]);
    expect(arity((...a: number[]) => a.length)).toBe(NoMatch);
    expect(arity(function named(a: number, b = [1, 2], c = 'x,y)', d = { e: 1 }) { return [a, b, c, d]; })).toEqual([1, 2, 3, 4]);
    expect(arity(async (a: number, b: number) => a + b)).toBe(2);
    expect(arity(sin)).toBe(1);
    // a single parameter without parentheses, from source text
    // (written as source text: the test transform adds the parentheses)
    expect(arity(runInNewContext('x => Math.abs(x)') as (x: number) => number)).toBe(1);
    // TypeScript optional parameters leave no trace at run time (SymPy arity(log) is (1, 2))
    expect(arity(log)).toBe(2);
  });
  it('uses nargs or eval of defined functions', () => {
    expect(arity(defineFunction('g2', { nargs: [2, 1] }))).toEqual([1, 2]);
    expect(arity(defineFunction('g3', { nargs: 3 }))).toBe(3);
    expect(arity(defineFunction('g4', { eval: (a) => a }))).toBe(1);
    // SymPy Function.eval(*args): no fixed count
    expect(arity(defineFunction('g5'))).toBe(NoMatch);
  });
});

describe('func of a defined function', () => {
  it('is the function defineFunction made', () => {
    const f = sj.defineFunction('fhead', { nargs: 1 });
    const [x] = sj.symbols('x');
    expect(sj.func(f(x))).toBe(f);
    expect(sj.func(sj.Mod(x, 3))).toBe(sj.Mod);
  });
});
