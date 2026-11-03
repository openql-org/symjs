// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/defun.ts.
// User-defined functions (defineFunction). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import {
  type Expr,
  SymFunction,
  defineFunction,
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
