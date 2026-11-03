// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/calculus/diff.ts.
// Differentiation: diff and Derivative. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import {
  Derivative,
  type Expr,
  I,
  Limit,
  Lt,
  Product,
  diff,
  exp,
  floor,
  log,
  mul,
  pow,
  rational,
  sin,
  str,
  symbols,
} from '../../src';
import { NotImplementedError } from '../../src/core/errors';
import { cast } from '../../src/core/guard';
import { Integral } from '../../src/core/nodes';

const [x, y, k, n, h] = symbols('x y k n h');

const r = sj.symbol('r', { real: true });
const f = sj.SymFunction('f');
const g = sj.SymFunction('g');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [x, y, k, n, h, r] });
const s = (e: unknown): string => String(e);

const s2 = (e: unknown): string => str(e as Expr);

describe('diff', () => {
  it('differentiates', () => {
    expect(diff(pow(x, 3), x).toString()).toBe('3*x**2');
    expect(diff(sin(mul(2, x)), x).toString()).toBe('2*cos(2*x)');
    expect(diff(exp(mul(I, x)), x).toString()).toBe('I*exp(I*x)');
    expect(diff(mul(x, log(x)), x).toString()).toBe('log(x) + 1');
    expect(diff(pow(x, 4), x, 2).toString()).toBe('12*x**2');
    expect(diff(pow(2, x), x).toString()).toBe('2**x*log(2)');
  });
});

describe('diff (SymPy diff)', () => {
  it.each([
    ['asin(x)', '1/sqrt(1 - x**2)'],
    ['acos(x)', '-1/sqrt(1 - x**2)'],
    ['atan(x)', '1/(x**2 + 1)'],
    ['sinh(x)', 'cosh(x)'],
    ['cosh(x)', 'sinh(x)'],
    ['tanh(x)', '1 - tanh(x)**2'],
    ['tan(x)', 'tan(x)**2 + 1'],
    ['log(x)', '1/x'],
    ['2**x', '2**x*log(2)'],
    ['x**x', 'x**x*(log(x) + 1)'],
    ['exp(x**2)', '2*x*exp(x**2)'],
  ])('d/dx %s', (e, expected) => {
    expect(s(sj.diff(P(e), x))).toBe(expected);
  });

  it('differentiates conjugate, re, im and Abs', () => {
    expect(s(sj.diff(sj.Abs(sj.add(sj.pow(r, 2), 1)), r))).toBe('2*r');
    expect(s(sj.diff(sj.conjugate(sj.pow(r, 2)), r))).toBe('2*r');
    expect(s(sj.diff(sj.re(sj.mul(r, sj.I)), r))).toBe('0');
    expect(s(sj.diff(sj.im(sj.mul(r, sj.I)), r))).toBe('1');
    // conjugate is not holomorphic: Derivative(conjugate(x), x) stays unevaluated for a variable that may be complex
    expect(s(sj.diff(sj.conjugate(sj.sin(x)), x))).toBe('cos(conjugate(x))*Derivative(conjugate(x), x)');
    expect(s(sj.diff(sj.re(x), x))).toBe('Derivative(re(x), x)');
    expect(() => sj.diff(sj.Abs(sj.sin(x)), x)).toThrow(sj.NotImplementedError);
    // SymPy 1.14: cos(r)*sign(sin(r)), equal where sin(r) != 0
    expect(s(sj.diff(sj.Abs(sj.sin(r)), r))).toBe('sin(r)*cos(r)/Abs(sin(r))');
    expect(s(sj.diff(sj.conjugate(f(r)), r))).toBe('conjugate(Derivative(f(r), r))');
    expect(s(sj.diff(sj.re(f(r)), r))).toBe('re(Derivative(f(r), r))');
    expect(s(sj.diff(sj.im(f(r)), r))).toBe('im(Derivative(f(r), r))');
  });

  it('differentiates undefined functions, derivatives, sums and piecewise functions', () => {
    expect(s(sj.diff(f(g(x)), x))).toBe('Derivative(f(g(x)), g(x))*Derivative(g(x), x)');
    expect(s(sj.diff(f(x, y), x))).toBe('Derivative(f(x, y), x)');
    expect(s(sj.diff(sj.diff(f(x), x), y))).toBe('0');
    expect(s(sj.diff(sj.diff(f(x), x), x))).toBe('Derivative(f(x), (x, 2))');
    expect(s(sj.diff(sj.Sum(sj.mul(sj.pow(x, k), y), [k, 0, n]), y))).toBe('Sum(x**k, (k, 0, n))');
    expect(() => sj.diff(sj.Sum(sj.pow(x, k), [k, 0, n]), n)).toThrow(sj.NotImplementedError);
    expect(s(sj.diff(sj.Piecewise([sj.pow(x, 2), sj.Gt(x, 0)], [x, true]), x))).toBe('Piecewise((2*x, x > 0), (1, True))');
    expect(s(sj.diff(x, x, 0))).toBe('x');
    expect(s(sj.diff(f(sj.add(x, 1)), x))).toBe('Subs(Derivative(f(_xi_1), _xi_1), _xi_1, x + 1)');
    expect(s(sj.diff(f(sj.add(x, 1), sj.mul(2, x)), x))).toBe(
      'Subs(Derivative(f(_xi_1, 2*x), _xi_1), _xi_1, x + 1) + 2*Subs(Derivative(f(x + 1, _xi_2), _xi_2), _xi_2, 2*x)',
    );
  });

  it('keeps derivatives it does not know unevaluated', () => {
    expect(s(sj.diff(sj.parse('floor(x)', { symbols: [x] }), x))).toBe('Derivative(floor(x), x)');
    expect(s(sj.diff(sj.parse('ceiling(x)', { symbols: [x] }), x))).toBe('Derivative(ceiling(x), x)');
    expect(s(sj.diff(sj.parse('sign(x)', { symbols: [x] }), x))).toBe('Derivative(sign(x), x)');
    expect(s(sj.diff(sj.parse('floor(x**2)', { symbols: [x] }), x))).toBe('Derivative(floor(x**2), x)');
    // SymPy 1.14: 2*DiracDelta(r); DiracDelta is defined above the calculus module (integrals), so it stays unevaluated
    expect(s(sj.diff(sj.parse('sign(r)', { symbols: [r] }), r))).toBe('Derivative(sign(r), r)');
    expect(s(sj.diff(sj.parse('arg(r)', { symbols: [r] }), r))).toBe('0');
    // SymPy 1.14: (re(x)*Derivative(im(x), x) - im(x)*Derivative(re(x), x))/(re(x)**2 + im(x)**2)
    expect(s(sj.diff(sj.parse('arg(x)', { symbols: [x] }), x))).toBe('Derivative(arg(x), x)');
  });

  it('differentiates integrals (Leibniz rule)', () => {
    const I = (...a: sj.ExprLike[]): sj.Expr => new Integral(a.map((v) => sj.sympify(v)));
    expect(s(sj.diff(I(sj.mul(x, y), y, 0, x), x))).toBe('x**2 + Integral(y, (y, 0, x))');
    expect(s(sj.diff(I(sj.mul(x, y), y, x), x))).toBe('x**2 + Integral(y, (y, x))');
    expect(s(sj.diff(I(f(y), y, x, 1), x))).toBe('-f(x)');
    expect(s(sj.diff(I(I(f(y), y), y, x), x))).toBe('Integral(f(y), (y, x))');
    expect(s(sj.diff(I(sj.mul(x, y), y), x))).toBe('Integral(y, y)');
    expect(s(sj.diff(I(f(y), y, 0, 1), x))).toBe('0');
  });

  it('differentiates with respect to functions and derivatives', () => {
    expect(s(sj.diff(sj.pow(f(x), 2), f(x)))).toBe('2*f(x)');
    expect(s(sj.diff(sj.mul(f(x), g(x)), f(x)))).toBe('g(x)');
    expect(s(sj.diff(sj.pow(sj.diff(f(x), x), 2), sj.diff(f(x), x)))).toBe('2*Derivative(f(x), x)');
    expect(s(sj.diff(sj.pow(f(x), 2), f(x), 2))).toBe('2');
  });

  it('differentiates with respect to matrix elements', () => {
    const X = sj.MatrixSymbol('X', 2, 2);
    const Z = sj.MatrixSymbol('Z', n, n);
    expect(s(sj.diff(sj.Trace(X), X.at(0, 0)))).toBe('1');
    expect(s(sj.diff(sj.Trace(X), X.at(0, 1)))).toBe('0');
    expect(s(sj.diff(sj.mul(X.at(0, 0), X.at(1, 1)), X.at(0, 0)))).toBe('X[1, 1]');
    expect(s(sj.diff(sj.Determinant(X), X.at(0, 0)))).toBe('Derivative(Determinant(X), X[0, 0])');
    expect(s(sj.diff(X.asExplicit().det(), X.at(0, 0)))).toBe('X[1, 1]');
    expect(s(sj.diff(X.at(0, 1), X.at(0, 0)))).toBe('0');
    expect(s(sj.diff(Z.at(0, 1), Z.at(0, 0)))).toBe('0');
    expect(s(sj.diff(cast(sj.MatMul(X, X), sj.MatrixExpr).at(0, 0), X.at(0, 0)))).toBe('2*X[0, 0]');
    expect(s(sj.diff(sj.Trace(sj.MatMul(X, X)), X.at(0, 1)))).toBe('2*X[1, 0]');
    expect(s(sj.diff(sj.pow(X.at(0, 0), 3), X.at(0, 0), 2))).toBe('6*X[0, 0]');
    // SymPy 1.14: Sum(KroneckerDelta(0, i, (0, n - 1)), (i, 0, n - 1)); symjs has no KroneckerDelta range and keeps delta**2
    expect(s(sj.diff(sj.Trace(Z), Z.at(0, 0)))).toBe('Sum(KroneckerDelta(0, i)**2, (i, 0, n - 1))');
  });
});

describe('diff', () => {
  it('differentiates derivatives, integrals and unevaluated objects', () => {
    expect(s2(diff(Derivative(f(y), y), x))).toBe('0');
    expect(s2(diff(Derivative(f(mul(x, y)), y), x))).toBe('x*y*Subs(Derivative(f(_xi_1), (_xi_1, 2)), _xi_1, x*y) + Subs(Derivative(f(_xi_1), _xi_1), _xi_1, x*y)');
    expect(s2(diff(Derivative(mul(x, f(x)), x), x))).toBe('x*Derivative(f(x), (x, 2)) + 2*Derivative(f(x), x)');
    // SymPy evaluates Derivative(floor(x*y), y) through Subs; symjs keeps it and appends x
    expect(s2(diff(Derivative(floor(mul(x, y)), y), x))).toBe('Derivative(floor(x*y), y, x)');
    expect(s2(diff(new Integral([f(x), x]), x))).toBe('f(x)');
    expect(s2(diff(new Integral([pow(x, 2), x, rational(0), x]), x))).toBe('x**2');
    expect(s2(diff(new Integral([mul(x, y), y, rational(0), rational(1)]), x))).toBe('Integral(y, (y, 0, 1))');
    expect(s2(diff(Lt(x, 1), x))).toBe('Derivative(x < 1, x)');
    expect(s2(diff(new Limit([mul(sin(mul(x, y)), pow(y, -1)), y, rational(0)], '+'), x))).toBe("Derivative(Limit(sin(x*y)/y, y, 0, dir='+'), x)");
    // SymPy: Sum(_h*Product(k*x, (k, 1, _h - 1))*Product(k*x, (k, _h + 1, n)), (_h, 1, n))
    expect(() => diff(Product(mul(x, k), [k, 1, n]), x)).toThrow(NotImplementedError);
    expect(() => diff(x, x, -1)).toThrow(RangeError);
    expect(() => diff(x, x, 1.5)).toThrow(RangeError);
  });
  it('merges the variables of an evaluated derivative', () => {
    expect(s2(diff(diff(diff(f(x, y), x), y), x))).toBe('Derivative(f(x, y), (x, 2), y)');
    const [z] = symbols('z');
    expect(s2(diff(diff(diff(f(x, y, z), z), y), x))).toBe('Derivative(f(x, y, z), x, y, z)');
    expect(s2(diff(diff(diff(f(x, y, z), x), y), z))).toBe('Derivative(f(x, y, z), x, y, z)');
    // two symbols named x (one real): sorted by name, so the order is kept
    const [xr] = symbols('x', { real: true });
    expect(s2(diff(diff(f(x, xr as Expr), x), xr as Expr))).toBe('Derivative(f(x, x), x, x)');
  });
});
