// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/traverse.ts.
// Substitution (subs, xreplace) and bound variables. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import {
  Derivative,
  type Expr,
  Integral,
  Lambda,
  O,
  Subs,
  Sum,
  add,
  exp,
  freeSymbols,
  mul,
  pi,
  pow,
  rational,
  rebuild,
  sin,
  sqrt,
  str,
  subs,
  symbols,
  xreplace,
} from '../../src';

const [x, y, C1, C2, z, w, n] = symbols('x y C1 C2 z w n');

const f = sj.SymFunction('f');
const s = (e: unknown): string => String(e);

const [pp] = symbols('p', { positive: true });
const p = pp as Expr;

const s2 = (e: unknown): string => str(e as Expr);
const sb = (e: Expr, from: Expr, to: Expr | number): string => s2(subs(e, [[from, to]]));

describe('bound variables', () => {
  const I = new Integral([mul(x, y), x, mul(0), y]);
  const S = Sum(mul(x, y), [x, 0, y]);

  it('are not free', () => {
    expect([...freeSymbols(I)].map(String)).toEqual(['y']);
    expect([...freeSymbols(S)].map(String)).toEqual(['y']);
    // the variable of an indefinite integral stays free (SymPy)
    expect([...freeSymbols(new Integral([mul(x, y), x]))].map(String).sort()).toEqual(['x', 'y']);
  });

  it('are not substituted', () => {
    expect(subs(I, [[x, 2]]).toString()).toBe('Integral(x*y, (x, 0, y))');
    expect(subs(S, [[x, 2]]).toString()).toBe('Sum(x*y, (x, 0, y))');
    expect(subs(I, [[y, 2]]).toString()).toBe('Integral(2*x, (x, 0, 2))');
    expect(subs(S, [[y, 2]]).toString()).toBe('Sum(2*x, (x, 0, 2))');
  });
});

describe('Mul substitution (SymPy Mul._eval_subs)', () => {
  const R = (p: number, q: number): sj.Expr => sj.Rational.of(BigInt(p), BigInt(q));
  it.each([
    [sj.mul(2, y, sj.pow(C1, -1)), sj.mul(2, sj.pow(C1, -1)), 'C2*y'],
    [sj.mul(4, x), sj.mul(2, x), '2*C2'],
    [sj.mul(6, x), sj.mul(2, x), '3*C2'],
    [sj.mul(3, x), sj.mul(2, x), '3*x'],
    [sj.mul(4, sj.pow(x, 2)), sj.mul(2, x), 'C2**2'],
    [sj.mul(2, sj.pow(x, 2)), sj.mul(2, x), 'C2*x'],
    [sj.mul(8, sj.pow(x, 3)), sj.mul(2, x), 'C2**3'],
    [sj.mul(R(1, 2), x), sj.mul(R(1, 2), x), 'C2'],
    [sj.mul(R(3, 4), x), sj.mul(R(1, 2), x), '3*C2/2'],
    [sj.mul(R(1, 4), x), sj.mul(R(1, 2), x), 'C2/2'],
    [sj.mul(-2, x), sj.mul(2, x), '-C2'],
    [sj.mul(-4, x), sj.mul(-2, x), '2*C2'],
    [sj.mul(2, x), sj.mul(-2, x), '2*x'],
    [sj.mul(6, x, y), sj.mul(3, x), '2*C2*y'],
    [sj.mul(R(9, 2), x), sj.mul(R(3, 2), x), '3*C2'],
    [sj.mul(2, sj.I, x), sj.mul(2, x), 'I*C2'],
    [sj.mul(4, x, y), sj.mul(2, x), '2*C2*y'],
  ])('(%s).subs(%s, C2)', (e, old, expected) => {
    expect(s(sj.subs(e, [[old, C2]]))).toBe(expected);
  });

  it('substitutes sums, powers, noncommutative products and several pairs', () => {
    const A = sj.symbol('A', { commutative: false });
    const B = sj.symbol('B', { commutative: false });
    const z = sj.symbol('z');
    expect(s(sj.subs(sj.mul(x, y), [[sj.mul(2, x), z]]))).toBe('x*y');
    expect(s(sj.subs(sj.mul(A, B, x), [[sj.mul(A, B), z]]))).toBe('x*z');
    expect(s(sj.subs(sj.mul(A, x), [[sj.mul(A, B), z]]))).toBe('x*A');
    expect(s(sj.subs(sj.mul(A, B), [[sj.mul(2, A, B), z]]))).toBe('A*B');
    expect(s(sj.subs(sj.add(x, y, 2), [[sj.add(x, y, 1), z]]))).toBe('z + 1');
    expect(s(sj.subs(sj.add(sj.mul(-1, x), sj.mul(-1, y), 2), [[sj.add(x, y, 1), z]]))).toBe('3 - z');
    expect(s(sj.subs(sj.pow(x, 3), [[sj.pow(x, 2), y]]))).toBe('x**3');
    expect(s(sj.subs(sj.add(x, y), { x: 1, y: 2 }))).toBe('3');
    expect(s(sj.subs(sj.add(x, y), new Map([[x, y], [y, x]]), { simultaneous: true }))).toBe('x + y');
    expect(s(sj.subs(sj.mul(x, y), [[x, y], [y, 2]]))).toBe('4');
    expect(s(sj.subs(sj.diff(f(x), x, 2), [[sj.diff(f(x), x), y]]))).toBe('Derivative(y, x)');
    expect(s(sj.subs(sj.diff(f(x), x), [[sj.diff(f(x), x, 2), y]]))).toBe('Derivative(f(x), x)');
  });
});

describe('xreplace and rebuild', () => {
  it('accepts a Map, pairs or an object keyed by symbol name', () => {
    const e = add(sin(x), y);
    expect(s2(xreplace(e, { x: 2 }))).toBe('y + sin(2)');
    expect(s2(xreplace(e, new Map([[x, 2]])))).toBe('y + sin(2)');
    expect(s2(xreplace(e, [[x, 2]]))).toBe('y + sin(2)');
    expect(s2(subs(e, { x: 2 }))).toBe('y + sin(2)');
    expect(s2(subs(e, new Map([[x, 2]])))).toBe('y + sin(2)');
  });
  it('rebuilds an Order term', () => {
    expect(s2(xreplace(O(x), [[x, y]]))).toBe('O(y)');
  });
  it('keeps a rebuilt derivative unevaluated', () => {
    expect(sb(Derivative(f(x), x), f(x), pow(x, 2))).toBe('Derivative(x**2, x)');
    expect(s2(xreplace(Derivative(f(x), x), [[f(x), pow(x, 2)]]))).toBe('Derivative(x**2, x)');
  });
  it('returns an atom as it is', () => {
    expect(rebuild(x, [])).toBe(x);
  });
});

describe('subs of powers (SymPy Pow._eval_subs)', () => {
  it('substitutes a power of the same base', () => {
    expect(sb(pow(x, 4), pow(x, 2), w)).toBe('w**2');
    expect(sb(pow(x, 3), pow(x, 2), w)).toBe('x**3');
    // a positive base: (p**2)**(3/2) == p**3
    expect(sb(pow(p, 3), pow(p, 2), w)).toBe('w**(3/2)');
    expect(sb(pow(x, mul(6, y)), pow(x, mul(3, y)), w)).toBe('w**2');
    expect(sb(pow(x, mul(y, z)), pow(x, y), w)).toBe('x**(y*z)');
    expect(sb(pow(x, mul(2, pi)), pow(x, pi), w)).toBe('w**2');
  });
  it('substitutes term by term in a sum exponent', () => {
    expect(sb(exp(add(x, y)), exp(x), w)).toBe('w*exp(y)');
    expect(sb(exp(add(mul(2, x), y)), exp(x), w)).toBe('w**2*exp(y)');
    expect(sb(exp(add(x, y, z)), exp(x), w)).toBe('w*exp(y + z)');
    // the terms of exp(x + y) are not terms of x + y + z one by one
    expect(sb(exp(add(x, y, z)), exp(add(x, y)), w)).toBe('exp(x + y + z)');
    expect(sb(pow(x, add(mul(6, y), z)), pow(x, mul(3, y)), w)).toBe('w**2*x**z');
    expect(sb(pow(x, add(mul(6, y), 1)), pow(x, mul(3, y)), w)).toBe('w**2*x');
    expect(sb(pow(p, add(mul(3, x), 1)), pow(p, mul(2, x)), w)).toBe('p**(3*x + 1)');
  });
});

describe('subs of derivatives (SymPy Derivative._eval_subs)', () => {
  const fxy = f(x, y);
  it('substitutes a lower derivative', () => {
    expect(sb(Derivative(fxy, x, y), Derivative(fxy, y, x), w)).toBe('w');
    expect(sb(Derivative(fxy, x, x, y), Derivative(fxy, x, y), w)).toBe('Derivative(w, x)');
    expect(sb(Derivative(fxy, x, y), Derivative(fxy, x, x), w)).toBe('Derivative(f(x, y), x, y)');
  });
});

describe('subs of sums (SymPy Add._eval_subs)', () => {
  it('matches the terms and the numeric coefficient', () => {
    expect(sb(add(x, y, z), add(mul(-1, x), mul(-1, y)), w)).toBe('-w + z');
    expect(sb(add(x, y, 2), add(x, y, 3), w)).toBe('w - 1');
    expect(sb(add(x, y, 2), add(mul(-1, x), mul(-1, y), 3), w)).toBe('5 - w');
    // a Float coefficient only combines with an equal one
    expect(sb(add(x, y, 2.5), add(x, y), z)).toBe('x + y + 2.5');
    expect(sb(add(x, y, z, 2.5), add(x, y, 2.5), w)).toBe('w + z');
    expect(sb(add(x, y, z, 2.5), add(x, y, 1.5), w)).toBe('x + y + z + 2.5');
    expect(sb(add(x, y, 2), add(x, 1), w)).toBe('w + y + 1');
    expect(sb(add(x, 2), add(y, 1), w)).toBe('x + 2');
    expect(sb(add(x, 2), add(x, 3), w)).toBe('w - 1');
    // pi is not a numeric coefficient
    expect(sb(add(pi, x, y), add(x, y), z)).toBe('z + pi');
  });
});

describe('subs of products (SymPy Mul._eval_subs)', () => {
  it('substitutes factors with symbolic exponents', () => {
    expect(sb(mul(2, pow(x, y), z), mul(pow(x, y), z), w)).toBe('2*w');
    // sqrt(x**y) and x**(2*y) are both powers of x**y: SymPy answers w*x**(3*y/2), which is
    // not equal in general ((x**y)**(3/2) != x**(3*y/2) for complex x**y); z*x**y*(x**y)**(3/2) is
    expect(sb(mul(z, sqrt(pow(x, y)), pow(x, mul(2, y))), mul(z, pow(x, y)), w)).toBe('w*(x**y)**(3/2)');
  });
  it('needs one denominator to divide the other', () => {
    expect(sb(mul(sqrt(x), y), mul(pow(x, rational(1, 3)), y), z)).toBe('sqrt(x)*y');
  });
  it('handles negative coefficients', () => {
    expect(sb(mul(-4, x, y), mul(-2, x), w)).toBe('2*w*y');
    expect(sb(mul(4, x, y), mul(-2, x), w)).toBe('4*x*y');
    expect(sb(mul(x, y), mul(-2, x), w)).toBe('x*y');
    expect(sb(mul(x, y), mul(2, x), w)).toBe('x*y');
    expect(sb(mul(6, x, y), mul(4, x), w)).toBe('6*x*y');
  });
});

describe('subs of bound variables', () => {
  it('substitutes only the limits', () => {
    expect(sb(new Integral([x, x, rational(0), x]), x, y)).toBe('Integral(x, (x, 0, y))');
    expect(sb(new Integral([x, x, rational(0), y]), x, y)).toBe('Integral(x, (x, 0, y))');
    expect(sb(Sum(x, [x, 1, n]), x, 2)).toBe('Sum(x, (x, 1, n))');
    expect(sb(Sum(x, [x, 1, x]), x, 2)).toBe('Sum(x, (x, 1, 2))');
    expect(sb(Subs(Derivative(f(x), x), x, 2), x, 3)).toBe('Subs(Derivative(f(x), x), x, 2)');
    expect(sb(Subs(Derivative(f(x), x), x, add(x, 1)), x, 2)).toBe('Subs(Derivative(f(x), x), x, 3)');
    expect(sb(Lambda(x, add(x, y)), y, 2)).toBe('Lambda(x, x + 2)');
  });
});
