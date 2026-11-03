// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, collect, dsolve, mul, parse, pow, symbol, symbols } from '../src';

const [x, a] = symbols('x a');
const P = parse;

const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe("collect: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["collect(P('C1 + C2*x + C3*x**2'), P('x**2'))", () => collect(P('C1 + C2*x + C3*x**2'), P('x**2')), "C1 + C2*x + C3*x**2"],
    ["collect(P('x + x**3 + x**4*y'), P('x**2'))", () => collect(P('x + x**3 + x**4*y'), P('x**2')), "x**4*y + x**3 + x"],
    ["collect(P('x**4*y + x**4 + x*a + x'), P('x**2'))", () => collect(P('x**4*y + x**4 + x*a + x'), P('x**2')), "a*x + x**4*(y + 1) + x"],
    ["collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)'))", () => collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)')), "sqrt(x)*(y + 1) + x*(a + 1)"],
    ["collect(P('a*x**2 + b*x**2 + a*x - b*x'), x)", () => collect(P('a*x**2 + b*x**2 + a*x - b*x'), x), "x**2*(a + b) + x*(a - b)"],
    ["collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y'))", () => collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y')), "2**(2*y)*(a + b) + 2**y"],
    ["collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)'))", () => collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)')), "(a + b)*exp(2*x)"],
    ["dsolve(P('Derivative(f(x), x, 3) - x'), P('f(x)'))", () => dsolve(P('Derivative(f(x), x, 3) - x'), P('f(x)')), "Eq(f(x), C1 + C2*x + C3*x**2 + x**4/24)"],
    ["collect(P('x*a + x'), P('x**2'))", () => collect(P('x*a + x'), P('x**2')), "a*x + x"],
    ["collect(P('x**3*a + x**3'), P('x**2'))", () => collect(P('x**3*a + x**3'), P('x**2')), "a*x**3 + x**3"],
    ["collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)'))", () => collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)')), "x**(3/2)*(a + 1)"],
    ["collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2'))", () => collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2')), "1/x + (a + 1)/x**2"],
    ["(() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })()", () => (() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })(), "p**3*(a + 1) + p*(a + 1)"],
    ["collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)'))", () => collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)')), "2**(3*y)*a + 2**(3*y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
