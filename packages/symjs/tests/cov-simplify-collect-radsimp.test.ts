// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Wild, add, collect, factor, mul, parse, pow, rcollect, symbol, symbols } from '../src';

const [x, y, n, k, z, a, b] = symbols('x y n k z a b');
const r = symbol('r', { real: true });
const p = symbol('p', { positive: true });
const kk = symbol('kk', { integer: true });
const P = (s: string) => parse(s, { symbols: [x, y, n, k, r, p, kk, z, a, b] });

const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe("collect: SymPy 1.14 test_radsimp cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["collect(1, P(\"x\"))", () => collect(1, P("x")), "1"],
    ["collect(P(\"x*y + x\"), P(\"x\"))", () => collect(P("x*y + x"), P("x")), "x*(y + 1)"],
    ["collect(P(\"x**2 + x\"), P(\"x\"))", () => collect(P("x**2 + x"), P("x")), "x**2 + x"],
    ["collect(P(\"x**2*y + x**2\"), P(\"x\"))", () => collect(P("x**2*y + x**2"), P("x")), "x**2*(y + 1)"],
    ["collect(P(\"x**2 + x*y\"), P(\"x\"))", () => collect(P("x**2 + x*y"), P("x")), "x**2 + x*y"],
    ["collect(P(\"x**2*y + 2*x**2 + 3*x*y\"), [P(\"x\")])", () => collect(P("x**2*y + 2*x**2 + 3*x*y"), [P("x")]), "x**2*(y + 2) + 3*x*y"],
    ["collect(P(\"x**2*y + 2*x**2 + 3*x*y\"), [P(\"y\")])", () => collect(P("x**2*y + 2*x**2 + 3*x*y"), [P("y")]), "2*x**2 + y*(x**2 + 3*x)"],
    ["collect(P(\"x**4 + 4*x**3*y + 4*x**3 + 6*x**2*y**2 + 12*x**2*y + 6*x**2 + 4*x*y**3 + 12*x*y**2 + 12*x*y + 4*x + y**4 + 4*y**3 + 6*y**2 + 4*y + 1\"), P(\"x\"))", () => collect(P("x**4 + 4*x**3*y + 4*x**3 + 6*x**2*y**2 + 12*x**2*y + 6*x**2 + 4*x*y**3 + 12*x*y**2 + 12*x*y + 4*x + y**4 + 4*y**3 + 6*y**2 + 4*y + 1"), P("x")), "x**4 + x**3*(4*y + 4) + x**2*(6*y**2 + 12*y + 6) + x*(4*y**3 + 12*y**2 + 12*y + 4) + y**4 + 4*y**3 + 6*y**2 + 4*y + 1"],
    ["collect(P(\"x*exp(x) + 3*x + y*sin(x) + 2*sin(x)\"), P(\"x\"), { exact: null })", () => collect(P("x*exp(x) + 3*x + y*sin(x) + 2*sin(x)"), P("x"), { exact: null }), "x*exp(x) + 3*x + (y + 2)*sin(x)"],
    ["collect(P(\"x*y*exp(x) + x*y + x*exp(x) + 3*x + y*sin(x) + 2*sin(x)\"), P(\"x\"), { exact: null })", () => collect(P("x*y*exp(x) + x*y + x*exp(x) + 3*x + y*sin(x) + 2*sin(x)"), P("x"), { exact: null }), "x*(y + 1)*exp(x) + x*(y + 3) + (y + 2)*sin(x)"],
    ["collect(P(\"a*(sin(x) + cos(x)) + b*(sin(x) + cos(x))\"), P(\"sin(x) + cos(x)\"))", () => collect(P("a*(sin(x) + cos(x)) + b*(sin(x) + cos(x))"), P("sin(x) + cos(x)")), "(a + b)*(sin(x) + cos(x))"],
    ["collect(P(\"x*y - x/8\"), P(\"-x\"))", () => collect(P("x*y - x/8"), P("-x")), "x*(y - 1/8)"],
    ["collect(P(\"x*y**2 + 1\"), P(\"x*y\"))", () => collect(P("x*y**2 + 1"), P("x*y")), "x*y**2 + 1"],
    ["collect(P(\"a*x*y + x*y\"), P(\"x*y\"))", () => collect(P("a*x*y + x*y"), P("x*y")), "x*y*(a + 1)"],
    ["collect(P(\"a*x*y + x*y + 1\"), P(\"x*y\"))", () => collect(P("a*x*y + x*y + 1"), P("x*y")), "x*y*(a + 1) + 1"],
    ["collect(P(\"a*x*f(x) + b*x*f(x)\"), P(\"x*f(x)\"))", () => collect(P("a*x*f(x) + b*x*f(x)"), P("x*f(x)")), "x*(a + b)*f(x)"],
    ["collect(P(\"a*x*log(x) + b*x*log(x)\"), P(\"x*log(x)\"))", () => collect(P("a*x*log(x) + b*x*log(x)"), P("x*log(x)")), "x*(a + b)*log(x)"],
    ["collect(P(\"a*x**2*log(x)**2 + b*x**2*log(x)**2\"), P(\"x*log(x)\"))", () => collect(P("a*x**2*log(x)**2 + b*x**2*log(x)**2"), P("x*log(x)")), "x**2*(a + b)*log(x)**2"],
    ["collect(P(\"a*x*y*z + x*y*z\"), P(\"x*y*z\"))", () => collect(P("a*x*y*z + x*y*z"), P("x*y*z")), "x*y*z*(a + 1)"],
    ["collect(P(\"a*x**c + b*x**c\"), P(\"x**c\"))", () => collect(P("a*x**c + b*x**c"), P("x**c")), "x**c*(a + b)"],
    ["collect(P(\"a*x**(2*c) + b*x**(2*c)\"), P(\"x**c\"))", () => collect(P("a*x**(2*c) + b*x**(2*c)"), P("x**c")), "x**(2*c)*(a + b)"],
    ["collect(P(\"a*z + x**2*y**4*z + x**2*y**4 + z\"), [P(\"x*y**2\"), P(\"z\")])", () => collect(P("a*z + x**2*y**4*z + x**2*y**4 + z"), [P("x*y**2"), P("z")]), "x**2*y**4*(z + 1) + z*(a + 1)"],
    ["collect(P(\"x**2 + 2*x*y + x + y**2 + y + 1\"), [P(\"x\"), P(\"y\")])", () => collect(P("x**2 + 2*x*y + x + y**2 + y + 1"), [P("x"), P("y")]), "x**2 + x*(2*y + 1) + y**2 + y + 1"],
    ["collect(P(\"a*Derivative(f(x), x) + b*Derivative(f(x), x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("a*Derivative(f(x), x) + b*Derivative(f(x), x)"), P("Derivative(f(x), x)")), "(a + b)*Derivative(f(x), x)"],
    ["collect(P(\"5*f(x) + 3*Derivative(f(x), x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("5*f(x) + 3*Derivative(f(x), x)"), P("Derivative(f(x), x)")), "5*f(x) + 3*Derivative(f(x), x)"],
    ["collect(P(\"x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)"), P("Derivative(f(x), x)")), "(x*f(x) + f(x))*Derivative(f(x), x) + f(x)"],
    ["collect(P(\"x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)\"), P(\"Derivative(f(x), x)\"), { exact: true })", () => collect(P("x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)"), P("Derivative(f(x), x)"), { exact: true }), "(x*f(x) + f(x))*Derivative(f(x), x) + f(x)"],
    ["collect(P(\"x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)\"), P(\"Derivative(f(x), x)\"), { exact: true })", () => collect(P("x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)"), P("Derivative(f(x), x)"), { exact: true }), "(x/f(x) + 1/f(x))*Derivative(f(x), x) + 1/f(x)"],
    ["collect(P(\"x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)"), P("Derivative(f(x), x)")), "(x/f(x) + 1/f(x))*Derivative(f(x), x) + 1/f(x)"],
    ["collect(P(\"a**3 + 3*a**2*x + 3*a**2 + 3*a*x**2 + 6*a*x + 3*a + x**3 + 3*x**2 + 3*x + 1\"), P(\"x\"))", () => collect(P("a**3 + 3*a**2*x + 3*a**2 + 3*a*x**2 + 6*a*x + 3*a + x**3 + 3*x**2 + 3*x + 1"), P("x")), "a**3 + 3*a**2 + 3*a + x**3 + x**2*(3*a + 3) + x*(3*a**2 + 6*a + 3) + 1"],
    ["collect(P(\"f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)\"), P(\"w_\"))", () => collect(P("f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"), P("w_")), "f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"],
    ["collect(P(\"x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)\"), P(\"f(x)\"))", () => collect(P("x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)"), P("f(x)")), "(x*Derivative(f(x), x) + Derivative(f(x), x) + 1)*f(x)"],
    ["collect(P(\"f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)\"), [P(\"f(x)\"), P(\"Derivative(f(x), x)\")])", () => collect(P("f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"), [P("f(x)"), P("Derivative(f(x), x)")]), "(Derivative(f(x), x) + 1)*f(x) + Derivative(f(x), x)"],
    ["collect(P(\"f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)\"), [P(\"Derivative(f(x), x)\"), P(\"f(x)\")])", () => collect(P("f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"), [P("Derivative(f(x), x)"), P("f(x)")]), "(f(x) + 1)*Derivative(f(x), x) + f(x)"],
    ["collect(P(\"exp(3*x/4)\"), P(\"exp(x)\"))", () => collect(P("exp(3*x/4)"), P("exp(x)")), "exp(3*x/4)"],
    ["collect(P(\"D**3*a/Re + aA**3*b/Re\"), [P(\"aA**3/Re\"), P(\"a\")])", () => collect(P("D**3*a/Re + aA**3*b/Re"), [P("aA**3/Re"), P("a")]), "D**3*a/Re + aA**3*b/Re"],
    ["collect(P('x + x**3 + x**4*y'), P('x**2'))", () => collect(P('x + x**3 + x**4*y'), P('x**2')), "x**4*y + x**3 + x"],
    ["collect(P('x**4*y + x**4 + x*a + x'), P('x**2'))", () => collect(P('x**4*y + x**4 + x*a + x'), P('x**2')), "a*x + x**4*(y + 1) + x"],
    ["collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)'))", () => collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)')), "sqrt(x)*(y + 1) + x*(a + 1)"],
    ["collect(P('a*x**2 + b*x**2 + a*x - b*x'), x)", () => collect(P('a*x**2 + b*x**2 + a*x - b*x'), x), "x**2*(a + b) + x*(a - b)"],
    ["collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y'))", () => collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y')), "2**(2*y)*(a + b) + 2**y"],
    ["collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)'))", () => collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)')), "(a + b)*exp(2*x)"],
    ["collect(P('x*a + x'), P('x**2'))", () => collect(P('x*a + x'), P('x**2')), "a*x + x"],
    ["collect(P('x**3*a + x**3'), P('x**2'))", () => collect(P('x**3*a + x**3'), P('x**2')), "a*x**3 + x**3"],
    ["collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)'))", () => collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)')), "x**(3/2)*(a + 1)"],
    ["collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2'))", () => collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2')), "1/x + (a + 1)/x**2"],
    ["(() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })()", () => (() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })(), "p**3*(a + 1) + p*(a + 1)"],
    ["collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)'))", () => collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)')), "2**(3*y)*a + 2**(3*y)"],
    ["collect(P('a*x*y + b*x*y + x'), P('x*y'))", () => collect(P('a*x*y + b*x*y + x'), P('x*y')), "x*y*(a + b) + x"],
    ["collect(P('a*x*y + b*x*y + x'), P('x*y'), { exact: true })", () => collect(P('a*x*y + b*x*y + x'), P('x*y'), { exact: true }), "x*y*(a + b) + x"],
    ["collect(P('a*x**2*y + b*x**2*y'), P('x*y'), { exact: true })", () => collect(P('a*x**2*y + b*x**2*y'), P('x*y'), { exact: true }), "x*y*(a*x + b*x)"],
    ["collect(P('a/x + b/x + x'), x)", () => collect(P('a/x + b/x + x'), x), "x + (a + b)/x"],
    ["collect(P('a*x**2*y + b*x**2*y + x*y'), P('x*y'))", () => collect(P('a*x**2*y + b*x**2*y + x*y'), P('x*y')), "x*y*(a*x + b*x + 1)"],
    ["collect(P('a*x + b*x + a*y + b*y'), [x, y], { exact: null })", () => collect(P('a*x + b*x + a*y + b*y'), [x, y], { exact: null }), "x*(a + b) + y*(a + b)"],
    ["collect(P('a*x*y + b*x*y + a*y + 2*y'), [x, y], { exact: null })", () => collect(P('a*x*y + b*x*y + a*y + 2*y'), [x, y], { exact: null }), "x*y*(a + b) + y*(a + 2)"],
    ["collect(P('a*x + b*x + c'), [x], { func: factor })", () => collect(P('a*x + b*x + c'), [x], { func: factor }), "c + x*(a + b)"],
    ["collect(P('a*x**2 + 2*a*x + a + x'), [x], { exact: null, func: factor })", () => collect(P('a*x**2 + 2*a*x + a + x'), [x], { exact: null, func: factor }), "a*x**2 + a + x*(2*a + 1)"],
    ["collect(P('a*x + b*x'), [])", () => collect(P('a*x + b*x'), []), "a*x + b*x"],
    ["rcollect(P('(x + a*x)*y + (x + b*x)/y'), x)", () => rcollect(P('(x + a*x)*y + (x + b*x)/y'), x), "x*(y*(a + 1) + (b + 1)/y)"],
    ["rcollect(P('sin(a*x + b*x)'), x)", () => rcollect(P('sin(a*x + b*x)'), x), "sin(x*(a + b))"],
    ["rcollect(P('a*x + b*x + y'), x, y)", () => rcollect(P('a*x + b*x + y'), x, y), "x*(a + b) + y"],
    ["rcollect(x, x)", () => rcollect(x, x), "x"],
    ["collect(P('a*x**2/y + b*x**2/y'), P('x*y'))", () => collect(P('a*x**2/y + b*x**2/y'), P('x*y')), "a*x**2/y + b*x**2/y"],
    ["collect(P('a*x**2*y**2 + b*x**2*y**2'), P('x*y'), { exact: true })", () => collect(P('a*x**2*y**2 + b*x**2*y**2'), P('x*y'), { exact: true }), "a*x**2*y**2 + b*x**2*y**2"],
    ["collect(P('a/(x*y) + b/(x*y)'), P('x*y'))", () => collect(P('a/(x*y) + b/(x*y)'), P('x*y')), "(a + b)/(x*y)"],
    ["collect(P('a*(x + 1)**y + (x + 1)**y'), pow(new Wild('w'), y))", () => collect(P('a*(x + 1)**y + (x + 1)**y'), pow(new Wild('w'), y)), "(a + 1)*(x + 1)**y"],
    ["collect(P('a*(x + 1)**y + b'), pow(new Wild('w'), z))", () => collect(P('a*(x + 1)**y + b'), pow(new Wild('w'), z)), "a*(x + 1)**y + b"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
