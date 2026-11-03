// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Sym, parse, series, symbol } from '../src';
import type { Expr } from '../src';

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
const x = symbol('x');
/** The variable argument as a symbol. */
const V = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe("series: SymPy 1.14 test_series cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("cos(x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1 - x**2/2 + x**4/24 + O(x**6)"],
    ["series(Qs(\"exp(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1 + x + x**2/2 + x**3/6 + x**4/24 + x**5/120 + O(x**6)"],
    ["series(Qs(\"exp(cos(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(cos(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "E - E*x**2/2 + E*x**4/6 + O(x**6)"],
    ["series(Qs(\"1/(x**(-2) + x**(-3))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1/(x**(-2) + x**(-3))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x**3 - x**4 + x**5 + O(x**6)"],
    ["series(Qs(\"sin(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("sin(x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x - x**3/6 + x**5/120 + O(x**6)"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("cos(x)", []), V(Qs("x", [])), Qs("0", []), 3, "+"), "1 - x**2/2 + O(x**3)"],
    ["series(Qs(\"1/x\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1/x", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1/x"],
    ["series(Qs(\"x*log(x) - x\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("x*log(x) - x", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x*(log(x) - 1)"],
    ["series(Qs(\"sqrt(a + b + c*x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(a + b + c*x)", []), V(Qs("x", [])), Qs("0", []), 1, "+"), "sqrt(a + b) + O(x)"],
    ["series(Qs(\"sqrt(a + b + c*x + c)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(a + b + c*x + c)", []), V(Qs("x", [])), Qs("0", []), 1, "+"), "sqrt(a + b + c) + O(x)"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"1\", []), 1, \"+\")", () => series(Qs("cos(x)", []), V(Qs("x", [])), Qs("1", []), 1, "+"), "cos(1) + O(x - 1, (x, 1))"],
    ["series(Qs(\"(1 - 1/(x/2 - 1/(2*x))**4)**(1/8)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 17, \"+\")", () => series(Qs("(1 - 1/(x/2 - 1/(2*x))**4)**(1/8)", []), V(Qs("x", [])), Qs("0", []), 17, "+"), "1 - 2*x**4 - 8*x**6 - 34*x**8 - 152*x**10 - 714*x**12 - 3472*x**14 - 17318*x**16 + O(x**17)"],
    ["series(Qs(\"x**a\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("x**a", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x**a"],
    ["series(Qs(\"x**(-2*a)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("x**(-2*a)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x**(-2*a)"],
    ["series(Qs(\"exp(a*log(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(a*log(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "exp(a*log(x))"],
    ["series(Qs(\"exp(x)/x**(3/2)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("exp(x)/x**(3/2)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x**(-3/2) + 1/sqrt(x) + sqrt(x)/2 + x**(3/2)/6 + x**(5/2)/24 + x**(7/2)/120 + x**(9/2)/720 + x**(11/2)/5040 + O(x**6)"],
    ["series(Qs(\"x*(x*(1 - x) + 1)/(x*(1 - x) - (1 - x)**2 + 1)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 4, \"+\")", () => series(Qs("x*(x*(1 - x) + 1)/(x*(1 - x) - (1 - x)**2 + 1)", []), V(Qs("x", [])), Qs("oo", []), 4, "+"), "-9/(32*x**3) - 3/(16*x**2) - 1/(8*x) + 1/4 + x/2 + O(x**(-4), (x, oo))"],
    ["series(Qs(\"exp(-I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("exp(-I*pi*(2*x + 1))", []), V(Qs("x", [])), Qs("0", []), 3, "+"), "-1 + 2*I*pi*x + 2*pi**2*x**2 + O(x**3)"],
    ["series(Qs(\"exp(-I*pi*(2*x + 1))*gamma(x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("exp(-I*pi*(2*x + 1))*gamma(x + 1)", []), V(Qs("x", [])), Qs("0", []), 3, "+"), "-1 + x*(EulerGamma + 2*I*pi) + x**2*(-EulerGamma**2/2 + 23*pi**2/12 - 2*EulerGamma*I*pi) + O(x**3)"],
    ["series(Qs(\"2**(-I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("2**(-I*pi*(2*x + 1))", []), V(Qs("x", [])), Qs("0", []), 2, "+"), "exp(-I*pi*log(2)) - 2*I*pi*x*exp(-I*pi*log(2))*log(2) + O(x**2)"],
    ["series(Qs(\"y**(I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("y**(I*pi*(2*x + 1))", []), V(Qs("x", [])), Qs("0", []), 2, "+"), "exp(I*pi*log(y)) + 2*I*pi*x*exp(I*pi*log(y))*log(y) + O(x**2)"],
    ["series(Qs(\"(I*y)**(I*pi*(2*x + 1))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("(I*y)**(I*pi*(2*x + 1))", []), V(Qs("x", [])), Qs("0", []), 2, "+"), "exp(I*pi*log(I*y)) + 2*I*pi*x*exp(I*pi*log(I*y))*log(I*y) + O(x**2)"],
    ["series(Qs(\"cos(x**2 + x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 5, \"+\")", () => series(Qs("cos(x**2 + x + 1)", []), V(Qs("x", [])), Qs("0", []), 5, "+"), "cos(1) - x*sin(1) + x**2*(-sin(1) - cos(1)/2) + x**3*(-cos(1) + sin(1)/6) + x**4*(-11*cos(1)/24 + sin(1)/2) + O(x**5)"],
    ["series(Qs(\"1\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"1\", []), 6, \"+\")", () => series(Qs("cos(x)", []), V(Qs("x", [])), Qs("1", []), 6, "+"), "cos(1) - (x - 1)*sin(1) - (x - 1)**2*cos(1)/2 + (x - 1)**3*sin(1)/6 + (x - 1)**4*cos(1)/24 - (x - 1)**5*sin(1)/120 + O((x - 1)**6, (x, 1))"],
    ["series(Qs(\"cos(x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("cos(x + 1)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "cos(1) - x*sin(1) - x**2*cos(1)/2 + x**3*sin(1)/6 + x**4*cos(1)/24 - x**5*sin(1)/120 + O(x**6)"],
    ["series(Qs(\"exp(x)\", []), V(Qs(\"x\", [])), Qs(\"1\", []), 3, \"-\")", () => series(Qs("exp(x)", []), V(Qs("x", [])), Qs("1", []), 3, "-"), "E - E*(1 - x) + E*(1 - x)**2/2 + O((x - 1)**3, (x, 1))"],
    ["series(Qs(\"sin(1/x)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 5, \"+\")", () => series(Qs("sin(1/x)", []), V(Qs("x", [])), Qs("oo", []), 5, "+"), "-1/(6*x**3) + 1/x + O(x**(-5), (x, oo))"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 5, \"+\")", () => series(Qs("Abs(x)", []), V(Qs("x", [])), Qs("oo", []), 5, "+"), "x"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"-oo\", []), 5, \"-\")", () => series(Qs("Abs(x)", []), V(Qs("x", [])), Qs("-oo", []), 5, "-"), "-x"],
    ["series(Qs(\"1/cos(x/log(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("1/cos(x/log(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1 + x**2/(2*log(x)**2) + 5*x**4/(24*log(x)**4) + O(x**6)"],
    ["series(Qs(\"cos(x)\", []), V(Qs(\"x\", [])), Qs(\"pi\", []), 3, \"+\")", () => series(Qs("cos(x)", []), V(Qs("x", [])), Qs("pi", []), 3, "+"), "-1 + (x - pi)**2/2 + O((x - pi)**3, (x, pi))"],
    ["series(Qs(\"(x**2 + x + 1)/(x**3 + x**2)\", []), V(Qs(\"x\", [])), Qs(\"oo\", []), 6, \"+\")", () => series(Qs("(x**2 + x + 1)/(x**3 + x**2)", []), V(Qs("x", [])), Qs("oo", []), 6, "+"), "x**(-5) - 1/x**4 + x**(-3) + 1/x + O(x**(-6), (x, oo))"],
    ["series(Qs(\"Subs(sin(x), x, y)\", []), V(Qs(\"z\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("Subs(sin(x), x, y)", []), V(Qs("z", [])), Qs("0", []), 6, "+"), "Subs(sin(x), x, y)"],
    ["series(Qs(\"sin(x*y)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("sin(x*y)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x*y - x**3*y**3/6 + x**5*y**5/120 + O(x**6)"],
    ["series(Qs(\"exp(x)\", []), V(Qs(\"x\", [])), Qs(\"10\", []), 1, \"+\")", () => series(Qs("exp(x)", []), V(Qs("x", [])), Qs("10", []), 1, "+"), "exp(10) + O(x - 10, (x, 10))"],
    ["series(Qs(\"ceiling(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"ceiling(-x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(-x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"ceiling(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(sin(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"ceiling(-sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(-sin(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"ceiling(-cos(x)) + 1\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("ceiling(-cos(x)) + 1", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "1"],
    ["series(Qs(\"ceiling(x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("ceiling(x)", []), V(Qs("x", [])), Qs("2", []), 6, "+"), "3"],
    ["series(Qs(\"ceiling(-x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("ceiling(-x)", []), V(Qs("x", [])), Qs("2", []), 6, "+"), "-2"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("Abs(x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x"],
    ["series(Qs(\"Abs(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"-\")", () => series(Qs("Abs(x)", []), V(Qs("x", [])), Qs("0", []), 6, "-"), "-x"],
    ["series(Qs(\"floor(x) + 2\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(x) + 2", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "2"],
    ["series(Qs(\"floor(x) + 2\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"-\")", () => series(Qs("floor(x) + 2", []), V(Qs("x", [])), Qs("0", []), 6, "-"), "1"],
    ["series(Qs(\"sin(x + y)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"-\")", () => series(Qs("sin(x + y)", []), V(Qs("x", [])), Qs("0", []), 6, "-"), "sin(y) + x*cos(y) - x**2*sin(y)/2 - x**3*cos(y)/6 + x**4*sin(y)/24 + x**5*cos(y)/120 + O(x**6)"],
    ["series(Qs(\"sin(x + y)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("sin(x + y)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "sin(y) + x*cos(y) - x**2*sin(y)/2 - x**3*cos(y)/6 + x**4*sin(y)/24 + x**5*cos(y)/120 + O(x**6)"],
    ["series(Qs(\"(x + 1)*log(sin(2*x)/x)\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 2, \"+\")", () => series(Qs("(x + 1)*log(sin(2*x)/x)", [symbol("x", { real: true })]), V(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 2, "+"), "log(2) + x*log(2) + O(x**2)"],
    ["series(Qs(\"exp((x + 1)*log(sin(2*x)/x))\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 2, \"+\")", () => series(Qs("exp((x + 1)*log(sin(2*x)/x))", [symbol("x", { real: true })]), V(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 2, "+"), "2 + 2*x*log(2) + O(x**2)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("exp(sin(x))", []), V(Qs("x", [])), Qs("0", []), 1, "+"), "1 + O(x)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 2, \"+\")", () => series(Qs("exp(sin(x))", []), V(Qs("x", [])), Qs("0", []), 2, "+"), "1 + x + O(x**2)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("exp(sin(x))", []), V(Qs("x", [])), Qs("0", []), 3, "+"), "1 + x + x**2/2 + O(x**3)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 4, \"+\")", () => series(Qs("exp(sin(x))", []), V(Qs("x", [])), Qs("0", []), 4, "+"), "1 + x + x**2/2 + O(x**4)"],
    ["series(Qs(\"exp(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 5, \"+\")", () => series(Qs("exp(sin(x))", []), V(Qs("x", [])), Qs("0", []), 5, "+"), "1 + x + x**2/2 - x**4/8 + O(x**5)"],
    ["series(Qs(\"floor(x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(-x)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-x)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "-1"],
    ["series(Qs(\"floor(sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(sin(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(-sin(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-sin(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "-1"],
    ["series(Qs(\"floor(x**3)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(x**3)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(-x**3)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-x**3)", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "-1"],
    ["series(Qs(\"floor(cos(x))\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(cos(x))", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "0"],
    ["series(Qs(\"floor(sin(x)) + 5\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(sin(x)) + 5", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "5"],
    ["series(Qs(\"floor(-sin(x)) + 5\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("floor(-sin(x)) + 5", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "4"],
    ["series(Qs(\"floor(x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("floor(x)", []), V(Qs("x", [])), Qs("2", []), 6, "+"), "2"],
    ["series(Qs(\"floor(-x)\", []), V(Qs(\"x\", [])), Qs(\"2\", []), 6, \"+\")", () => series(Qs("floor(-x)", []), V(Qs("x", [])), Qs("2", []), 6, "+"), "-3"],
    ["series(Qs(\"asin(a*x)/x\", []), V(Qs(\"x\", [])), Qs(\"4\", []), 2, \"+\")", () => series(Qs("asin(a*x)/x", []), V(Qs("x", [])), Qs("4", []), 2, "+"), "asin(4*a)/4 + (x - 4)*(a/(4*sqrt(1 - 16*a**2)) - asin(4*a)/16) + O((x - 4)**2, (x, 4))"],
    ["series(Qs(\"log(sin(x))\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 5, \"+\")", () => series(Qs("log(sin(x))", [symbol("x", { real: true })]), V(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 5, "+"), "log(x) - x**2/6 - x**4/180 + O(x**5)"],
    ["series(Qs(\"x*(-log(x) + log(sin(2*x))) - log(x) + log(sin(2*x))\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"0\", [symbol(\"x\", { real: true })]), 5, \"+\")", () => series(Qs("x*(-log(x) + log(sin(2*x))) - log(x) + log(sin(2*x))", [symbol("x", { real: true })]), V(Qs("x", [symbol("x", { real: true })])), Qs("0", [symbol("x", { real: true })]), 5, "+"), "log(2) + x*log(2) - 2*x**2/3 - 2*x**3/3 - 4*x**4/45 + O(x**5)"],
    ["series(Qs(\"1/(a*x + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 5, \"+\")", () => series(Qs("1/(a*x + 1)", []), V(Qs("x", [])), Qs("0", []), 5, "+"), "1 - a*x + a**2*x**2 - a**3*x**3 + a**4*x**4 + O(x**5)"],
    ["series(Qs(\"1/(x*(a + b) + 1)\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 3, \"+\")", () => series(Qs("1/(x*(a + b) + 1)", []), V(Qs("x", [])), Qs("0", []), 3, "+"), "1 + x*(-a - b) + x**2*(a + b)**2 + O(x**3)"],
    ["series(Qs(\"(x + 1)**2\", []), V(Qs(\"x\", [])), Qs(\"0\", []), 6, \"+\")", () => series(Qs("(x + 1)**2", []), V(Qs("x", [])), Qs("0", []), 6, "+"), "x**2 + 2*x + 1"],
    ["series(Qs(\"(a**2 + x**2)**(-2)\", []), V(Qs(\"x\", [])), Qs(\"I*a\", []), 0, \"+\")", () => series(Qs("(a**2 + x**2)**(-2)", []), V(Qs("x", [])), Qs("I*a", []), 0, "+"), "-I/(4*a**3*(-I*a + x)) - 1/(4*a**2*(-I*a + x)**2) + O(1, (x, I*a))"],
    ["series(Qs(\"(a**2 + x**2)**(-2)\", []), V(Qs(\"x\", [])), Qs(\"I*a\", []), 1, \"+\")", () => series(Qs("(a**2 + x**2)**(-2)", []), V(Qs("x", [])), Qs("I*a", []), 1, "+"), "3/(16*a**4) - I/(4*a**3*(-I*a + x)) - 1/(4*a**2*(-I*a + x)**2) + O(-I*a + x, (x, I*a))"],
    ["series(Qs(\"sqrt(x + z)\", []), V(Qs(\"z\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(x + z)", []), V(Qs("z", [])), Qs("0", []), 1, "+"), "sqrt(x) + O(z)"],
    ["series(Qs(\"sqrt(x + y + z)\", []), V(Qs(\"z\", [])), Qs(\"0\", []), 1, \"+\")", () => series(Qs("sqrt(x + y + z)", []), V(Qs("z", [])), Qs("0", []), 1, "+"), "sqrt(x + y) + O(z)"],
    ["series(Qs(\"(sin(2*w)/w)**(w + 1)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 1, \"+\")", () => series(Qs("(sin(2*w)/w)**(w + 1)", [symbol("w", { real: true })]), V(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 1, "+"), "2 + O(w)"],
    ["series(Qs(\"(sin(2*w)/w)**(w + 1)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 3, \"+\")", () => series(Qs("(sin(2*w)/w)**(w + 1)", [symbol("w", { real: true })]), V(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 3, "+"), "2 + 2*w*log(2) + w**2*(-4/3 + log(2)**2) + O(w**3)"],
    ["series(Qs(\"(sin(2*w)/w)**(w + 1)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 2, \"+\")", () => series(Qs("(sin(2*w)/w)**(w + 1)", [symbol("w", { real: true })]), V(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 2, "+"), "2 + 2*w*log(2) + O(w**2)"],
    ["series(Qs(\"log(sin(2*w)/w)\", [symbol(\"w\", { real: true })]), V(Qs(\"w\", [symbol(\"w\", { real: true })])), Qs(\"0\", [symbol(\"w\", { real: true })]), 5, \"+\")", () => series(Qs("log(sin(2*w)/w)", [symbol("w", { real: true })]), V(Qs("w", [symbol("w", { real: true })])), Qs("0", [symbol("w", { real: true })]), 5, "+"), "log(2) - 2*w**2/3 - 4*w**4/45 + O(w**5)"],
    ["series(P('ceiling(x)'), V(x), 0)", () => series(P('ceiling(x)'), V(x), 0), "1"],
    ["series(P('ceiling(-x)'), V(x), 0)", () => series(P('ceiling(-x)'), V(x), 0), "0"],
    ["series(P('floor(x)'), V(x), 0)", () => series(P('floor(x)'), V(x), 0), "0"],
    ["series(P('floor(-x)'), V(x), 0)", () => series(P('floor(-x)'), V(x), 0), "-1"],
    ["series(P('floor(sin(x))'), V(x), 0, 6, '-')", () => series(P('floor(sin(x))'), V(x), 0, 6, '-'), "-1"],
    ["series(P('ceiling(sin(x))'), V(x), 0)", () => series(P('ceiling(sin(x))'), V(x), 0), "1"],
    ["series(P('floor(x + 1/2)'), V(x), 0)", () => series(P('floor(x + 1/2)'), V(x), 0), "0"],
    ["series(P('floor(x + sqrt(2))'), V(x), 0)", () => series(P('floor(x + sqrt(2))'), V(x), 0), "1"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
