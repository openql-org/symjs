// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/concrete/summations.ts.

// Sums, products and their convergence. Expected values are the str() forms printed by SymPy 1.14; where P is
// parse with p a positive, q a negative and r a real symbol, Pplain is plain parse.

import { describe, expect, it } from 'vitest';
import { Concrete, Product, Sum, Sym, doit, eulerMaclaurin, isAbsolutelyConvergent, isConvergent, oo, parse, product, reverseOrder, subs, summation } from '../../src';
import * as sj from '../../src';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';

const Pplain = parse;
/** Sum / Product as Concrete nodes (the convergence tests and reverseOrder take a Concrete). */
const concExpr = (e: Expr): Concrete => {
  if (!(e instanceof Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const showStr = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y, z, n, k, a, b, c, m, t] = [V('x'), V('y'), V('z'), V('n'), V('k'), V('a'), V('b'), V('c'), V('m'), V('t')];
const [pp, qq, rr] = [V('p'), V('q'), V('r')];
const show = (v: unknown): string =>
  Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v === undefined ? 'None' : v instanceof Expr || v instanceof NoMatchResult ? v.toString() : typeof v === 'string' ? v : JSON.stringify(v);
const pw = (e: unknown): sj.Piecewise => {
  if (!(e instanceof sj.Piecewise)) throw new TypeError('a Piecewise expected');
  return e;
};
/** The result, or the class name and message of what it throws. */
const run = (f: () => unknown): string => {
  try {
    return show(f());
  } catch (e) {
    return e instanceof Error ? `ERR ${e.constructor.name}: ${e.message}` : 'ERR';
  }
};
const conc = (e: unknown): sj.Concrete => {
  if (!(e instanceof sj.Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const conv = (e: unknown) => sj.isConvergent(conc(e));
const aconv = (e: unknown) => sj.isAbsolutelyConvergent(conc(e));
const moo = P('-oo');
void [x, y, z, n, k, a, b, c, m, t, pp, qq, rr, conv, aconv, moo, pw];

describe("summations: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["summation(x, [k, 1, n])", () => summation(x, [k, 1, n]), "n*x"],
    ["summation(x, [k, 1, oo])", () => summation(x, [k, 1, oo]), "oo*x"],
    ["summation(k, [k, 5, 1])", () => summation(k, [k, 5, 1]), "-9"],
    ["summation(P('k**2'), [k, 10, 1])", () => summation(Pplain('k**2'), [k, 10, 1]), "-284"],
    ["summation(P('1/(k**2+1)'), [k, 0, oo])", () => summation(Pplain('1/(k**2+1)'), [k, 0, oo]), "1/2 + pi/(2*tanh(pi))"],
    ["summation(P('(-1)**k/(k**2+1)'), [k, 0, oo])", () => summation(Pplain('(-1)**k/(k**2+1)'), [k, 0, oo]), "pi/(2*sinh(pi)) + 1/2"],
    ["summation(P('1/(k**2+4)'), [k, 0, oo])", () => summation(Pplain('1/(k**2+4)'), [k, 0, oo]), "1/8 + pi/(4*tanh(2*pi))"],
    ["summation(P('1/(k**2+1)'), [k, 3, oo])", () => summation(Pplain('1/(k**2+1)'), [k, 3, oo]), "-6/5 + pi/(2*tanh(pi))"],
    ["summation(P('1/(k**2+1)'), [k, -2, oo])", () => summation(Pplain('1/(k**2+1)'), [k, -2, oo]), "6/5 + pi/(2*tanh(pi))"],
    ["summation(P('1/((k+1)**2+1)'), [k, 0, oo])", () => summation(Pplain('1/((k+1)**2+1)'), [k, 0, oo]), "-1/2 + pi/(2*tanh(pi))"],
    ["summation(P('1/((k-2)**2+1)'), [k, 0, oo])", () => summation(Pplain('1/((k-2)**2+1)'), [k, 0, oo]), "6/5 + pi/(2*tanh(pi))"],
    ["summation(P('(-1)**k/((k+1)**2+1)'), [k, 0, oo])", () => summation(Pplain('(-1)**k/((k+1)**2+1)'), [k, 0, oo]), "-pi/(2*sinh(pi)) + 1/2"],
    ["summation(P('1/(k**2+x)'), [k, 0, oo])", () => summation(Pplain('1/(k**2+x)'), [k, 0, oo]), "Sum(1/(k**2 + x), (k, 0, oo))"],
    ["summation(P('1/(k**3+1)'), [k, 0, oo])", () => summation(Pplain('1/(k**3+1)'), [k, 0, oo]), "Sum(1/(k**3 + 1), (k, 0, oo))"],
    ["summation(P('k/(k**3+1)'), [k, 0, oo])", () => summation(Pplain('k/(k**3+1)'), [k, 0, oo]), "Sum(k/(k**3 + 1), (k, 0, oo))"],
    ["summation(P('1/(k**2+k+1)'), [k, 0, oo])", () => summation(Pplain('1/(k**2+k+1)'), [k, 0, oo]), "Sum(1/(k**2 + k + 1), (k, 0, oo))"],
    ["summation(P('1/(k**2+2*k+2)'), [k, 0, oo])", () => summation(Pplain('1/(k**2+2*k+2)'), [k, 0, oo]), "-1/2 + pi/(2*tanh(pi))"],
    ["summation(P('1/(k**2+2*k+2)'), [k, 1, oo])", () => summation(Pplain('1/(k**2+2*k+2)'), [k, 1, oo]), "-1 + pi/(2*tanh(pi))"],
    ["summation(P('1/(k**2-2*k+2)'), [k, 5, oo])", () => summation(Pplain('1/(k**2-2*k+2)'), [k, 5, oo]), "-13/10 + pi/(2*tanh(pi))"],
    ["summation(P('(-1)**k/(k**2+2*k+2)'), [k, 0, oo])", () => summation(Pplain('(-1)**k/(k**2+2*k+2)'), [k, 0, oo]), "-pi/(2*sinh(pi)) + 1/2"],
    ["summation(P('1/(2*k**2+1)'), [k, 0, oo])", () => summation(Pplain('1/(2*k**2+1)'), [k, 0, oo]), "1/2 + sqrt(2)*pi/(4*tanh(sqrt(2)*pi/2))"],
    ["summation(P('2**(-k)'), [k, 0, oo])", () => summation(Pplain('2**(-k)'), [k, 0, oo]), "2"],
    ["summation(P('2**k'), [k, 0, oo])", () => summation(Pplain('2**k'), [k, 0, oo]), "oo"],
    ["summation(P('x**k'), [k, 0, oo])", () => summation(Pplain('x**k'), [k, 0, oo]), "Piecewise((1/(1 - x), Abs(x) < 1), (Sum(x**k, (k, 0, oo)), True))"],
    ["summation(P('3*x**k'), [k, 0, n])", () => summation(Pplain('3*x**k'), [k, 0, n]), "3*Piecewise((n + 1, Eq(x, 1)), ((1 - x**(n + 1))/(1 - x), True))"],
    ["summation(P('x**(2*k)'), [k, 1, n])", () => summation(Pplain('x**(2*k)'), [k, 1, n]), "Piecewise((n, Eq(x**2, 1)), ((x**2 - (x**2)**(n + 1))/(1 - x**2), True))"],
    ["summation(P('x**k/factorial(k)'), [k, 0, oo])", () => summation(Pplain('x**k/factorial(k)'), [k, 0, oo]), "exp(x)"],
    ["summation(P('sin(k)'), [k, 1, n])", () => summation(Pplain('sin(k)'), [k, 1, n]), "Sum(sin(k), (k, 1, n))"],
    ["summation(P('k**3+2*k'), [k, 1, n])", () => summation(Pplain('k**3+2*k'), [k, 1, n]), "n**4/4 + n**3/2 + 5*n**2/4 + n"],
    ["summation(P('x**(k**2)'), [k, 0, n])", () => summation(Pplain('x**(k**2)'), [k, 0, n]), "Sum(x**(k**2), (k, 0, n))"],
    ["summation(P('x**(1/k)'), [k, 0, n])", () => summation(Pplain('x**(1/k)'), [k, 0, n]), "Sum(x**(1/k), (k, 0, n))"],
    ["summation(P('k'), [k, 1, n], [n, 1, m])", () => summation(Pplain('k'), [k, 1, n], [n, 1, m]), "m**3/6 + m**2/2 + m/3"],
    ["product(P('k'), [k, 1, n])", () => product(Pplain('k'), [k, 1, n]), "factorial(n)"],
    ["product(P('2'), [k, 1, n])", () => product(Pplain('2'), [k, 1, n]), "2**n"],
    ["product(P('1'), [k, 1, n])", () => product(Pplain('1'), [k, 1, n]), "1"],
    ["product(P('x'), [k, a, n])", () => product(Pplain('x'), [k, a, n]), "x**(-a + n + 1)"],
    ["product(P('k'), [k, 5, 1])", () => product(Pplain('k'), [k, 5, 1]), "1/24"],
    ["product(P('k'), [k, 7, 1])", () => product(Pplain('k'), [k, 7, 1]), "1/720"],
    ["product(P('k**2'), [k, 1, n])", () => product(Pplain('k**2'), [k, 1, n]), "factorial(n)**2"],
    ["product(P('k+1'), [k, 1, n])", () => product(Pplain('k+1'), [k, 1, n]), "RisingFactorial(2, n)"],
    ["product(P('2*k'), [k, 1, n])", () => product(Pplain('2*k'), [k, 1, n]), "2**n*factorial(n)"],
    ["product(P('k*(k+1)'), [k, 1, n])", () => product(Pplain('k*(k+1)'), [k, 1, n]), "RisingFactorial(2, n)*factorial(n)"],
    ["product(P('x*k'), [k, 1, n])", () => product(Pplain('x*k'), [k, 1, n]), "x**n*factorial(n)"],
    ["product(P('k**2+1'), [k, 1, n])", () => product(Pplain('k**2+1'), [k, 1, n]), "RisingFactorial(1 - I, n)*RisingFactorial(1 + I, n)"],
    ["product(P('(k+1)**x'), [k, 1, n])", () => product(Pplain('(k+1)**x'), [k, 1, n]), "RisingFactorial(2, n)**x"],
    ["product(P('sin(k)'), [k, 1, n])", () => product(Pplain('sin(k)'), [k, 1, n]), "Product(sin(k), (k, 1, n))"],
    ["product(P('k**k'), [k, 1, n])", () => product(Pplain('k**k'), [k, 1, n]), "Product(k**k, (k, 1, n))"],
    ["product(P('k'), [k, n, n])", () => product(Pplain('k'), [k, n, n]), "n"],
    ["product(P('k**3-2'), [k, 1, n])", () => product(Pplain('k**3-2'), [k, 1, n]), "RisingFactorial(1 - 2**(1/3), n)*RisingFactorial(2**(1/3)/2 + 1 - 2**(1/3)*sqrt(3)*I/2, n)*RisingFactorial(2**(1/3)/2 + 1 + 2**(1/3)*sqrt(3)*I/2, n)"],
    ["summation(x, [k, P('-oo'), 0])", () => summation(x, [k, Pplain('-oo'), 0]), "oo*x"],
    ["summation(P('k**2'), [k, n, 1])", () => summation(Pplain('k**2'), [k, n, 1]), "-n**3/3 + n**2/2 - n/6 + 1"],
    ["summation(P('1/(k**2+1)'), [k, P('-oo'), oo])", () => summation(Pplain('1/(k**2+1)'), [k, Pplain('-oo'), oo]), "pi/tanh(pi)"],
    ["summation(P('(-1)**k/(k**2+1)'), [k, P('-oo'), oo])", () => summation(Pplain('(-1)**k/(k**2+1)'), [k, Pplain('-oo'), oo]), "pi/sinh(pi)"],
    ["summation(P('1/(k**2-1)'), [k, P('-oo'), oo])", () => summation(Pplain('1/(k**2-1)'), [k, Pplain('-oo'), oo]), "Sum(1/(k**2 - 1), (k, -oo, oo))"],
    ["summation(P('1/(k**2+1)'), [k, P('-oo'), n])", () => summation(Pplain('1/(k**2+1)'), [k, Pplain('-oo'), n]), "Sum(1/(k**2 + 1), (k, -oo, n))"],
    ["summation(P('1/(k**2+x)'), [k, P('-oo'), oo])", () => summation(Pplain('1/(k**2+x)'), [k, Pplain('-oo'), oo]), "Sum(1/(k**2 + x), (k, -oo, oo))"],
    ["summation(P('1/(k**2+1)'), [k, n, oo])", () => summation(Pplain('1/(k**2+1)'), [k, n, oo]), "Sum(1/(k**2 + 1), (k, n, oo))"],
    ["summation(P('1/((k+1)**2+1)'), [k, P('-oo'), oo])", () => summation(Pplain('1/((k+1)**2+1)'), [k, Pplain('-oo'), oo]), "-pi*(-I/(2*tan(pi*(-1 + I))) + I/(2*tan(pi*(-1 - I))))"],
    ["summation(P('1/(k**2+1)/2'), [k, 0, oo])", () => summation(Pplain('1/(k**2+1)/2'), [k, 0, oo]), "1/4 + pi/(4*tanh(pi))"],
    ["summation(P('2**(k+1)'), [k, 0, n])", () => summation(Pplain('2**(k+1)'), [k, 0, n]), "2*2**(n + 1) - 2"],
    ["summation(P('2**(k+1)'), [k, 0, oo])", () => summation(Pplain('2**(k+1)'), [k, 0, oo]), "oo"],
    ["summation(P('-2**(k+1)'), [k, 0, oo])", () => summation(Pplain('-2**(k+1)'), [k, 0, oo]), "-oo"],
    ["summation(P('2**(2*k+1)'), [k, 0, n])", () => summation(Pplain('2**(2*k+1)'), [k, 0, n]), "2*4**(n + 1)/3 - 2/3"],
    ["summation(P('x**k'), [k, a, n])", () => summation(Pplain('x**k'), [k, a, n]), "Piecewise((-a + n + 1, Eq(x, 1)), ((x**a - x**(n + 1))/(1 - x), True))"],
    ["summation(P('x**k'), [k, 0, n])", () => summation(Pplain('x**k'), [k, 0, n]), "Piecewise((n + 1, Eq(x, 1)), ((1 - x**(n + 1))/(1 - x), True))"],
    ["summation(P('sqrt(2)**k'), [k, 0, n])", () => summation(Pplain('sqrt(2)**k'), [k, 0, n]), "(1 - 2**(n/2 + 1/2))/(1 - sqrt(2))"],
    ["summation(P('(-1)**k'), [k, 0, n])", () => summation(Pplain('(-1)**k'), [k, 0, n]), "1/2 - (-1)**(n + 1)/2"],
    ["summation(P('0'), [k, 1, oo])", () => summation(Pplain('0'), [k, 1, oo]), "0"],
    ["summation(P('-2'), [k, 1, oo])", () => summation(Pplain('-2'), [k, 1, oo]), "-oo"],
    ["summation(P('1/(k**5+k+1)'), [k, 0, oo])", () => summation(Pplain('1/(k**5+k+1)'), [k, 0, oo]), "Sum(1/(k**5 + k + 1), (k, 0, oo))"],
    ["summation(P('1/(k**2+sqrt(2)*k+1)'), [k, 0, oo])", () => summation(Pplain('1/(k**2+sqrt(2)*k+1)'), [k, 0, oo]), "Sum(1/(k**2 + sqrt(2)*k + 1), (k, 0, oo))"],
    ["summation(P('1/(k**3+k)'), [k, 1, oo])", () => summation(Pplain('1/(k**3+k)'), [k, 1, oo]), "Sum(1/(k**3 + k), (k, 1, oo))"],
    ["summation(P('1/((k-1)*(k-3)+5)'), [k, 0, oo])", () => summation(Pplain('1/((k-1)*(k-3)+5)'), [k, 0, oo]), "9/20 + pi/(4*tanh(2*pi))"],
    ["summation(P('1/(k**2+3)'), [k, -3, oo])", () => summation(Pplain('1/(k**2+3)'), [k, -3, oo]), "9/14 + sqrt(3)*pi/(6*tanh(sqrt(3)*pi))"],
    ["summation(P('1/(k**2+4)'), [k, 0, n])", () => summation(Pplain('1/(k**2+4)'), [k, 0, n]), "Sum(1/(k**2 + 4), (k, 0, n))"],
    ["summation(P('2**k/factorial(k)'), [k, 0, oo])", () => summation(Pplain('2**k/factorial(k)'), [k, 0, oo]), "exp(2)"],
    ["summation(P('(-1)**k/(2*k**2+1)'), [k, 0, oo])", () => summation(Pplain('(-1)**k/(2*k**2+1)'), [k, 0, oo]), "sqrt(2)*pi/(4*sinh(sqrt(2)*pi/2)) + 1/2"],
    ["summation(P('exp(k)'), [k, 0, n])", () => summation(Pplain('exp(k)'), [k, 0, n]), "(1 - exp(n + 1))/(1 - E)"],
    ["summation(P('exp(-k)'), [k, 0, oo])", () => summation(Pplain('exp(-k)'), [k, 0, oo]), "1/(1 - exp(-1))"],
    ["summation(P('exp(I*k)'), [k, 0, oo])", () => summation(Pplain('exp(I*k)'), [k, 0, oo]), "Sum(exp(I*k), (k, 0, oo))"],
    ["product(P('k**5+k+1'), [k, 1, n])", () => product(Pplain('k**5+k+1'), [k, 1, n]), "RisingFactorial(3/2 - sqrt(3)*I/2, n)*RisingFactorial(3/2 + sqrt(3)*I/2, n)*RisingFactorial(2/3 + (-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3 + 1/(3*(-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)), n)*RisingFactorial(2/3 + 1/(3*(-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3, n)*RisingFactorial(1/(3*(3*sqrt(69)/2 + 25/2)**(1/3)) + 2/3 + (3*sqrt(69)/2 + 25/2)**(1/3)/3, n)"],
    ["product(P('x**(k+1)'), [k, 1, n])", () => product(Pplain('x**(k+1)'), [k, 1, n]), "x**(n**2/2 + 3*n/2)"],
    ["product(P('sin(k)**2'), [k, 1, n])", () => product(Pplain('sin(k)**2'), [k, 1, n]), "Product(sin(k)**2, (k, 1, n))"],
    ["product(P('(k+1)**2*x'), [k, 1, n])", () => product(Pplain('(k+1)**2*x'), [k, 1, n]), "x**n*RisingFactorial(2, n)**2"],
    ["product(P('3*k'), [k, 1, 3])", () => product(Pplain('3*k'), [k, 1, 3]), "162"],
    ["product(P('1/k'), [k, 1, n])", () => product(Pplain('1/k'), [k, 1, n]), "1/factorial(n)"],
    ["product(P('k'), [k, 1, 0])", () => product(Pplain('k'), [k, 1, 0]), "1"],
    ["product(P('2'), [k, a, n])", () => product(Pplain('2'), [k, a, n]), "2**(-a + n + 1)"],
    ["product(P('k**2+k+1'), [k, a, n])", () => product(Pplain('k**2+k+1'), [k, a, n]), "RisingFactorial(a + 1/2 - sqrt(3)*I/2, -a + n + 1)*RisingFactorial(a + 1/2 + sqrt(3)*I/2, -a + n + 1)"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/k**2'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/k'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/k'), [k, 1, 10])))", () => isConvergent(concExpr(Sum(Pplain('1/k'), [k, 1, 10]))), "true"],
    ["isConvergent(conc(Sum(P('1/k'), [k, P('-oo'), -1])))", () => isConvergent(concExpr(Sum(Pplain('1/k'), [k, Pplain('-oo'), -1]))), "false"],
    ["isConvergent(conc(Sum(P('k'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('k**(-3/2)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('k**(-3/2)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/sqrt(k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/sqrt(k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2+1)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('k/(k**2+1)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('k/(k**2+1)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/k**2/2'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/k**2/2'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('2**(-k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('2**(-k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/factorial(k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/factorial(k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('factorial(k)/10**k'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('factorial(k)/10**k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('k**3/2**k'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('k**3/2**k'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/k'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k/k'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/sqrt(k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k/sqrt(k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k*k'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k*k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('sin(1/k**2)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('sin(1/k**2)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('sin(1/k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('sin(1/k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('exp(-k**2)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('exp(-k**2)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2-I)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2-I)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/log(k)'), [k, 2, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k/log(k)'), [k, 2, oo]))), "true"],
    ["isConvergent(conc(Product(P('1+1/k**2'), [k, 1, oo])))", () => isConvergent(concExpr(Product(Pplain('1+1/k**2'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Product(P('1+1/k'), [k, 1, oo])))", () => isConvergent(concExpr(Product(Pplain('1+1/k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Product(P('k'), [k, 1, oo])))", () => isConvergent(concExpr(Product(Pplain('k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Product(P('2'), [k, 1, oo])))", () => isConvergent(concExpr(Product(Pplain('2'), [k, 1, oo]))), "false"],
    ["isAbsolutelyConvergent(conc(Sum(P('(-1)**k/k'), [k, 1, oo])))", () => isAbsolutelyConvergent(concExpr(Sum(Pplain('(-1)**k/k'), [k, 1, oo]))), "false"],
    ["isAbsolutelyConvergent(conc(Sum(P('(-1)**k/k**2'), [k, 1, oo])))", () => isAbsolutelyConvergent(concExpr(Sum(Pplain('(-1)**k/k**2'), [k, 1, oo]))), "true"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 1, n])))", () => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, 1, n]))), "[n**2/2 + n/2, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k**2'), [k, 1, n])), 0, 2)", () => eulerMaclaurin(concExpr(Sum(Pplain('k**2'), [k, 1, n])), 0, 2), "[n**3/3 + n**2/2 + n/6, 0]"],
    ["eulerMaclaurin(conc(Sum(P('1/k**2'), [k, 1, oo])), 2, 2)", () => eulerMaclaurin(concExpr(Sum(Pplain('1/k**2'), [k, 1, oo])), 2, 2), "[23983/14580, 1/91854]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 1, 3])), 5)", () => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, 1, 3])), 5), "[6, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 1, 10])), 3)", () => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, 1, 10])), 3), "[55, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 5, 1])))", () => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, 5, 1]))), "[-9, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 5, 4])))", () => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, 5, 4]))), "[0, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, n, m])), 2)", () => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, n, m])), 2), "[m**2/2 + m/2 + 5*n/2 - (n + 2)**2/2 + 2, 0]"],
    ["reverseOrder(conc(Sum(P('k'), [k, 1, n])), 0)", () => reverseOrder(concExpr(Sum(Pplain('k'), [k, 1, n])), 0), "Sum(-k, (k, n + 1, 0))"],
    ["reverseOrder(conc(Sum(P('k*x'), [k, 1, n], [x, 2, 5])), x)", () => reverseOrder(concExpr(Sum(Pplain('k*x'), [k, 1, n], [x, 2, 5])), x), "Sum(-k*x, (k, 1, n), (x, 6, 1))"],
    ["reverseOrder(conc(Product(P('k'), [k, 1, n])), k)", () => reverseOrder(concExpr(Product(Pplain('k'), [k, 1, n])), k), "Product(1/k, (k, n + 1, 0))"],
    ["reverseOrder(conc(Product(P('k'), [k, 1, n])), 0, 0)", () => reverseOrder(concExpr(Product(Pplain('k'), [k, 1, n])), 0, 0), "Product(1/k, (k, n + 1, 0))"],
    ["doit(Sum(P('k'), [k, 1, n]))", () => doit(Sum(Pplain('k'), [k, 1, n])), "n**2/2 + n/2"],
    ["doit(Product(P('k'), [k, 1, 4]))", () => doit(Product(Pplain('k'), [k, 1, 4])), "24"],
    ["product(P('k'), [k, 1, oo])", () => product(Pplain('k'), [k, 1, oo]), "Product(k, (k, 1, oo))"],
    ["product(P('1-1/k**2'), [k, 2, oo])", () => product(Pplain('1-1/k**2'), [k, 2, oo]), "Product(1 - 1/k**2, (k, 2, oo))"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, P('-oo'), -1])))", () => isConvergent(concExpr(Sum(Pplain('1/k**2'), [k, Pplain('-oo'), -1]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, P('-oo'), oo])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2+1)'), [k, Pplain('-oo'), oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, P('-oo')])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2+1)'), [k, 1, Pplain('-oo')]))), "true"],
    ["isConvergent(conc(Sum(P('k/(k**2+1)'), [k, P('-oo'), oo])))", () => isConvergent(concExpr(Sum(Pplain('k/(k**2+1)'), [k, Pplain('-oo'), oo]))), "false"],
    ["isConvergent(conc(Sum(P('2**k'), [k, P('-oo'), 0])))", () => isConvergent(concExpr(Sum(Pplain('2**k'), [k, Pplain('-oo'), 0]))), "true"],
    ["isConvergent(conc(Product(P('exp(1/k**2)'), [k, 1, oo])))", () => isConvergent(concExpr(Product(Pplain('exp(1/k**2)'), [k, 1, oo]))), "true"],
    ["summation(P('sin(k)'), [k, P('n+5'), n])", () => summation(Pplain('sin(k)'), [k, Pplain('n+5'), n]), "-sin(n + 1) - sin(n + 2) - sin(n + 3) - sin(n + 4)"],
    ["product(P('sin(k)'), [k, P('n+5'), n])", () => product(Pplain('sin(k)'), [k, Pplain('n+5'), n]), "1/(sin(n + 1)*sin(n + 2)*sin(n + 3)*sin(n + 4))"],
    ["summation(P('(-2)**k'), [k, 0, oo])", () => summation(Pplain('(-2)**k'), [k, 0, oo]), "Sum((-2)**k, (k, 0, oo))"],
    ["summation(P('(-1)**k*k/(k**2+1)'), [k, 0, oo])", () => summation(Pplain('(-1)**k*k/(k**2+1)'), [k, 0, oo]), "Sum((-1)**k*k/(k**2 + 1), (k, 0, oo))"],
    ["summation(P('k/(k**5-5*k**3+4*k)'), [k, 3, oo])", () => summation(Pplain('k/(k**5-5*k**3+4*k)'), [k, 3, oo]), "5/144"],
    ["summation(P('k/(k**5-5*k**3+4*k)'), [k, 4, oo])", () => summation(Pplain('k/(k**5-5*k**3+4*k)'), [k, 4, oo]), "7/720"],
    ["summation(P('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 3, oo])", () => summation(Pplain('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 3, oo]), "-1/48"],
    ["summation(P('(-1)**k/(k**2+2*k+2)'), [k, P('-oo'), oo])", () => summation(Pplain('(-1)**k/(k**2+2*k+2)'), [k, Pplain('-oo'), oo]), "-pi*(I/(2*sin(pi*(-1 - I))) - I/(2*sin(pi*(-1 + I))))"],
    ["summation(P('(-1)**k/(k**2+2*k+2)'), [k, 3, oo])", () => summation(Pplain('(-1)**k/(k**2+2*k+2)'), [k, 3, oo]), "-pi/(2*sinh(pi)) + 1/10"],
    ["summation(P('1/(k**2+k+1)**2'), [k, 0, oo])", () => summation(Pplain('1/(k**2+k+1)**2'), [k, 0, oo]), "Sum((k**2 + k + 1)**(-2), (k, 0, oo))"],
    ["summation(P('1/(k**4+2*k**3+k**2+1)'), [k, 0, oo])", () => summation(Pplain('1/(k**4+2*k**3+k**2+1)'), [k, 0, oo]), "Sum(1/(k**4 + 2*k**3 + k**2 + 1), (k, 0, oo))"],
    ["summation(P('1/(k**3+3*k**2+3*k+2)'), [k, 0, oo])", () => summation(Pplain('1/(k**3+3*k**2+3*k+2)'), [k, 0, oo]), "Sum(1/(k**3 + 3*k**2 + 3*k + 2), (k, 0, oo))"],
    ["summation(P('1/(k**2+1)'), [k, P('1/2'), oo])", () => summation(Pplain('1/(k**2+1)'), [k, Pplain('1/2'), oo]), "Sum(1/(k**2 + 1), (k, 1/2, oo))"],
    ["product(P('k**3+k+1'), [k, 1, n])", () => product(Pplain('k**3+k+1'), [k, 1, n]), "RisingFactorial(1 + (-1/2 - sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)/3 - 1/((-1/2 - sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)), n)*RisingFactorial(1 - 1/((-1/2 + sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)/3, n)*RisingFactorial(-1/(27/2 + 3*sqrt(93)/2)**(1/3) + 1 + (27/2 + 3*sqrt(93)/2)**(1/3)/3, n)"],
    ["product(P('k*(k**5+k+1)'), [k, 1, n])", () => product(Pplain('k*(k**5+k+1)'), [k, 1, n]), "RisingFactorial(3/2 - sqrt(3)*I/2, n)*RisingFactorial(3/2 + sqrt(3)*I/2, n)*RisingFactorial(2/3 + (-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3 + 1/(3*(-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)), n)*RisingFactorial(2/3 + 1/(3*(-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3, n)*RisingFactorial(1/(3*(3*sqrt(69)/2 + 25/2)**(1/3)) + 2/3 + (3*sqrt(69)/2 + 25/2)**(1/3)/3, n)*factorial(n)"],
    ["product(P('k**x'), [k, 1, n])", () => product(Pplain('k**x'), [k, 1, n]), "factorial(n)**x"],
    ["product(P('(k**5+k+1)**2'), [k, 1, n])", () => product(Pplain('(k**5+k+1)**2'), [k, 1, n]), "RisingFactorial(3/2 - sqrt(3)*I/2, n)**2*RisingFactorial(3/2 + sqrt(3)*I/2, n)**2*RisingFactorial(2/3 + (-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3 + 1/(3*(-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)), n)**2*RisingFactorial(2/3 + 1/(3*(-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3, n)**2*RisingFactorial(1/(3*(3*sqrt(69)/2 + 25/2)**(1/3)) + 2/3 + (3*sqrt(69)/2 + 25/2)**(1/3)/3, n)**2"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, 1, n])))", () => isConvergent(concExpr(Sum(Pplain('1/k**2'), [k, 1, n]))), "true"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, n, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/k**2'), [k, n, oo]))), "true"],
    ["isConvergent(conc(Sum(P('exp(-k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('exp(-k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(3/2)**k/k**4'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(3/2)**k/k**4'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('(-1)**k*log(k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k*log(k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('(-1)**k*(1+1/k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k*(1+1/k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, P('-oo'), 5])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2+1)'), [k, Pplain('-oo'), 5]))), "true"],
    ["isConvergent(conc(Sum(P('2**k'), [k, P('-oo'), oo])))", () => isConvergent(concExpr(Sum(Pplain('2**k'), [k, Pplain('-oo'), oo]))), "false"],
    ["eulerMaclaurin(conc(Sum(P('k**3'), [k, 1, n])), 0, 3)", () => eulerMaclaurin(concExpr(Sum(Pplain('k**3'), [k, 1, n])), 0, 3), "[n**4/4 + n**3/2 + n**2/4, 0]"],
    ["summation(P('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 5, oo])", () => summation(Pplain('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 5, oo]), "-1/720"],
    ["summation(P('1/(k*(k**2+1))'), [k, 1, oo])", () => summation(Pplain('1/(k*(k**2+1))'), [k, 1, oo]), "Sum(1/(k*(k**2 + 1)), (k, 1, oo))"],
    ["summation(P('2**k'), [k, P('-oo'), 0])", () => summation(Pplain('2**k'), [k, Pplain('-oo'), 0]), "2"],
    ["summation(P('x**k'), [k, P('-oo'), oo])", () => summation(Pplain('x**k'), [k, Pplain('-oo'), oo]), "Sum(x**k, (k, -oo, oo))"],
    ["summation(P('1/(k**2+1)**2'), [k, P('-oo'), oo])", () => summation(Pplain('1/(k**2+1)**2'), [k, Pplain('-oo'), oo]), "Sum((k**2 + 1)**(-2), (k, -oo, oo))"],
    ["summation(P('1/(k**4-1)'), [k, P('-oo'), oo])", () => summation(Pplain('1/(k**4-1)'), [k, Pplain('-oo'), oo]), "Sum(1/(k**4 - 1), (k, -oo, oo))"],
    ["product(P('k*sin(k)'), [k, 1, 3])", () => product(Pplain('k*sin(k)'), [k, 1, 3]), "6*sin(1)*sin(2)*sin(3)"],
    ["product(P('x**k'), [k, 1, n])", () => product(Pplain('x**k'), [k, 1, n]), "x**(n**2/2 + n/2)"],
    ["product(P('(k*x)**k'), [k, 1, n])", () => product(Pplain('(k*x)**k'), [k, 1, n]), "Product((k*x)**k, (k, 1, n))"],
    ["product(P('sin(k)**k'), [k, 1, n])", () => product(Pplain('sin(k)**k'), [k, 1, n]), "Product(sin(k)**k, (k, 1, n))"],
    ["product(P('1/(k**2+1)'), [k, 1, n])", () => product(Pplain('1/(k**2+1)'), [k, 1, n]), "1/(RisingFactorial(1 - I, n)*RisingFactorial(1 + I, n))"],
    ["product(P('2**k'), [k, a, n])", () => product(Pplain('2**k'), [k, a, n]), "2**(-a**2/2 + a/2 + n**2/2 + n/2)"],
    ["product(P('0'), [k, 1, n])", () => product(Pplain('0'), [k, 1, n]), "0**n"],
    ["summation(P('2**k*3**k'), [k, 1, n])", () => summation(Pplain('2**k*3**k'), [k, 1, n]), "6**(n + 1)/5 - 6/5"],
    ["summation(P('2**(k**2)'), [k, 1, n])", () => summation(Pplain('2**(k**2)'), [k, 1, n]), "Sum(2**(k**2), (k, 1, n))"],
    ["summation(P('x**k*factorial(k)'), [k, 0, oo])", () => summation(Pplain('x**k*factorial(k)'), [k, 0, oo]), "Sum(x**k*factorial(k), (k, 0, oo))"],
    ["summation(P('1/(k**2+1)'), [k, 0, n])", () => summation(Pplain('1/(k**2+1)'), [k, 0, n]), "Sum(1/(k**2 + 1), (k, 0, n))"],
    ["summation(P('1/(k**2+1)'), [k, 1, oo], [x, 0, 1])", () => summation(Pplain('1/(k**2+1)'), [k, 1, oo], [x, 0, 1]), "-1 + pi/tanh(pi)"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, oo], [x, 1, 2])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2+1)'), [k, 1, oo], [x, 1, 2]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2+I*k)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('1/(k**2+I*k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/k**(1/3)'), [k, 1, oo])))", () => isConvergent(concExpr(Sum(Pplain('(-1)**k/k**(1/3)'), [k, 1, oo]))), "true"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showStr(run())).toBe(want);
  });
});

// Values SymPy prints in another (equal) closed form: compared numerically with N() of SymPy's result.
describe('summations: values equal SymPy 1.14 numerically', () => {
  const near = (e: Expr, want: number) => {
    const v = e.toComplex();
    expect(v.re).toBeCloseTo(want, 12);
    expect(Math.abs(v.im)).toBeLessThan(1e-12);
  };
  it('residue sums with complex poles', () => {
    near(summation(Pplain('1/(k**4+4)'), [k, Pplain('-oo'), oo]), 0.788337023734291);
    near(summation(Pplain('1/(k**4+1)'), [k, 0, oo]), 1.57847757966714);
    near(summation(Pplain('1/((k**2+1)*(k**2+4))'), [k, 0, oo]), 0.388756802049155);
    near(summation(Pplain('1/(k**4+1)'), [k, 3, oo]), 0.0196540502553721);
  });
  it('a product whose exponent SymPy factors', () => {
    // SymPy: 2**(n*(n + 1)/2)
    const e = product(Pplain('2**k'), [k, 1, n]);
    expect(subs(e, [[n, 5]]).toString()).toBe('32768');
  });
});

describe('summations: ranges ending at -oo', () => {
  it('follows the Karr convention', () => {
    // SymPy 1.14 gives summation(2**k, (k, 0, -3)) = -3/4 (Karr: -sum_{k=-2}^{-1}) but
    // summation(2**k, (k, 0, -oo)) = 1 = +sum_{k=-oo}^{-1}, contradicting its own convention;
    // the consistent value is -summation(2**k, (k, -oo, -1)) = -1.
    expect(summation(Pplain('2**k'), [k, 0, -3]).toString()).toBe('-3/4');
    expect(summation(Pplain('2**k'), [k, 0, Pplain('-oo')]).toString()).toBe('-1');
  });
  it('mirrors a sum from -oo', () => {
    // SymPy leaves Sum(1/(k**2 + 1), (k, -oo, 0)) unevaluated; it equals SymPy's
    // summation(1/(k**2 + 1), (k, 0, oo)) = 1/2 + pi/(2*tanh(pi))
    expect(summation(Pplain('1/(k**2+1)'), [k, Pplain('-oo'), 0]).toString()).toBe('1/2 + pi/(2*tanh(pi))');
  });
});

describe('summations: convergence where SymPy 1.14 raises', () => {
  it('decides series SymPy cannot handle', () => {
    // SymPy raises NotImplementedError (I counts as a second symbol); |f| ~ 1/k**2
    expect(String(isConvergent(concExpr(Sum(Pplain('1/(k**2-I)'), [k, 1, oo]))))).toBe('true');
    expect(String(isConvergent(concExpr(Sum(Pplain('1/(k**2+I*k)'), [k, 1, oo]))))).toBe('true');
    // SymPy raises ValueError; absolutely convergent (|f| <= 1/k**2)
    expect(String(isConvergent(concExpr(Sum(Pplain('(-1)**k*sin(k)/k**2'), [k, 1, oo]))))).toBe('true');
    // SymPy raises ValueError; alternating with sin(1/k) decreasing to 0
    expect(String(isConvergent(concExpr(Sum(Pplain('(-1)**k*sin(1/k)'), [k, 1, oo]))))).toBe('true');
    // SymPy raises NotImplementedError: the answer depends on x
    expect(String(isConvergent(concExpr(Sum(Pplain('x**k'), [k, 1, oo]))))).toBe('unknown');
  });
});

describe('summations: errors', () => {
  it('eulerMaclaurin needs a single limit (SymPy raises ValueError)', () => {
    expect(() => eulerMaclaurin(concExpr(Sum(Pplain('k'), [k, 1, n], [n, 1, 3])))).toThrow(TypeError);
  });
});

describe('results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["sj.summation(P('g(2)**k'), [k, 0, sj.oo])", () => sj.summation(P('g(2)**k'), [k, 0, sj.oo]), "Piecewise((1/(1 - g(2)), Abs(g(2)) < 1), (Sum(g(2)**k, (k, 0, oo)), True))"],
    ["conv(sj.Sum(P('log(k)/k**2'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('log(k)/k**2'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('(-1)**k/k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k/k'), [k, 1, sj.oo])), "true"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // poles at k = 0 and 1 inside the range (SymPy: zoo)
    ["sj.summation(P('k/(k**3 - k)'), [k, 0, sj.oo])", () => sj.summation(P('k/(k**3 - k)'), [k, 0, sj.oo]), "Sum(k/(k**3 - k), (k, 0, oo))", "zoo"],
    // comparison with 1/(n*log(log(n))) is not implemented
    ["conv(sj.Sum(P('1/(k*log(log(k)))'), [k, 3, sj.oo]))", () => conv(sj.Sum(P('1/(k*log(log(k)))'), [k, 3, sj.oo])), "unknown", "false"],
    // SymPy raises ValueError
    ["conv(sj.Sum(P('(-1)**k*sin(k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k*sin(k)'), [k, 1, sj.oo])), "unknown", "ERR ValueError"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["sj.summation(P('sin(k)'), [k, 200, 1]).toString().length", () => sj.summation(P('sin(k)'), [k, 200, 1]).toString().length, "2070"],
    ["sj.summation(P('sin(k)'), [k, 1, 150]).toString().length", () => sj.summation(P('sin(k)'), [k, 1, 150]).toString().length, "1539"],
    ["sj.summation(P('k**2'), [k, 1, 500])", () => sj.summation(P('k**2'), [k, 1, 500]), "41791750"],
    ["sj.summation(P('1/k'), [k, 1, 120])", () => sj.summation(P('1/k'), [k, 1, 120]), "18661952910524692834612799443020757786224277983797/3475956553913558034594585593659201286533187398464"],
    ["sj.summation(P('sin(k)'), [k, 0, moo])", () => sj.summation(P('sin(k)'), [k, 0, moo]), "Sum(sin(k), (k, 0, -oo))"],
    ["sj.summation(P('1/k**2'), [k, moo, -1])", () => sj.summation(P('1/k**2'), [k, moo, -1]), "pi**2/6"],
    ["sj.summation(P('1/(k**2+1)'), [k, moo, sj.oo])", () => sj.summation(P('1/(k**2+1)'), [k, moo, sj.oo]), "pi/tanh(pi)"],
    ["sj.summation(P('(-1)**k/(k**2+1)'), [k, moo, sj.oo])", () => sj.summation(P('(-1)**k/(k**2+1)'), [k, moo, sj.oo]), "pi/sinh(pi)"],
    ["sj.summation(P('1/((k+1/2)**2+1)'), [k, 0, sj.oo])", () => sj.summation(P('1/((k+1/2)**2+1)'), [k, 0, sj.oo]), "Sum(1/((k + 1/2)**2 + 1), (k, 0, oo))"],
    ["sj.summation(P('1/(k**2+2*k+2)'), [k, x, sj.oo])", () => sj.summation(P('1/(k**2+2*k+2)'), [k, x, sj.oo]), "Sum(1/(k**2 + 2*k + 2), (k, x, oo))"],
    ["sj.summation(P('(-1)**k/(k**2+2*k+2)'), [k, 0, sj.oo])", () => sj.summation(P('(-1)**k/(k**2+2*k+2)'), [k, 0, sj.oo]), "-pi/(2*sinh(pi)) + 1/2"],
    ["sj.summation(P('k/(k**4+1)'), [k, 0, sj.oo])", () => sj.summation(P('k/(k**4+1)'), [k, 0, sj.oo]), "Sum(k/(k**4 + 1), (k, 0, oo))"],
    ["sj.summation(P('x**k'), [k, 0, sj.oo])", () => sj.summation(P('x**k'), [k, 0, sj.oo]), "Piecewise((1/(1 - x), Abs(x) < 1), (Sum(x**k, (k, 0, oo)), True))"],
    ["sj.summation(P('2**k'), [k, 0, sj.oo])", () => sj.summation(P('2**k'), [k, 0, sj.oo]), "oo"],
    ["sj.summation(P('(-2)**k'), [k, 0, sj.oo])", () => sj.summation(P('(-2)**k'), [k, 0, sj.oo]), "Sum((-2)**k, (k, 0, oo))"],
    ["sj.summation(P('-2**k'), [k, 0, sj.oo])", () => sj.summation(P('-2**k'), [k, 0, sj.oo]), "-oo"],
    ["sj.summation(P('(1/2)**k'), [k, 0, sj.oo])", () => sj.summation(P('(1/2)**k'), [k, 0, sj.oo]), "2"],
    ["sj.summation(P('I**k'), [k, 0, sj.oo])", () => sj.summation(P('I**k'), [k, 0, sj.oo]), "Sum(I**k, (k, 0, oo))"],
    ["sj.summation(P('0*2**k'), [k, 0, sj.oo])", () => sj.summation(P('0*2**k'), [k, 0, sj.oo]), "0"],
    ["sj.summation(P('x**k/factorial(k)'), [k, 0, sj.oo])", () => sj.summation(P('x**k/factorial(k)'), [k, 0, sj.oo]), "exp(x)"],
    ["sj.summation(P('2**k'), [k, 0, n])", () => sj.summation(P('2**k'), [k, 0, n]), "2**(n + 1) - 1"],
    ["sj.summation(P('x**k'), [k, 0, n])", () => sj.summation(P('x**k'), [k, 0, n]), "Piecewise((n + 1, Eq(x, 1)), ((1 - x**(n + 1))/(1 - x), True))"],
    ["sj.summation(P('3*2**(2*k+1)'), [k, 1, n])", () => sj.summation(P('3*2**(2*k+1)'), [k, 1, n]), "2*4**(n + 1) - 8"],
    ["sj.summation(P('x'), [k, moo, 3])", () => sj.summation(P('x'), [k, moo, 3]), "oo*x"],
    ["sj.summation(P('sin(k)'), [k, 0, n])", () => sj.summation(P('sin(k)'), [k, 0, n]), "Sum(sin(k), (k, 0, n))"],
    ["sj.product(P('sin(k)'), [k, 200, 1]).toString().length", () => sj.product(P('sin(k)'), [k, 200, 1]).toString().length, "1679"],
    ["sj.product(P('k'), [k, 1, 120])", () => sj.product(P('k'), [k, 1, 120]), "6689502913449127057588118054090372586752746333138029810295671352301633557244962989366874165271984981308157637893214090552534408589408121859898481114389650005964960521256960000000000000000000000000000"],
    ["sj.product(P('k**5-k-1'), [k, 1, n])", () => sj.product(P('k**5-k-1'), [k, 1, n]), "Product(k**5 - k - 1, (k, 1, n))"],
    ["sj.product(P('k*sin(k)'), [k, 1, n])", () => sj.product(P('k*sin(k)'), [k, 1, n]), "factorial(n)*Product(sin(k), (k, 1, n))"],
    ["sj.product(P('x*sin(k)'), [k, 1, n])", () => sj.product(P('x*sin(k)'), [k, 1, n]), "x**n*Product(sin(k), (k, 1, n))"],
    ["sj.product(P('sin(k)*cos(k)'), [k, 1, n])", () => sj.product(P('sin(k)*cos(k)'), [k, 1, n]), "Product(sin(k)*cos(k), (k, 1, n))"],
    ["sj.product(P('k**2'), [k, 1, n])", () => sj.product(P('k**2'), [k, 1, n]), "factorial(n)**2"],
    ["sj.product(P('(k+1)**(1/2)'), [k, 1, n])", () => sj.product(P('(k+1)**(1/2)'), [k, 1, n]), "sqrt(RisingFactorial(2, n))"],
    ["sj.product(P('sin(k)**2'), [k, 1, n])", () => sj.product(P('sin(k)**2'), [k, 1, n]), "Product(sin(k)**2, (k, 1, n))"],
    ["sj.product(P('k**k'), [k, 1, n])", () => sj.product(P('k**k'), [k, 1, n]), "Product(k**k, (k, 1, n))"],
    ["sj.product(P('x'), [k, 1, n])", () => sj.product(P('x'), [k, 1, n]), "x**n"],
    ["sj.product(P('1'), [k, 1, n])", () => sj.product(P('1'), [k, 1, n]), "1"],
    ["sj.reverseOrder(conc(sj.Sum(P('x*y'), [x, 1, 3], [y, 2, 4])), x, y)", () => sj.reverseOrder(conc(sj.Sum(P('x*y'), [x, 1, 3], [y, 2, 4])), x, y), "Sum(x*y, (x, 4, 0), (y, 5, 1))"],
    ["sj.reverseOrder(conc(sj.Product(P('x*y'), [x, 1, 3], [y, 2, 4])), 0, 1)", () => sj.reverseOrder(conc(sj.Product(P('x*y'), [x, 1, 3], [y, 2, 4])), 0, 1), "Product(x*y, (x, 4, 0), (y, 5, 1))"],
    ["sj.reverseOrder(conc(sj.Product(P('x'), [x, 1, 3])), 0)", () => sj.reverseOrder(conc(sj.Product(P('x'), [x, 1, 3])), 0), "Product(1/x, (x, 4, 0))"],
    ["conv(sj.Sum(P('I*sin(1/k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('I*sin(1/k)'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('(-1)**k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('(-1)**k*k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k*k'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('1/k**2'), [k, sj.oo, 5]))", () => conv(sj.Sum(P('1/k**2'), [k, sj.oo, 5])), "true"],
    ["conv(sj.Sum(P('1/k'), [k, sj.oo, 5]))", () => conv(sj.Sum(P('1/k'), [k, sj.oo, 5])), "false"],
    ["conv(sj.Product(P('1+1/k'), [k, 1, sj.oo]))", () => conv(sj.Product(P('1+1/k'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Product(P('1+1/k**2'), [k, 1, sj.oo]))", () => conv(sj.Product(P('1+1/k**2'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Product(P('2'), [k, 1, sj.oo]))", () => conv(sj.Product(P('2'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('1/k**2'), [k, moo, sj.oo]))", () => conv(sj.Sum(P('1/k**2'), [k, moo, sj.oo])), "true"],
    ["conv(sj.Sum(P('1/k**2'), [k, moo, -3]))", () => conv(sj.Sum(P('1/k**2'), [k, moo, -3])), "true"],
    ["conv(sj.Sum(P('1/k'), [k, 3, moo]))", () => conv(sj.Sum(P('1/k'), [k, 3, moo])), "false"],
    ["conv(sj.Sum(P('factorial(k)/k**k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('factorial(k)/k**k'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('3**k*factorial(k)/k**k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('3**k*factorial(k)/k**k'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('2**k/factorial(k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('2**k/factorial(k)'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('k**k/factorial(k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('k**k/factorial(k)'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('(-1)**k/log(k)'), [k, 2, sj.oo]))", () => conv(sj.Sum(P('(-1)**k/log(k)'), [k, 2, sj.oo])), "true"],
    ["conv(sj.Sum(P('(-1)**k/sqrt(k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('(-1)**k/sqrt(k)'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('1/(k*log(k))'), [k, 2, sj.oo]))", () => conv(sj.Sum(P('1/(k*log(k))'), [k, 2, sj.oo])), "false"],
    ["conv(sj.Sum(P('1/(k*log(k)**2)'), [k, 2, sj.oo]))", () => conv(sj.Sum(P('1/(k*log(k)**2)'), [k, 2, sj.oo])), "true"],
    ["conv(sj.Sum(P('exp(-k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('exp(-k)'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('sin(1/k)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('sin(1/k)'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('sin(1/k)**2'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('sin(1/k)**2'), [k, 1, sj.oo])), "true"],
    ["conv(sj.Sum(P('k**(-3/2)'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('k**(-3/2)'), [k, 1, sj.oo])), "true"],
    ["aconv(sj.Sum(P('(-1)**k/k'), [k, 1, sj.oo]))", () => aconv(sj.Sum(P('(-1)**k/k'), [k, 1, sj.oo])), "false"],
    ["aconv(sj.Sum(P('(-1)**k/k**2'), [k, 1, sj.oo]))", () => aconv(sj.Sum(P('(-1)**k/k**2'), [k, 1, sj.oo])), "true"],
    ["sj.eulerMaclaurin(conc(sj.Sum(P('k'), [k, 3, 1])), 0, 0)", () => sj.eulerMaclaurin(conc(sj.Sum(P('k'), [k, 3, 1])), 0, 0), "[-2, 0]"],
    ["sj.eulerMaclaurin(conc(sj.Sum(P('k'), [k, 2, 1])), 0, 0)", () => sj.eulerMaclaurin(conc(sj.Sum(P('k'), [k, 2, 1])), 0, 0), "[0, 0]"],
    ["sj.eulerMaclaurin(conc(sj.Sum(P('k**2'), [k, 1, 5])), 10, 0)", () => sj.eulerMaclaurin(conc(sj.Sum(P('k**2'), [k, 1, 5])), 10, 0), "[55, 0]"],
    ["sj.eulerMaclaurin(conc(sj.Sum(P('k**2'), [k, a, b])), 2, 1)", () => sj.eulerMaclaurin(conc(sj.Sum(P('k**2'), [k, a, b])), 2, 1), "[a**2 - a/6 + b**3/3 + b**2/2 + b/6 + (a + 1)**2 - (a + 2)**3/3 + (a + 2)**2/2 - 1/3, 0]"],
    ["sj.eulerMaclaurin(conc(sj.Sum(P('1/k**2'), [k, 1, sj.oo])), 2, 2)", () => sj.eulerMaclaurin(conc(sj.Sum(P('1/k**2'), [k, 1, sj.oo])), 2, 2), "[23983/14580, 1/91854]"],
    ["sj.summation(P('1/k**2'), [k, 1, sj.oo])", () => sj.summation(P('1/k**2'), [k, 1, sj.oo]), "pi**2/6"],
    ["sj.summation(P('1/k**3'), [k, 2, sj.oo])", () => sj.summation(P('1/k**3'), [k, 2, sj.oo]), "-1 + zeta(3)"],
    ["sj.summation(P('1/k'), [k, 1, n])", () => sj.summation(P('1/k'), [k, 1, n]), "harmonic(n)"],
    ["sj.summation(P('x/k**2'), [k, 3, n])", () => sj.summation(P('x/k**2'), [k, 3, n]), "x*(harmonic(n, 2) - 5/4)"],
    ["sj.summation(P('1/k'), [k, 1, sj.oo])", () => sj.summation(P('1/k'), [k, 1, sj.oo]), "oo"],
    ["sj.summation(P('1/k**2'), [k, 0, n])", () => sj.summation(P('1/k**2'), [k, 0, n]), "Sum(k**(-2), (k, 0, n))"],
    // SymPy's product() applies powsimp to the result
    ["sj.product(P('x*k*2**k'), [k, 1, n])", () => sj.product(P('x*k*2**k'), [k, 1, n]), "2**(n*(n + 1)/2)*x**n*factorial(n)"],
    ["sj.product(P('2**k'), [k, 1, n])", () => sj.product(P('2**k'), [k, 1, n]), "2**(n*(n + 1)/2)"],
    // the terms tend to AccumBounds(-1, 1), not to 0 (or 1)
    ["conv(sj.Product(P('sin(k)'), [k, 1, sj.oo]))", () => conv(sj.Product(P('sin(k)'), [k, 1, sj.oo])), "false"],
    ["conv(sj.Sum(P('sin(k)'), [k, moo, sj.oo]))", () => conv(sj.Sum(P('sin(k)'), [k, moo, sj.oo])), "false"],
    ["sj.summation(P('1/(k*(k + 1))'), [k, 1, n])", () => sj.summation(P('1/(k*(k + 1))'), [k, 1, n]), "1 - 1/(n + 1)"],
    ["sj.summation(P('1/(k*(k + 2))'), [k, 1, n])", () => sj.summation(P('1/(k*(k + 2))'), [k, 1, n]), "3/4 - 1/(2*(n + 2)) - 1/(2*(n + 1))"],
    ["sj.summation(P('log(k + 1) - log(k)'), [k, 1, n])", () => sj.summation(P('log(k + 1) - log(k)'), [k, 1, n]), "log(n + 1)"],
    ["sj.summation(P('cos(k + 1) - cos(k)'), [k, 1, n])", () => sj.summation(P('cos(k + 1) - cos(k)'), [k, 1, n]), "cos(n + 1) - cos(1)"],
    ["sj.summation(P('cos(k) - cos(k + 1)'), [k, 1, n])", () => sj.summation(P('cos(k) - cos(k + 1)'), [k, 1, n]), "-cos(n + 1) + cos(1)"],
    ["sj.Product(P('2**k'), [k, 1, n]).doit()", () => sj.doit(sj.Product(P('2**k'), [k, 1, n])), "2**(n**2/2 + n/2)"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // double poles are not summed by residues (SymPy gives a long closed form)
    ["sj.summation(P('1/(k**2+1)**2'), [k, 0, sj.oo])", () => sj.summation(P('1/(k**2+1)**2'), [k, 0, sj.oo]), "Sum((k**2 + 1)**(-2), (k, 0, oo))", "1/2 - pi*(-1/(2*tanh(pi)) - I*(-I*pi/tanh(pi) + I*pi*tanh(pi))/(4*tanh(pi)) + I*(-I*pi*tanh(pi) + I*pi/tanh(pi))/(4*tanh(pi)))/2"],
    // integer poles that are not consecutive (SymPy's value divides by 105 - 105*exp_polar(0) = 0)
    ["sj.summation(P('1/((k**2-1)*(k**2-9))'), [k, 5, sj.oo])", () => sj.summation(P('1/((k**2-1)*(k**2-9))'), [k, 5, sj.oo]), "Sum(1/((k**2 - 9)*(k**2 - 1)), (k, 5, oo))", "(90 - 118*exp_polar(0))/(288*(105 - 105*exp_polar(0))) + 7*(5*exp_polar(0) + 15)/(1440*(105 - 105*exp_polar(0)))"],
    // a pole inside the range (the term at k = 1 is zoo)
    ["sj.summation(P('1/(k**2-1)'), [k, 0, sj.oo])", () => sj.summation(P('1/(k**2-1)'), [k, 0, sj.oo]), "Sum(1/(k**2 - 1), (k, 0, oo))", "zoo"],
    // telescoping sums are not implemented
    ["sj.summation(P('1/(k**2-1)'), [k, 2, sj.oo])", () => sj.summation(P('1/(k**2-1)'), [k, 2, sj.oo]), "Sum(1/(k**2 - 1), (k, 2, oo))", "3/4"],
    // the denominator has no roots in radicals here; SymPy's 1/4 is wrong (the terms for k = 0, 1 already give 3/4)
    ["sj.summation(P('1/(k**4+k**2+2)'), [k, 0, sj.oo])", () => sj.summation(P('1/(k**4+k**2+2)'), [k, 0, sj.oo]), "Sum(1/(k**4 + k**2 + 2), (k, 0, oo))", "1/4"],
    // the term at k = 0 is zoo
    ["sj.summation(P('1/k**2'), [k, moo, sj.oo])", () => sj.summation(P('1/k**2'), [k, moo, sj.oo]), "Sum(k**(-2), (k, -oo, oo))", "zoo"],
    // k -> -k gives the sum from -3 to oo (SymPy leaves it unevaluated)
    ["sj.summation(P('1/(k**2+1)'), [k, moo, 3])", () => sj.summation(P('1/(k**2+1)'), [k, moo, 3]), "13/10 + pi/(2*tanh(pi))", "Sum(1/(k**2 + 1), (k, -oo, 3))"],
    // arithmetic-geometric sums are not implemented
    ["sj.summation(P('k*2**k'), [k, 0, n])", () => sj.summation(P('k*2**k'), [k, 0, n]), "Sum(2**k*k, (k, 0, n))", "2*(2**n*n - 2**n + 1)"],
    // the roots are not computed for an irreducible quartic
    ["sj.product(P('k**4+k**2+2'), [k, 1, n])", () => sj.product(P('k**4+k**2+2'), [k, 1, n]), "Product(k**4 + k**2 + 2, (k, 1, n))", "RisingFactorial(-2**(1/4)*sin(atan(sqrt(7))/2) + 1 - 2**(1/4)*I*cos(atan(sqrt(7))/2), n)*RisingFactorial(-2**(1/4)*sin(atan(sqrt(7))/2) + 1 + 2**(1/4)*I*cos(atan(sqrt(7))/2), n)*RisingFactorial(2**(1/4)*sin(atan(sqrt(7))/2) + 1 - 2**(1/4)*I*cos(atan(sqrt(7))/2), n)*RisingFactorial(2**(1/4)*sin(atan(sqrt(7))/2) + 1 + 2**(1/4)*I*cos(atan(sqrt(7))/2), n)"],
    // comparison with |sin(k)| <= 1 is not implemented
    ["conv(sj.Sum(P('sin(k)/k**3'), [k, moo, sj.oo]))", () => conv(sj.Sum(P('sin(k)/k**3'), [k, moo, sj.oo])), "unknown", "true"],
    // SymPy raises ValueError
    ["conv(sj.Sum(P('1/k**2'), [k, 1, P('zoo')]))", () => conv(sj.Sum(P('1/k**2'), [k, 1, P('zoo')])), "unknown", "ERR ValueError"],
    // SymPy raises NotImplementedError
    ["conv(sj.Sum(P('x**k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('x**k'), [k, 1, sj.oo])), "unknown", "ERR NotImplementedError"],
    // the series converges (Dirichlet's test), SymPy's False is wrong
    ["conv(sj.Sum(P('sin(k)/k'), [k, 1, sj.oo]))", () => conv(sj.Sum(P('sin(k)/k'), [k, 1, sj.oo])), "unknown", "false"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('summations: telescoping sums and convergence tests (SymPy 1.14)', () => {
  const [k, n] = sj.symbols('k n');
  it('sums two terms that cancel after a shift', () => {
    expect(String(sj.summation(sj.parse('sin(k) - sin(k + 2)'), [k, 1, n]))).toBe('-sin(n + 1) - sin(n + 2) + sin(1) + sin(2)');
    expect(String(sj.summation(sj.parse('1/(k**2 - 1)'), [k, 2, n]))).toBe('3/4 - 1/(2*(n + 1)) - 1/(2*n)');
    // no shift makes the terms cancel
    expect(String(sj.summation(sj.parse('sin(k) + cos(k)'), [k, 1, n]))).toBe('Sum(sin(k) + cos(k), (k, 1, n))');
  });
  it('writes the exponent of a product as SymPy does', () => {
    const [a] = sj.symbols('a');
    expect(String(sj.product(sj.parse('2**k'), [k, a, n]))).toBe('2**(-a**2/2 + a/2 + n**2/2 + n/2)');
    expect(String(sj.product(sj.parse('2**y'), [k, 1, n]))).toBe('(2**y)**n');
    expect(String(sj.product(sj.parse('sqrt(2)'), [k, 1, n]))).toBe('2**(n/2)');
  });
  it('uses the ratio test when the terms have no limit', () => {
    const conv = (s: string) => {
      const sum = sj.Sum(sj.parse(s), [k, 1, sj.oo]);
      expect(sum).toBeInstanceOf(Concrete);
      return String(sj.isConvergent(sum as Concrete));
    };
    expect(conv('(-1)**k*binomial(2*k, k)/3**k')).toBe('false');
    expect(conv('(-1)**k*factorial(k)/2**k')).toBe('false');
    // SymPy raises NotImplementedError
    expect(conv('(-1)**k/k + 1/k**2')).toBe('unknown');
  });
});
