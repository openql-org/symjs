// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Sums, products and their convergence (concrete/summations.ts). Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Sym, parse } from '../src';
import { Expr } from '../src/core/nodes';
import { NoMatchResult } from '../src/core/truth';

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
    // the same value: SymPy's product() applies powsimp, which factors the exponent
    ["sj.product(P('x*k*2**k'), [k, 1, n])", () => sj.product(P('x*k*2**k'), [k, 1, n]), "2**(n**2/2 + n/2)*x**n*factorial(n)", "2**(n*(n + 1)/2)*x**n*factorial(n)"],
    // the same value: SymPy's product() applies powsimp, which factors the exponent
    ["sj.product(P('2**k'), [k, 1, n])", () => sj.product(P('2**k'), [k, 1, n]), "2**(n**2/2 + n/2)", "2**(n*(n + 1)/2)"],
    // AccumBounds limits are not implemented
    ["conv(sj.Product(P('sin(k)'), [k, 1, sj.oo]))", () => conv(sj.Product(P('sin(k)'), [k, 1, sj.oo])), "unknown", "false"],
    // AccumBounds limits are not implemented
    ["conv(sj.Sum(P('sin(k)'), [k, moo, sj.oo]))", () => conv(sj.Sum(P('sin(k)'), [k, moo, sj.oo])), "unknown", "false"],
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
