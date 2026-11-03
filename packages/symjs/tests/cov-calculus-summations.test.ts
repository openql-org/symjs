// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Concrete, Product, Sum, doit, eulerMaclaurin, isAbsolutelyConvergent, isConvergent, limit, oo, parse, product, reverseOrder, subs, summation, symbols } from '../src';
import type { Expr } from '../src';

const [x, n, m, k, a] = symbols('x n m k a');
const P = parse;
/** Sum / Product as Concrete nodes (the convergence tests and reverseOrder take a Concrete). */
const conc = (e: Expr): Concrete => {
  if (!(e instanceof Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};

const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe("summations: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["summation(x, [k, 1, n])", () => summation(x, [k, 1, n]), "n*x"],
    ["summation(x, [k, 1, oo])", () => summation(x, [k, 1, oo]), "oo*x"],
    ["summation(k, [k, 5, 1])", () => summation(k, [k, 5, 1]), "-9"],
    ["summation(P('k**2'), [k, 10, 1])", () => summation(P('k**2'), [k, 10, 1]), "-284"],
    ["summation(P('1/(k**2+1)'), [k, 0, oo])", () => summation(P('1/(k**2+1)'), [k, 0, oo]), "1/2 + pi/(2*tanh(pi))"],
    ["summation(P('(-1)**k/(k**2+1)'), [k, 0, oo])", () => summation(P('(-1)**k/(k**2+1)'), [k, 0, oo]), "pi/(2*sinh(pi)) + 1/2"],
    ["summation(P('1/(k**2+4)'), [k, 0, oo])", () => summation(P('1/(k**2+4)'), [k, 0, oo]), "1/8 + pi/(4*tanh(2*pi))"],
    ["summation(P('1/(k**2+1)'), [k, 3, oo])", () => summation(P('1/(k**2+1)'), [k, 3, oo]), "-6/5 + pi/(2*tanh(pi))"],
    ["summation(P('1/(k**2+1)'), [k, -2, oo])", () => summation(P('1/(k**2+1)'), [k, -2, oo]), "6/5 + pi/(2*tanh(pi))"],
    ["summation(P('1/((k+1)**2+1)'), [k, 0, oo])", () => summation(P('1/((k+1)**2+1)'), [k, 0, oo]), "-1/2 + pi/(2*tanh(pi))"],
    ["summation(P('1/((k-2)**2+1)'), [k, 0, oo])", () => summation(P('1/((k-2)**2+1)'), [k, 0, oo]), "6/5 + pi/(2*tanh(pi))"],
    ["summation(P('(-1)**k/((k+1)**2+1)'), [k, 0, oo])", () => summation(P('(-1)**k/((k+1)**2+1)'), [k, 0, oo]), "-pi/(2*sinh(pi)) + 1/2"],
    ["summation(P('1/(k**2+x)'), [k, 0, oo])", () => summation(P('1/(k**2+x)'), [k, 0, oo]), "Sum(1/(k**2 + x), (k, 0, oo))"],
    ["summation(P('1/(k**3+1)'), [k, 0, oo])", () => summation(P('1/(k**3+1)'), [k, 0, oo]), "Sum(1/(k**3 + 1), (k, 0, oo))"],
    ["summation(P('k/(k**3+1)'), [k, 0, oo])", () => summation(P('k/(k**3+1)'), [k, 0, oo]), "Sum(k/(k**3 + 1), (k, 0, oo))"],
    ["summation(P('1/(k**2+k+1)'), [k, 0, oo])", () => summation(P('1/(k**2+k+1)'), [k, 0, oo]), "Sum(1/(k**2 + k + 1), (k, 0, oo))"],
    ["summation(P('1/(k**2+2*k+2)'), [k, 0, oo])", () => summation(P('1/(k**2+2*k+2)'), [k, 0, oo]), "-1/2 + pi/(2*tanh(pi))"],
    ["summation(P('1/(k**2+2*k+2)'), [k, 1, oo])", () => summation(P('1/(k**2+2*k+2)'), [k, 1, oo]), "-1 + pi/(2*tanh(pi))"],
    ["summation(P('1/(k**2-2*k+2)'), [k, 5, oo])", () => summation(P('1/(k**2-2*k+2)'), [k, 5, oo]), "-13/10 + pi/(2*tanh(pi))"],
    ["summation(P('(-1)**k/(k**2+2*k+2)'), [k, 0, oo])", () => summation(P('(-1)**k/(k**2+2*k+2)'), [k, 0, oo]), "-pi/(2*sinh(pi)) + 1/2"],
    ["summation(P('1/(2*k**2+1)'), [k, 0, oo])", () => summation(P('1/(2*k**2+1)'), [k, 0, oo]), "1/2 + sqrt(2)*pi/(4*tanh(sqrt(2)*pi/2))"],
    ["summation(P('2**(-k)'), [k, 0, oo])", () => summation(P('2**(-k)'), [k, 0, oo]), "2"],
    ["summation(P('2**k'), [k, 0, oo])", () => summation(P('2**k'), [k, 0, oo]), "oo"],
    ["summation(P('x**k'), [k, 0, oo])", () => summation(P('x**k'), [k, 0, oo]), "Piecewise((1/(1 - x), Abs(x) < 1), (Sum(x**k, (k, 0, oo)), True))"],
    ["summation(P('3*x**k'), [k, 0, n])", () => summation(P('3*x**k'), [k, 0, n]), "3*Piecewise((n + 1, Eq(x, 1)), ((1 - x**(n + 1))/(1 - x), True))"],
    ["summation(P('x**(2*k)'), [k, 1, n])", () => summation(P('x**(2*k)'), [k, 1, n]), "Piecewise((n, Eq(x**2, 1)), ((x**2 - (x**2)**(n + 1))/(1 - x**2), True))"],
    ["summation(P('x**k/factorial(k)'), [k, 0, oo])", () => summation(P('x**k/factorial(k)'), [k, 0, oo]), "exp(x)"],
    ["summation(P('sin(k)'), [k, 1, n])", () => summation(P('sin(k)'), [k, 1, n]), "Sum(sin(k), (k, 1, n))"],
    ["summation(P('k**3+2*k'), [k, 1, n])", () => summation(P('k**3+2*k'), [k, 1, n]), "n**4/4 + n**3/2 + 5*n**2/4 + n"],
    ["summation(P('x**(k**2)'), [k, 0, n])", () => summation(P('x**(k**2)'), [k, 0, n]), "Sum(x**(k**2), (k, 0, n))"],
    ["summation(P('x**(1/k)'), [k, 0, n])", () => summation(P('x**(1/k)'), [k, 0, n]), "Sum(x**(1/k), (k, 0, n))"],
    ["summation(P('k'), [k, 1, n], [n, 1, m])", () => summation(P('k'), [k, 1, n], [n, 1, m]), "m**3/6 + m**2/2 + m/3"],
    ["product(P('k'), [k, 1, n])", () => product(P('k'), [k, 1, n]), "factorial(n)"],
    ["product(P('2'), [k, 1, n])", () => product(P('2'), [k, 1, n]), "2**n"],
    ["product(P('1'), [k, 1, n])", () => product(P('1'), [k, 1, n]), "1"],
    ["product(P('x'), [k, a, n])", () => product(P('x'), [k, a, n]), "x**(-a + n + 1)"],
    ["product(P('k'), [k, 5, 1])", () => product(P('k'), [k, 5, 1]), "1/24"],
    ["product(P('k'), [k, 7, 1])", () => product(P('k'), [k, 7, 1]), "1/720"],
    ["product(P('k**2'), [k, 1, n])", () => product(P('k**2'), [k, 1, n]), "factorial(n)**2"],
    ["product(P('k+1'), [k, 1, n])", () => product(P('k+1'), [k, 1, n]), "RisingFactorial(2, n)"],
    ["product(P('2*k'), [k, 1, n])", () => product(P('2*k'), [k, 1, n]), "2**n*factorial(n)"],
    ["product(P('k*(k+1)'), [k, 1, n])", () => product(P('k*(k+1)'), [k, 1, n]), "RisingFactorial(2, n)*factorial(n)"],
    ["product(P('x*k'), [k, 1, n])", () => product(P('x*k'), [k, 1, n]), "x**n*factorial(n)"],
    ["product(P('k**2+1'), [k, 1, n])", () => product(P('k**2+1'), [k, 1, n]), "RisingFactorial(1 - I, n)*RisingFactorial(1 + I, n)"],
    ["product(P('(k+1)**x'), [k, 1, n])", () => product(P('(k+1)**x'), [k, 1, n]), "RisingFactorial(2, n)**x"],
    ["product(P('sin(k)'), [k, 1, n])", () => product(P('sin(k)'), [k, 1, n]), "Product(sin(k), (k, 1, n))"],
    ["product(P('k**k'), [k, 1, n])", () => product(P('k**k'), [k, 1, n]), "Product(k**k, (k, 1, n))"],
    ["product(P('k'), [k, n, n])", () => product(P('k'), [k, n, n]), "n"],
    ["product(P('k**3-2'), [k, 1, n])", () => product(P('k**3-2'), [k, 1, n]), "RisingFactorial(1 - 2**(1/3), n)*RisingFactorial(2**(1/3)/2 + 1 - 2**(1/3)*sqrt(3)*I/2, n)*RisingFactorial(2**(1/3)/2 + 1 + 2**(1/3)*sqrt(3)*I/2, n)"],
    ["summation(x, [k, P('-oo'), 0])", () => summation(x, [k, P('-oo'), 0]), "oo*x"],
    ["summation(P('k**2'), [k, n, 1])", () => summation(P('k**2'), [k, n, 1]), "-n**3/3 + n**2/2 - n/6 + 1"],
    ["summation(P('1/(k**2+1)'), [k, P('-oo'), oo])", () => summation(P('1/(k**2+1)'), [k, P('-oo'), oo]), "pi/tanh(pi)"],
    ["summation(P('(-1)**k/(k**2+1)'), [k, P('-oo'), oo])", () => summation(P('(-1)**k/(k**2+1)'), [k, P('-oo'), oo]), "pi/sinh(pi)"],
    ["summation(P('1/(k**2-1)'), [k, P('-oo'), oo])", () => summation(P('1/(k**2-1)'), [k, P('-oo'), oo]), "Sum(1/(k**2 - 1), (k, -oo, oo))"],
    ["summation(P('1/(k**2+1)'), [k, P('-oo'), n])", () => summation(P('1/(k**2+1)'), [k, P('-oo'), n]), "Sum(1/(k**2 + 1), (k, -oo, n))"],
    ["summation(P('1/(k**2+x)'), [k, P('-oo'), oo])", () => summation(P('1/(k**2+x)'), [k, P('-oo'), oo]), "Sum(1/(k**2 + x), (k, -oo, oo))"],
    ["summation(P('1/(k**2+1)'), [k, n, oo])", () => summation(P('1/(k**2+1)'), [k, n, oo]), "Sum(1/(k**2 + 1), (k, n, oo))"],
    ["summation(P('1/((k+1)**2+1)'), [k, P('-oo'), oo])", () => summation(P('1/((k+1)**2+1)'), [k, P('-oo'), oo]), "-pi*(-I/(2*tan(pi*(-1 + I))) + I/(2*tan(pi*(-1 - I))))"],
    ["summation(P('1/(k**2+1)/2'), [k, 0, oo])", () => summation(P('1/(k**2+1)/2'), [k, 0, oo]), "1/4 + pi/(4*tanh(pi))"],
    ["summation(P('2**(k+1)'), [k, 0, n])", () => summation(P('2**(k+1)'), [k, 0, n]), "2*2**(n + 1) - 2"],
    ["summation(P('2**(k+1)'), [k, 0, oo])", () => summation(P('2**(k+1)'), [k, 0, oo]), "oo"],
    ["summation(P('-2**(k+1)'), [k, 0, oo])", () => summation(P('-2**(k+1)'), [k, 0, oo]), "-oo"],
    ["summation(P('2**(2*k+1)'), [k, 0, n])", () => summation(P('2**(2*k+1)'), [k, 0, n]), "2*4**(n + 1)/3 - 2/3"],
    ["summation(P('x**k'), [k, a, n])", () => summation(P('x**k'), [k, a, n]), "Piecewise((-a + n + 1, Eq(x, 1)), ((x**a - x**(n + 1))/(1 - x), True))"],
    ["summation(P('x**k'), [k, 0, n])", () => summation(P('x**k'), [k, 0, n]), "Piecewise((n + 1, Eq(x, 1)), ((1 - x**(n + 1))/(1 - x), True))"],
    ["summation(P('sqrt(2)**k'), [k, 0, n])", () => summation(P('sqrt(2)**k'), [k, 0, n]), "(1 - 2**(n/2 + 1/2))/(1 - sqrt(2))"],
    ["summation(P('(-1)**k'), [k, 0, n])", () => summation(P('(-1)**k'), [k, 0, n]), "1/2 - (-1)**(n + 1)/2"],
    ["summation(P('0'), [k, 1, oo])", () => summation(P('0'), [k, 1, oo]), "0"],
    ["summation(P('-2'), [k, 1, oo])", () => summation(P('-2'), [k, 1, oo]), "-oo"],
    ["summation(P('1/(k**5+k+1)'), [k, 0, oo])", () => summation(P('1/(k**5+k+1)'), [k, 0, oo]), "Sum(1/(k**5 + k + 1), (k, 0, oo))"],
    ["summation(P('1/(k**2+sqrt(2)*k+1)'), [k, 0, oo])", () => summation(P('1/(k**2+sqrt(2)*k+1)'), [k, 0, oo]), "Sum(1/(k**2 + sqrt(2)*k + 1), (k, 0, oo))"],
    ["summation(P('1/(k**3+k)'), [k, 1, oo])", () => summation(P('1/(k**3+k)'), [k, 1, oo]), "Sum(1/(k**3 + k), (k, 1, oo))"],
    ["summation(P('1/((k-1)*(k-3)+5)'), [k, 0, oo])", () => summation(P('1/((k-1)*(k-3)+5)'), [k, 0, oo]), "9/20 + pi/(4*tanh(2*pi))"],
    ["summation(P('1/(k**2+3)'), [k, -3, oo])", () => summation(P('1/(k**2+3)'), [k, -3, oo]), "9/14 + sqrt(3)*pi/(6*tanh(sqrt(3)*pi))"],
    ["summation(P('1/(k**2+4)'), [k, 0, n])", () => summation(P('1/(k**2+4)'), [k, 0, n]), "Sum(1/(k**2 + 4), (k, 0, n))"],
    ["summation(P('2**k/factorial(k)'), [k, 0, oo])", () => summation(P('2**k/factorial(k)'), [k, 0, oo]), "exp(2)"],
    ["summation(P('(-1)**k/(2*k**2+1)'), [k, 0, oo])", () => summation(P('(-1)**k/(2*k**2+1)'), [k, 0, oo]), "sqrt(2)*pi/(4*sinh(sqrt(2)*pi/2)) + 1/2"],
    ["summation(P('exp(k)'), [k, 0, n])", () => summation(P('exp(k)'), [k, 0, n]), "(1 - exp(n + 1))/(1 - E)"],
    ["summation(P('exp(-k)'), [k, 0, oo])", () => summation(P('exp(-k)'), [k, 0, oo]), "1/(1 - exp(-1))"],
    ["summation(P('exp(I*k)'), [k, 0, oo])", () => summation(P('exp(I*k)'), [k, 0, oo]), "Sum(exp(I*k), (k, 0, oo))"],
    ["product(P('k**5+k+1'), [k, 1, n])", () => product(P('k**5+k+1'), [k, 1, n]), "RisingFactorial(3/2 - sqrt(3)*I/2, n)*RisingFactorial(3/2 + sqrt(3)*I/2, n)*RisingFactorial(2/3 + (-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3 + 1/(3*(-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)), n)*RisingFactorial(2/3 + 1/(3*(-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3, n)*RisingFactorial(1/(3*(3*sqrt(69)/2 + 25/2)**(1/3)) + 2/3 + (3*sqrt(69)/2 + 25/2)**(1/3)/3, n)"],
    ["product(P('x**(k+1)'), [k, 1, n])", () => product(P('x**(k+1)'), [k, 1, n]), "x**(n**2/2 + 3*n/2)"],
    ["product(P('sin(k)**2'), [k, 1, n])", () => product(P('sin(k)**2'), [k, 1, n]), "Product(sin(k)**2, (k, 1, n))"],
    ["product(P('(k+1)**2*x'), [k, 1, n])", () => product(P('(k+1)**2*x'), [k, 1, n]), "x**n*RisingFactorial(2, n)**2"],
    ["product(P('3*k'), [k, 1, 3])", () => product(P('3*k'), [k, 1, 3]), "162"],
    ["product(P('1/k'), [k, 1, n])", () => product(P('1/k'), [k, 1, n]), "1/factorial(n)"],
    ["product(P('k'), [k, 1, 0])", () => product(P('k'), [k, 1, 0]), "1"],
    ["product(P('2'), [k, a, n])", () => product(P('2'), [k, a, n]), "2**(-a + n + 1)"],
    ["product(P('k**2+k+1'), [k, a, n])", () => product(P('k**2+k+1'), [k, a, n]), "RisingFactorial(a + 1/2 - sqrt(3)*I/2, -a + n + 1)*RisingFactorial(a + 1/2 + sqrt(3)*I/2, -a + n + 1)"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/k**2'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/k'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/k'), [k, 1, 10])))", () => isConvergent(conc(Sum(P('1/k'), [k, 1, 10]))), "true"],
    ["isConvergent(conc(Sum(P('1/k'), [k, P('-oo'), -1])))", () => isConvergent(conc(Sum(P('1/k'), [k, P('-oo'), -1]))), "false"],
    ["isConvergent(conc(Sum(P('k'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('k**(-3/2)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('k**(-3/2)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/sqrt(k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/sqrt(k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('k/(k**2+1)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('k/(k**2+1)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/k**2/2'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/k**2/2'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('2**(-k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('2**(-k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/factorial(k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/factorial(k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('factorial(k)/10**k'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('factorial(k)/10**k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('k**3/2**k'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('k**3/2**k'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/k'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(-1)**k/k'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/sqrt(k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(-1)**k/sqrt(k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k*k'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(-1)**k*k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('sin(1/k**2)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('sin(1/k**2)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('sin(1/k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('sin(1/k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('exp(-k**2)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('exp(-k**2)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2-I)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/(k**2-I)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/log(k)'), [k, 2, oo])))", () => isConvergent(conc(Sum(P('(-1)**k/log(k)'), [k, 2, oo]))), "true"],
    ["isConvergent(conc(Product(P('1+1/k**2'), [k, 1, oo])))", () => isConvergent(conc(Product(P('1+1/k**2'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Product(P('1+1/k'), [k, 1, oo])))", () => isConvergent(conc(Product(P('1+1/k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Product(P('k'), [k, 1, oo])))", () => isConvergent(conc(Product(P('k'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Product(P('2'), [k, 1, oo])))", () => isConvergent(conc(Product(P('2'), [k, 1, oo]))), "false"],
    ["isAbsolutelyConvergent(conc(Sum(P('(-1)**k/k'), [k, 1, oo])))", () => isAbsolutelyConvergent(conc(Sum(P('(-1)**k/k'), [k, 1, oo]))), "false"],
    ["isAbsolutelyConvergent(conc(Sum(P('(-1)**k/k**2'), [k, 1, oo])))", () => isAbsolutelyConvergent(conc(Sum(P('(-1)**k/k**2'), [k, 1, oo]))), "true"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 1, n])))", () => eulerMaclaurin(conc(Sum(P('k'), [k, 1, n]))), "[n**2/2 + n/2, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k**2'), [k, 1, n])), 0, 2)", () => eulerMaclaurin(conc(Sum(P('k**2'), [k, 1, n])), 0, 2), "[n**3/3 + n**2/2 + n/6, 0]"],
    ["eulerMaclaurin(conc(Sum(P('1/k**2'), [k, 1, oo])), 2, 2)", () => eulerMaclaurin(conc(Sum(P('1/k**2'), [k, 1, oo])), 2, 2), "[23983/14580, 1/91854]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 1, 3])), 5)", () => eulerMaclaurin(conc(Sum(P('k'), [k, 1, 3])), 5), "[6, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 1, 10])), 3)", () => eulerMaclaurin(conc(Sum(P('k'), [k, 1, 10])), 3), "[55, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 5, 1])))", () => eulerMaclaurin(conc(Sum(P('k'), [k, 5, 1]))), "[-9, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, 5, 4])))", () => eulerMaclaurin(conc(Sum(P('k'), [k, 5, 4]))), "[0, 0]"],
    ["eulerMaclaurin(conc(Sum(P('k'), [k, n, m])), 2)", () => eulerMaclaurin(conc(Sum(P('k'), [k, n, m])), 2), "[m**2/2 + m/2 + 5*n/2 - (n + 2)**2/2 + 2, 0]"],
    ["reverseOrder(conc(Sum(P('k'), [k, 1, n])), 0)", () => reverseOrder(conc(Sum(P('k'), [k, 1, n])), 0), "Sum(-k, (k, n + 1, 0))"],
    ["reverseOrder(conc(Sum(P('k*x'), [k, 1, n], [x, 2, 5])), x)", () => reverseOrder(conc(Sum(P('k*x'), [k, 1, n], [x, 2, 5])), x), "Sum(-k*x, (k, 1, n), (x, 6, 1))"],
    ["reverseOrder(conc(Product(P('k'), [k, 1, n])), k)", () => reverseOrder(conc(Product(P('k'), [k, 1, n])), k), "Product(1/k, (k, n + 1, 0))"],
    ["reverseOrder(conc(Product(P('k'), [k, 1, n])), 0, 0)", () => reverseOrder(conc(Product(P('k'), [k, 1, n])), 0, 0), "Product(1/k, (k, n + 1, 0))"],
    ["doit(Sum(P('k'), [k, 1, n]))", () => doit(Sum(P('k'), [k, 1, n])), "n**2/2 + n/2"],
    ["doit(Product(P('k'), [k, 1, 4]))", () => doit(Product(P('k'), [k, 1, 4])), "24"],
    ["product(P('k'), [k, 1, oo])", () => product(P('k'), [k, 1, oo]), "Product(k, (k, 1, oo))"],
    ["product(P('1-1/k**2'), [k, 2, oo])", () => product(P('1-1/k**2'), [k, 2, oo]), "Product(1 - 1/k**2, (k, 2, oo))"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, P('-oo'), -1])))", () => isConvergent(conc(Sum(P('1/k**2'), [k, P('-oo'), -1]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, P('-oo'), oo])))", () => isConvergent(conc(Sum(P('1/(k**2+1)'), [k, P('-oo'), oo]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, P('-oo')])))", () => isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, P('-oo')]))), "true"],
    ["isConvergent(conc(Sum(P('k/(k**2+1)'), [k, P('-oo'), oo])))", () => isConvergent(conc(Sum(P('k/(k**2+1)'), [k, P('-oo'), oo]))), "false"],
    ["isConvergent(conc(Sum(P('2**k'), [k, P('-oo'), 0])))", () => isConvergent(conc(Sum(P('2**k'), [k, P('-oo'), 0]))), "true"],
    ["isConvergent(conc(Product(P('exp(1/k**2)'), [k, 1, oo])))", () => isConvergent(conc(Product(P('exp(1/k**2)'), [k, 1, oo]))), "true"],
    ["limit(P('k**3/2**k'), k, oo)", () => limit(P('k**3/2**k'), k, oo), "0"],
    ["limit(P('1/(k**2-I)'), k, oo)", () => limit(P('1/(k**2-I)'), k, oo), "0"],
    ["limit(P('k**2-I'), k, oo)", () => limit(P('k**2-I'), k, oo), "oo"],
    ["limit(P('x*exp(-x)'), x, oo)", () => limit(P('x*exp(-x)'), x, oo), "0"],
    ["limit(P('x**2*3**(-x)'), x, oo)", () => limit(P('x**2*3**(-x)'), x, oo), "0"],
    ["limit(P('3**x/x**5'), x, oo)", () => limit(P('3**x/x**5'), x, oo), "oo"],
    ["summation(P('sin(k)'), [k, P('n+5'), n])", () => summation(P('sin(k)'), [k, P('n+5'), n]), "-sin(n + 1) - sin(n + 2) - sin(n + 3) - sin(n + 4)"],
    ["product(P('sin(k)'), [k, P('n+5'), n])", () => product(P('sin(k)'), [k, P('n+5'), n]), "1/(sin(n + 1)*sin(n + 2)*sin(n + 3)*sin(n + 4))"],
    ["summation(P('(-2)**k'), [k, 0, oo])", () => summation(P('(-2)**k'), [k, 0, oo]), "Sum((-2)**k, (k, 0, oo))"],
    ["summation(P('(-1)**k*k/(k**2+1)'), [k, 0, oo])", () => summation(P('(-1)**k*k/(k**2+1)'), [k, 0, oo]), "Sum((-1)**k*k/(k**2 + 1), (k, 0, oo))"],
    ["summation(P('k/(k**5-5*k**3+4*k)'), [k, 3, oo])", () => summation(P('k/(k**5-5*k**3+4*k)'), [k, 3, oo]), "5/144"],
    ["summation(P('k/(k**5-5*k**3+4*k)'), [k, 4, oo])", () => summation(P('k/(k**5-5*k**3+4*k)'), [k, 4, oo]), "7/720"],
    ["summation(P('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 3, oo])", () => summation(P('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 3, oo]), "-1/48"],
    ["summation(P('(-1)**k/(k**2+2*k+2)'), [k, P('-oo'), oo])", () => summation(P('(-1)**k/(k**2+2*k+2)'), [k, P('-oo'), oo]), "-pi*(I/(2*sin(pi*(-1 - I))) - I/(2*sin(pi*(-1 + I))))"],
    ["summation(P('(-1)**k/(k**2+2*k+2)'), [k, 3, oo])", () => summation(P('(-1)**k/(k**2+2*k+2)'), [k, 3, oo]), "-pi/(2*sinh(pi)) + 1/10"],
    ["summation(P('1/(k**2+k+1)**2'), [k, 0, oo])", () => summation(P('1/(k**2+k+1)**2'), [k, 0, oo]), "Sum((k**2 + k + 1)**(-2), (k, 0, oo))"],
    ["summation(P('1/(k**4+2*k**3+k**2+1)'), [k, 0, oo])", () => summation(P('1/(k**4+2*k**3+k**2+1)'), [k, 0, oo]), "Sum(1/(k**4 + 2*k**3 + k**2 + 1), (k, 0, oo))"],
    ["summation(P('1/(k**3+3*k**2+3*k+2)'), [k, 0, oo])", () => summation(P('1/(k**3+3*k**2+3*k+2)'), [k, 0, oo]), "Sum(1/(k**3 + 3*k**2 + 3*k + 2), (k, 0, oo))"],
    ["summation(P('1/(k**2+1)'), [k, P('1/2'), oo])", () => summation(P('1/(k**2+1)'), [k, P('1/2'), oo]), "Sum(1/(k**2 + 1), (k, 1/2, oo))"],
    ["product(P('k**3+k+1'), [k, 1, n])", () => product(P('k**3+k+1'), [k, 1, n]), "RisingFactorial(1 + (-1/2 - sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)/3 - 1/((-1/2 - sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)), n)*RisingFactorial(1 - 1/((-1/2 + sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(27/2 + 3*sqrt(93)/2)**(1/3)/3, n)*RisingFactorial(-1/(27/2 + 3*sqrt(93)/2)**(1/3) + 1 + (27/2 + 3*sqrt(93)/2)**(1/3)/3, n)"],
    ["product(P('k*(k**5+k+1)'), [k, 1, n])", () => product(P('k*(k**5+k+1)'), [k, 1, n]), "RisingFactorial(3/2 - sqrt(3)*I/2, n)*RisingFactorial(3/2 + sqrt(3)*I/2, n)*RisingFactorial(2/3 + (-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3 + 1/(3*(-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)), n)*RisingFactorial(2/3 + 1/(3*(-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3, n)*RisingFactorial(1/(3*(3*sqrt(69)/2 + 25/2)**(1/3)) + 2/3 + (3*sqrt(69)/2 + 25/2)**(1/3)/3, n)*factorial(n)"],
    ["product(P('k**x'), [k, 1, n])", () => product(P('k**x'), [k, 1, n]), "factorial(n)**x"],
    ["product(P('(k**5+k+1)**2'), [k, 1, n])", () => product(P('(k**5+k+1)**2'), [k, 1, n]), "RisingFactorial(3/2 - sqrt(3)*I/2, n)**2*RisingFactorial(3/2 + sqrt(3)*I/2, n)**2*RisingFactorial(2/3 + (-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3 + 1/(3*(-1/2 - sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)), n)**2*RisingFactorial(2/3 + 1/(3*(-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(3*sqrt(69)/2 + 25/2)**(1/3)/3, n)**2*RisingFactorial(1/(3*(3*sqrt(69)/2 + 25/2)**(1/3)) + 2/3 + (3*sqrt(69)/2 + 25/2)**(1/3)/3, n)**2"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, 1, n])))", () => isConvergent(conc(Sum(P('1/k**2'), [k, 1, n]))), "true"],
    ["isConvergent(conc(Sum(P('1/k**2'), [k, n, oo])))", () => isConvergent(conc(Sum(P('1/k**2'), [k, n, oo]))), "true"],
    ["isConvergent(conc(Sum(P('exp(-k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('exp(-k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(3/2)**k/k**4'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(3/2)**k/k**4'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('(-1)**k*log(k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(-1)**k*log(k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('(-1)**k*(1+1/k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(-1)**k*(1+1/k)'), [k, 1, oo]))), "false"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, P('-oo'), 5])))", () => isConvergent(conc(Sum(P('1/(k**2+1)'), [k, P('-oo'), 5]))), "true"],
    ["isConvergent(conc(Sum(P('2**k'), [k, P('-oo'), oo])))", () => isConvergent(conc(Sum(P('2**k'), [k, P('-oo'), oo]))), "false"],
    ["eulerMaclaurin(conc(Sum(P('k**3'), [k, 1, n])), 0, 3)", () => eulerMaclaurin(conc(Sum(P('k**3'), [k, 1, n])), 0, 3), "[n**4/4 + n**3/2 + n**2/4, 0]"],
    ["summation(P('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 5, oo])", () => summation(P('(-1)**k*k/(k**5-5*k**3+4*k)'), [k, 5, oo]), "-1/720"],
    ["summation(P('1/(k*(k**2+1))'), [k, 1, oo])", () => summation(P('1/(k*(k**2+1))'), [k, 1, oo]), "Sum(1/(k*(k**2 + 1)), (k, 1, oo))"],
    ["summation(P('2**k'), [k, P('-oo'), 0])", () => summation(P('2**k'), [k, P('-oo'), 0]), "2"],
    ["summation(P('x**k'), [k, P('-oo'), oo])", () => summation(P('x**k'), [k, P('-oo'), oo]), "Sum(x**k, (k, -oo, oo))"],
    ["summation(P('1/(k**2+1)**2'), [k, P('-oo'), oo])", () => summation(P('1/(k**2+1)**2'), [k, P('-oo'), oo]), "Sum((k**2 + 1)**(-2), (k, -oo, oo))"],
    ["summation(P('1/(k**4-1)'), [k, P('-oo'), oo])", () => summation(P('1/(k**4-1)'), [k, P('-oo'), oo]), "Sum(1/(k**4 - 1), (k, -oo, oo))"],
    ["product(P('k*sin(k)'), [k, 1, 3])", () => product(P('k*sin(k)'), [k, 1, 3]), "6*sin(1)*sin(2)*sin(3)"],
    ["product(P('x**k'), [k, 1, n])", () => product(P('x**k'), [k, 1, n]), "x**(n**2/2 + n/2)"],
    ["product(P('(k*x)**k'), [k, 1, n])", () => product(P('(k*x)**k'), [k, 1, n]), "Product((k*x)**k, (k, 1, n))"],
    ["product(P('sin(k)**k'), [k, 1, n])", () => product(P('sin(k)**k'), [k, 1, n]), "Product(sin(k)**k, (k, 1, n))"],
    ["product(P('1/(k**2+1)'), [k, 1, n])", () => product(P('1/(k**2+1)'), [k, 1, n]), "1/(RisingFactorial(1 - I, n)*RisingFactorial(1 + I, n))"],
    ["product(P('2**k'), [k, a, n])", () => product(P('2**k'), [k, a, n]), "2**(-a**2/2 + a/2 + n**2/2 + n/2)"],
    ["product(P('0'), [k, 1, n])", () => product(P('0'), [k, 1, n]), "0**n"],
    ["summation(P('2**k*3**k'), [k, 1, n])", () => summation(P('2**k*3**k'), [k, 1, n]), "6**(n + 1)/5 - 6/5"],
    ["summation(P('2**(k**2)'), [k, 1, n])", () => summation(P('2**(k**2)'), [k, 1, n]), "Sum(2**(k**2), (k, 1, n))"],
    ["summation(P('x**k*factorial(k)'), [k, 0, oo])", () => summation(P('x**k*factorial(k)'), [k, 0, oo]), "Sum(x**k*factorial(k), (k, 0, oo))"],
    ["summation(P('1/(k**2+1)'), [k, 0, n])", () => summation(P('1/(k**2+1)'), [k, 0, n]), "Sum(1/(k**2 + 1), (k, 0, n))"],
    ["summation(P('1/(k**2+1)'), [k, 1, oo], [x, 0, 1])", () => summation(P('1/(k**2+1)'), [k, 1, oo], [x, 0, 1]), "-1 + pi/tanh(pi)"],
    ["isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, oo], [x, 1, 2])))", () => isConvergent(conc(Sum(P('1/(k**2+1)'), [k, 1, oo], [x, 1, 2]))), "true"],
    ["isConvergent(conc(Sum(P('1/(k**2+I*k)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('1/(k**2+I*k)'), [k, 1, oo]))), "true"],
    ["isConvergent(conc(Sum(P('(-1)**k/k**(1/3)'), [k, 1, oo])))", () => isConvergent(conc(Sum(P('(-1)**k/k**(1/3)'), [k, 1, oo]))), "true"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
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
    near(summation(P('1/(k**4+4)'), [k, P('-oo'), oo]), 0.788337023734291);
    near(summation(P('1/(k**4+1)'), [k, 0, oo]), 1.57847757966714);
    near(summation(P('1/((k**2+1)*(k**2+4))'), [k, 0, oo]), 0.388756802049155);
    near(summation(P('1/(k**4+1)'), [k, 3, oo]), 0.0196540502553721);
  });
  it('a product whose exponent SymPy factors', () => {
    // SymPy: 2**(n*(n + 1)/2)
    const e = product(P('2**k'), [k, 1, n]);
    expect(subs(e, [[n, 5]]).toString()).toBe('32768');
  });
});

describe('summations: ranges ending at -oo', () => {
  it('follows the Karr convention', () => {
    // SymPy 1.14 gives summation(2**k, (k, 0, -3)) = -3/4 (Karr: -sum_{k=-2}^{-1}) but
    // summation(2**k, (k, 0, -oo)) = 1 = +sum_{k=-oo}^{-1}, contradicting its own convention;
    // the consistent value is -summation(2**k, (k, -oo, -1)) = -1.
    expect(summation(P('2**k'), [k, 0, -3]).toString()).toBe('-3/4');
    expect(summation(P('2**k'), [k, 0, P('-oo')]).toString()).toBe('-1');
  });
  it('mirrors a sum from -oo', () => {
    // SymPy leaves Sum(1/(k**2 + 1), (k, -oo, 0)) unevaluated; it equals SymPy's
    // summation(1/(k**2 + 1), (k, 0, oo)) = 1/2 + pi/(2*tanh(pi))
    expect(summation(P('1/(k**2+1)'), [k, P('-oo'), 0]).toString()).toBe('1/2 + pi/(2*tanh(pi))');
  });
});

describe('summations: convergence where SymPy 1.14 raises', () => {
  it('decides series SymPy cannot handle', () => {
    // SymPy raises NotImplementedError (I counts as a second symbol); |f| ~ 1/k**2
    expect(String(isConvergent(conc(Sum(P('1/(k**2-I)'), [k, 1, oo]))))).toBe('true');
    expect(String(isConvergent(conc(Sum(P('1/(k**2+I*k)'), [k, 1, oo]))))).toBe('true');
    // SymPy raises ValueError; absolutely convergent (|f| <= 1/k**2)
    expect(String(isConvergent(conc(Sum(P('(-1)**k*sin(k)/k**2'), [k, 1, oo]))))).toBe('true');
    // SymPy raises ValueError; alternating with sin(1/k) decreasing to 0
    expect(String(isConvergent(conc(Sum(P('(-1)**k*sin(1/k)'), [k, 1, oo]))))).toBe('true');
    // SymPy raises NotImplementedError: the answer depends on x
    expect(String(isConvergent(conc(Sum(P('x**k'), [k, 1, oo]))))).toBe('unknown');
  });
});

describe('summations: errors', () => {
  it('eulerMaclaurin needs a single limit (SymPy raises ValueError)', () => {
    expect(() => eulerMaclaurin(conc(Sum(P('k'), [k, 1, n], [n, 1, 3])))).toThrow(TypeError);
  });
});
