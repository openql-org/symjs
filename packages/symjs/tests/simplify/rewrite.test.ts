// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/rewrite.ts.

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, defineFunction, fn, parse, rewrite, sub, symbol, symbols } from '../../src';

const [x, y, n, k] = symbols('x y n k');
const r = symbol('r', { real: true });
const p = symbol('p', { positive: true });
const kk = symbol('kk', { integer: true });
const P = (s: string) => parse(s, { symbols: [x, y, n, k, r, p, kk] });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe('rewrite', () => {
  it('rewrites trigonometric functions like SymPy', async () => {
    const { rewrite, sin, cos, tan, mul, add, I, str, symbols: syms } = await import('../../src');
    const [t] = syms('t');
    expect(str(rewrite(add(cos(t!), mul(I, sin(t!))), 'exp'))).toBe('exp(I*t)');
    expect(str(rewrite(tan(t!), 'sin'))).toBe('2*sin(t)**2/sin(2*t)');
    expect(str(rewrite(sin(t!), 'cos'))).toBe('cos(t - pi/2)');
  });
});

describe("rewrite: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["rewrite(P('sin(x)'), 'exp')", () => rewrite(P('sin(x)'), 'exp'), "-I*(exp(I*x) - exp(-I*x))/2"],
    ["rewrite(P('sin(x)'), 'cos')", () => rewrite(P('sin(x)'), 'cos'), "cos(x - pi/2)"],
    ["rewrite(P('sin(x)'), 'tan')", () => rewrite(P('sin(x)'), 'tan'), "2*tan(x/2)/(tan(x/2)**2 + 1)"],
    ["rewrite(P('sin(log(x))'), 'Pow')", () => rewrite(P('sin(log(x))'), 'Pow'), "-I*x**I/2 + I/(2*x**I)"],
    ["rewrite(P('sin(x)'), 'Pow')", () => rewrite(P('sin(x)'), 'Pow'), "sin(x)"],
    ["rewrite(P('sin(x)'), 'sincos')", () => rewrite(P('sin(x)'), 'sincos'), "sin(x)"],
    ["rewrite(P('sin(sinh(x))'), 'exp')", () => rewrite(P('sin(sinh(x))'), 'exp'), "-I*(-exp(I*(-exp(x)/2 + exp(-x)/2)) + exp(I*(exp(x)/2 - exp(-x)/2)))/2"],
    ["rewrite(P('cos(x)'), 'exp')", () => rewrite(P('cos(x)'), 'exp'), "exp(I*x)/2 + exp(-I*x)/2"],
    ["rewrite(P('cos(x)'), 'sin')", () => rewrite(P('cos(x)'), 'sin'), "sin(x + pi/2)"],
    ["rewrite(P('cos(x)'), 'tan')", () => rewrite(P('cos(x)'), 'tan'), "(1 - tan(x/2)**2)/(tan(x/2)**2 + 1)"],
    ["rewrite(P('cos(log(x))'), 'Pow')", () => rewrite(P('cos(log(x))'), 'Pow'), "x**I/2 + 1/(2*x**I)"],
    ["rewrite(P('cos(x)'), 'Pow')", () => rewrite(P('cos(x)'), 'Pow'), "cos(x)"],
    ["rewrite(P('cos(x)'), 'sincos')", () => rewrite(P('cos(x)'), 'sincos'), "cos(x)"],
    ["rewrite(P('tan(x)'), 'exp')", () => rewrite(P('tan(x)'), 'exp'), "I*(-exp(I*x) + exp(-I*x))/(exp(I*x) + exp(-I*x))"],
    ["rewrite(P('tan(x)'), 'cos')", () => rewrite(P('tan(x)'), 'cos'), "cos(x - pi/2)/cos(x)"],
    ["rewrite(P('tan(x)'), 'sin')", () => rewrite(P('tan(x)'), 'sin'), "2*sin(x)**2/sin(2*x)"],
    ["rewrite(P('tan(x)'), 'sincos')", () => rewrite(P('tan(x)'), 'sincos'), "sin(x)/cos(x)"],
    ["rewrite(P('tan(log(x))'), 'Pow')", () => rewrite(P('tan(log(x))'), 'Pow'), "I*(-x**I + x**(-I))/(x**I + x**(-I))"],
    ["rewrite(P('tan(x)'), 'Pow')", () => rewrite(P('tan(x)'), 'Pow'), "tan(x)"],
    ["rewrite(P('exp(x)'), 'cos')", () => rewrite(P('exp(x)'), 'cos'), "sinh(x) + cosh(x)"],
    ["rewrite(P('exp(x)'), 'sin')", () => rewrite(P('exp(x)'), 'sin'), "sinh(x) + cosh(x)"],
    ["rewrite(P('exp(x)'), 'tanh')", () => rewrite(P('exp(x)'), 'tanh'), "(tanh(x/2) + 1)/(1 - tanh(x/2))"],
    ["rewrite(P('exp(2*log(x))'), 'Pow')", () => rewrite(P('exp(2*log(x))'), 'Pow'), "x**2"],
    ["rewrite(P('exp(y*log(x))'), 'Pow')", () => rewrite(P('exp(y*log(x))'), 'Pow'), "x**y"],
    ["rewrite(P('exp(x)'), 'Pow')", () => rewrite(P('exp(x)'), 'Pow'), "exp(x)"],
    ["rewrite(P('exp(x*y)'), 'Pow')", () => rewrite(P('exp(x*y)'), 'Pow'), "exp(x*y)"],
    ["rewrite(P('exp(I*pi/3)'), 'sqrt')", () => rewrite(P('exp(I*pi/3)'), 'sqrt'), "1/2 + sqrt(3)*I/2"],
    ["rewrite(P('exp(x)'), 'sqrt')", () => rewrite(P('exp(x)'), 'sqrt'), "exp(x)"],
    ["rewrite(P('exp(I*pi*x)'), 'sqrt')", () => rewrite(P('exp(I*pi*x)'), 'sqrt'), "exp(I*pi*x)"],
    ["rewrite(P('exp(I*pi/7)'), 'sqrt')", () => rewrite(P('exp(I*pi/7)'), 'sqrt'), "exp(I*pi/7)"],
    ["rewrite(P('sinh(x)'), 'exp')", () => rewrite(P('sinh(x)'), 'exp'), "exp(x)/2 - exp(-x)/2"],
    ["rewrite(P('sinh(x)'), 'cosh')", () => rewrite(P('sinh(x)'), 'cosh'), "sinh(x)"],
    ["rewrite(P('sinh(x)'), 'sin')", () => rewrite(P('sinh(x)'), 'sin'), "sinh(x)"],
    ["rewrite(P('sinh(x)'), 'tanh')", () => rewrite(P('sinh(x)'), 'tanh'), "2*tanh(x/2)/(1 - tanh(x/2)**2)"],
    ["rewrite(P('cosh(x)'), 'exp')", () => rewrite(P('cosh(x)'), 'exp'), "exp(x)/2 + exp(-x)/2"],
    ["rewrite(P('cosh(x)'), 'cos')", () => rewrite(P('cosh(x)'), 'cos'), "cos(I*x)"],
    ["rewrite(P('cosh(x)'), 'sinh')", () => rewrite(P('cosh(x)'), 'sinh'), "-I*sinh(x + I*pi/2)"],
    ["rewrite(P('cosh(x)'), 'tanh')", () => rewrite(P('cosh(x)'), 'tanh'), "(tanh(x/2)**2 + 1)/(1 - tanh(x/2)**2)"],
    ["rewrite(P('tanh(x)'), 'exp')", () => rewrite(P('tanh(x)'), 'exp'), "(exp(x) - exp(-x))/(exp(x) + exp(-x))"],
    ["rewrite(P('tanh(x)'), 'cosh')", () => rewrite(P('tanh(x)'), 'cosh'), "I*cosh(-x + I*pi/2)/cosh(x)"],
    ["rewrite(P('tanh(x)'), 'sinh')", () => rewrite(P('tanh(x)'), 'sinh'), "I*sinh(x)/sinh(-x + I*pi/2)"],
    ["rewrite(P('tanh(x)'), 'tan')", () => rewrite(P('tanh(x)'), 'tan'), "-I*tan(I*x)"],
    ["rewrite(P('asin(x)'), 'log')", () => rewrite(P('asin(x)'), 'log'), "-I*log(I*x + sqrt(1 - x**2))"],
    ["rewrite(P('asin(x)'), 'acos')", () => rewrite(P('asin(x)'), 'acos'), "-acos(x) + pi/2"],
    ["rewrite(P('asin(x)'), 'atan')", () => rewrite(P('asin(x)'), 'atan'), "2*atan(x/(sqrt(1 - x**2) + 1))"],
    ["rewrite(P('acos(x)'), 'log')", () => rewrite(P('acos(x)'), 'log'), "I*log(I*x + sqrt(1 - x**2)) + pi/2"],
    ["rewrite(P('acos(x)'), 'asin')", () => rewrite(P('acos(x)'), 'asin'), "-asin(x) + pi/2"],
    ["rewrite(P('acos(x)'), 'atan')", () => rewrite(P('acos(x)'), 'atan'), "pi*(-x*sqrt(x**(-2)) + 1)/2 + atan(sqrt(1 - x**2)/x)"],
    ["rewrite(P('atan(x)'), 'log')", () => rewrite(P('atan(x)'), 'log'), "I*(log(-I*x + 1) - log(I*x + 1))/2"],
    ["rewrite(P('atan(x)'), 'asin')", () => rewrite(P('atan(x)'), 'asin'), "(-asin(1/sqrt(x**2 + 1)) + pi/2)*sqrt(x**2)/x"],
    ["rewrite(P('atan(x)'), 'acos')", () => rewrite(P('atan(x)'), 'acos'), "sqrt(x**2)*acos(1/sqrt(x**2 + 1))/x"],
    ["rewrite(P('atan2(y, x)'), 'log')", () => rewrite(P('atan2(y, x)'), 'log'), "-I*log((x + I*y)/sqrt(x**2 + y**2))"],
    ["rewrite(P('atan2(y, x)'), 'atan')", () => rewrite(P('atan2(y, x)'), 'atan'), "Piecewise((2*atan(y/(x + sqrt(x**2 + y**2))), Ne(y, 0)), (pi, re(x) < 0), (0, Ne(x, 0)), (nan, True))"],
    ["rewrite(P('Abs(x)'), 'sign')", () => rewrite(P('Abs(x)'), 'sign'), "x/sign(x)"],
    ["rewrite(P('Abs(x)'), 'conjugate')", () => rewrite(P('Abs(x)'), 'conjugate'), "sqrt(x*conjugate(x))"],
    ["rewrite(P('Abs(r)'), 'Piecewise')", () => rewrite(P('Abs(r)'), 'Piecewise'), "Piecewise((r, r >= 0), (-r, True))"],
    ["rewrite(P('Abs(x)'), 'Piecewise')", () => rewrite(P('Abs(x)'), 'Piecewise'), "Abs(x)"],
    ["rewrite(P('sign(x)'), 'Abs')", () => rewrite(P('sign(x)'), 'Abs'), "Piecewise((0, Eq(x, 0)), (x/Abs(x), True))"],
    ["rewrite(P('sign(r)'), 'Piecewise')", () => rewrite(P('sign(r)'), 'Piecewise'), "Piecewise((1, r > 0), (-1, r < 0), (0, True))"],
    ["rewrite(P('sign(x)'), 'Piecewise')", () => rewrite(P('sign(x)'), 'Piecewise'), "sign(x)"],
    ["rewrite(P('Abs(x)'), 'abs')", () => rewrite(P('Abs(x)'), 'abs'), "Abs(x)"],
    ["rewrite(P('factorial(n)'), 'gamma')", () => rewrite(P('factorial(n)'), 'gamma'), "gamma(n + 1)"],
    ["rewrite(P('gamma(x)'), 'factorial')", () => rewrite(P('gamma(x)'), 'factorial'), "factorial(x - 1)"],
    ["rewrite(P('binomial(n, k)'), 'factorial')", () => rewrite(P('binomial(n, k)'), 'factorial'), "factorial(n)/(factorial(k)*factorial(-k + n))"],
    ["rewrite(P('binomial(n, k)'), 'gamma')", () => rewrite(P('binomial(n, k)'), 'gamma'), "gamma(n + 1)/(gamma(k + 1)*gamma(-k + n + 1))"],
    ["rewrite(P('binomial(n, kk)'), 'FallingFactorial')", () => rewrite(P('binomial(n, kk)'), 'FallingFactorial'), "FallingFactorial(n, kk)/factorial(kk)"],
    ["rewrite(P('binomial(n, k)'), 'FallingFactorial')", () => rewrite(P('binomial(n, k)'), 'FallingFactorial'), "binomial(n, k)"],
    ["rewrite(P('catalan(n)'), 'binomial')", () => rewrite(P('catalan(n)'), 'binomial'), "binomial(2*n, n)/(n + 1)"],
    ["rewrite(P('catalan(n)'), 'factorial')", () => rewrite(P('catalan(n)'), 'factorial'), "factorial(2*n)/(factorial(n)*factorial(n + 1))"],
    ["rewrite(P('catalan(n)'), 'gamma')", () => rewrite(P('catalan(n)'), 'gamma'), "4**n*gamma(n + 1/2)/(sqrt(pi)*gamma(n + 2))"],
    ["rewrite(P('harmonic(n)'), 'polygamma')", () => rewrite(P('harmonic(n)'), 'polygamma'), "polygamma(0, n + 1) + EulerGamma"],
    ["rewrite(P('harmonic(n, 2)'), 'polygamma')", () => rewrite(P('harmonic(n, 2)'), 'polygamma'), "-polygamma(1, n + 1) + pi**2/6"],
    ["rewrite(P('harmonic(n, x)'), 'polygamma')", () => rewrite(P('harmonic(n, x)'), 'polygamma'), "harmonic(n, x)"],
    ["rewrite(P('harmonic(n)'), 'digamma')", () => rewrite(P('harmonic(n)'), 'digamma'), "polygamma(0, n + 1) + EulerGamma"],
    ["rewrite(P('polygamma(0, x)'), 'harmonic')", () => rewrite(P('polygamma(0, x)'), 'harmonic'), "harmonic(x - 1) - EulerGamma"],
    ["rewrite(P('polygamma(2, x)'), 'harmonic')", () => rewrite(P('polygamma(2, x)'), 'harmonic'), "2*harmonic(x - 1, 3) - 2*zeta(3)"],
    ["rewrite(P('polygamma(y, x)'), 'harmonic')", () => rewrite(P('polygamma(y, x)'), 'harmonic'), "polygamma(y, x)"],
    ["rewrite(P('li(x)'), 'Ei')", () => rewrite(P('li(x)'), 'Ei'), "Ei(log(x))"],
    ["rewrite(P('li(x)'), 'Li')", () => rewrite(P('li(x)'), 'Li'), "Li(x) + li(2)"],
    ["rewrite(P('li(x)'), 'Shi')", () => rewrite(P('li(x)'), 'Shi'), "-log(1/log(x))/2 + log(log(x))/2 + Chi(log(x)) - Shi(log(x))"],
    ["rewrite(P('li(x)'), 'Chi')", () => rewrite(P('li(x)'), 'Chi'), "-log(1/log(x))/2 + log(log(x))/2 + Chi(log(x)) - Shi(log(x))"],
    ["rewrite(P('li(x)'), 'Si')", () => rewrite(P('li(x)'), 'Si'), "-log(I*log(x)) - log(1/log(x))/2 + log(log(x))/2 + Ci(I*log(x)) + Shi(log(x))"],
    ["rewrite(P('li(x)'), 'Ci')", () => rewrite(P('li(x)'), 'Ci'), "-log(I*log(x)) - log(1/log(x))/2 + log(log(x))/2 + Ci(I*log(x)) + Shi(log(x))"],
    ["rewrite(P('Li(x)'), 'li')", () => rewrite(P('Li(x)'), 'li'), "li(x) - li(2)"],
    ["rewrite(P('Ei(x)'), 'Shi')", () => rewrite(P('Ei(x)'), 'Shi'), "Chi(x) + Shi(x)"],
    ["rewrite(P('Ei(r)'), 'Chi')", () => rewrite(P('Ei(r)'), 'Chi'), "Chi(r) + Shi(r)"],
    ["rewrite(P('Ei(-p)'), 'Si')", () => rewrite(P('Ei(-p)'), 'Si'), "Chi(-p) - Shi(p) - I*pi"],
    ["rewrite(P('Ei(log(x))'), 'li')", () => rewrite(P('Ei(log(x))'), 'li'), "li(x)"],
    ["rewrite(P('Ei(x)'), 'li')", () => rewrite(P('Ei(x)'), 'li'), "li(exp(x))"],
    ["rewrite(P('expint(y, x)'), 'uppergamma')", () => rewrite(P('expint(y, x)'), 'uppergamma'), "x**(y - 1)*uppergamma(1 - y, x)"],
    ["rewrite(P('Ei(x)'), 'expint')", () => rewrite(P('Ei(x)'), 'expint'), "-expint(1, x*exp_polar(I*pi)) - I*pi"],
    ["rewrite(P('Ci(x)'), 'expint')", () => rewrite(P('Ci(x)'), 'expint'), "-expint(1, x*exp_polar(-I*pi/2))/2 - expint(1, x*exp_polar(I*pi/2))/2"],
    ["rewrite(P('Si(x)'), 'expint')", () => rewrite(P('Si(x)'), 'expint'), "-I*(-expint(1, x*exp_polar(-I*pi/2))/2 + expint(1, x*exp_polar(I*pi/2))/2) + pi/2"],
    ["rewrite(P('Shi(x)'), 'expint')", () => rewrite(P('Shi(x)'), 'expint'), "expint(1, x)/2 - expint(1, x*exp_polar(I*pi))/2 - I*pi/2"],
    ["rewrite(P('Chi(x)'), 'expint')", () => rewrite(P('Chi(x)'), 'expint'), "-expint(1, x)/2 - expint(1, x*exp_polar(I*pi))/2 - I*pi/2"],
    ["rewrite(P('frac(x)'), 'floor')", () => rewrite(P('frac(x)'), 'floor'), "x - floor(x)"],
    ["rewrite(P('frac(x)'), 'ceiling')", () => rewrite(P('frac(x)'), 'ceiling'), "x + ceiling(-x)"],
    ["rewrite(P('floor(x)'), 'ceiling')", () => rewrite(P('floor(x)'), 'ceiling'), "-ceiling(-x)"],
    ["rewrite(P('ceiling(x)'), 'floor')", () => rewrite(P('ceiling(x)'), 'floor'), "-floor(-x)"],
    ["rewrite(P('floor(x)'), 'frac')", () => rewrite(P('floor(x)'), 'frac'), "x - frac(x)"],
    ["rewrite(P('ceiling(x)'), 'frac')", () => rewrite(P('ceiling(x)'), 'frac'), "x + frac(-x)"],
    ["rewrite(P('sin(x) + cos(y)'), 'exp')", () => rewrite(P('sin(x) + cos(y)'), 'exp'), "-I*(exp(I*x) - exp(-I*x))/2 + exp(I*y)/2 + exp(-I*y)/2"],
    ["rewrite(P('sin(x)*exp(y)'), 'cos')", () => rewrite(P('sin(x)*exp(y)'), 'cos'), "(sinh(y) + cosh(y))*cos(x - pi/2)"],
    ["rewrite(P('x'), 'exp')", () => rewrite(P('x'), 'exp'), "x"],
    ["rewrite(P('sin(cos(x))'), 'exp')", () => rewrite(P('sin(cos(x))'), 'exp'), "-I*(-exp(I*(-exp(I*x)/2 - exp(-I*x)/2)) + exp(I*(exp(I*x)/2 + exp(-I*x)/2)))/2"],
    ["rewrite(P('sin(x) + cos(x)'), 'exp', { pattern: ['sin'] })", () => rewrite(P('sin(x) + cos(x)'), 'exp', { pattern: ['sin'] }), "-I*(exp(I*x) - exp(-I*x))/2 + cos(x)"],
    ["rewrite(P('sin(x) + cos(x)'), 'exp', { pattern: ['tanh'] })", () => rewrite(P('sin(x) + cos(x)'), 'exp', { pattern: ['tanh'] }), "sin(x) + cos(x)"],
    ["rewrite(P('sin(sin(x))'), 'exp', { deep: false })", () => rewrite(P('sin(sin(x))'), 'exp', { deep: false }), "-I*(-exp(-exp(I*x)/2 + exp(-I*x)/2) + exp(exp(I*x)/2 - exp(-I*x)/2))/2"],
    ["rewrite(P('harmonic(n)'), 'Sum').toString().replace(/_k\\b/g,'k')", () => rewrite(P('harmonic(n)'), 'Sum').toString().replace(/_k\b/g,'k'), "Sum(1/k, (k, 1, n))"],
    ["rewrite(P('harmonic(n, 3)'), 'Sum').toString().replace(/_k\\b/g,'k')", () => rewrite(P('harmonic(n, 3)'), 'Sum').toString().replace(/_k\b/g,'k'), "Sum(k**(-3), (k, 1, n))"],
    ["rewrite(P('Si(x)'), 'sinc').toString().replace(/_t\\b/g,'t')", () => rewrite(P('Si(x)'), 'sinc').toString().replace(/_t\b/g,'t'), "Integral(sinc(t), (t, 0, x))"],
    ["rewrite(P('Si(x)'), 'Integral').toString().replace(/_t\\b/g,'t')", () => rewrite(P('Si(x)'), 'Integral').toString().replace(/_t\b/g,'t'), "Integral(sinc(t), (t, 0, x))"],
    ["rewrite(P('Ei(x)'), 'Integral').toString().replace(/_t\\b/g,'t')", () => rewrite(P('Ei(x)'), 'Integral').toString().replace(/_t\b/g,'t'), "Integral(exp(t)/t, (t, -oo, x))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe('rewrite: user-defined functions and the method form', () => {
  // SymPy: class mysin(Function): def _eval_rewrite_as_cos(self, a): return cos(a - pi/2, evaluate=False)
  const mysin = defineFunction('mysin', { rewrite: { cos: (a) => fn('cos', [sub(a, P('pi/2'))], { evaluate: false }) } });
  it('uses the rules of a defined function', () => {
    expect(rewrite(mysin(x), 'cos').toString()).toBe('cos(x - pi/2)');
    expect(rewrite(mysin(x), 'sin').toString()).toBe('mysin(x)');
    // SymPy prints mysin(x) + cos(x - pi/2); the term order of a user function is a printer matter
    expect(rewrite(add(mysin(x), P('sin(x)')), 'cos', { pattern: ['sin'] }).args.map(String).sort()).toEqual(['cos(x - pi/2)', 'mysin(x)']);
    expect(rewrite(add(mysin(x), P('sin(x)')), 'cos', { pattern: ['mysin'] }).toString()).toBe('sin(x) + cos(x - pi/2)');
    expect(rewrite(add(mysin(x), P('sin(x)')), 'cos').toString()).toBe('2*cos(x - pi/2)');
  });
  it('rewrites inside exp and through the method', () => {
    expect(P('exp(sin(x))').rewrite('exp').toString()).toBe('exp(-I*(exp(I*x) - exp(-I*x))/2)');
  });
});
