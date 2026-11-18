// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/rewrite.ts.

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { I, SymFunction, add, defineFunction, fn, harmonic, mul, parse, rational, rewrite, sstr, sub, subs, symbol, symbols, toComplex, zeta } from '../../src';
import { registerRewrite, rewriteRules } from '../../src/core/nodes';

it('rewrites harmonic sums to polygamma or zeta where the order allows it', () => {
  const n = symbol('n');
  const m = symbol('m', { integer: true, positive: true });
  const p = symbol('p', { positive: true });
  const order = add(p, 1);
  expect(rewrite(harmonic(n), 'tractable')).toEqual(rewrite(harmonic(n), 'polygamma'));
  expect(rewrite(harmonic(n), 'zeta')).toEqual(rewrite(harmonic(n), 'polygamma'));
  expect(rewrite(harmonic(n, m), 'tractable')).toEqual(rewrite(harmonic(n, m), 'polygamma'));
  expect(rewrite(harmonic(n, p), 'tractable')).toEqual(harmonic(n, p));
  const difference = add(zeta(order), mul(-1, zeta(order, add(n, 1))));
  expect(rewrite(harmonic(n, order), 'tractable')).toEqual(difference);
  expect(rewrite(harmonic(n, order), 'zeta')).toEqual(difference);
});

const [x, y, n, k] = symbols('x y n k');
const r = symbol('r', { real: true });
const p = symbol('p', { positive: true });
const kk = symbol('kk', { integer: true });
const P = (s: string) => parse(s, { symbols: [x, y, n, k, r, p, kk] });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

it('rewrites exact tangent and cotangent values through sine and cosine radicals', () => {
  const angle = P('2*pi/5');
  const raw = { evaluate: false };
  expect(sstr(rewrite(fn('tan', [angle], raw), 'sqrt'))).toBe('sqrt(sqrt(5)/8 + 5/8)/(-1/4 + sqrt(5)/4)');
  expect(sstr(rewrite(fn('cot', [angle], raw), 'sqrt'))).toBe('(-1/4 + sqrt(5)/4)/sqrt(sqrt(5)/8 + 5/8)');
  expect(rewrite(fn('tan', [x], raw), 'sqrt').equals(fn('tan', [x]))).toBe(true);
  expect(sstr(rewrite(fn('tan', [mul(I, x)], raw), 'sqrt'))).toBe('I*sinh(x)/cosh(x)');
  expect(sstr(rewrite(P('arg(re(x) + I*re(y))'), 'atan2'))).toBe('atan2(re(y), re(x))');
});

it('rewrites Piecewise to ITE only with a Boolean value on every branch', () => {
  expect(sstr(rewrite(P('Piecewise((x < 1, x > 1), (y < 2, True))'), 'ITE'))).toBe('ITE(x > 1, x < 1, y < 2)');
  for (const source of ['Piecewise((x < 1, x > 1))', 'Piecewise((x < 1, x > 1), (3, True))', 'Piecewise((3, x > 1), (y < 2, True))']) {
    const value = P(source);
    expect(rewrite(value, 'ITE').equals(value)).toBe(true);
  }
});

describe('rewrite', () => {
  it('rewrites trigonometric functions like SymPy', async () => {
    const { rewrite, sin, cos, tan, mul, add, I, str, symbols: syms } = await import('../../src');
    const [t] = syms('t');
    expect(str(rewrite(add(cos(t!), mul(I, sin(t!))), 'exp'))).toBe('exp(I*t)');
    expect(str(rewrite(tan(t!), 'sin'))).toBe('2*sin(t)**2/sin(2*t)');
    expect(str(rewrite(sin(t!), 'cos'))).toBe('cos(t - pi/2)');
  });
});

it('rewrites incomplete beta as an integral and normalizes by the full interval', () => {
  const integrand = fn('betainc', [x, y, rational(1, 3), rational(1, 2)]);
  expect(String(rewrite(integrand, 'Integral'))).toBe('Integral(_t**(x - 1)*(1 - _t)**(y - 1), (_t, 1/3, 1/2))');
  const normalized = fn('betainc_regularized', integrand.args);
  expect(String(rewrite(normalized, 'Integral'))).toContain('(_t, 0, 1)');
  expect(rewrite(fn('betainc_regularized', [x, y, 0, 1]), 'Integral').equals(1)).toBe(true);
});

it('rewrites the gamma derivatives in terms of polygamma, harmonic numbers and zeta', () => {
  const digamma = fn('digamma', [x], { evaluate: false });
  const trigamma = fn('trigamma', [x], { evaluate: false });
  expect(rewrite(digamma, 'polygamma').equals(P('polygamma(0,x)'))).toBe(true);
  expect(rewrite(trigamma, 'polygamma').equals(P('polygamma(1,x)'))).toBe(true);
  expect(rewrite(digamma, 'harmonic').equals(P('harmonic(x-1)-EulerGamma'))).toBe(true);
  expect(rewrite(trigamma, 'harmonic').equals(P('pi**2/6-harmonic(x-1,2)'))).toBe(true);
  expect(rewrite(trigamma, 'zeta').equals(P('zeta(2,x)'))).toBe(true);
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

describe('rewrite(..., log) of the inverse trigonometric and hyperbolic functions (SymPy _eval_rewrite_as_log)', () => {
  it('matches SymPy', () => {
    const cases: [string, string][] = [
      ['asinh(x)', 'log(x + sqrt(x**2 + 1))'],
      ['asinh(2*y + 1)', 'log(2*y + sqrt((2*y + 1)**2 + 1) + 1)'],
      ['acosh(x)', 'log(x + sqrt(x - 1)*sqrt(x + 1))'],
      ['acosh(2*y + 1)', 'log(sqrt(2)*sqrt(y)*sqrt(2*y + 2) + 2*y + 1)'],
      ['atanh(x)', '-log(1 - x)/2 + log(x + 1)/2'],
      ['atanh(2*y + 1)', '-log(-2*y)/2 + log(2*y + 2)/2'],
      ['acoth(x)', '-log(1 - 1/x)/2 + log(1 + 1/x)/2'],
      ['acoth(2*y + 1)', '-log(1 - 1/(2*y + 1))/2 + log(1 + 1/(2*y + 1))/2'],
      ['asech(x)', 'log(sqrt(-1 + 1/x)*sqrt(1 + 1/x) + 1/x)'],
      ['asech(2*y + 1)', 'log(sqrt(-1 + 1/(2*y + 1))*sqrt(1 + 1/(2*y + 1)) + 1/(2*y + 1))'],
      ['acsch(x)', 'log(sqrt(1 + x**(-2)) + 1/x)'],
      ['acsch(2*y + 1)', 'log(sqrt(1 + (2*y + 1)**(-2)) + 1/(2*y + 1))'],
      ['asin(x)', '-I*log(I*x + sqrt(1 - x**2))'],
      ['asin(2*y + 1)', '-I*log(sqrt(1 - (2*y + 1)**2) + I*(2*y + 1))'],
      ['acos(x)', 'I*log(I*x + sqrt(1 - x**2)) + pi/2'],
      ['acos(2*y + 1)', 'I*log(sqrt(1 - (2*y + 1)**2) + I*(2*y + 1)) + pi/2'],
      ['atan(x)', 'I*(log(-I*x + 1) - log(I*x + 1))/2'],
      ['atan(2*y + 1)', 'I*(log(-I*(2*y + 1) + 1) - log(I*(2*y + 1) + 1))/2'],
      ['acot(x)', 'I*(log(1 - I/x) - log(1 + I/x))/2'],
      ['acot(2*y + 1)', 'I*(log(1 - I/(2*y + 1)) - log(1 + I/(2*y + 1)))/2'],
      ['asec(x)', 'I*log(sqrt(1 - 1/x**2) + I/x) + pi/2'],
      ['asec(2*y + 1)', 'I*log(sqrt(1 - 1/(2*y + 1)**2) + I/(2*y + 1)) + pi/2'],
      ['acsc(x)', '-I*log(sqrt(1 - 1/x**2) + I/x)'],
      ['acsc(2*y + 1)', '-I*log(sqrt(1 - 1/(2*y + 1)**2) + I/(2*y + 1))'],
    ];
    for (const [e, r] of cases) expect(String(rewrite(parse(e), 'log'))).toBe(r);
  });
});

describe('rewrite of a power as exp (SymPy Pow._eval_rewrite_as_exp)', () => {
  it('writes b**e as exp(e*log(b))', async () => {
    const { I, Pow: PowNode, S: s, exp: e, pow, sqrt } = await import('../../src');
    expect(String(rewrite(pow(x, y), 'exp'))).toBe('exp(y*log(x))');
    expect(String(rewrite(pow(7, x), 'exp'))).toBe('exp(x*log(7))');
    expect(String(rewrite(pow(I, I), 'exp'))).toBe('exp(-pi/2)');
    expect(String(rewrite(P('(2 + 3*I)**x'), 'exp'))).toBe('exp(x*(log(sqrt(13)) + I*atan(3/2)))');
    // a power of a symbol to an exponent without symbols stays a power
    expect(String(rewrite(pow(x, 2), 'exp'))).toBe('x**2');
    // a power of 0 or one that contains exp is kept
    expect(String(rewrite(new PowNode(s.Zero, x), 'exp'))).toBe('0**x');
    expect(String(rewrite(pow(e(x), y), 'exp'))).toBe('exp(x)**y');
    expect(String(rewrite(pow(x, e(y)), 'exp'))).toBe('x**exp(y)');
    expect(String(rewrite(sqrt(2), 'exp'))).toBe('sqrt(2)');
  });
});

describe('rewrites between trigonometric, hyperbolic and inverse functions (SymPy _eval_rewrite_as_*)', () => {
  const x = symbol('x');
  /** e and its rewrite agree at a point of the domain (the value of x). */
  const agrees = (f: string, target: string, at: number): void => {
    const e = parse(f, { symbols: [x] });
    const r = rewrite(e, target);
    expect(r.has(e), `${f} -> ${target}`).toBe(false);
    const v = (u: typeof e) => toComplex(subsNum(u, at));
    const [a, b] = [v(e), v(r)];
    expect(Math.hypot(a.re - b.re, a.im - b.im), `${f} -> ${target}: ${sstr(r)}`).toBeLessThan(1e-9);
  };
  const subsNum = (e: ReturnType<typeof parse>, at: number) => subs(e, [[x, rational(Math.round(at * 1000), 1000)]]);

  it('rewrites the reciprocal trigonometric functions', () => {
    for (const [f, targets] of [
      ['sin(x)', ['cot', 'csc', 'sec']], ['cos(x)', ['cot', 'sec', 'csc']], ['tan(x)', ['cot', 'sec', 'csc']],
      ['cot(x)', ['exp', 'sin', 'cos', 'sincos', 'tan', 'sec', 'csc']], ['sec(x)', ['cot', 'cos', 'sincos', 'sin', 'tan', 'csc', 'exp']],
      ['csc(x)', ['sin', 'sincos', 'cot', 'cos', 'sec', 'tan', 'exp']], ['cot(sin(x))', ['exp']],
    ] as const) for (const t of targets) agrees(f, t, 0.7);
  });

  it('rewrites the hyperbolic functions', () => {
    for (const [f, targets] of [
      ['sinh(x)', ['coth']], ['cosh(x)', ['coth']], ['tanh(x)', ['coth']], ['coth(x)', ['sinh', 'cosh', 'tanh']],
      ['csch(x)', ['cosh', 'exp', 'tanh', 'coth']], ['sech(x)', ['sinh', 'exp', 'tanh', 'coth']], ['sinc(x)', ['sin']],
    ] as const) for (const t of targets) agrees(f, t, 0.7);
  });

  it('rewrites the inverse trigonometric functions', () => {
    for (const [f, targets, at] of [
      ['asin(x)', ['acot', 'asec', 'acsc'], 0.4], ['acos(x)', ['acot', 'asec', 'acsc'], 0.4], ['atan(x)', ['acot', 'asec', 'acsc'], 0.4],
      ['acot(x)', ['asin', 'acos', 'atan', 'asec', 'acsc'], 0.4], ['asec(x)', ['asin', 'acos', 'atan', 'acot', 'acsc'], 1.7],
      ['acsc(x)', ['asin', 'acos', 'atan', 'acot', 'asec'], 1.7],
    ] as const) for (const t of targets) agrees(f, t, at);
  });

  it('rewrites the inverse hyperbolic functions', () => {
    for (const [f, targets, at] of [
      ['asinh(x)', ['atanh', 'asin', 'acos'], 0.4], ['acosh(x)', ['asin', 'asinh', 'atanh'], 1.7], ['atanh(x)', ['asinh'], 0.4],
      ['acoth(x)', ['atanh', 'asinh'], 1.7], ['asech(x)', ['acosh', 'asinh', 'atanh'], 0.4], ['acsch(x)', ['asinh', 'atanh'], 0.4],
    ] as const) for (const t of targets) agrees(f, t, at);
  });

  it('writes Exp1, re, im, Abs, Max and Min in other terms', () => {
    expect(sstr(rewrite(parse('E'), 'cos'))).toBe('sinh(1) + cosh(1)');
    expect(sstr(rewrite(parse('E'), 'sin'))).toBe('sinh(1) + cosh(1)');
    expect(sstr(rewrite(parse('re(x)', { symbols: [x] }), 'im'))).toBe('x - I*im(x)');
    expect(sstr(rewrite(parse('im(x)', { symbols: [x] }), 're'))).toBe('-I*(x - re(x))');
    const i = symbol('i', { imaginary: true });
    expect(sstr(rewrite(parse('Abs(i)', { symbols: [i] }), 'Piecewise'))).toBe('Piecewise((I*i, I*i >= 0), (-I*i, True))');
    expect(sstr(rewrite(parse('Abs(x)', { symbols: [x] }), 'Piecewise'))).toBe('Abs(x)');
    const [a, b, c] = symbols('a b c');
    expect(sstr(rewrite(parse('Max(a, b)', { symbols: [a, b] }), 'Piecewise'))).toBe('Piecewise((a, a >= b), (b, True))');
    expect(sstr(rewrite(parse('Min(a, b, c)', { symbols: [a, b, c] }), 'Piecewise'))).toBe('Piecewise((a, (a <= b) & (a <= c)), (b, b <= c), (c, True))');
    expect(sstr(rewrite(parse('cot(log(x))', { symbols: [x] }), 'Pow'))).toBe('-I*(x**I + x**(-I))/(-x**I + x**(-I))');
    expect(sstr(rewrite(parse('cot(x)', { symbols: [x] }), 'Pow'))).toBe('cot(x)');
    expect(sstr(rewrite(parse('sec(log(x))', { symbols: [x] }), 'Pow'))).toBe('1/(x**I/2 + 1/(2*x**I))');
    expect(sstr(rewrite(parse('sec(x)', { symbols: [x] }), 'Pow'))).toBe('sec(x)');
  });

  it('rewrites trigonometric functions with Bessel functions', () => {
    for (const f of ['sin(x)', 'cos(x)', 'tan(x)', 'cot(x)', 'sec(x)', 'csc(x)']) agrees(f, 'besselj', 0.7);
  });
});

it('recognizes undefined functions in rewrite patterns and rewrites Ci using E1', () => {
  const f = SymFunction('f')(x);
  expect(rewrite(f, 'exp', { pattern: ['f'] })).toBe(f);
  expect(String(rewrite(P('Ci(x)'), 'expint'))).toBe('-expint(1, x*exp_polar(-I*pi/2))/2 - expint(1, x*exp_polar(I*pi/2))/2');
});

it('passes rewrite hints from the expression to a rule in the core registry', () => {
  const name = 'rewriteHintExample';
  const f = SymFunction(name)(x);
  registerRewrite(name, 'exp', (_args, _self, hints) => hints?.['replacement']);
  try {
    expect(f.rewrite('exp', { pattern: [name], hints: { replacement: y } })).toBe(y);
    expect(rewrite(f, 'exp', { pattern: [name] })).toBe(f);
  } finally {
    delete rewriteRules[name];
  }
});

it('rewrites special functions in unevaluated form', () => {
  for (const [name, args, target, expected] of [
    ['sin', [x], 'sinc', 'x*sinc(x)'],
    ['coth', [x], 'tractable', '(exp(x) + exp(-x))/(exp(x) - exp(-x))'],
    ['factorial2', [x], 'gamma', '2**(x/2)*gamma(x/2 + 1)*Piecewise((1, Eq(Mod(x, 2), 0)), (sqrt(2)/sqrt(pi), Eq(Mod(x, 2), 1)))'],
    ['beta', [x, y], 'gamma', 'gamma(x)*gamma(y)/gamma(x + y)'],
    ['loggamma', [x], 'intractable', 'log(gamma(x))'],
    ['lowergamma', [x, y], 'uppergamma', 'gamma(x) - uppergamma(x, y)'],
    ['uppergamma', [x, y], 'lowergamma', 'gamma(x) - lowergamma(x, y)'],
    ['uppergamma', [x, y], 'expint', 'y**x*expint(1 - x, y)'],
    ['lowergamma', [x, y], 'expint', '-y**x*expint(1 - x, y) + gamma(x)'],
    ['lowergamma', [-1, y], 'expint', 'lowergamma(-1, y)'],
    ['lowergamma', [symbol('j', { integer: true, positive: true }), y], 'expint', '-y**j*expint(1 - j, y) + gamma(j)'],
    ['polygamma', [1, x], 'zeta', 'zeta(2, x)'],
    ['polygamma', [0, x], 'zeta', 'polygamma(0, x)'],
    ['polygamma', [y, x], 'zeta', 'polygamma(y, x)'],
    ['zeta', [2], 'bernoulli', 'pi**2/6'],
    ['zeta', [x], 'bernoulli', 'bernoulli(1 - x)/(x - 1)'],
    ['zeta', [2, x], 'bernoulli', 'bernoulli(-1, x)'],
    ['zeta', [-2], 'bernoulli', '0'],
  ] as const) expect(String(rewrite(fn(name, args, { evaluate: false }), target))).toBe(expected);
});
