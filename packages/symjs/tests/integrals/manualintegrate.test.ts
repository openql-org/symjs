// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/manualintegrate.ts (SymPy sqrt_quadratic_rule). Expected values are those of SymPy 1.14
// manualintegrate.

import { describe, expect, it } from 'vitest';
import { Sym, parse, sstr } from '../../src';
import { sqrtQuadraticRule } from '../../src/integrals/manualintegrate';

const x = new Sym('x');
const M = (s: string): string => {
  const r = sqrtQuadraticRule(parse(s), x);
  return r === undefined ? 'None' : sstr(r);
};

describe('sqrt_quadratic_rule', () => {
  it.each([
    ['sqrt(x**2+a*x+b)', '(a/4 + x/2)*sqrt(a*x + b + x**2) + (-a**2/8 + b/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))'],
    ['x*sqrt(x**2+a*x+b)', '(-a*b/12 - a*(-a**2/8 + b/3)/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True)) + sqrt(a*x + b + x**2)*(-a**2/8 + a*x/12 + b/3 + x**2/3)'],
    ['x*sqrt(a*x**2+b*x+c)', 'Piecewise(((-b*c/(12*a) - b*(c/3 - b**2/(8*a))/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + (x**2/3 + b*x/(12*a) + (c/3 - b**2/(8*a))/a)*sqrt(a*x**2 + b*x + c), Ne(a, 0)), (2*(-c*(b*x + c)**(3/2)/3 + (b*x + c)**(5/2)/5)/b**2, Ne(b, 0)), (sqrt(c)*x**2/2, True))'],
    ['sqrt(a*x**2+b*x+c)', 'Piecewise(((c/2 - b**2/(8*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + (x/2 + b/(4*a))*sqrt(a*x**2 + b*x + c), Ne(a, 0)), (2*(b*x + c)**(3/2)/(3*b), Ne(b, 0)), (sqrt(c)*x, True))'],
    ['(x**2+1)*sqrt(a*x**2+b*x+c)', 'Piecewise(((c - b*(b - b*c/(12*a) - 3*b*(a + c/4 - 5*b**2/(48*a))/(4*a))/(2*a) - c*(a + c/4 - 5*b**2/(48*a))/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + sqrt(a*x**2 + b*x + c)*(x**3/4 + b*x**2/(24*a) + x*(a + c/4 - 5*b**2/(48*a))/(2*a) + (b - b*c/(12*a) - 3*b*(a + c/4 - 5*b**2/(48*a))/(4*a))/a), Ne(a, 0)), (2*(-2*c*(b*x + c)**(5/2)/(5*b**2) + (b**2 + c**2)*(b*x + c)**(3/2)/(3*b**2) + (b*x + c)**(7/2)/(7*b**2))/b, Ne(b, 0)), (sqrt(c)*(x**3/3 + x), True))'],
    ['x**2/sqrt(x**2+a*x+b)', '(-3*a/4 + x/2)*sqrt(a*x + b + x**2) + (3*a**2/8 - b/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))'],
    ['x**3/sqrt(a*x**2+b*x+c)', 'Piecewise(((-b*(-2*c/(3*a) + 5*b**2/(8*a**2))/(2*a) + 5*b*c/(12*a**2))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + (x**2/(3*a) + (-2*c/(3*a) + 5*b**2/(8*a**2))/a - 5*b*x/(12*a**2))*sqrt(a*x**2 + b*x + c), Ne(a, 0)), (2*(-c**3*sqrt(b*x + c) + c**2*(b*x + c)**(3/2) - 3*c*(b*x + c)**(5/2)/5 + (b*x + c)**(7/2)/7)/b**4, Ne(b, 0)), (x**4/(4*sqrt(c)), True))'],
    ['(2*x+a)*sqrt(x**2+a*x+b)', '(2*a*x/3 + 2*b/3 + 2*x**2/3)*sqrt(a*x + b + x**2)'],
    ['sqrt(2*x**2+a*x+b)', '(a/8 + x/2)*sqrt(a*x + b + 2*x**2) + (-a**2/16 + b/2)*Piecewise((sqrt(2)*log(a + 4*x + 2*sqrt(2)*sqrt(a*x + b + 2*x**2))/2, Ne(a**2/8 - b, 0)), (sqrt(2)*(a/4 + x)*log(a/4 + x)/(2*sqrt((a/4 + x)**2)), True))'],
    ['x*sqrt(x**2+a*x)', 'a**3*Piecewise((log(a + 2*x + 2*sqrt(a*x + x**2)), Ne(a**2, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))/16 + sqrt(a*x + x**2)*(-a**2/8 + a*x/12 + x**2/3)'],
    ['x*sqrt(a*x**2+2*x)', 'Piecewise((sqrt(a*x**2 + 2*x)*(x**2/3 + x/(6*a) - 1/(2*a**2)) + Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + 2*x) + 2*a*x + 2)/sqrt(a), Ne(1/a, 0)), ((x + 1/a)*log(x + 1/a)/sqrt(a*(x + 1/a)**2), True))/(2*a**2), Ne(a, 0)), (2*sqrt(2)*x**(5/2)/5, True))'],
    ['sqrt(a*x**2+2*x+b)', 'Piecewise(((b/2 - 1/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b + 2*x) + 2*a*x + 2)/sqrt(a), Ne(b - 1/a, 0)), ((x + 1/a)*log(x + 1/a)/sqrt(a*(x + 1/a)**2), True)) + (x/2 + 1/(2*a))*sqrt(a*x**2 + b + 2*x), Ne(a, 0)), ((b + 2*x)**(3/2)/3, True))'],
  ])('%s', (f, want) => expect(M(f)).toBe(want));

  it('applies to symbolic coefficients with b != 0 and odd powers 1 and -1 only', () => {
    // SymPy integrate: sqrt(a)*x*sqrt(1 + x**2/a)/2 + a*asinh(x/sqrt(a))/2 (meijerint before manualintegrate)
    expect(M('sqrt(x**2+a)')).toBe('None');
    // real coefficients: SymPy chooses asinh (integrate handles them itself)
    expect(M('sqrt(x**2+x+1)')).toBe('None');
    // a numerator of degree below 2 under 1/sqrt (SymPy: inverse_trig_rule)
    expect(M('1/sqrt(x**2+a*x+b)')).toBe('Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))');
    expect(M('(x**2+a*x+b)**(3/2)')).toBe('None');
    expect(M('x*sqrt(x**3+a)')).toBe('None');
    expect(M('sin(x)*sqrt(x**2+a*x+1)')).toBe('None');
    expect(M('exp(x)')).toBe('None');
  });
});

import * as sj from '../../src';
it('exposes elementary manual integration through the calculus entry', () => {
  for (const [input, expected] of [
    ['1/x', 'log(x)'], ['log(x)', 'x*log(x) - x'],
    ['exp(x)/(1 + exp(2*x))', 'atan(exp(x))'],
    ['cos(x)**4*sin(x)', '-cos(x)**5/5'],
    ['cos(x)**4*sin(x)**3', 'cos(x)**7/7 - cos(x)**5/5'],
    ['tan(x)', '-log(cos(x))'],
  ]) {
    const primitive = sj.manualintegrate(parse(input!), x);
    expect(String(primitive)).toBe(expected);
    expect(String(sj.trigsimp(sj.simplify(sj.sub(sj.diff(primitive, x), parse(input!)))))).toBe('0');
  }
  expect(String(sj.manualintegrate(sj.tan(sj.pow(x, 2)), x))).toContain('Integral');
});

it('retains the constant-radicand case when a quadratic coefficient vanishes', () => {
  const r = sqrtQuadraticRule(parse('1/sqrt(a*x**2 + 1)'), x);
  expect(String(r)).toBe('Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + 1) + 2*a*x)/sqrt(a), Ne(a, 0)), (x, True))');
});

it.each([
  ['(x + 2)**3', '(x + 2)**4/4'],
  ['(3*x + 4)**2', '(3*x + 4)**3/9'],
  ['sec(x)', 'log(tan(x) + sec(x))'],
  ['csc(x)', '-log(cot(x) + csc(x))'],
  ['sec(x)**2', 'tan(x)'],
  ['csc(x)**2', '-cot(x)'],
  ['x*sec(x**2)', 'log(tan(x**2) + sec(x**2))/2'],
  ['cos(x)*csc(sin(x))', '-log(cot(sin(x)) + csc(sin(x)))'],
  ['cot(x)', 'log(sin(x))'],
  ['coth(x)', 'log(sinh(x))'],
  ['sech(x)', '2*atan(tanh(x/2))'],
  ['csch(x)', 'log(tanh(x/2))'],
  ['exp(2*x)/x', 'Ei(2*x)'],
  ['sin(3*x + 2)/x', 'sin(2)*Ci(3*x) + cos(2)*Si(3*x)'],
  ['cos(2*x - 3)/x', 'cos(3)*Ci(2*x) + sin(3)*Si(2*x)'],
  ['sinh(3*x - 2)/x', '-sinh(2)*Chi(3*x) + cosh(2)*Shi(3*x)'],
  ['cosh(x/2)/x', 'Chi(x/2)'],
  ['cos(x**2)/x', 'Ci(x**2)/2'],
  ['sin(x**2)/x', 'Si(x**2)/2'],
  ['sinh(x**2)/x', 'Shi(x**2)/2'],
  ['cosh(x**2)/x', 'Chi(x**2)/2'],
  ['1/log(2*x + 1)', 'li(2*x + 1)/2'],
  ['polylog(2, 5*x)/x', 'polylog(3, 5*x)'],
  ['5/sqrt(3 - 2*sin(x)**2)', '5*sqrt(3)*elliptic_f(x, 2/3)/3'],
  ['sqrt(9*sin(x)**2 + 4)', '2*elliptic_e(x, -9/4)'],
  ['exp(x**2)', 'sqrt(pi)*erfi(x)/2'],
  ['exp(-x**2)', 'sqrt(pi)*erf(x)/2'],
  ['sqrt(x**(5/3))', '6*x*sqrt(x**(5/3))/11'],
  ['x*sqrt(x**(-4))', 'x**2*sqrt(x**(-4))*log(x)'],
])('manual rule for %s', (input, expected) => {
  expect(String(sj.manualintegrate(parse(input), x))).toBe(expected);
});

it('removes one occurrence of the integration variable from a derivative', () => {
  const y = new Sym('y');
  const f = sj.sin(x);
  expect(sj.manualintegrate(new sj.Derivative([f, x, sj.S.One]), x)).toBe(f);
  expect(String(sj.manualintegrate(new sj.Derivative([f, x, sj.S.Two, y, sj.S.One]), x)))
    .toBe('Derivative(sin(x), x, y)');
  expect(String(sj.manualintegrate(new sj.Derivative([sj.fn('sin', [y]), y, sj.S.One]), x)))
    .toBe('x*Derivative(sin(y), y)');
});

it('substitutes logarithms with their inverse without replacing unrelated logarithms', () => {
  const y = new Sym('y');
  expect(String(sj.manualSubs(parse('exp(x) + log(x)'), sj.log(x), y))).toBe('y + exp(exp(y))');
  expect(String(sj.manualSubs(parse('exp(x) + log(x)'), sj.exp(x), y))).toBe('y + log(x)');
  expect(String(sj.manualSubs(parse('x**2 + log(x)'), new Map([[sj.log(x), y]])))).toBe('y + exp(2*y)');
  expect(String(sj.manualSubs(x, [[x, y]]))).toBe('y');
  expect(() => sj.manualSubs(x, x)).toThrow(RangeError);
  expect(() => sj.manualSubs(x, x, x, y)).toThrow(RangeError);
});

it('finds derivative-dividing substitutions', () => {
  const u = new Sym('u');
  expect(sj.findSubstitutions(parse('(cot(x)**2 + 1)**2*csc(x)**2*cot(x)**2'), x, u).map((r) => r.map(String)))
    .toEqual([['cot(x)', '1', '-u**6 - 2*u**4 - u**2']]);
  expect(sj.findSubstitutions(parse('(sec(x)**2 + tan(x)*sec(x))/(sec(x) + tan(x))'), x, u).map((r) => r.map(String)))
    .toEqual([['tan(x) + sec(x)', '1', '1/u']]);
  expect(sj.findSubstitutions(sj.sin(x), x, u)).toEqual([]);
});

it('subtracts the Heaviside boundary value', () => {
  expect(String(sj.manualintegrate(sj.Heaviside(x), x))).toBe('x*Heaviside(x)');
  expect(String(sj.manualintegrate(sj.mul(x, sj.Heaviside(sj.neg(x))), x))).toBe('x**2*Heaviside(-x)/2');
  expect(String(sj.manualintegrate(sj.mul(sj.sin(sj.add(x, 7)), sj.Heaviside(sj.add(sj.mul(3, x), -7))), x)))
    .toBe('(-cos(x + 7) + cos(28/3))*Heaviside(3*x - 7)');
});

it.each([
  ['x + sin(x)', 'x**2/2 - cos(x)'],
  ['cosh(x + 1)/x', 'cosh(1)*Chi(x) + sinh(1)*Shi(x)'],
  ['sin(x**2 + 4*x + 1)', 'sqrt(2)*sqrt(pi)*(-sin(3)*fresnelc(sqrt(2)*(2*x + 4)/(2*sqrt(pi))) + cos(3)*fresnels(sqrt(2)*(2*x + 4)/(2*sqrt(pi))))/2'],
  ['cos(x**2)', 'sqrt(2)*sqrt(pi)*fresnelc(sqrt(2)*x/sqrt(pi))/2'],
  ['x**(1/3)*exp(-x/8)', '-16*uppergamma(4/3, x/8)'],
  ['(5*x**3 + 4)/sqrt(3*x + 2)', '10*(3*x + 2)**(7/2)/567 - 4*(3*x + 2)**(5/2)/27 + 40*(3*x + 2)**(3/2)/81 + 136*sqrt(3*x + 2)/81'],
  ['sqrt(x)', '2*x**(3/2)/3'],
])('preserves the manual rule form for %s', (input, expected) => {
  expect(String(sj.manualintegrate(parse(input), x))).toBe(expected);
});

it('leaves unsupported special-function and nonlinear substitutions unevaluated', () => {
  for (const input of ['1/log(x**2+1)', 'polylog(2, x+1)/x', 'gamma(x)/x', 'exp(x**3)', 'sin(sin(x))', 'x**x', 'exp(x)*x**2', 'exp(x)*x**a', 'exp(x)*sin(x)**a', 'sqrt(sin(x)**2)', 'sqrt(2-2*sin(x)**2)', '(x+sin(x))/sqrt(x+1)']) {
    expect(sj.manualintegrate(parse(input), x)).toBeInstanceOf(sj.Expr);
  }
  expect(String(sj.manualintegrate(sj.mul(sj.sin(x), sj.Heaviside(sj.sin(x))), x))).toContain('Integral');
  expect(sj.manualintegrate(sj.sin(sj.add(x, sj.tan(new Sym('y')))), x)).toBeInstanceOf(sj.Expr);
  const derivative = new sj.Derivative([sj.sin(x), new Sym('y'), sj.S.One]);
  expect(sj.manualintegrate(derivative, x)).toBeInstanceOf(sj.Expr);
});

it('validates substitution argument shapes and accepts numeric replacements', () => {
  expect(sj.manualSubs(x, x, 2)).toEqual(sj.sympify(2));
  expect(sj.manualSubs(x, x, 3n)).toEqual(sj.sympify(3));
  expect(() => sj.manualSubs(x, new Map(), x)).toThrow(RangeError);
  expect(sj.findSubstitutions(new sj.Pow(x, sj.S.Zero), x, new Sym('u'))).toEqual([]);
});

it('selects inverse hyperbolic, inverse circular and logarithmic quadratic rules', () => {
  expect(M('x**2/sqrt(x**2+1)')).toBe('x*sqrt(x**2 + 1)/2 - asinh(x)/2');
  expect(M('x**2/sqrt(1-x**2)')).toBe('-x*sqrt(1 - x**2)/2 + asin(x)/2');
  expect(M('x**2/sqrt(c*x**2+1)')).toContain('log(');
  expect(M('x**2/sqrt(-x**2-1)')).toBe('None');
});

it('integrates affine delta distributions with a zero-slope fallback', () => {
  const a = new Sym('a'), b = new Sym('b');
  expect(String(sj.manualintegrate(sj.DiracDelta(sj.add(sj.mul(3, x), 2)), x))).toBe('Heaviside(3*x + 2)/3');
  expect(String(sj.manualintegrate(sj.DiracDelta(sj.add(a, sj.mul(b, x)), 1), x)))
    .toBe('Piecewise((DiracDelta(a + b*x)/b, Ne(b, 0)), (x*DiracDelta(a, 1), True))');
  expect(sj.manualintegrate(sj.DiracDelta(sj.sin(x)), x)).toBeInstanceOf(sj.Integral);
});

it('uses parts for polynomial multiples of trigonometric and unevaluated derivatives', () => {
  expect(String(sj.manualintegrate(parse('x*sec(x)*tan(x)'), x))).toBe('x*sec(x) - log(tan(x) + sec(x))');
  expect(String(sj.manualintegrate(parse('x*sec(x)**2'), x))).toBe('x*tan(x) + log(cos(x))');
  const f = sj.SymFunction('f')(x);
  const derivative = new sj.Derivative([f, x, sj.sympify(4)]);
  expect(String(sj.manualintegrate(sj.mul(sj.pow(x, 3), derivative), x)))
    .toBe('x**3*Derivative(f(x), (x, 3)) - 3*x**2*Derivative(f(x), (x, 2)) + 6*x*Derivative(f(x), x) - 6*f(x)');
  expect(String(sj.manualintegrate(parse('(exp(x) - exp(-x))/x'), x))).toBe('-Ei(-x) + Ei(x)');
  expect(String(sj.manualintegrate(parse('(2*x+1)*exp(x**2+x)'), x))).toBe('exp(x**2 + x)');
});

it('handles symbolic affine nested powers and zero assumptions', () => {
  const a = new Sym('a'), b = new Sym('b'), c = new Sym('c'), d = new Sym('d'), e = new Sym('e');
  const f = sj.pow(sj.mul(c, sj.pow(sj.add(a, sj.mul(b, x)), d)), e);
  expect(String(sj.manualintegrate(f, x)))
    .toBe('Piecewise((Piecewise(((c*(a + b*x)**d)**e*(a/b + x)/(d*e + 1), Ne(d*e, -1)), ((c*(a + b*x)**d)**e*(a/b + x)*log(a/b + x), True)), Ne(b, 0)), (x*(a**d*c)**e, True))');
  expect(String(sj.manualintegrate(sj.pow(sj.add(new Sym('y', { zero: true }), 1), x), x))).toBe('x');
  expect(sj.manualintegrate(parse('(sin(x)*cos(x))**a'), x)).toBeInstanceOf(sj.Integral);
});

it('retains affine-power fallbacks and quadratic degeneracies', () => {
  const a = new Sym('a'), b = new Sym('b');
  expect(String(sj.manualintegrate(parse('1/(1+x**2)'), x))).toBe('atan(x)');
  expect(String(sj.manualintegrate(parse('1/(1-x**2)'), x))).toBe('-log(x - 1)/2 + log(x + 1)/2');
  expect(String(sj.manualintegrate(parse('1/(x**2+x+1)'), x))).toBe('2*sqrt(3)*atan(2*sqrt(3)*x/3 + sqrt(3)/3)/3');
  const negativeA = new Sym('a', { negative: true });
  expect(String(sj.manualintegrate(sj.pow(sj.add(negativeA, sj.mul(b, sj.pow(x, 2))), -1), x))).toBe('atan(x/sqrt(a/b))/(b*sqrt(a/b))');
  expect(String(sj.manualintegrate(parse('sqrt(a+c*x**2)'), x))).toContain('Ne(c, 0)');
  for (const input of ['((1+x)*sin(x))**a', '((1+x)**x)**a', '(c*(x + x**2)**d)**e']) {
    expect(String(sj.manualintegrate(parse(input), x))).toBe(`Integral(${String(parse(input))}, x)`);
  }
  expect(String(sj.manualintegrate(sj.pow(sj.mul(a, sj.pow(sj.mul(b, x), a)), b), x))).toContain('Ne(b, 0)');
  expect(String(sj.manualintegrate(new sj.Pow(sj.pow(x, 2), sj.S.NegHalf), x))).toContain('log(x)');
  expect(String(sj.manualintegrate(sj.DiracDelta(sj.mul(3, x)), x))).toBe('Heaviside(3*x)/3');
});

it('substitutes powers into Gaussians and exponential quadratic radicals', () => {
  for (const [source, expected] of [
    ['x*exp(x**4)', '-I*sqrt(pi)*erf(I*x**2)/4'],
    ['exp(x)*sqrt(1+exp(2*x))', 'exp(x)*sqrt(1+exp(2*x))/2+asinh(exp(x))/2'],
    ['x/(x**2+1)', 'log(x**2+1)/2'],
    ['1/(x*log(x))', 'log(log(x))'],
  ] as const) expect(sj.manualintegrate(parse(source), x).equals(parse(expected))).toBe(true);
});

it('retains unresolved substitutions when the change of variable still depends on x', () => {
  for (const source of [
    '1/sqrt(1+sqrt(x**2+1))', 'sqrt(1+sqrt(a*x+1))', 'sqrt(1+sin(x)+sqrt(x+2))',
    'exp(x*log(x))', 'exp(x**2)*sqrt(1+exp(x**2))', 'sin(x)/log(x)',
  ]) {
    const f = parse(source);
    expect(sj.manualintegrate(f, x).equals(sj.integral(f, x))).toBe(true);
  }
});

it('reduces quadratic denominators with vanishing coefficients', () => {
  for (const [source, expected] of [
    ['x/(x**2+x)', 'log(x+1)'],
    ['x/(x**2+2)', 'log(x**2+2)/2'],
  ] as const) expect(sj.manualintegrate(parse(source), x).equals(parse(expected))).toBe(true);
});

it('preserves radicals outside the quadratic substitution and secants without a multiple angle', () => {
  for (const f of [parse('sqrt(1+sqrt(x))'), parse('sec(x)*sin(x)')]) {
    expect(sj.manualintegrate(f, x).equals(sj.integral(f, x))).toBe(true);
  }
});

it('distinguishes a held constant logarithm from a dilogarithm derivative', () => {
  const two = new sj.Add([x, x.neg(), sj.S.Two]);
  const f = new sj.Mul([new sj.Fn('log', [two]), sj.pow(x, -1)]);
  expect(sj.manualintegrate(f,x).equals(parse('log(2)*log(x)'))).toBe(true);
});

it('uses a common radical only when the change of variable is rational', () => {
  const f = parse('sqrt(3*x)/(1+(2*x)**(1/3))');
  const primitive = sj.manualintegrate(f, x);
  expect(sj.diff(primitive, x).subs(x, 2).toNumber()).toBeCloseTo(f.subs(x, 2).toNumber(), 12);
  const withSine = parse('sin(x)*sqrt(3*x)/((2*x)**(1/3)+1)');
  expect(String(sj.manualintegrate(withSine, x))).toBe('sqrt(3)*Integral(sqrt(x)*sin(x)/(2**(1/3)*x**(1/3) + 1), x)');
});

it('distributes an affine numerator over a repeated shifted quadratic after trying substitution', () => {
  const q = parse('x**2-2*x+2'), den = sj.expand(sj.pow(q, 2));
  const primitive = sj.manualintegrate(sj.mul(sj.sub(x, 3), sj.pow(q, -2)), x);
  expect(primitive.equals(sj.sub(sj.integral(sj.mul(x, sj.pow(den, -1)), x), sj.mul(3, sj.integral(sj.pow(den, -1), x))))).toBe(true);
  expect(sj.manualintegrate(sj.mul(sj.sub(x, 1), sj.pow(q, -2)), x).equals(sj.mul(sj.S.NegHalf, sj.pow(q, -1)))).toBe(true);
});

it('retains the tangent substitution for a centered repeated quadratic', () => {
  expect(sj.manualintegrate(parse('1/(x**2+1)**2'), x).equals(parse('x/(2*x**2+2)+atan(x)/2'))).toBe(true);
});
