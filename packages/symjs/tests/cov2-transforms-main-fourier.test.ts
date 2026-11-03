// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Fourier, sine, cosine and Hankel transforms; expected values from SymPy 1.14
// (x, k, r, nu, m plain symbols, a and b positive).

import { describe, expect, it } from 'vitest';
import type { Expr, TransformResult } from '../src';
import {
  CosineTransform,
  DiracDelta,
  FourierTransform,
  HankelTransform,
  Heaviside,
  InverseCosineTransform,
  InverseFourierTransform,
  InverseHankelTransform,
  InverseSineTransform,
  SineTransform,
  Sym,
  cosineTransform,
  fourierTransform,
  hankelTransform,
  inverseCosineTransform,
  inverseFourierTransform,
  inverseHankelTransform,
  inverseSineTransform,
  latex,
  parse,
  simplify,
  sineTransform,
  sstr,
  sub,
  symbols,
} from '../src';
import { hyperexpandForm } from '../src/integrals/transforms/fourier';

const [x, k, r, nu, m] = symbols('x k r nu m');
const a = new Sym('a', { positive: true });
const b = new Sym('b', { positive: true });
const P = (q: string): Expr => parse(q, { symbols: [x, k, r, nu, m, a, b], locals: { Heaviside, DiracDelta } });
const S = (v: TransformResult): string => (Array.isArray(v) ? `(${v.map((e) => sstr(e as Expr)).join(', ')})` : sstr(v as Expr));

describe('fourier_transform', () => {
  const cases: [string, () => TransformResult, string][] = [
    // DiracDelta of a polynomial: the sum over its simple real roots
    ['DiracDelta(x**2 - 1)', () => fourierTransform(P('DiracDelta(x**2 - 1)'), x, k), 'cos(2*pi*k)'],
    ['DiracDelta(x**2 - a**2)', () => fourierTransform(P('DiracDelta(x**2 - a**2)'), x, k), 'cos(2*pi*a*k)/a'],
    ['DiracDelta(x**3 - x)', () => fourierTransform(P('DiracDelta(x**3 - x)'), x, k), 'cos(2*pi*k) + 1'],
    ['DiracDelta(x - 1)*exp(x)', () => fourierTransform(P('DiracDelta(x - 1)*exp(x)'), x, k), 'exp(-2*I*pi*k + 1)'],
    ['DiracDelta(x - 1)*x', () => fourierTransform(P('DiracDelta(x - 1)*x'), x, k), 'exp(-2*I*pi*k)'],
    ['DiracDelta(m*x - 1)', () => fourierTransform(P('DiracDelta(m*x - 1)'), x, k), 'exp(-2*I*pi*k/m)/Abs(m)'],
    // a double root and no real root: unevaluated in SymPy too
    ['DiracDelta(x**2)', () => fourierTransform(P('DiracDelta(x**2)'), x, k), 'FourierTransform(DiracDelta(x**2), x, k)'],
    ['DiracDelta(x**2 + 1)', () => fourierTransform(P('DiracDelta(x**2 + 1)'), x, k), 'FourierTransform(DiracDelta(x**2 + 1), x, k)'],
    // SymPy gives cos(2*pi*k*sqrt(m))/Abs(sqrt(m)), which is wrong for m < 0 (no real root: the transform is 0)
    ['DiracDelta(x**2 - m)', () => fourierTransform(P('DiracDelta(x**2 - m)'), x, k), 'FourierTransform(DiracDelta(-m + x**2), x, k)'],
    ['Heaviside(x)*x**2*exp(-a*x)', () => fourierTransform(P('Heaviside(x)*x**2*exp(-a*x)'), x, k), '2/(a + 2*I*pi*k)**3'],
    // convergent only for Re(c) > 0: unevaluated in SymPy for c = m and c = -I
    ['Heaviside(x)*exp(-m*x)', () => fourierTransform(P('Heaviside(x)*exp(-m*x)'), x, k), 'FourierTransform(exp(-m*x)*Heaviside(x), x, k)'],
    ['Heaviside(x)*exp(I*x)', () => fourierTransform(P('Heaviside(x)*exp(I*x)'), x, k), 'FourierTransform(exp(I*x)*Heaviside(x), x, k)'],
    ['exp(-m*x**2)', () => fourierTransform(P('exp(-m*x**2)'), x, k), 'FourierTransform(exp(-m*x**2), x, k)'],
    ['exp(-m*Abs(x))', () => fourierTransform(P('exp(-m*Abs(x))'), x, k), 'FourierTransform(exp(-m*Abs(x)), x, k)'],
    ['exp(x**2)', () => fourierTransform(P('exp(x**2)'), x, k), 'FourierTransform(exp(x**2), x, k)'],
    ['exp(-x)', () => fourierTransform(P('exp(-x)'), x, k), 'FourierTransform(exp(-x), x, k)'],
    ['exp(sin(x))', () => fourierTransform(P('exp(sin(x))'), x, k), 'FourierTransform(exp(sin(x)), x, k)'],
    ['x**m*exp(-x**2)', () => fourierTransform(P('x**m*exp(-x**2)'), x, k), 'FourierTransform(x**m*exp(-x**2), x, k)'],
    ['Heaviside(x)*log(x)', () => fourierTransform(P('Heaviside(x)*log(x)'), x, k), 'FourierTransform(log(x)*Heaviside(x), x, k)'],
    ['Heaviside(x)*exp(x)', () => fourierTransform(P('Heaviside(x)*exp(x)'), x, k), 'FourierTransform(exp(x)*Heaviside(x), x, k)'],
    ['Heaviside(x)*x', () => fourierTransform(P('Heaviside(x)*x'), x, k), 'FourierTransform(x*Heaviside(x), x, k)'],
    ['exp(-x**2) + log(x)', () => fourierTransform(P('exp(-x**2) + log(x)'), x, k), 'FourierTransform(log(x), x, k) + sqrt(pi)*exp(-pi**2*k**2)'],
    ['exp(-x**2), noconds=False', () => fourierTransform(P('exp(-x**2)'), x, k, { noconds: false }), '(sqrt(pi)*exp(-pi**2*k**2), True)'],
    ['x**2*exp(-x**2), noconds=False', () => fourierTransform(P('exp(-x**2)*x**2'), x, k, { noconds: false }), '(sqrt(pi)*(-pi**2*k**2 + 1/2)*exp(-pi**2*k**2), True)'],
    ['inverse of sqrt(pi)*exp(-pi**2*k**2)', () => inverseFourierTransform(P('sqrt(pi)*exp(-pi**2*k**2)'), k, x), 'exp(-x**2)'],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(S(f())).toBe(want));
});

describe('sine and cosine transforms', () => {
  const cases: [string, () => TransformResult, string][] = [
    ['inverse sine of a Gaussian', () => inverseSineTransform(P('sqrt(2)*k*exp(-k**2/(4*a))/(4*a**(3/2))'), k, x), 'x*exp(-a*x**2)'],
    ['inverse cosine of a Lorentzian', () => inverseCosineTransform(P('sqrt(2)*a/(sqrt(pi)*(a**2 + k**2))'), k, x), 'exp(-a*x)'],
    ['sine x/(x**2 + b**2)', () => sineTransform(P('x/(x**2 + b**2)'), x, k), 'sqrt(2)*sqrt(pi)*exp(-b*k)/2'],
    ['cosine 1/(x**2 + b**2)', () => cosineTransform(P('1/(x**2 + b**2)'), x, k), 'sqrt(2)*sqrt(pi)*exp(-b*k)/(2*b)'],
    ['cosine exp(-a*sqrt(x))*cos(a*sqrt(x))', () => cosineTransform(P('exp(-a*sqrt(x))*cos(a*sqrt(x))'), x, k), 'a*exp(-a**2/(2*k))/(2*k**(3/2))'],
    ['sine x**(-1/2)', () => sineTransform(P('x**(-1/2)'), x, k), '1/sqrt(k)'],
    ['cosine x**(-1/2)', () => cosineTransform(P('x**(-1/2)'), x, k), '1/sqrt(k)'],
    ['sine x**m', () => sineTransform(P('x**m'), x, k), '2**(m + 1/2)*k**(-m - 1)*gamma(m/2 + 1)/gamma(1/2 - m/2)'],
    ['sine x*exp(-a*x)', () => sineTransform(P('x*exp(-a*x)'), x, k), '2*sqrt(2)*a*k/(sqrt(pi)*(a**2 + k**2)**2)'],
    ['cosine exp(-m*x)', () => cosineTransform(P('exp(-m*x)'), x, k), 'sqrt(2)*m/(sqrt(pi)*(k**2 + m**2))'],
    // outside the strips of convergence: unevaluated in SymPy too
    ['sine x**2', () => sineTransform(P('x**2'), x, k), 'SineTransform(x**2, x, k)'],
    ['cosine x', () => cosineTransform(P('x'), x, k), 'CosineTransform(x, x, k)'],
    ['sine exp(x)', () => sineTransform(P('exp(x)'), x, k), 'SineTransform(exp(x), x, k)'],
    ['cosine exp(x**2)', () => cosineTransform(P('exp(x**2)'), x, k), 'CosineTransform(exp(x**2), x, k)'],
    ['cosine exp(-m*x**2)', () => cosineTransform(P('exp(-m*x**2)'), x, k), 'sqrt(2)*exp(-k**2/(4*m))/(2*sqrt(m))'],
    ['sine log(x)', () => sineTransform(P('log(x)'), x, k), 'SineTransform(log(x), x, k)'],
    // SymPy's Meijer G integrator evaluates these; symjs's table does not have them:
    // sqrt(2)*atan(k/a)/sqrt(pi)
    ['sine exp(-a*x)/x', () => sineTransform(P('exp(-a*x)/x'), x, k), 'SineTransform(exp(-a*x)/x, x, k)'],
    // sqrt(2)/(2*sqrt(pi)*a) + sqrt(2)*I*k*exp(-k**2/(4*a))*erf(I*k/(2*sqrt(a)))/(4*a**(3/2))
    ['cosine x*exp(-a*x**2)', () => cosineTransform(P('x*exp(-a*x**2)'), x, k), 'CosineTransform(x*exp(-a*x**2), x, k)'],
    // -sqrt(2)*I*exp(-k**2/(4*a))*erf(I*k/(2*sqrt(a)))/(2*sqrt(a))
    ['sine exp(-a*x**2)', () => sineTransform(P('exp(-a*x**2)'), x, k), 'SineTransform(exp(-a*x**2), x, k)'],
    // sqrt(2)*((pi - 2*Si(k))*sin(k)/2 - cos(k)*Ci(k))/sqrt(pi)
    ['cosine 1/(x + 1)', () => cosineTransform(P('1/(x + 1)'), x, k), 'CosineTransform(1/(x + 1), x, k)'],
    // -sqrt(2)*sqrt(pi)*(b*k*sinh(b*k) - b*k*cosh(b*k) + sinh(b*k) - cosh(b*k))/(4*b**3)
    ['cosine 1/(x**2 + b**2)**2', () => cosineTransform(P('1/(x**2 + b**2)**2'), x, k), 'CosineTransform(1/(b**4 + 2*b**2*x**2 + x**4), x, k)'],
    // (SymPy: a long expression in fresnels and fresnelc)
    ['cosine exp(-a*sqrt(x))*sin(a*sqrt(x))', () => cosineTransform(P('exp(-a*sqrt(x))*sin(a*sqrt(x))'), x, k), 'CosineTransform(exp(-a*sqrt(x))*sin(a*sqrt(x)), x, k)'],
    // (SymPy does not finish these within 20 s)
    ['cosine exp(-x)*log(x)', () => cosineTransform(P('log(x)*exp(-x)'), x, k), 'CosineTransform(exp(-x)*log(x), x, k)'],
    ['cosine exp(-a*sqrt(x))*cos(b*sqrt(x))', () => cosineTransform(P('exp(-a*sqrt(x))*cos(b*sqrt(x))'), x, k), 'CosineTransform(exp(-a*sqrt(x))*cos(b*sqrt(x)), x, k)'],
    ['cosine sqrt(1/x**2 + sin(x))', () => cosineTransform(P('sqrt(1/x**2 + sin(x))'), x, k), 'CosineTransform(sqrt(sin(x) + x**(-2)), x, k)'],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(S(f())).toBe(want));

  it('noconds and simplify hints', () => {
    // SymPy: (sqrt(2)*sqrt(pi)*exp(-b*k)/(2*b), Eq(Abs(arg(k)), 0)); the condition of the Meijer G
    // integrator on arg(k) is not derived, k is taken positive
    expect(S(cosineTransform(P('1/(x**2 + b**2)'), x, k, { noconds: false }))).toBe('(sqrt(2)*sqrt(pi)*exp(-b*k)/(2*b), True)');
    // SymPy: sqrt(2)/(sqrt(pi)*a*(1 + k**2/a**2)), the same function
    expect(S(cosineTransform(P('exp(-a*x)'), x, k, { simplify: false }))).toBe('sqrt(2)*a/(sqrt(pi)*(a**2 + k**2))');
  });
});

describe('hankel_transform', () => {
  const cases: [string, () => TransformResult, string][] = [
    ['r**nu*exp(-a*r), order nu', () => hankelTransform(P('r**(nu - 1)*exp(-a*r)'), r, k, nu), '2**nu*k**(-nu - 1)*(a**2/k**2 + 1)**(-nu - 1/2)*gamma(nu + 1/2)/sqrt(pi)'],
    ['r*exp(-a*r**2), order 1', () => hankelTransform(P('r*exp(-a*r**2)'), r, k, 1), 'k*exp(-k**2/(4*a))/(4*a**2)'],
    ['r**2*exp(-a*r**2), order 0', () => hankelTransform(P('r**2*exp(-a*r**2)'), r, k, 0), '(4*a - k**2)*exp(-k**2/(4*a))/(8*a**3)'],
    ['r/(r**2 + b**2)**(3/2), order 1', () => hankelTransform(P('r/(r**2 + b**2)**(3/2)'), r, k, 1), 'exp(-b*k)'],
    ['1/sqrt(r**2 + b**2), order 0', () => hankelTransform(P('1/(r**2 + b**2)**(1/2)'), r, k, 0), 'exp(-b*k)/k'],
    ['1/(r**2 + b**2)**(3/2), order 0', () => hankelTransform(P('1/(r**2 + b**2)**(3/2)'), r, k, 0), 'exp(-b*k)/b'],
    ['noconds=False', () => hankelTransform(P('r*exp(-a*r**2)'), r, k, 1, { noconds: false }), '(k*exp(-k**2/(4*a))/(4*a**2), True)'],
    ['inverse of k*exp(-k**2/(4*a))/(4*a**2)', () => inverseHankelTransform(P('r*exp(-a*r**2)'), r, k, 1), 'k*exp(-k**2/(4*a))/(4*a**2)'],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(S(f())).toBe(want));

  it('forms that differ from SymPy only in how they are written', () => {
    // SymPy: 2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi);
    // symjs's Mul keeps 2*2**nu apart
    expect(S(hankelTransform(P('r**nu*exp(-a*r)'), r, k, nu))).toBe('2*2**nu*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)');
    // (SymPy prints 2*2**m here too)
    expect(S(hankelTransform(P('r**m'), r, k, nu))).toBe('2*2**m*k**(-m - 2)*gamma(m/2 + nu/2 + 1)/gamma(-m/2 + nu/2)');
    // SymPy: meijerg(((0,), ()), ((0, 0), (0,)), b**2*k**2/4)/2, which is besselk(0, b*k)
    // (both 0.034739504386279248072 at b*k = 3 with mpmath)
    expect(S(hankelTransform(P('1/(r**2 + b**2)'), r, k, 0))).toBe('besselk(0, b*k)');
  });

  it('raises like SymPy when the integral is not known', () => {
    // SymPy: sqrt(pi)*k*(besseli(0, k**2/(8*a)) - besseli(1, k**2/(8*a)))*exp(-k**2/(8*a))/(8*a**(3/2))
    expect(() => hankelTransform(P('exp(-a*r**2)'), r, k, 1)).toThrow('Hankel Transform could not be computed');
    // SymPy: -pi*besseli(1, b*k)/2 + hyper((1,), (1/2, 3/2), b**2*k**2/4)
    expect(() => hankelTransform(P('1/(r**2 + b**2)'), r, k, 1)).toThrow('Hankel Transform could not be computed');
    // SymPy: b*sinh(b*k) - b*cosh(b*k) - sinh(b*k)/k + cosh(b*k)/k
    expect(() => hankelTransform(P('r**2/(r**2 + b**2)**(3/2)'), r, k, 0)).toThrow('Hankel Transform could not be computed');
    // divergent
    expect(() => hankelTransform(P('exp(r)'), r, k, 0)).toThrow('Hankel Transform could not be computed');
    expect(() => inverseHankelTransform(P('log(k)'), k, r, 0)).toThrow('Inverse Hankel Transform could not be computed');
  });
});

describe('the unevaluated transform objects', () => {
  const objs = [
    new FourierTransform(P('exp(x)'), x, k),
    new InverseFourierTransform(P('exp(x)'), x, k),
    new SineTransform(P('exp(x)'), x, k),
    new InverseSineTransform(P('exp(x)'), x, k),
    new CosineTransform(P('exp(x)'), x, k),
    new InverseCosineTransform(P('exp(x)'), x, k),
  ];
  it('as_integral, latex, subs and needeval', () => {
    // SymPy: SineTransform(f, x, k).rewrite(Integral) etc.
    expect(objs.map((o) => sstr(o.asIntegral))).toEqual([
      'Integral(exp(x)*exp(-2*I*pi*k*x), (x, -oo, oo))',
      'Integral(exp(x)*exp(2*I*pi*k*x), (x, -oo, oo))',
      'Integral(sqrt(2)*exp(x)*sin(k*x)/sqrt(pi), (x, 0, oo))',
      'Integral(sqrt(2)*exp(x)*sin(k*x)/sqrt(pi), (x, 0, oo))',
      'Integral(sqrt(2)*exp(x)*cos(k*x)/sqrt(pi), (x, 0, oo))',
      'Integral(sqrt(2)*exp(x)*cos(k*x)/sqrt(pi), (x, 0, oo))',
    ]);
    expect(objs.map((o) => latex(o))).toEqual([
      '\\mathcal{F}_{x}\\left[e^{x}\\right]\\left(k\\right)',
      '\\mathcal{F}^{-1}_{x}\\left[e^{x}\\right]\\left(k\\right)',
      '\\mathcal{SIN}_{x}\\left[e^{x}\\right]\\left(k\\right)',
      '\\mathcal{SIN}^{-1}_{x}\\left[e^{x}\\right]\\left(k\\right)',
      '\\mathcal{COS}_{x}\\left[e^{x}\\right]\\left(k\\right)',
      '\\mathcal{COS}^{-1}_{x}\\left[e^{x}\\right]\\left(k\\right)',
    ]);
    // FourierTransform(exp(x), x, k).subs(k, 2) -> FourierTransform(exp(x), x, 2)
    expect(objs.map((o) => sstr(o.subs(k, 2)))).toEqual([
      'FourierTransform(exp(x), x, 2)',
      'InverseFourierTransform(exp(x), x, 2)',
      'SineTransform(exp(x), x, 2)',
      'InverseSineTransform(exp(x), x, 2)',
      'CosineTransform(exp(x), x, 2)',
      'InverseCosineTransform(exp(x), x, 2)',
    ]);
    // IntegralTransformError: '<name> Transform could not be computed: needeval'
    for (const [o, name] of objs.map((o, i) => [o, ['Fourier', 'Inverse Fourier', 'Sine', 'Inverse Sine', 'Cosine', 'Inverse Cosine'][i]] as const)) {
      expect(() => o.doit({ needeval: true })).toThrow(`${name} Transform could not be computed`);
    }
  });

  it('Hankel transforms', () => {
    const h = new HankelTransform(P('exp(-a*r)'), r, k, 0);
    const ih = new InverseHankelTransform(P('exp(-a*k)'), k, r, 0);
    expect(sstr(h.asIntegral)).toBe('Integral(r*exp(-a*r)*besselj(0, k*r), (r, 0, oo))');
    expect(sstr(h.subs(k, 2))).toBe('HankelTransform(exp(-a*r), r, 2, 0)');
    expect(sstr(ih.subs(r, 2))).toBe('InverseHankelTransform(exp(-a*k), k, 2, 0)');
    // SymPy prints the Hankel transforms in the generic form
    expect(latex(h)).toBe('\\operatorname{HankelTransform}{\\left(e^{- a r},r,k,0 \\right)}');
    expect(latex(ih)).toBe('\\operatorname{InverseHankelTransform}{\\left(e^{- a k},k,r,0 \\right)}');
    // a function variable that is not a symbol stays (SymPy: ValueError for the invalid limits of the Integral)
    expect(sstr(new HankelTransform(P('exp(-a*r)'), 2, k, 0).doit() as Expr)).toBe('HankelTransform(exp(-a*r), 2, k, 0)');
  });
});

describe('Heaviside(x) factors over the half line', () => {
  it('sines and cosines are written with exponentials', () => {
    // SymPy: 1/((2*I*pi*k + 1)**2 + 1), the same rational function
    const F = fourierTransform(P('Heaviside(x)*exp(-x)*sin(x)'), x, k) as Expr;
    expect(sstr(simplify(sub(F, P('1/((2*I*pi*k + 1)**2 + 1)'))))).toBe('0');
  });
  it('exponents that are not linear in x are not in the table', () => {
    // SymPy: sqrt(pi)*exp(-pi**2*k**2)*erfc(I*pi*k)/2
    expect(S(fourierTransform(P('Heaviside(x)*exp(-x**2)'), x, k))).toBe('FourierTransform(exp(-x**2)*Heaviside(x), x, k)');
    // SymPy: an expression in erf((-1)**(3/4)*sqrt(2)/(4*sqrt(pi)*sqrt(k)))
    expect(S(fourierTransform(P('Heaviside(x)*exp(-sqrt(x))'), x, k))).toBe('FourierTransform(exp(-sqrt(x))*Heaviside(x), x, k)');
  });
});

describe('the hyperexpand form of the Hankel transforms', () => {
  // (A + k**2)**p = k**(2*p)*(A/k**2 + 1)**p for k > 0, the form of SymPy's hyperexpand
  it('rewrites powers of A + k**2 only', () => {
    expect(sstr(hyperexpandForm(P('(a**2 + k**2)**(-3/2)'), k))).toBe('1/(k**3*(a**2/k**2 + 1)**(3/2))');
    // no k**2 term, or a k in A: unchanged
    expect(sstr(hyperexpandForm(P('(a + k)**(1/2)'), k))).toBe('sqrt(a + k)');
    expect(sstr(hyperexpandForm(P('(k**2 + (k + 1)**2)**(3/2)'), k))).toBe('(k**2 + (k + 1)**2)**(3/2)');
  });
});
