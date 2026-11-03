// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transforms/fourier.ts.
// Fourier, sine, cosine and Hankel transforms. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  type Expr,
  S,
  add,
  cos,
  exp,
  gamma,
  mul,
  pi,
  pow,
  sqrt,
  symbols,
  DiracDelta,
  Heaviside,
  Sym,
  cosineTransform,
  fourierTransform,
  hankelTransform,
  inverseCosineTransform,
  inverseFourierTransform,
  inverseHankelTransform,
  inverseSineTransform,
  parse,
  sineTransform,
  symbol,
  type TransformResult,
  CosineTransform,
  FourierTransform,
  HankelTransform,
  InverseCosineTransform,
  InverseFourierTransform,
  InverseHankelTransform,
  InverseSineTransform,
  SineTransform,
  latex,
  simplify,
  sstr,
  sub,
} from '../../../src';
import { hyperexpandForm } from '../../../src/integrals/transforms/fourier';

/** str of a result; tuples print like SymPy's. */
const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

const half = S.Half;

describe('sympy.integrals.transforms doctests', () => {
  it('cosine_transform', () => {
    const [x, k, a] = symbols('x k a');
    expect(String(cosineTransform(exp(mul(-1, a, x)), x, k))).toBe('sqrt(2)*a/(sqrt(pi)*(a**2 + k**2))');
    expect(String(cosineTransform(mul(exp(mul(-1, a, sqrt(x))), cos(mul(a, sqrt(x)))), x, k))).toBe('a*exp(-a**2/(2*k))/(2*k**(3/2))');
  });

  it('fourier_transform', () => {
    const [x, k] = symbols('x k');
    expect(String(fourierTransform(exp(mul(-1, pow(x, 2))), x, k))).toBe('sqrt(pi)*exp(-pi**2*k**2)');
    expect(show(fourierTransform(exp(mul(-1, pow(x, 2))), x, k, { noconds: false }))).toBe('(sqrt(pi)*exp(-pi**2*k**2), True)');
  });

  it('hankel_transform and inverse_hankel_transform', () => {
    const [r, k, m, nu, a] = symbols('r k m nu a');
    const ht = hankelTransform(pow(r, mul(-1, m)), r, k, nu) as Expr;
    expect(String(ht)).toBe('2*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/(2**m*gamma(m/2 + nu/2))');
    expect(String(inverseHankelTransform(ht, k, r, nu))).toBe('r**(-m)');
    const ht2 = hankelTransform(exp(mul(-1, a, r)), r, k, 0) as Expr;
    expect(String(ht2)).toBe('a/(k**3*(a**2/k**2 + 1)**(3/2))');
    expect(String(inverseHankelTransform(ht2, k, r, 0))).toBe('exp(-a*r)');
  });

  it('inverse_cosine_transform', () => {
    const [x, k, a] = symbols('x k a');
    expect(String(inverseCosineTransform(mul(sqrt(2), a, pow(mul(sqrt(pi), add(pow(a, 2), pow(k, 2))), -1)), k, x))).toBe('exp(-a*x)');
    expect(String(inverseCosineTransform(pow(sqrt(k), -1), k, x))).toBe('1/sqrt(x)');
  });

  it('inverse_fourier_transform', () => {
    const [x, k] = symbols('x k');
    const F = mul(sqrt(pi), exp(mul(-1, pow(mul(pi, k), 2))));
    expect(String(inverseFourierTransform(F, k, x))).toBe('exp(-x**2)');
    expect(show(inverseFourierTransform(F, k, x, { noconds: false }))).toBe('(exp(-x**2), True)');
  });

  it('inverse_sine_transform', () => {
    const [x, k, a] = symbols('x k a');
    const F1 = mul(pow(2, mul(add(1, mul(-2, a)), half)), pow(k, add(a, -1)), gamma(add(mul(-1, a, half), 1)), pow(gamma(mul(add(a, 1), half)), -1));
    expect(String(inverseSineTransform(F1, k, x))).toBe('x**(-a)');
    const F2 = mul(sqrt(2), k, exp(mul(-1, pow(k, 2), pow(mul(4, a), -1))), pow(mul(4, pow(sqrt(a), 3)), -1));
    expect(String(inverseSineTransform(F2, k, x))).toBe('x*exp(-a*x**2)');
  });

  it('sine_transform', () => {
    const [x, k, a] = symbols('x k a');
    expect(String(sineTransform(mul(x, exp(mul(-1, a, pow(x, 2)))), x, k))).toBe('sqrt(2)*k*exp(-k**2/(4*a))/(4*a**(3/2))');
    expect(String(sineTransform(pow(x, mul(-1, a)), x, k))).toBe('2**(1/2 - a)*k**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)');
  });
});

// Expected values are the str() forms printed by SymPy 1.14.

const PH = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
/** The variable argument as a symbol. */
const V = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

describe("integral transforms: SymPy 1.14 test_transforms cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["fourierTransform(P(\"f(x)\"), V(P(\"x\")), P(\"s\"))", () => fourierTransform(PH("f(x)"), V(PH("x")), PH("s")), "FourierTransform(f(x), x, s)"],
    ["fourierTransform(Qs(\"f(x)\", [symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("f(x)", [symbol("k", { real: true })]), V(Qs("x", [symbol("k", { real: true })])), Qs("k", [symbol("k", { real: true })])), "FourierTransform(f(x), x, k)"],
    ["fourierTransform(Qs(\"exp(-a*x)*Heaviside(x)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("exp(-a*x)*Heaviside(x)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "1/(a + 2*I*pi*k)"],
    ["fourierTransform(Qs(\"x*exp(-a*x)*Heaviside(x)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("x*exp(-a*x)*Heaviside(x)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "(a + 2*I*pi*k)**(-2)"],
    ["fourierTransform(Qs(\"exp(-a*x**2)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("exp(-a*x**2)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)"],
    ["fourierTransform(Qs(\"exp(-a*Abs(x))\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("exp(-a*Abs(x))", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "2*a/(a**2 + 4*pi**2*k**2)"],
    ["fourierTransform(Qs(\"exp(x)\", [symbol(\"y\", { real: true }), symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"y\", { real: true }), symbol(\"x\", { real: true })])), Qs(\"y\", [symbol(\"y\", { real: true }), symbol(\"x\", { real: true })]))", () => fourierTransform(Qs("exp(x)", [symbol("y", { real: true }), symbol("x", { real: true })]), V(Qs("x", [symbol("y", { real: true }), symbol("x", { real: true })])), Qs("y", [symbol("y", { real: true }), symbol("x", { real: true })])), "FourierTransform(exp(x), x, y)"],
    ["inverseFourierTransform(P(\"f(s)\"), V(P(\"s\")), P(\"x\"))", () => inverseFourierTransform(PH("f(s)"), V(PH("s")), PH("x")), "InverseFourierTransform(f(s), s, x)"],
    ["inverseFourierTransform(Qs(\"f(k)\", [symbol(\"k\", { real: true })]), V(Qs(\"k\", [symbol(\"k\", { real: true })])), Qs(\"x\", [symbol(\"k\", { real: true })]))", () => inverseFourierTransform(Qs("f(k)", [symbol("k", { real: true })]), V(Qs("k", [symbol("k", { real: true })])), Qs("x", [symbol("k", { real: true })])), "InverseFourierTransform(f(k), k, x)"],
    ["inverseFourierTransform(Qs(\"sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => inverseFourierTransform(Qs("sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), "exp(-a*x**2)"],
    ["sineTransform(P(\"f(t)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(PH("f(t)"), V(PH("t")), PH("w")), "SineTransform(f(t), t, w)"],
    ["sineTransform(P(\"1/sqrt(t)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(PH("1/sqrt(t)"), V(PH("t")), PH("w")), "1/sqrt(w)"],
    ["sineTransform(P(\"t**(-3/2)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(PH("t**(-3/2)"), V(PH("t")), PH("w")), "2*sqrt(w)"],
    ["sineTransform(P(\"t**(-a)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(PH("t**(-a)"), V(PH("t")), PH("w")), "2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)"],
    ["sineTransform(P(\"exp(-a*t)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(PH("exp(-a*t)"), V(PH("t")), PH("w")), "sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))"],
    ["sineTransform(P(\"t*exp(-a*t**2)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(PH("t*exp(-a*t**2)"), V(PH("t")), PH("w")), "sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))"],
    ["inverseSineTransform(P(\"f(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(PH("f(w)"), V(PH("w")), PH("t")), "InverseSineTransform(f(w), w, t)"],
    ["inverseSineTransform(P(\"1/sqrt(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(PH("1/sqrt(w)"), V(PH("w")), PH("t")), "1/sqrt(t)"],
    ["inverseSineTransform(P(\"2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(PH("2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)"), V(PH("w")), PH("t")), "t**(-a)"],
    ["inverseSineTransform(P(\"sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(PH("sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))"), V(PH("w")), PH("t")), "exp(-a*t)"],
    ["inverseSineTransform(P(\"sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(PH("sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))"), V(PH("w")), PH("t")), "t*exp(-a*t**2)"],
    ["cosineTransform(P(\"f(t)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(PH("f(t)"), V(PH("t")), PH("w")), "CosineTransform(f(t), t, w)"],
    ["cosineTransform(P(\"1/sqrt(t)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(PH("1/sqrt(t)"), V(PH("t")), PH("w")), "1/sqrt(w)"],
    ["cosineTransform(P(\"1/(a**2 + t**2)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(PH("1/(a**2 + t**2)"), V(PH("t")), PH("w")), "sqrt(2)*sqrt(pi)*exp(-a*w)/(2*a)"],
    ["cosineTransform(P(\"t**(-a)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(PH("t**(-a)"), V(PH("t")), PH("w")), "2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)"],
    ["cosineTransform(P(\"exp(-a*t)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(PH("exp(-a*t)"), V(PH("t")), PH("w")), "sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))"],
    ["cosineTransform(P(\"exp(-a*sqrt(t))*cos(a*sqrt(t))\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(PH("exp(-a*sqrt(t))*cos(a*sqrt(t))"), V(PH("t")), PH("w")), "a*exp(-a**2/(2*w))/(2*w**(3/2))"],
    ["inverseCosineTransform(P(\"f(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(PH("f(w)"), V(PH("w")), PH("t")), "InverseCosineTransform(f(w), w, t)"],
    ["inverseCosineTransform(P(\"1/sqrt(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(PH("1/sqrt(w)"), V(PH("w")), PH("t")), "1/sqrt(t)"],
    ["inverseCosineTransform(P(\"2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(PH("2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)"), V(PH("w")), PH("t")), "t**(-a)"],
    ["inverseCosineTransform(P(\"sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(PH("sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))"), V(PH("w")), PH("t")), "exp(-a*t)"],
    ["hankelTransform(P(\"1/r\"), V(P(\"r\")), P(\"k\"), 0)", () => hankelTransform(PH("1/r"), V(PH("r")), PH("k"), 0), "1/k"],
    ["hankelTransform(P(\"r**(-m)\"), V(P(\"r\")), P(\"k\"), P(\"nu\"))", () => hankelTransform(PH("r**(-m)"), V(PH("r")), PH("k"), PH("nu")), "2*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/(2**m*gamma(m/2 + nu/2))"],
    ["inverseHankelTransform(P(\"1/k\"), V(P(\"k\")), P(\"r\"), 0)", () => inverseHankelTransform(PH("1/k"), V(PH("k")), PH("r"), 0), "1/r"],
    ["inverseHankelTransform(P(\"2**(1 - m)*k**(m - 2)*gamma(1 - m/2)/gamma(m/2)\"), V(P(\"k\")), P(\"r\"), 0)", () => inverseHankelTransform(PH("2**(1 - m)*k**(m - 2)*gamma(1 - m/2)/gamma(m/2)"), V(PH("k")), PH("r"), 0), "r**(-m)"],
    ["inverseHankelTransform(P(\"2**(1 - m)*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/gamma(m/2 + nu/2)\"), V(P(\"k\")), P(\"r\"), P(\"nu\"))", () => inverseHankelTransform(PH("2**(1 - m)*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/gamma(m/2 + nu/2)"), V(PH("k")), PH("r"), PH("nu")), "r**(-m)"],
    ["inverseHankelTransform(P(\"2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)\"), V(P(\"k\")), P(\"r\"), P(\"nu\"))", () => inverseHankelTransform(PH("2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)"), V(PH("k")), PH("r"), PH("nu")), "r**nu*exp(-a*r)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});


const [x, s, t, k, a, b] = symbols('x s t k a b');
const nu = symbol('nu');
const p = symbol('p', { positive: true });
const Px = (q: string) => parse(q, { symbols: [x, s, t, k, a, b, nu, p], locals: { Heaviside, DiracDelta } });

describe("integral transforms: more SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["fourierTransform(P('exp(-x**2)'), x, k)", () => fourierTransform(Px('exp(-x**2)'), x, k), "sqrt(pi)*exp(-pi**2*k**2)"],
    ["fourierTransform(P('exp(-p*x**2)'), x, k)", () => fourierTransform(Px('exp(-p*x**2)'), x, k), "sqrt(pi)*exp(-pi**2*k**2/p)/sqrt(p)"],
    ["fourierTransform(P('exp(-Abs(x))'), x, k)", () => fourierTransform(Px('exp(-Abs(x))'), x, k), "2/(4*pi**2*k**2 + 1)"],
    ["fourierTransform(P('Heaviside(x)*exp(-x)'), x, k)", () => fourierTransform(Px('Heaviside(x)*exp(-x)'), x, k), "1/(2*I*pi*k + 1)"],
    ["fourierTransform(P('x*exp(-x**2)'), x, k)", () => fourierTransform(Px('x*exp(-x**2)'), x, k), "-I*pi**(3/2)*k*exp(-pi**2*k**2)"],
    ["fourierTransform(P('DiracDelta(x)'), x, k)", () => fourierTransform(Px('DiracDelta(x)'), x, k), "1"],
    ["fourierTransform(P('DiracDelta(x - 1)'), x, k)", () => fourierTransform(Px('DiracDelta(x - 1)'), x, k), "exp(-2*I*pi*k)"],
    ["fourierTransform(P('exp(-x)*Heaviside(x)*x'), x, k)", () => fourierTransform(Px('exp(-x)*Heaviside(x)*x'), x, k), "(2*I*pi*k + 1)**(-2)"],
    ["sineTransform(P('exp(-x)'), x, k)", () => sineTransform(Px('exp(-x)'), x, k), "sqrt(2)*k/(sqrt(pi)*(k**2 + 1))"],
    ["cosineTransform(P('exp(-x)'), x, k)", () => cosineTransform(Px('exp(-x)'), x, k), "sqrt(2)/(sqrt(pi)*(k**2 + 1))"],
    ["sineTransform(P('x*exp(-x)'), x, k)", () => sineTransform(Px('x*exp(-x)'), x, k), "2*sqrt(2)*k/(sqrt(pi)*(k**2 + 1)**2)"],
    ["sineTransform(P('1/x'), x, k)", () => sineTransform(Px('1/x'), x, k), "sqrt(2)*sqrt(pi)/2"],
    ["sineTransform(P('exp(-p*x)'), x, k)", () => sineTransform(Px('exp(-p*x)'), x, k), "sqrt(2)*k/(sqrt(pi)*(k**2 + p**2))"],
    ["cosineTransform(P('exp(-p*x)'), x, k)", () => cosineTransform(Px('exp(-p*x)'), x, k), "sqrt(2)*p/(sqrt(pi)*(k**2 + p**2))"],
    ["sineTransform(P('x/(x**2 + 1)'), x, k)", () => sineTransform(Px('x/(x**2 + 1)'), x, k), "sqrt(2)*sqrt(pi)*exp(-k)/2"],
    ["sineTransform(P('1/sqrt(x)'), x, k)", () => sineTransform(Px('1/sqrt(x)'), x, k), "1/sqrt(k)"],
    ["cosineTransform(P('1/sqrt(x)'), x, k)", () => cosineTransform(Px('1/sqrt(x)'), x, k), "1/sqrt(k)"],
    ["cosineTransform(P('exp(-x**2)'), x, k)", () => cosineTransform(Px('exp(-x**2)'), x, k), "sqrt(2)*exp(-k**2/4)/2"],
    ["hankelTransform(P('1/x'), x, k, 0)", () => hankelTransform(Px('1/x'), x, k, 0), "1/k"],
    ["inverseHankelTransform(P('1/x'), x, k, 0)", () => inverseHankelTransform(Px('1/x'), x, k, 0), "1/k"],
    ["hankelTransform(P('exp(-x**2)'), x, k, 0)", () => hankelTransform(Px('exp(-x**2)'), x, k, 0), "exp(-k**2/4)/2"],
    ["inverseHankelTransform(P('exp(-x**2)'), x, k, 0)", () => inverseHankelTransform(Px('exp(-x**2)'), x, k, 0), "exp(-k**2/4)/2"],
    ["hankelTransform(P('1/sqrt(x**2 + 1)'), x, k, 0)", () => hankelTransform(Px('1/sqrt(x**2 + 1)'), x, k, 0), "exp(-k)/k"],
    ["inverseHankelTransform(P('1/sqrt(x**2 + 1)'), x, k, 0)", () => inverseHankelTransform(Px('1/sqrt(x**2 + 1)'), x, k, 0), "exp(-k)/k"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

// Fourier, sine, cosine and Hankel transforms; expected values from SymPy 1.14
// (x, k, r, nu, m plain symbols; ap and bp are the positive symbols a and b).

const [r, m] = symbols('r m');
const ap = new Sym('a', { positive: true });
const bp = new Sym('b', { positive: true });
const Pf = (q: string): Expr => parse(q, { symbols: [x, k, r, nu, m, ap, bp], locals: { Heaviside, DiracDelta } });
const showT = (v: TransformResult): string => (Array.isArray(v) ? `(${v.map((e) => sstr(e as Expr)).join(', ')})` : sstr(v as Expr));

describe('fourier_transform', () => {
  const cases: [string, () => TransformResult, string][] = [
    // DiracDelta of a polynomial: the sum over its simple real roots
    ['DiracDelta(x**2 - 1)', () => fourierTransform(Pf('DiracDelta(x**2 - 1)'), x, k), 'cos(2*pi*k)'],
    ['DiracDelta(x**2 - a**2)', () => fourierTransform(Pf('DiracDelta(x**2 - a**2)'), x, k), 'cos(2*pi*a*k)/a'],
    ['DiracDelta(x**3 - x)', () => fourierTransform(Pf('DiracDelta(x**3 - x)'), x, k), 'cos(2*pi*k) + 1'],
    ['DiracDelta(x - 1)*exp(x)', () => fourierTransform(Pf('DiracDelta(x - 1)*exp(x)'), x, k), 'exp(-2*I*pi*k + 1)'],
    ['DiracDelta(x - 1)*x', () => fourierTransform(Pf('DiracDelta(x - 1)*x'), x, k), 'exp(-2*I*pi*k)'],
    ['DiracDelta(m*x - 1)', () => fourierTransform(Pf('DiracDelta(m*x - 1)'), x, k), 'exp(-2*I*pi*k/m)/Abs(m)'],
    // a double root and no real root: unevaluated in SymPy too
    ['DiracDelta(x**2)', () => fourierTransform(Pf('DiracDelta(x**2)'), x, k), 'FourierTransform(DiracDelta(x**2), x, k)'],
    ['DiracDelta(x**2 + 1)', () => fourierTransform(Pf('DiracDelta(x**2 + 1)'), x, k), 'FourierTransform(DiracDelta(x**2 + 1), x, k)'],
    // SymPy gives cos(2*pi*k*sqrt(m))/Abs(sqrt(m)), which is wrong for m < 0 (no real root: the transform is 0)
    ['DiracDelta(x**2 - m)', () => fourierTransform(Pf('DiracDelta(x**2 - m)'), x, k), 'FourierTransform(DiracDelta(-m + x**2), x, k)'],
    ['Heaviside(x)*x**2*exp(-a*x)', () => fourierTransform(Pf('Heaviside(x)*x**2*exp(-a*x)'), x, k), '2/(a + 2*I*pi*k)**3'],
    // convergent only for Re(c) > 0: unevaluated in SymPy for c = m and c = -I
    ['Heaviside(x)*exp(-m*x)', () => fourierTransform(Pf('Heaviside(x)*exp(-m*x)'), x, k), 'FourierTransform(exp(-m*x)*Heaviside(x), x, k)'],
    ['Heaviside(x)*exp(I*x)', () => fourierTransform(Pf('Heaviside(x)*exp(I*x)'), x, k), 'FourierTransform(exp(I*x)*Heaviside(x), x, k)'],
    ['exp(-m*x**2)', () => fourierTransform(Pf('exp(-m*x**2)'), x, k), 'FourierTransform(exp(-m*x**2), x, k)'],
    ['exp(-m*Abs(x))', () => fourierTransform(Pf('exp(-m*Abs(x))'), x, k), 'FourierTransform(exp(-m*Abs(x)), x, k)'],
    ['exp(x**2)', () => fourierTransform(Pf('exp(x**2)'), x, k), 'FourierTransform(exp(x**2), x, k)'],
    ['exp(-x)', () => fourierTransform(Pf('exp(-x)'), x, k), 'FourierTransform(exp(-x), x, k)'],
    ['exp(sin(x))', () => fourierTransform(Pf('exp(sin(x))'), x, k), 'FourierTransform(exp(sin(x)), x, k)'],
    ['x**m*exp(-x**2)', () => fourierTransform(Pf('x**m*exp(-x**2)'), x, k), 'FourierTransform(x**m*exp(-x**2), x, k)'],
    ['Heaviside(x)*log(x)', () => fourierTransform(Pf('Heaviside(x)*log(x)'), x, k), 'FourierTransform(log(x)*Heaviside(x), x, k)'],
    ['Heaviside(x)*exp(x)', () => fourierTransform(Pf('Heaviside(x)*exp(x)'), x, k), 'FourierTransform(exp(x)*Heaviside(x), x, k)'],
    ['Heaviside(x)*x', () => fourierTransform(Pf('Heaviside(x)*x'), x, k), 'FourierTransform(x*Heaviside(x), x, k)'],
    ['exp(-x**2) + log(x)', () => fourierTransform(Pf('exp(-x**2) + log(x)'), x, k), 'FourierTransform(log(x), x, k) + sqrt(pi)*exp(-pi**2*k**2)'],
    ['exp(-x**2), noconds=False', () => fourierTransform(Pf('exp(-x**2)'), x, k, { noconds: false }), '(sqrt(pi)*exp(-pi**2*k**2), True)'],
    ['x**2*exp(-x**2), noconds=False', () => fourierTransform(Pf('exp(-x**2)*x**2'), x, k, { noconds: false }), '(sqrt(pi)*(-pi**2*k**2 + 1/2)*exp(-pi**2*k**2), True)'],
    ['inverse of sqrt(pi)*exp(-pi**2*k**2)', () => inverseFourierTransform(Pf('sqrt(pi)*exp(-pi**2*k**2)'), k, x), 'exp(-x**2)'],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(showT(f())).toBe(want));
});

describe('sine and cosine transforms', () => {
  const cases: [string, () => TransformResult, string][] = [
    ['inverse sine of a Gaussian', () => inverseSineTransform(Pf('sqrt(2)*k*exp(-k**2/(4*a))/(4*a**(3/2))'), k, x), 'x*exp(-a*x**2)'],
    ['inverse cosine of a Lorentzian', () => inverseCosineTransform(Pf('sqrt(2)*a/(sqrt(pi)*(a**2 + k**2))'), k, x), 'exp(-a*x)'],
    ['sine x/(x**2 + b**2)', () => sineTransform(Pf('x/(x**2 + b**2)'), x, k), 'sqrt(2)*sqrt(pi)*exp(-b*k)/2'],
    ['cosine 1/(x**2 + b**2)', () => cosineTransform(Pf('1/(x**2 + b**2)'), x, k), 'sqrt(2)*sqrt(pi)*exp(-b*k)/(2*b)'],
    ['cosine exp(-a*sqrt(x))*cos(a*sqrt(x))', () => cosineTransform(Pf('exp(-a*sqrt(x))*cos(a*sqrt(x))'), x, k), 'a*exp(-a**2/(2*k))/(2*k**(3/2))'],
    ['sine x**(-1/2)', () => sineTransform(Pf('x**(-1/2)'), x, k), '1/sqrt(k)'],
    ['cosine x**(-1/2)', () => cosineTransform(Pf('x**(-1/2)'), x, k), '1/sqrt(k)'],
    ['sine x**m', () => sineTransform(Pf('x**m'), x, k), '2**(m + 1/2)*k**(-m - 1)*gamma(m/2 + 1)/gamma(1/2 - m/2)'],
    ['sine x*exp(-a*x)', () => sineTransform(Pf('x*exp(-a*x)'), x, k), '2*sqrt(2)*a*k/(sqrt(pi)*(a**2 + k**2)**2)'],
    ['cosine exp(-m*x)', () => cosineTransform(Pf('exp(-m*x)'), x, k), 'sqrt(2)*m/(sqrt(pi)*(k**2 + m**2))'],
    // outside the strips of convergence: unevaluated in SymPy too
    ['sine x**2', () => sineTransform(Pf('x**2'), x, k), 'SineTransform(x**2, x, k)'],
    ['cosine x', () => cosineTransform(Pf('x'), x, k), 'CosineTransform(x, x, k)'],
    ['sine exp(x)', () => sineTransform(Pf('exp(x)'), x, k), 'SineTransform(exp(x), x, k)'],
    ['cosine exp(x**2)', () => cosineTransform(Pf('exp(x**2)'), x, k), 'CosineTransform(exp(x**2), x, k)'],
    ['cosine exp(-m*x**2)', () => cosineTransform(Pf('exp(-m*x**2)'), x, k), 'sqrt(2)*exp(-k**2/(4*m))/(2*sqrt(m))'],
    ['sine log(x)', () => sineTransform(Pf('log(x)'), x, k), 'SineTransform(log(x), x, k)'],
    // SymPy's Meijer G integrator evaluates these; symjs's table does not have them:
    // sqrt(2)*atan(k/a)/sqrt(pi)
    ['sine exp(-a*x)/x', () => sineTransform(Pf('exp(-a*x)/x'), x, k), 'SineTransform(exp(-a*x)/x, x, k)'],
    // sqrt(2)/(2*sqrt(pi)*a) + sqrt(2)*I*k*exp(-k**2/(4*a))*erf(I*k/(2*sqrt(a)))/(4*a**(3/2))
    ['cosine x*exp(-a*x**2)', () => cosineTransform(Pf('x*exp(-a*x**2)'), x, k), 'CosineTransform(x*exp(-a*x**2), x, k)'],
    // -sqrt(2)*I*exp(-k**2/(4*a))*erf(I*k/(2*sqrt(a)))/(2*sqrt(a))
    ['sine exp(-a*x**2)', () => sineTransform(Pf('exp(-a*x**2)'), x, k), 'SineTransform(exp(-a*x**2), x, k)'],
    // sqrt(2)*((pi - 2*Si(k))*sin(k)/2 - cos(k)*Ci(k))/sqrt(pi)
    ['cosine 1/(x + 1)', () => cosineTransform(Pf('1/(x + 1)'), x, k), 'CosineTransform(1/(x + 1), x, k)'],
    // -sqrt(2)*sqrt(pi)*(b*k*sinh(b*k) - b*k*cosh(b*k) + sinh(b*k) - cosh(b*k))/(4*b**3)
    ['cosine 1/(x**2 + b**2)**2', () => cosineTransform(Pf('1/(x**2 + b**2)**2'), x, k), 'CosineTransform(1/(b**4 + 2*b**2*x**2 + x**4), x, k)'],
    // (SymPy: a long expression in fresnels and fresnelc)
    ['cosine exp(-a*sqrt(x))*sin(a*sqrt(x))', () => cosineTransform(Pf('exp(-a*sqrt(x))*sin(a*sqrt(x))'), x, k), 'CosineTransform(exp(-a*sqrt(x))*sin(a*sqrt(x)), x, k)'],
    // (SymPy does not finish these within 20 s)
    ['cosine exp(-x)*log(x)', () => cosineTransform(Pf('log(x)*exp(-x)'), x, k), 'CosineTransform(exp(-x)*log(x), x, k)'],
    ['cosine exp(-a*sqrt(x))*cos(b*sqrt(x))', () => cosineTransform(Pf('exp(-a*sqrt(x))*cos(b*sqrt(x))'), x, k), 'CosineTransform(exp(-a*sqrt(x))*cos(b*sqrt(x)), x, k)'],
    ['cosine sqrt(1/x**2 + sin(x))', () => cosineTransform(Pf('sqrt(1/x**2 + sin(x))'), x, k), 'CosineTransform(sqrt(sin(x) + x**(-2)), x, k)'],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(showT(f())).toBe(want));

  it('noconds and simplify hints', () => {
    // SymPy: (sqrt(2)*sqrt(pi)*exp(-b*k)/(2*b), Eq(Abs(arg(k)), 0)); the condition of the Meijer G
    // integrator on arg(k) is not derived, k is taken positive
    expect(showT(cosineTransform(Pf('1/(x**2 + b**2)'), x, k, { noconds: false }))).toBe('(sqrt(2)*sqrt(pi)*exp(-b*k)/(2*b), True)');
    // SymPy: sqrt(2)/(sqrt(pi)*a*(1 + k**2/a**2)), the same function
    expect(showT(cosineTransform(Pf('exp(-a*x)'), x, k, { simplify: false }))).toBe('sqrt(2)*a/(sqrt(pi)*(a**2 + k**2))');
  });
});

describe('hankel_transform', () => {
  const cases: [string, () => TransformResult, string][] = [
    ['r**nu*exp(-a*r), order nu', () => hankelTransform(Pf('r**(nu - 1)*exp(-a*r)'), r, k, nu), '2**nu*k**(-nu - 1)*(a**2/k**2 + 1)**(-nu - 1/2)*gamma(nu + 1/2)/sqrt(pi)'],
    ['r*exp(-a*r**2), order 1', () => hankelTransform(Pf('r*exp(-a*r**2)'), r, k, 1), 'k*exp(-k**2/(4*a))/(4*a**2)'],
    ['r**2*exp(-a*r**2), order 0', () => hankelTransform(Pf('r**2*exp(-a*r**2)'), r, k, 0), '(4*a - k**2)*exp(-k**2/(4*a))/(8*a**3)'],
    ['r/(r**2 + b**2)**(3/2), order 1', () => hankelTransform(Pf('r/(r**2 + b**2)**(3/2)'), r, k, 1), 'exp(-b*k)'],
    ['1/sqrt(r**2 + b**2), order 0', () => hankelTransform(Pf('1/(r**2 + b**2)**(1/2)'), r, k, 0), 'exp(-b*k)/k'],
    ['1/(r**2 + b**2)**(3/2), order 0', () => hankelTransform(Pf('1/(r**2 + b**2)**(3/2)'), r, k, 0), 'exp(-b*k)/b'],
    ['noconds=False', () => hankelTransform(Pf('r*exp(-a*r**2)'), r, k, 1, { noconds: false }), '(k*exp(-k**2/(4*a))/(4*a**2), True)'],
    ['inverse of k*exp(-k**2/(4*a))/(4*a**2)', () => inverseHankelTransform(Pf('r*exp(-a*r**2)'), r, k, 1), 'k*exp(-k**2/(4*a))/(4*a**2)'],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(showT(f())).toBe(want));

  it('forms that differ from SymPy only in how they are written', () => {
    // SymPy: 2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi);
    // symjs's Mul keeps 2*2**nu apart
    expect(showT(hankelTransform(Pf('r**nu*exp(-a*r)'), r, k, nu))).toBe('2*2**nu*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)');
    // (SymPy prints 2*2**m here too)
    expect(showT(hankelTransform(Pf('r**m'), r, k, nu))).toBe('2*2**m*k**(-m - 2)*gamma(m/2 + nu/2 + 1)/gamma(-m/2 + nu/2)');
    // SymPy: meijerg(((0,), ()), ((0, 0), (0,)), b**2*k**2/4)/2, which is besselk(0, b*k)
    // (both 0.034739504386279248072 at b*k = 3 with mpmath)
    expect(showT(hankelTransform(Pf('1/(r**2 + b**2)'), r, k, 0))).toBe('besselk(0, b*k)');
  });

  it('raises like SymPy when the integral is not known', () => {
    // SymPy: sqrt(pi)*k*(besseli(0, k**2/(8*a)) - besseli(1, k**2/(8*a)))*exp(-k**2/(8*a))/(8*a**(3/2))
    expect(() => hankelTransform(Pf('exp(-a*r**2)'), r, k, 1)).toThrow('Hankel Transform could not be computed');
    // SymPy: -pi*besseli(1, b*k)/2 + hyper((1,), (1/2, 3/2), b**2*k**2/4)
    expect(() => hankelTransform(Pf('1/(r**2 + b**2)'), r, k, 1)).toThrow('Hankel Transform could not be computed');
    // SymPy: b*sinh(b*k) - b*cosh(b*k) - sinh(b*k)/k + cosh(b*k)/k
    expect(() => hankelTransform(Pf('r**2/(r**2 + b**2)**(3/2)'), r, k, 0)).toThrow('Hankel Transform could not be computed');
    // divergent
    expect(() => hankelTransform(Pf('exp(r)'), r, k, 0)).toThrow('Hankel Transform could not be computed');
    expect(() => inverseHankelTransform(Pf('log(k)'), k, r, 0)).toThrow('Inverse Hankel Transform could not be computed');
  });
});

describe('the unevaluated transform objects', () => {
  const objs = [
    new FourierTransform(Pf('exp(x)'), x, k),
    new InverseFourierTransform(Pf('exp(x)'), x, k),
    new SineTransform(Pf('exp(x)'), x, k),
    new InverseSineTransform(Pf('exp(x)'), x, k),
    new CosineTransform(Pf('exp(x)'), x, k),
    new InverseCosineTransform(Pf('exp(x)'), x, k),
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
    const h = new HankelTransform(Pf('exp(-a*r)'), r, k, 0);
    const ih = new InverseHankelTransform(Pf('exp(-a*k)'), k, r, 0);
    expect(sstr(h.asIntegral)).toBe('Integral(r*exp(-a*r)*besselj(0, k*r), (r, 0, oo))');
    expect(sstr(h.subs(k, 2))).toBe('HankelTransform(exp(-a*r), r, 2, 0)');
    expect(sstr(ih.subs(r, 2))).toBe('InverseHankelTransform(exp(-a*k), k, 2, 0)');
    // SymPy prints the Hankel transforms in the generic form
    expect(latex(h)).toBe('\\operatorname{HankelTransform}{\\left(e^{- a r},r,k,0 \\right)}');
    expect(latex(ih)).toBe('\\operatorname{InverseHankelTransform}{\\left(e^{- a k},k,r,0 \\right)}');
    // a function variable that is not a symbol stays (SymPy: ValueError for the invalid limits of the Integral)
    expect(sstr(new HankelTransform(Pf('exp(-a*r)'), 2, k, 0).doit() as Expr)).toBe('HankelTransform(exp(-a*r), 2, k, 0)');
  });
});

describe('Heaviside(x) factors over the half line', () => {
  it('sines and cosines are written with exponentials', () => {
    // SymPy: 1/((2*I*pi*k + 1)**2 + 1), the same rational function
    const F = fourierTransform(Pf('Heaviside(x)*exp(-x)*sin(x)'), x, k) as Expr;
    expect(sstr(simplify(sub(F, Pf('1/((2*I*pi*k + 1)**2 + 1)'))))).toBe('0');
  });
  it('exponents that are not linear in x are not in the table', () => {
    // SymPy: sqrt(pi)*exp(-pi**2*k**2)*erfc(I*pi*k)/2
    expect(showT(fourierTransform(Pf('Heaviside(x)*exp(-x**2)'), x, k))).toBe('FourierTransform(exp(-x**2)*Heaviside(x), x, k)');
    // SymPy: an expression in erf((-1)**(3/4)*sqrt(2)/(4*sqrt(pi)*sqrt(k)))
    expect(showT(fourierTransform(Pf('Heaviside(x)*exp(-sqrt(x))'), x, k))).toBe('FourierTransform(exp(-sqrt(x))*Heaviside(x), x, k)');
  });
});

describe('the hyperexpand form of the Hankel transforms', () => {
  // (A + k**2)**p = k**(2*p)*(A/k**2 + 1)**p for k > 0, the form of SymPy's hyperexpand
  it('rewrites powers of A + k**2 only', () => {
    expect(sstr(hyperexpandForm(Pf('(a**2 + k**2)**(-3/2)'), k))).toBe('1/(k**3*(a**2/k**2 + 1)**(3/2))');
    // no k**2 term, or a k in A: unchanged
    expect(sstr(hyperexpandForm(Pf('(a + k)**(1/2)'), k))).toBe('sqrt(a + k)');
    expect(sstr(hyperexpandForm(Pf('(k**2 + (k + 1)**2)**(3/2)'), k))).toBe('(k**2 + (k + 1)**2)**(3/2)');
  });
});
