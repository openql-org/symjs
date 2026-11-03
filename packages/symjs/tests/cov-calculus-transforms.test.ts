// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Sym, cosineTransform, fourierTransform, hankelTransform, inverseCosineTransform, inverseFourierTransform, inverseHankelTransform, inverseMellinTransform, inverseSineTransform, mellinTransform, parse, sineTransform, symbol } from '../src';
import type { Expr } from '../src';

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
/** The variable argument as a symbol. */
const V = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

describe("integral transforms: SymPy 1.14 test_transforms cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["mellinTransform(P(\"f(x)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("f(x)"), V(P("x")), P("s")), "MellinTransform(f(x), x, s)"],
    ["mellinTransform(P(\"a*f(x)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("a*f(x)"), V(P("x")), P("s")), "a*MellinTransform(f(x), x, s)"],
    ["mellinTransform(P(\"1/(1 - x)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("1/(1 - x)"), V(P("x")), P("s")), "MellinTransform(1/(1 - x), x, s)"],
    ["mellinTransform(P(\"x**nu*Heaviside(x - 1)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("x**nu*Heaviside(x - 1)"), V(P("x")), P("s")), "(-1/(nu + s), (-oo, -re(nu)), True)"],
    ["mellinTransform(P(\"x**nu*Heaviside(1 - x)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("x**nu*Heaviside(1 - x)"), V(P("x")), P("s")), "(1/(nu + s), (-re(nu), oo), True)"],
    ["mellinTransform(P(\"(x + 1)**(-rho)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("(x + 1)**(-rho)"), V(P("x")), P("s")), "(gamma(s)*gamma(rho - s)/gamma(rho), (0, re(rho)), True)"],
    ["mellinTransform(P(\"exp(-x)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("exp(-x)"), V(P("x")), P("s")), "(gamma(s), (0, oo), True)"],
    ["mellinTransform(P(\"exp(-1/x)\"), V(P(\"x\")), P(\"s\"))", () => mellinTransform(P("exp(-1/x)"), V(P("x")), P("s")), "(gamma(-s), (-oo, 0), True)"],
    ["inverseMellinTransform(P(\"f(s)\"), V(P(\"s\")), P(\"x\"), [P(\"a\"), P(\"b\")])", () => inverseMellinTransform(P("f(s)"), V(P("s")), P("x"), [P("a"), P("b")]), "InverseMellinTransform(f(s), s, x, a, b)"],
    ["inverseMellinTransform(P(\"gamma(s)\"), V(P(\"s\")), P(\"x\"), [0, P(\"oo\")])", () => inverseMellinTransform(P("gamma(s)"), V(P("s")), P("x"), [0, P("oo")]), "exp(-x)"],
    ["inverseMellinTransform(P(\"gamma(-s)\"), V(P(\"s\")), P(\"x\"), [P(\"-oo\"), 0])", () => inverseMellinTransform(P("gamma(-s)"), V(P("s")), P("x"), [P("-oo"), 0]), "exp(-1/x)"],
    ["inverseMellinTransform(P(\"s/(2*s**2 - 2)\"), V(P(\"s\")), P(\"x\"), [2, P(\"oo\")])", () => inverseMellinTransform(P("s/(2*s**2 - 2)"), V(P("s")), P("x"), [2, P("oo")]), "(x**2/2 + 1/2)*Heaviside(1 - x)/(2*x)"],
    ["inverseMellinTransform(P(\"1/(s**2 - 1)\"), V(P(\"s\")), P(\"x\"), [-1, undefined])", () => inverseMellinTransform(P("1/(s**2 - 1)"), V(P("s")), P("x"), [-1, undefined]), "-x*Heaviside(1 - x)/2 - Heaviside(x - 1)/(2*x)"],
    ["inverseMellinTransform(P(\"1/(s**2 - 1)\"), V(P(\"s\")), P(\"x\"), [undefined, 1])", () => inverseMellinTransform(P("1/(s**2 - 1)"), V(P("s")), P("x"), [undefined, 1]), "-x*Heaviside(1 - x)/2 - Heaviside(x - 1)/(2*x)"],
    ["inverseMellinTransform(P(\"gamma(s) + gamma(s - 1)\"), V(P(\"s\")), P(\"x\"), [1, P(\"oo\")])", () => inverseMellinTransform(P("gamma(s) + gamma(s - 1)"), V(P("s")), P("x"), [1, P("oo")]), "(x + 1)*exp(-x)/x"],
    ["inverseMellinTransform(Qs(\"factorial(s/a)/(b**(s/a)*s)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"x\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), [0, Qs(\"oo\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])])", () => inverseMellinTransform(Qs("factorial(s/a)/(b**(s/a)*s)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("x", [symbol("b", { positive: true }), symbol("a", { positive: true })]), [0, Qs("oo", [symbol("b", { positive: true }), symbol("a", { positive: true })])]), "exp(-b*x**a)"],
    ["inverseMellinTransform(Qs(\"factorial(a/b + s/b)/(a + s)\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])), Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), [Qs(\"-a\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), Qs(\"oo\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])])", () => inverseMellinTransform(Qs("factorial(a/b + s/b)/(a + s)", [symbol("a", { positive: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("b", { positive: true })])), Qs("x", [symbol("a", { positive: true }), symbol("b", { positive: true })]), [Qs("-a", [symbol("a", { positive: true }), symbol("b", { positive: true })]), Qs("oo", [symbol("a", { positive: true }), symbol("b", { positive: true })])]), "x**a*exp(-x**b)"],
    ["inverseMellinTransform(Qs(\"-1/(nu + s)\", [symbol(\"nu\", { real: true })]), V(Qs(\"s\", [symbol(\"nu\", { real: true })])), Qs(\"x\", [symbol(\"nu\", { real: true })]), [Qs(\"-oo\", [symbol(\"nu\", { real: true })]), undefined])", () => inverseMellinTransform(Qs("-1/(nu + s)", [symbol("nu", { real: true })]), V(Qs("s", [symbol("nu", { real: true })])), Qs("x", [symbol("nu", { real: true })]), [Qs("-oo", [symbol("nu", { real: true })]), undefined]), "x**nu*Heaviside(x - 1)"],
    ["inverseMellinTransform(Qs(\"1/(nu + s)\", [symbol(\"nu\", { real: true })]), V(Qs(\"s\", [symbol(\"nu\", { real: true })])), Qs(\"x\", [symbol(\"nu\", { real: true })]), [undefined, Qs(\"oo\", [symbol(\"nu\", { real: true })])])", () => inverseMellinTransform(Qs("1/(nu + s)", [symbol("nu", { real: true })]), V(Qs("s", [symbol("nu", { real: true })])), Qs("x", [symbol("nu", { real: true })]), [undefined, Qs("oo", [symbol("nu", { real: true })])]), "x**nu*Heaviside(1 - x)"],
    ["inverseMellinTransform(P(\"gamma(s)*gamma(rho - s)/gamma(rho)\"), V(P(\"s\")), P(\"x\"), [0, undefined])", () => inverseMellinTransform(P("gamma(s)*gamma(rho - s)/gamma(rho)"), V(P("s")), P("x"), [0, undefined]), "(x + 1)**(-rho)"],
    ["inverseMellinTransform(P(\"24/s**5\"), V(P(\"s\")), P(\"x\"), [0, P(\"oo\")])", () => inverseMellinTransform(P("24/s**5"), V(P("s")), P("x"), [0, P("oo")]), "log(x)**4*Heaviside(1 - x)"],
    ["inverseMellinTransform(P(\"pi/cos(pi*s)\"), V(P(\"s\")), P(\"x\"), [0, P(\"1/2\")])", () => inverseMellinTransform(P("pi/cos(pi*s)"), V(P("s")), P("x"), [0, P("1/2")]), "sqrt(x)/(x + 1)"],
    ["fourierTransform(P(\"f(x)\"), V(P(\"x\")), P(\"s\"))", () => fourierTransform(P("f(x)"), V(P("x")), P("s")), "FourierTransform(f(x), x, s)"],
    ["fourierTransform(Qs(\"f(x)\", [symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("f(x)", [symbol("k", { real: true })]), V(Qs("x", [symbol("k", { real: true })])), Qs("k", [symbol("k", { real: true })])), "FourierTransform(f(x), x, k)"],
    ["fourierTransform(Qs(\"exp(-a*x)*Heaviside(x)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("exp(-a*x)*Heaviside(x)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "1/(a + 2*I*pi*k)"],
    ["fourierTransform(Qs(\"x*exp(-a*x)*Heaviside(x)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("x*exp(-a*x)*Heaviside(x)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "(a + 2*I*pi*k)**(-2)"],
    ["fourierTransform(Qs(\"exp(-a*x**2)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("exp(-a*x**2)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)"],
    ["fourierTransform(Qs(\"exp(-a*Abs(x))\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => fourierTransform(Qs("exp(-a*Abs(x))", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), "2*a/(a**2 + 4*pi**2*k**2)"],
    ["fourierTransform(Qs(\"exp(x)\", [symbol(\"y\", { real: true }), symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"y\", { real: true }), symbol(\"x\", { real: true })])), Qs(\"y\", [symbol(\"y\", { real: true }), symbol(\"x\", { real: true })]))", () => fourierTransform(Qs("exp(x)", [symbol("y", { real: true }), symbol("x", { real: true })]), V(Qs("x", [symbol("y", { real: true }), symbol("x", { real: true })])), Qs("y", [symbol("y", { real: true }), symbol("x", { real: true })])), "FourierTransform(exp(x), x, y)"],
    ["inverseFourierTransform(P(\"f(s)\"), V(P(\"s\")), P(\"x\"))", () => inverseFourierTransform(P("f(s)"), V(P("s")), P("x")), "InverseFourierTransform(f(s), s, x)"],
    ["inverseFourierTransform(Qs(\"f(k)\", [symbol(\"k\", { real: true })]), V(Qs(\"k\", [symbol(\"k\", { real: true })])), Qs(\"x\", [symbol(\"k\", { real: true })]))", () => inverseFourierTransform(Qs("f(k)", [symbol("k", { real: true })]), V(Qs("k", [symbol("k", { real: true })])), Qs("x", [symbol("k", { real: true })])), "InverseFourierTransform(f(k), k, x)"],
    ["inverseFourierTransform(Qs(\"sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]), V(Qs(\"k\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })])), Qs(\"x\", [symbol(\"a\", { positive: true }), symbol(\"k\", { real: true })]))", () => inverseFourierTransform(Qs("sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)", [symbol("a", { positive: true }), symbol("k", { real: true })]), V(Qs("k", [symbol("a", { positive: true }), symbol("k", { real: true })])), Qs("x", [symbol("a", { positive: true }), symbol("k", { real: true })])), "exp(-a*x**2)"],
    ["sineTransform(P(\"f(t)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(P("f(t)"), V(P("t")), P("w")), "SineTransform(f(t), t, w)"],
    ["sineTransform(P(\"1/sqrt(t)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(P("1/sqrt(t)"), V(P("t")), P("w")), "1/sqrt(w)"],
    ["sineTransform(P(\"t**(-3/2)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(P("t**(-3/2)"), V(P("t")), P("w")), "2*sqrt(w)"],
    ["sineTransform(P(\"t**(-a)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(P("t**(-a)"), V(P("t")), P("w")), "2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)"],
    ["sineTransform(P(\"exp(-a*t)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(P("exp(-a*t)"), V(P("t")), P("w")), "sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))"],
    ["sineTransform(P(\"t*exp(-a*t**2)\"), V(P(\"t\")), P(\"w\"))", () => sineTransform(P("t*exp(-a*t**2)"), V(P("t")), P("w")), "sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))"],
    ["inverseSineTransform(P(\"f(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(P("f(w)"), V(P("w")), P("t")), "InverseSineTransform(f(w), w, t)"],
    ["inverseSineTransform(P(\"1/sqrt(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(P("1/sqrt(w)"), V(P("w")), P("t")), "1/sqrt(t)"],
    ["inverseSineTransform(P(\"2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(P("2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)"), V(P("w")), P("t")), "t**(-a)"],
    ["inverseSineTransform(P(\"sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(P("sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))"), V(P("w")), P("t")), "exp(-a*t)"],
    ["inverseSineTransform(P(\"sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))\"), V(P(\"w\")), P(\"t\"))", () => inverseSineTransform(P("sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))"), V(P("w")), P("t")), "t*exp(-a*t**2)"],
    ["cosineTransform(P(\"f(t)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(P("f(t)"), V(P("t")), P("w")), "CosineTransform(f(t), t, w)"],
    ["cosineTransform(P(\"1/sqrt(t)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(P("1/sqrt(t)"), V(P("t")), P("w")), "1/sqrt(w)"],
    ["cosineTransform(P(\"1/(a**2 + t**2)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(P("1/(a**2 + t**2)"), V(P("t")), P("w")), "sqrt(2)*sqrt(pi)*exp(-a*w)/(2*a)"],
    ["cosineTransform(P(\"t**(-a)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(P("t**(-a)"), V(P("t")), P("w")), "2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)"],
    ["cosineTransform(P(\"exp(-a*t)\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(P("exp(-a*t)"), V(P("t")), P("w")), "sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))"],
    ["cosineTransform(P(\"exp(-a*sqrt(t))*cos(a*sqrt(t))\"), V(P(\"t\")), P(\"w\"))", () => cosineTransform(P("exp(-a*sqrt(t))*cos(a*sqrt(t))"), V(P("t")), P("w")), "a*exp(-a**2/(2*w))/(2*w**(3/2))"],
    ["inverseCosineTransform(P(\"f(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(P("f(w)"), V(P("w")), P("t")), "InverseCosineTransform(f(w), w, t)"],
    ["inverseCosineTransform(P(\"1/sqrt(w)\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(P("1/sqrt(w)"), V(P("w")), P("t")), "1/sqrt(t)"],
    ["inverseCosineTransform(P(\"2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(P("2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)"), V(P("w")), P("t")), "t**(-a)"],
    ["inverseCosineTransform(P(\"sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))\"), V(P(\"w\")), P(\"t\"))", () => inverseCosineTransform(P("sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))"), V(P("w")), P("t")), "exp(-a*t)"],
    ["hankelTransform(P(\"1/r\"), V(P(\"r\")), P(\"k\"), 0)", () => hankelTransform(P("1/r"), V(P("r")), P("k"), 0), "1/k"],
    ["hankelTransform(P(\"r**(-m)\"), V(P(\"r\")), P(\"k\"), P(\"nu\"))", () => hankelTransform(P("r**(-m)"), V(P("r")), P("k"), P("nu")), "2*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/(2**m*gamma(m/2 + nu/2))"],
    ["inverseHankelTransform(P(\"1/k\"), V(P(\"k\")), P(\"r\"), 0)", () => inverseHankelTransform(P("1/k"), V(P("k")), P("r"), 0), "1/r"],
    ["inverseHankelTransform(P(\"2**(1 - m)*k**(m - 2)*gamma(1 - m/2)/gamma(m/2)\"), V(P(\"k\")), P(\"r\"), 0)", () => inverseHankelTransform(P("2**(1 - m)*k**(m - 2)*gamma(1 - m/2)/gamma(m/2)"), V(P("k")), P("r"), 0), "r**(-m)"],
    ["inverseHankelTransform(P(\"2**(1 - m)*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/gamma(m/2 + nu/2)\"), V(P(\"k\")), P(\"r\"), P(\"nu\"))", () => inverseHankelTransform(P("2**(1 - m)*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/gamma(m/2 + nu/2)"), V(P("k")), P("r"), P("nu")), "r**(-m)"],
    ["inverseHankelTransform(P(\"2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)\"), V(P(\"k\")), P(\"r\"), P(\"nu\"))", () => inverseHankelTransform(P("2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)"), V(P("k")), P("r"), P("nu")), "r**nu*exp(-a*r)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
