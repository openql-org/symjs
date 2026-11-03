// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transforms/inverse-laplace.ts.
// The inverse Laplace transform. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  Sym,
  exp,
  mul,
  pow,
  symbols,
  DiracDelta,
  Heaviside,
  inverseLaplaceTransform,
  parse,
  symbol,
  type Expr,
  Derivative,
  Matrix,
  SymFunction,
  expand,
} from '../../../src';
import { InverseLaplaceTransform } from '../../../src/integrals/transforms';
import { at } from '../../../src/core/guard';

describe('sympy.integrals.laplace doctests', () => {
  it('inverse_laplace_transform', () => {
    const [s, t] = symbols('s t');
    const a = new Sym('a', { positive: true });
    expect(String(inverseLaplaceTransform(mul(exp(mul(-1, a, s)), pow(s, -1)), s, t))).toBe('Heaviside(-a + t)');
  });

});

// Expected values are the str() forms printed by SymPy 1.14.

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
/** The variable argument as a symbol. */
const V = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

describe("Laplace transforms: SymPy 1.14 test_laplace cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["inverseLaplaceTransform(Qs(\"F(s)*exp(-a*s)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("F(s)*exp(-a*s)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "InverseLaplaceTransform(F(s), s, -a + t, _None)"],
    ["inverseLaplaceTransform(2, V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(2, V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "2*DiracDelta(t)"],
    ["inverseLaplaceTransform(Qs(\"1/s\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/s", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"s**(-2)\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("s**(-2)", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "t*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"s**(-5)\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("s**(-5)", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "t**4*Heaviside(t)/24"],
    ["inverseLaplaceTransform(Qs(\"s**(-n)\", [symbol(\"t\", { real: true }), symbol(\"n\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true }), symbol(\"n\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true }), symbol(\"n\", { real: true })]))", () => inverseLaplaceTransform(Qs("s**(-n)", [symbol("t", { real: true }), symbol("n", { real: true })]), V(Qs("s", [symbol("t", { real: true }), symbol("n", { real: true })])), Qs("t", [symbol("t", { real: true }), symbol("n", { real: true })])), "t**(n - 1)*Heaviside(t)/gamma(n)"],
    ["inverseLaplaceTransform(Qs(\"a/(a + s)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("a/(a + s)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "a*exp(-a*t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"s/(a + s)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("s/(a + s)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "-a*exp(-a*t)*Heaviside(t) + DiracDelta(t)"],
    ["inverseLaplaceTransform(Qs(\"b*s/(a + s)**2\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("b*s/(a + s)**2", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "b*(-a*t*exp(-a*t)*Heaviside(t) + exp(-a*t)*Heaviside(t))"],
    ["inverseLaplaceTransform(Qs(\"(-a + s)**(-b)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("(-a + s)**(-b)", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "t**(b - 1)*exp(a*t)*Heaviside(t)/gamma(b)"],
    ["inverseLaplaceTransform(Qs(\"(a + s)**(-2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(a + s)**(-2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "t*exp(-a*t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(a + s)**(-5)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(a + s)**(-5)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "t**4*exp(-a*t)*Heaviside(t)/24"],
    ["inverseLaplaceTransform(Qs(\"s**2/(s**2 + 1)\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("s**2/(s**2 + 1)", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "-sin(t)*Heaviside(t) + DiracDelta(t)"],
    ["inverseLaplaceTransform(Qs(\"1 - 1/(s**2 + 1)\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1 - 1/(s**2 + 1)", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "-sin(t)*Heaviside(t) + DiracDelta(t)"],
    ["inverseLaplaceTransform(Qs(\"a/(a**2 + s**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("a/(a**2 + s**2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "sin(a*t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"s/(a**2 + s**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("s/(a**2 + s**2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "cos(a*t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"b/(b**2 + (a + s)**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("b/(b**2 + (a + s)**2)", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "exp(-a*t)*sin(b*t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"b*s/(b**2 + (a + s)**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("b*s/(b**2 + (a + s)**2)", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "b*(-a*exp(-a*t)*sin(b*t)/b + exp(-a*t)*cos(b*t))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"1/(s**2*(s**2 + 1))\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/(s**2*(s**2 + 1))", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "t*Heaviside(t) - sin(t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"b/(-a**2 + s**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("b/(-a**2 + s**2)", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "b*(exp(a*t)*Heaviside(t)/(2*a) - exp(-a*t)*Heaviside(t)/(2*a))"],
    ["inverseLaplaceTransform(Qs(\"b/(s*(a + s))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("b/(s*(a + s))", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "b*(Heaviside(t)/a - exp(-a*t)*Heaviside(t)/a)"],
    ["inverseLaplaceTransform(Qs(\"1/(a*s**2 + b*s + c)\", [symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true }), symbol(\"b\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true }), symbol(\"b\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true }), symbol(\"b\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/(a*s**2 + b*s + c)", [symbol("a", { positive: true }), symbol("c", { positive: true }), symbol("b", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("c", { positive: true }), symbol("b", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("c", { positive: true }), symbol("b", { positive: true }), symbol("t", { real: true })])), "2*exp(-b*t/(2*a))*sin(t*sqrt(4*a*c - b**2)/(2*a))*Heaviside(t)/sqrt(4*a*c - b**2)"],
    ["inverseLaplaceTransform(Qs(\"1/(s*sqrt(k*s)*(-a + c*s))\", [symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"k\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"k\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"k\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/(s*sqrt(k*s)*(-a + c*s))", [symbol("a", { positive: true }), symbol("c", { positive: true }), symbol("t", { real: true }), symbol("k", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("c", { positive: true }), symbol("t", { real: true }), symbol("k", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("c", { positive: true }), symbol("t", { real: true }), symbol("k", { real: true })])), "(-2*c*sqrt(t)/(sqrt(pi)*a) + c**(3/2)*exp(a*t/c)*erf(sqrt(a)*sqrt(t)/sqrt(c))/a**(3/2))*Heaviside(t)/(c*sqrt(k))"],
    ["inverseLaplaceTransform(Qs(\"1/(a + sqrt(c)*sqrt(s))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"c\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"c\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"c\", { positive: true })]))", () => inverseLaplaceTransform(Qs("1/(a + sqrt(c)*sqrt(s))", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("c", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("c", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("c", { positive: true })])), "(-a*exp(a**2*t/c)*erfc(a*sqrt(t)/sqrt(c))/c + 1/(sqrt(pi)*sqrt(c)*sqrt(t)))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"a/(s*(a + b*sqrt(s)))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("a/(s*(a + b*sqrt(s)))", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "(-exp(a**2*t/b**2)*erfc(a*sqrt(t)/b) + 1)*Heaviside(t)"],
    // SymPy 1.14 (and its test of Bateman 5.3 (6)) has erfc(sqrt(b)*sqrt(t)), which is wrong; see inverse-laplace.ts
    ["inverseLaplaceTransform(Qs(\"sqrt(s)*(a - b)/((sqrt(a) + sqrt(s))*(-b + s))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("sqrt(s)*(a - b)/((sqrt(a) + sqrt(s))*(-b + s))", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "(sqrt(a)*sqrt(b)*exp(b*t)*erf(sqrt(b)*sqrt(t)) + a*exp(a*t)*erfc(sqrt(a)*sqrt(t)) - b*exp(b*t))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"a**2/(s**(3/2)*(a + sqrt(s)))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("a**2/(s**(3/2)*(a + sqrt(s)))", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(2*a*sqrt(t)/sqrt(pi) + exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"sqrt(b)*(a - b)/(sqrt(s)*(sqrt(a) + sqrt(s))*(-b + s))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("sqrt(b)*(a - b)/(sqrt(s)*(sqrt(a) + sqrt(s))*(-b + s))", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "(sqrt(a)*exp(b*t)*erf(sqrt(b)*sqrt(t)) + sqrt(b)*exp(a*t)*erfc(sqrt(a)*sqrt(t)) - sqrt(b)*exp(b*t))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(sqrt(a) + sqrt(s))**(-2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(sqrt(a) + sqrt(s))**(-2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(-2*sqrt(a)*sqrt(t)/sqrt(pi) + (-2*a*t + 1)*(erf(sqrt(a)*sqrt(t)) - 1)*exp(a*t) + 1)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"1/(s*(sqrt(a) + sqrt(s))**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/(s*(sqrt(a) + sqrt(s))**2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "((2*t - 1/a)*exp(a*t)*erfc(sqrt(a)*sqrt(t)) + 1/a - 2*sqrt(t)/(sqrt(pi)*sqrt(a)))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"1/(sqrt(s)*(a + sqrt(s))**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/(sqrt(s)*(a + sqrt(s))**2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(-2*a*t*exp(a**2*t)*erfc(a*sqrt(t)) + 2*sqrt(t)/sqrt(pi))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(a + sqrt(s))**(-3)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(a + sqrt(s))**(-3)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(-a*t*(2*a**2*t + 3)*exp(a**2*t)*erfc(a*sqrt(t)) + 2*sqrt(t)*(a**2*t + 1)/sqrt(pi))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"sqrt(s)/(a + sqrt(s))**3\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("sqrt(s)/(a + sqrt(s))**3", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(-2*a*sqrt(t)*(a**2*t + 2)/sqrt(pi) + (2*a**4*t**2 + 5*a**2*t + 1)*exp(a**2*t)*erfc(a*sqrt(t)))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"1/(sqrt(s)*(a + sqrt(s))**3)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("1/(sqrt(s)*(a + sqrt(s))**3)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(-2*a*t**(3/2)/sqrt(pi) + t*(2*a**2*t + 1)*exp(a**2*t)*erfc(a*sqrt(t)))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"3/(a + sqrt(s))**4\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("3/(a + sqrt(s))**4", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "3*(-2*a**3*t**(5/2)*(2*a**2*t + 5)/(3*sqrt(pi)) + t*(4*a**4*t**2 + 12*a**2*t + 3)*exp(a**2*t)*erfc(a*sqrt(t))/3)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(-a + sqrt(s))/(s*(a + sqrt(s)))\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(-a + sqrt(s))/(s*(a + sqrt(s)))", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(2*exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(-a + sqrt(s))**2/(s*(a + sqrt(s))**2)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(-a + sqrt(s))**2/(s*(a + sqrt(s))**2)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(8*a**2*t*exp(a**2*t)*erfc(a*sqrt(t)) - 8*a*sqrt(t)/sqrt(pi) + 1)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(-a + sqrt(s))**3/(s*(a + sqrt(s))**3)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(-a + sqrt(s))**3/(s*(a + sqrt(s))**3)", [symbol("a", { positive: true }), symbol("t", { real: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true })])), "(-8*a*sqrt(t)*(2*a**2*t + 1)/sqrt(pi) + (16*a**4*t**2 + 16*a**2*t + 2)*exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"sqrt(a + s)/(b + s)\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"t\", { real: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("sqrt(a + s)/(b + s)", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("t", { real: true }), symbol("b", { positive: true })])), "(sqrt(a - b)*exp(-b*t)*erf(sqrt(t)*sqrt(a - b)) + exp(-a*t)/(sqrt(pi)*sqrt(t)))*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"(s**2*exp(2*s) + 4*exp(s) - 4)*exp(-2*s)/(s*(s**2 + 1))\", [symbol(\"t\", { real: true })]), V(Qs(\"s\", [symbol(\"t\", { real: true })])), Qs(\"t\", [symbol(\"t\", { real: true })]))", () => inverseLaplaceTransform(Qs("(s**2*exp(2*s) + 4*exp(s) - 4)*exp(-2*s)/(s*(s**2 + 1))", [symbol("t", { real: true })]), V(Qs("s", [symbol("t", { real: true })])), Qs("t", [symbol("t", { real: true })])), "cos(t)*Heaviside(t) + 4*cos(t - 2)*Heaviside(t - 2) - 4*cos(t - 1)*Heaviside(t - 1) - 4*Heaviside(t - 2) + 4*Heaviside(t - 1)"],
    ["inverseLaplaceTransform(P(\"F(s)\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("F(s)"), V(P("s")), P("t")), "InverseLaplaceTransform(F(s), s, t, _None)"],
    ["inverseLaplaceTransform(Qs(\"exp(-a*s)/s\", [symbol(\"a\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true })]))", () => inverseLaplaceTransform(Qs("exp(-a*s)/s", [symbol("a", { positive: true })]), V(Qs("s", [symbol("a", { positive: true })])), Qs("t", [symbol("a", { positive: true })])), "Heaviside(-a + t)"],
    ["inverseLaplaceTransform(Qs(\"exp(-a*s)/(b + s)\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("exp(-a*s)/(b + s)", [symbol("a", { positive: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("b", { positive: true })])), "exp(-b*(-a + t))*Heaviside(-a + t)"],
    ["inverseLaplaceTransform(Qs(\"(b + s)/(a**2 + (b + s)**2)\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("(b + s)/(a**2 + (b + s)**2)", [symbol("a", { positive: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("b", { positive: true })])), "exp(-b*t)*cos(a*t)*Heaviside(t)"],
    ["inverseLaplaceTransform(Qs(\"exp(-a*s)/s**b\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), V(Qs(\"s\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])), Qs(\"t\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]))", () => inverseLaplaceTransform(Qs("exp(-a*s)/s**b", [symbol("a", { positive: true }), symbol("b", { positive: true })]), V(Qs("s", [symbol("a", { positive: true }), symbol("b", { positive: true })])), Qs("t", [symbol("a", { positive: true }), symbol("b", { positive: true })])), "(-a + t)**(b - 1)*Heaviside(-a + t)/gamma(b)"],
    ["inverseLaplaceTransform(P(\"s**42*f(s)\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("s**42*f(s)"), V(P("s")), P("t")), "Derivative(InverseLaplaceTransform(f(s), s, t, _None), (t, 42))"],
    ["inverseLaplaceTransform(P(\"cos(s)\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("cos(s)"), V(P("s")), P("t")), "InverseLaplaceTransform(cos(s), s, t, _None)"],
    ["inverseLaplaceTransform(P(\"5*s**3 + 3*s**2 + 2*s + 1\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("5*s**3 + 3*s**2 + 2*s + 1"), V(P("s")), P("t")), "DiracDelta(t) + 2*DiracDelta(t, 1) + 3*DiracDelta(t, 2) + 5*DiracDelta(t, 3)"],
    ["inverseLaplaceTransform(P(\"exp(-3*s)*cos(sin(7)/2)\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("exp(-3*s)*cos(sin(7)/2)"), V(P("s")), P("t")), "cos(sin(7)/2)*DiracDelta(t - 3)"],
    ["inverseLaplaceTransform(P(\"exp(2*s)\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("exp(2*s)"), V(P("s")), P("t")), "InverseLaplaceTransform(exp(2*s), s, t, _None)"],
    ["inverseLaplaceTransform(Qs(\"exp(r*s)\", [symbol(\"r\", { real: true })]), V(Qs(\"s\", [symbol(\"r\", { real: true })])), Qs(\"t\", [symbol(\"r\", { real: true })]))", () => inverseLaplaceTransform(Qs("exp(r*s)", [symbol("r", { real: true })]), V(Qs("s", [symbol("r", { real: true })])), Qs("t", [symbol("r", { real: true })])), "InverseLaplaceTransform(exp(r*s), s, t, _None)"],
    ["inverseLaplaceTransform(P(\"s**2/(s**2 + cos(sin(7)/2)**2)\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("s**2/(s**2 + cos(sin(7)/2)**2)"), V(P("s")), P("t")), "-sin(t*cos(sin(7)/2))*cos(sin(7)/2)*Heaviside(t) + DiracDelta(t)"],
    ["inverseLaplaceTransform(P(\"1/s - exp(-s)/s\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("1/s - exp(-s)/s"), V(P("s")), P("t")), "Heaviside(t) - Heaviside(t - 1)"],
    ["inverseLaplaceTransform(P(\"(exp(2*s) - 2*exp(s) + 1)*exp(-2*s)/s**2\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("(exp(2*s) - 2*exp(s) + 1)*exp(-2*s)/s**2"), V(P("s")), P("t")), "t*Heaviside(t) + (t - 2)*Heaviside(t - 2) - 2*(t - 1)*Heaviside(t - 1)"],
    ["inverseLaplaceTransform(P(\"exp(-1)*exp(-s)/(s + 1) + 1/s - exp(-s)/s\"), V(P(\"s\")), P(\"t\"))", () => inverseLaplaceTransform(P("exp(-1)*exp(-s)/(s + 1) + 1/s - exp(-s)/s"), V(P("s")), P("t")), "exp(-1)*exp(1 - t)*Heaviside(t - 1) + Heaviside(t) - Heaviside(t - 1)"],
  ];

  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

// Inverse Laplace transform (integrals/transforms/inverse-laplace.ts). The
// expected values are SymPy 1.14 inverse_laplace_transform(F, s, t,
// noconds=False) results; they are compared after parsing, so that the
// order of the factors in the printed form does not matter.

const [s, z] = symbols('s z');
const [t, k, r] = symbols('t k r', { real: true });
const [a, b] = symbols('a b', { positive: true });
const F = SymFunction('F');
/** The plane argument SymPy prints as _None. */
const None_ = at(new InverseLaplaceTransform(s, s, t).args, 3);
const ILT = (...xs: Expr[]): Expr => new InverseLaplaceTransform(at(xs, 0), at(xs, 1), at(xs, 2), at(xs, 3));
const Ps = (e: string): Expr => parse(e, { symbols: [s, z, t, k, r, a, b], locals: { Heaviside, DiracDelta, F, _None: None_, InverseLaplaceTransform: ILT } });
/** Equal after expansion (the printed forms of SymPy and symjs order the factors differently). */
const eq = (x: Expr, y: string): void => expect(expand(x).key, String(x)).toBe(expand(Ps(y)).key);
const ilt = (e: string): [Expr, Expr] => inverseLaplaceTransform(Ps(e), s, t, undefined, { noconds: false });
/** The transform agrees with SymPy's (f, cond). */
const same = (e: string, f: string, cond = 'True'): void => {
  const [rf, rc] = ilt(e);
  eq(rf, f);
  expect(String(rc)).toBe(cond);
};
const unevaluated = (e: string): void => same(e, `InverseLaplaceTransform(${e}, s, t, _None)`);

describe('InverseLaplaceTransform object', () => {
  it('name, plane, integral and doit', () => {
    const T = new InverseLaplaceTransform(Ps('1/s'), s, t);
    expect(InverseLaplaceTransform.transformName).toBe('Inverse Laplace');
    expect(T.transformName).toBe('Inverse Laplace');
    expect(T.fundamentalPlane).toBeUndefined();
    expect(String(new InverseLaplaceTransform(Ps('1/s'), s, t, a).fundamentalPlane)).toBe('a');
    // SymPy: -I*Integral(exp(s*t)/s, (s, _c - oo*I, _c + oo*I))/(2*pi)
    expect(String(T.asIntegral)).toBe('-I*Integral(exp(s*t)/s, (s, _c - oo*I, _c + oo*I))/(2*pi)');
    expect(String(T.doit())).toBe('Heaviside(t)');
    expect(String(T.doit({ noconds: false }))).toBe('Heaviside(t),True');
    // SymPy returns DiracDelta(t)/s here, reading 1/s as independent of the
    // variable 2*s; symjs leaves a transform in a non-symbol variable unevaluated
    const U = new InverseLaplaceTransform(Ps('1/s'), Ps('2*s'), t);
    expect(U.doit()).toBe(U);
  });
  it('a given plane is passed through (SymPy: Heaviside(t), Matrix([[Heaviside(t)]]))', () => {
    expect(String(inverseLaplaceTransform(Ps('1/s'), s, t, a))).toBe('Heaviside(t)');
    expect(String(inverseLaplaceTransform(Matrix.of([[Ps('1/s')]]), s, t, a))).toBe('Matrix([[Heaviside(t)]])');
  });
});

describe('time shift', () => {
  it('splits off the part of the exponent independent of s', () => {
    same('exp(-a*s - b)', 'exp(-b)*DiracDelta(-a + t)');
    same('exp(-a*s - b)/s', 'exp(-b)*Heaviside(-a + t)');
    same('exp(-a*s)*exp(b)', 'exp(b)*DiracDelta(-a + t)');
    same('exp(-a*s)*exp(-b*s)*exp(-b)', 'exp(-b)*DiracDelta(-a - b + t)');
    same('exp(-s*(a + b))', 'DiracDelta(-a - b + t)');
  });
  it('a shift that is not known to be a delay stays unevaluated', () => {
    // SymPy 1.14 gives exp(-b)*Heaviside(a + t), a time advance: the
    // original of exp(a*s)/s is not a causal function, so it is kept
    unevaluated('exp(a*s - b)/s');
    // SymPy gives Heaviside(-a + t + 1), correct only for a >= 1
    unevaluated('exp(-a*s + s)/s');
  });
});

describe('derivatives and the time differentiation rule', () => {
  it('sqrt(s)*F\'(s) has no rule (SymPy: unevaluated)', () => {
    unevaluated('sqrt(s)*Derivative(F(s), s)');
  });
  it('s*F(s) with an irrational F(s)', () => {
    same('s/(sqrt(s) + a)', '(-a**3*exp(a**2*t)*erfc(a*sqrt(t)) + a**2/(sqrt(pi)*sqrt(t)) - 1/(2*sqrt(pi)*t**(3/2)))*Heaviside(t)');
  });
  it('an unevaluated derivative of a known transform', () => {
    // SymPy: Derivative(1/s, s) -> -t*Heaviside(t) (rule a/s)
    expect(String(inverseLaplaceTransform(Derivative(Ps('1/s'), s), s, t))).toBe('-t*Heaviside(t)');
    // SymPy: -t*(exp(-t)*Heaviside(t) - exp(-2*t)*Heaviside(t)) (partial fractions)
    eq(inverseLaplaceTransform(Derivative(Ps('1/((s + 1)*(s + 2))'), s), s, t), '-t*(exp(-t)*Heaviside(t) - exp(-2*t)*Heaviside(t))');
    // SymPy: DiracDelta(t)*Derivative(1, s), reading Derivative(1, s) (which has no
    // free symbols) as a constant; symjs inverts the derivative of 1, the transform
    // of DiracDelta(t). Both are 0, as Derivative(1, s) and t*DiracDelta(t) are
    expect(String(inverseLaplaceTransform(Derivative(1, s), s, t))).toBe('-t*DiracDelta(t)');
  });
});

describe('irrational functions (Bateman 5.3)', () => {
  it('rules', () => {
    same('1/sqrt(s)/(sqrt(s) + a)', 'exp(a**2*t)*Heaviside(t)*erfc(a*sqrt(t))');
    same('s**(-3/2)/(sqrt(s) + a)', '(2*a*sqrt(t)/sqrt(pi) + exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)/a**2');
    same('1/((s - 1)*(sqrt(s) + 2)*sqrt(s))', '(exp(4*t)*erfc(2*sqrt(t))/3 + 2*exp(t)*erf(sqrt(t))/3 - exp(t)/3)*Heaviside(t)');
  });
  it('factor patterns without a rule stay unevaluated as in SymPy', () => {
    unevaluated('(s + 1)**(-s)');
    unevaluated('1/(sqrt(a + s)*sqrt(a + s + 1))');
    unevaluated('sqrt(s)/((s + 1)*(s + 2))');
    unevaluated('sqrt(s)*sqrt(s + 1)/(s + 2)');
    unevaluated('1/(s*(s + 1)*(s + 2)**(3/2))');
  });
  it('poles whose order is not decided by the assumptions', () => {
    // SymPy raises TypeError (cannot determine truth value of Relational: 1 < a)
    // when it sorts the poles; symjs keeps them in place and finds no rule
    unevaluated('1/(sqrt(a + s)*sqrt(s + 1))');
    unevaluated('1/(sqrt(k + s)*sqrt(r + s))');
  });
  it('rules whose conditions fail (SymPy evaluates these with Meijer G functions)', () => {
    // SymPy: (2*sqrt(pi)*... t**(z - 1/2)*besseli(-z - 1/2, ...), re(z) <= -1/2)
    unevaluated('(s**2 + 1)**z');
    // by the Meijer G-function integrator, as SymPy
    same('1/(s**(3/2)*(s + 1))', 'I*(-2*I*sqrt(t)*exp(t)/sqrt(pi) + erf(I*sqrt(t)))*exp(-t)*Heaviside(t)');
    // SymPy: (-2*I*(-2*I*sqrt(t)*exp(t)/sqrt(pi) + erf(I*sqrt(t)))*exp(-t)/5 + exp(4*t)*erfc(2*sqrt(t))/5 + (t - t*exp(-t))/(5*t))*Heaviside(t)
    unevaluated('1/(sqrt(s)*(sqrt(s) + 2)*(s + 1))');
    same('1/(s**(3/2)*(r + sqrt(s)))', '(-pi*r**2*t*(-2*r*sqrt(t)*exp(-r**2*t)/sqrt(pi) + erf(r*sqrt(t)))*exp(r**2*t) + pi*(r**2*t*exp(r**2*t) - r**2*t))*Heaviside(t)/(pi*r**4*t)');
  });
});

describe('corrections of SymPy rules', () => {
  it('Bateman 5.3 (6): erf, not erfc, in the second term', () => {
    // SymPy 1.14: (4*exp(4*t)*erfc(2*sqrt(t))/3 + 2*exp(t)*erfc(sqrt(t))/3 - exp(t)/3)*Heaviside(t), whose
    // Laplace transform at s = 5 is 0.14956..., not sqrt(5)/(4*(sqrt(5) + 2)) = 0.13196...; with erf it is
    same('sqrt(s)/((s - 1)*(sqrt(s) + 2))', '(4*exp(4*t)*erfc(2*sqrt(t))/3 + 2*exp(t)*erf(sqrt(t))/3 - exp(t)/3)*Heaviside(t)');
    // the rule needs b > 0 (SymPy: unevaluated)
    unevaluated('sqrt(s)/((sqrt(s) + 2)*(s + 1))');
  });
  it('Bateman 5.3 (2) only for sqrt(a2*s)', () => {
    // SymPy 1.14 applies the rule to sqrt(s + 2) as if it were sqrt(s):
    // (-2*sqrt(t)/sqrt(pi) + exp(t)*erf(sqrt(t)))*Heaviside(t), whose value at t = 1 is 1.1623...,
    // while the inversion (mpmath invertlaplace, talbot) gives 0.87201...
    unevaluated('1/(s*(s - 1)*sqrt(s + 2))');
    // with s*sqrt(s) combined into s**(3/2) (SymPy evaluates this with Meijer G functions)
    same('1/(s**(3/2)*(-a + s))', '-(2*sqrt(a)*sqrt(t)*exp(-a*t)/sqrt(pi) - erf(sqrt(a)*sqrt(t)))*exp(a*t)*Heaviside(t)/a**(3/2)');
    // a negative pole, by the Meijer G-function integrator as in SymPy (checked against the Laplace
    // transform at s = 3 for k = 2)
    same('1/(s*sqrt(k*s)*(a + s))', 'I*(-2*I*sqrt(a)*sqrt(t)*exp(a*t)/sqrt(pi) + erf(I*sqrt(a)*sqrt(t)))*exp(-a*t)*Heaviside(t)/(a**(3/2)*sqrt(k))');
    same('1/(s**(3/2)*(a + s))', 'I*(-2*I*sqrt(a)*sqrt(t)*exp(a*t)/sqrt(pi) + erf(I*sqrt(a)*sqrt(t)))*exp(-a*t)*Heaviside(t)/a**(3/2)');
  });
});

describe('expansion and partial fractions', () => {
  it('a quadratic with a negative constant gives sinh', () => {
    same('1/(s**2 - a)', 'sinh(sqrt(a)*t)*Heaviside(t)/sqrt(a)');
  });
  it('expansion of a logarithm for a positive s', () => {
    const [sp] = symbols('s', { positive: true });
    // SymPy: t*log(2)*Heaviside(t) + (-t**2*log(t) - EulerGamma*t**2 + t**2)*Heaviside(t)/t,
    // the second term from its Meijer G integration
    const r = inverseLaplaceTransform(parse('log(2*s)/s**2', { symbols: [sp] }), sp, t);
    expect(String(r)).toBe('t*log(2)*Heaviside(t) + (-t**2*log(t) - EulerGamma*t**2 + t**2)*Heaviside(t)/t');
  });
  it('a product with a sum that has no rule', () => {
    // SymPy 1.14 raises TypeError (_inverse_laplace_transform_integration()
    // takes 4 positional arguments but 5 were given), a bug in its fallback
    same('a*(sqrt(s) + cos(s))', 'a*InverseLaplaceTransform(sqrt(s) + cos(s), s, t, _None)');
  });
  it('improper fractions and powers of linear and quadratic factors', () => {
    same('s**3/(s + a)**2', '-a**3*t*exp(-a*t)*Heaviside(t) + 3*a**2*exp(-a*t)*Heaviside(t) - 2*a*DiracDelta(t) + DiracDelta(t, 1)');
    same('s**4/(s**2 + a)**2', 'sqrt(a)*(-sqrt(a)*t*cos(sqrt(a)*t) + sin(sqrt(a)*t))*Heaviside(t)/2 - 2*sqrt(a)*sin(sqrt(a)*t)*Heaviside(t) + DiracDelta(t)');
    same('s**5/(s**2 + a)**2', 'a**(3/2)*t*sin(sqrt(a)*t)*Heaviside(t)/2 - 2*a*cos(sqrt(a)*t)*Heaviside(t) + DiracDelta(t, 1)');
    same('1/(a*s + 1)**2', 't*exp(-t/a)*Heaviside(t)/a**2');
    same('1/(s + sqrt(2))**3', 't**2*exp(-sqrt(2)*t)*Heaviside(t)/2');
    same('s/(s + pi)**3', '-pi*t**2*exp(-pi*t)*Heaviside(t)/2 + t*exp(-pi*t)*Heaviside(t)');
    same('s**2/(s + a)**3', 'a**2*t**2*exp(-a*t)*Heaviside(t)/2 - 2*a*t*exp(-a*t)*Heaviside(t) + exp(-a*t)*Heaviside(t)');
    same('(s + b)/(s**2 + a)**2', 't*sin(sqrt(a)*t)*Heaviside(t)/(2*sqrt(a)) + b*(-sqrt(a)*t*cos(sqrt(a)*t) + sin(sqrt(a)*t))*Heaviside(t)/(2*a**(3/2))');
    same(
      '1/((s + 1)**2*(s**2 + 2)**2)',
      '-sqrt(2)*t*sin(sqrt(2)*t)*Heaviside(t)/18 + t*exp(-t)*Heaviside(t)/9 + (sqrt(2)*sin(sqrt(2)*t)/54 - 4*cos(sqrt(2)*t)/27)*Heaviside(t) - sqrt(2)*(-sqrt(2)*t*cos(sqrt(2)*t) + sin(sqrt(2)*t))*Heaviside(t)/72 + 4*exp(-t)*Heaviside(t)/27',
    );
  });
  it('repeated factors that SymPy inverts with Meijer G functions or not at all', () => {
    // by the Meijer G-function integrator, as SymPy
    expect(String(ilt('(s**3 + 2)**(-2)')[0])).toBe('2*sqrt(3)*pi*t**5*Heaviside(t)*hyper((), (7/3, 8/3), -2*t**3/27)/(729*gamma(7/3)*gamma(8/3))');
    // SymPy 1.14 raises ValueError (too many values to unpack) on these
    unevaluated('(a*s + s**2 + 1)**(-2)');
    unevaluated('(a + s**2 + s)**(-3)');
  });
});

describe('more SymPy 1.14 cases', () => {
  it('rules and shifts', () => {
    same('1/(s**2 + a**2)**2', '(-a*t*cos(a*t) + sin(a*t))*Heaviside(t)/(2*a**3)');
    same('1/(s*(a + s)**k)', 'Heaviside(t)*lowergamma(k, a*t)/(a**k*gamma(k))');
    same('(s - a)**(-b)', 't**(b - 1)*exp(a*t)*Heaviside(t)/gamma(b)');
    same('1/sqrt(s)', 'Heaviside(t)/(sqrt(pi)*sqrt(t))');
    same('s**(-5/2)', '4*t**(3/2)*Heaviside(t)/(3*sqrt(pi))');
    same('(s + 1)**(-1/3)', 'exp(-t)*Heaviside(t)/(t**(2/3)*gamma(1/3))');
    same('exp(-a*s)/s**b', '(-a + t)**(b - 1)*Heaviside(-a + t)/gamma(b)');
    same('exp(-a*s)/sqrt(s**2 + 1)', 'Heaviside(-a + t)*besselj(0, a - t)');
    same('1/(s*sqrt(s + 1))', 'Heaviside(t)*erf(sqrt(t))');
    same('k*F(s - a)', 'k*InverseLaplaceTransform(F(s), s, t, _None)*exp(-a*t)');
    same('exp(-a*s)*F(s)', 'InverseLaplaceTransform(F(s), s, -a + t, _None)');
    same('Derivative(F(s), s)*s', '-t*Derivative(InverseLaplaceTransform(F(s), s, t, _None), t) - InverseLaplaceTransform(F(s), s, t, _None)');
    same('a*Derivative(F(s), s)', '-a*t*InverseLaplaceTransform(F(s), s, t, _None)');
    same('exp(-a*s)*s', 'DiracDelta(-a + t, 1)');
    same('exp(-3*s)', 'DiracDelta(t - 3)');
    same('a*exp(-3*s)', 'a*DiracDelta(t - 3)');
    same('2*exp(3*s) - 5*exp(-7*s)', '2*InverseLaplaceTransform(exp(3*s), s, t, _None) - 5*DiracDelta(t - 7)');
    same(
      '(s**2*exp(2*s) + 4*exp(s) - 4)*exp(-2*s)/(s*(s**2 + 1))',
      'cos(t)*Heaviside(t) + 4*cos(t - 2)*Heaviside(t - 2) - 4*cos(t - 1)*Heaviside(t - 1) - 4*Heaviside(t - 2) + 4*Heaviside(t - 1)',
    );
    for (const e of ['cos(s)', 'exp(2*s)', 'exp(r*s)', 'exp(s*z)', 'exp(-s*z)/s', 'F(a + s)', 'F(-r + s)', 'Derivative(F(s), s, a)', 'exp(s**2)', 'log(s)']) unevaluated(e);
    // SymPy 1.14 raises TypeError / AttributeError on these two
    unevaluated('s**z/(s + 1)');
    unevaluated('1/(s**a + 1)');
    // by the Meijer G-function integrator, as SymPy
    same('log(s)/s', '(-t*log(t) - EulerGamma*t)*Heaviside(t)/t');
  });
  it('irrational rules', () => {
    same('1/sqrt(s**2 + a**2)', 'Heaviside(t)*besselj(0, a*t)');
    same('1/sqrt(s**2 - a**2)', 'Heaviside(t)*besseli(0, a*t)');
    same('1/sqrt(s**2 + r)', 'Heaviside(t)*besselj(0, sqrt(r)*t)');
    same('1/sqrt(s**2 - r)', 'Heaviside(t)*besselj(0, t*sqrt(-r))');
    same('1/sqrt(s + b)/(s + a)', 'exp(-a*t)*Heaviside(t)*erf(sqrt(t)*sqrt(-a + b))/sqrt(-a + b)');
    same('1/(s + a)/sqrt(s + r)', 'exp(-a*t)*Heaviside(t)*erf(sqrt(t)*sqrt(-a + r))/sqrt(-a + r)');
    same('sqrt(s + a)/(s + b)', '(sqrt(a - b)*exp(-b*t)*erf(sqrt(t)*sqrt(a - b)) + exp(-a*t)/(sqrt(pi)*sqrt(t)))*Heaviside(t)');
    same('1/(sqrt(s) + a)', '(-a*exp(a**2*t)*erfc(a*sqrt(t)) + 1/(sqrt(pi)*sqrt(t)))*Heaviside(t)');
    same('1/(s - a)/sqrt(s)', 'exp(a*t)*Heaviside(t)*erf(sqrt(a)*sqrt(t))/sqrt(a)');
    same('1/(sqrt(s) + r)**3/sqrt(s)', '(-2*r*t**(3/2)/sqrt(pi) + t*(2*r**2*t + 1)*exp(r**2*t)*erfc(r*sqrt(t)))*Heaviside(t)');
    same('sqrt(s)/(sqrt(s) + r)**3', '(-2*r*sqrt(t)*(r**2*t + 2)/sqrt(pi) + (2*r**4*t**2 + 5*r**2*t + 1)*exp(r**2*t)*erfc(r*sqrt(t)))*Heaviside(t)');
    same('(sqrt(s) - r)/(s*(sqrt(s) + r))', '(2*exp(r**2*t)*erfc(r*sqrt(t)) - 1)*Heaviside(t)');
    same('(sqrt(s) - r)**2/(s*(sqrt(s) + r)**2)', '(8*r**2*t*exp(r**2*t)*erfc(r*sqrt(t)) - 8*r*sqrt(t)/sqrt(pi) + 1)*Heaviside(t)');
    same('(sqrt(s) - r)**3/(s*(sqrt(s) + r)**3)', '(-8*r*sqrt(t)*(2*r**2*t + 1)/sqrt(pi) + (16*r**4*t**2 + 16*r**2*t + 2)*exp(r**2*t)*erfc(r*sqrt(t)) - 1)*Heaviside(t)');
    same(
      '1/(s - b)/(sqrt(s) + sqrt(a))/sqrt(s)',
      '(sqrt(a)*exp(b*t)*erf(sqrt(b)*sqrt(t)) + sqrt(b)*exp(a*t)*erfc(sqrt(a)*sqrt(t)) - sqrt(b)*exp(b*t))*Heaviside(t)/(sqrt(b)*(a - b))',
    );
    // the rules need a positive shift; the others by the Meijer G-function integrator (the results are
    // checked against the Laplace transforms at s = 3 for r = 7/10 and r = -7/10)
    for (const e of ['1/(-a + sqrt(s))', '1/(r + sqrt(s))']) unevaluated(e);
    same('(r + sqrt(s))**(-2)', '2*(sqrt(pi)*r**2*t*(-2*sqrt(pi)*erfc(r*sqrt(t)) + 2*exp(-r**2*t)/(r*sqrt(t)))*(-r**2*t - 1/2)*exp(r**2*t)/2 + sqrt(pi)*r*sqrt(t)/2)*Heaviside(t)/(pi*r**2*t)');
    same('(r + sqrt(s))**(-3)', '2*(3*sqrt(pi)*r**4*t**2*(4*sqrt(pi)*erfc(r*sqrt(t))/3 - (4*r**2*t/3 - 2/3)*exp(-r**2*t)/(r**3*t**(3/2)))*(-r**2*t - 3/2)*exp(r**2*t)/4 + 3*sqrt(pi)*r*sqrt(t)/4)*Heaviside(t)/(pi*r**3*t)');
    same('(r + sqrt(s))**(-4)', '4*(3*sqrt(pi)*r**4*t**2*(4*sqrt(pi)*erfc(r*sqrt(t))/3 - (4*r**2*t/3 - 2/3)*exp(-r**2*t)/(r**3*t**(3/2)))*(r**4*t**2 + 3*r**2*t + 3/4)*exp(r**2*t)/4 + 3*sqrt(pi)*r*sqrt(t)*(-r**2*t - 1/2)/4)*Heaviside(t)/(3*pi*r**4*t)');
    same('1/(sqrt(s)*(a + s))', '-I*exp(-a*t)*erf(I*sqrt(a)*sqrt(t))*Heaviside(t)/sqrt(a)');
    same('1/(s*(r + sqrt(s)))', '(pi*r**2*t*exp(r**2*t)*erf(r*sqrt(t)) - pi*(r**2*t*exp(r**2*t) - r**2*t))*Heaviside(t)/(pi*r**3*t)');
    same('1/(sqrt(s)*(r + sqrt(s)))', 'exp(r**2*t)*erfc(r*sqrt(t))*Heaviside(t)');
    same('1/(s*(r + sqrt(s))**2)', '2*(sqrt(pi)*r**5*t**(5/2)*(-2 - 2*sqrt(pi)*(3*r**2*t/2 - 3/4)*(-2*r*sqrt(t)*exp(-r**2*t)/sqrt(pi) + erf(r*sqrt(t)))*exp(r**2*t)/(3*r**3*t**(3/2))) + pi*(r**4*t**2*((2*r**2*t - 2)/(r**2*t) + 1/(r**2*t))*exp(r**2*t) + r**2*t)/2)*Heaviside(t)/(pi*r**4*t)');
    same('1/(sqrt(s)*(r + sqrt(s))**2)', 'r*t*(-2*sqrt(pi)*erfc(r*sqrt(t)) + 2*exp(-r**2*t)/(r*sqrt(t)))*exp(r**2*t)*Heaviside(t)/sqrt(pi)');
  });
  it('numerators that do not cancel the poles', () => {
    // SymPy: -a*InverseLaplaceTransform(1/(r*s + s**(3/2)), s, t, _None) + InverseLaplaceTransform(sqrt(s)/(r*s + s**(3/2)), s, t, _None),
    // the same transforms with the denominators expanded
    // (the terms by the Meijer G-function integrator)
    same('(sqrt(s) - a)/(s*(sqrt(s) + r))', '-a*(pi*r**2*t*exp(r**2*t)*erf(r*sqrt(t)) - pi*(r**2*t*exp(r**2*t) - r**2*t))*Heaviside(t)/(pi*r**3*t) + exp(r**2*t)*erfc(r*sqrt(t))*Heaviside(t)');
    // SymPy: a**2*ILT(1/(r**2*s + 2*r*s**(3/2) + s**2)) - 2*a*ILT(sqrt(s)/(r**2*s + 2*r*s**(3/2) + s**2)) + Derivative(ILT(1/(r**2*s + 2*r*s**(3/2) + s**2)), t)
    same(
      '(sqrt(s) - a)**2/(s*(sqrt(s) + r)**2)',
      'a**2*InverseLaplaceTransform(1/(s*(r**2 + 2*r*sqrt(s) + s)), s, t, _None) - 2*a*InverseLaplaceTransform(1/(sqrt(s)*(r**2 + 2*r*sqrt(s) + s)), s, t, _None) + InverseLaplaceTransform(1/(r**2 + 2*r*sqrt(s) + s), s, t, _None)',
    );
    // SymPy: the analogous four transforms, one of them as a time derivative
    same(
      '(sqrt(s) - a)**3/(s*(sqrt(s) + r)**3)',
      '-a**3*InverseLaplaceTransform(1/(s*(r**3 + 3*r**2*sqrt(s) + 3*r*s + s**(3/2))), s, t, _None) + 3*a**2*InverseLaplaceTransform(1/(sqrt(s)*(r**3 + 3*r**2*sqrt(s) + 3*r*s + s**(3/2))), s, t, _None) - 3*a*InverseLaplaceTransform(1/(r**3 + 3*r**2*sqrt(s) + 3*r*s + s**(3/2)), s, t, _None) + InverseLaplaceTransform(sqrt(s)/(r**3 + 3*r**2*sqrt(s) + 3*r*s + s**(3/2)), s, t, _None)',
    );
  });
  it('rational functions', () => {
    same('1/(s**3 + 1)', '(sqrt(3)*exp(t/2)*sin(sqrt(3)*t/2)/3 - exp(t/2)*cos(sqrt(3)*t/2)/3)*Heaviside(t) + exp(-t)*Heaviside(t)/3');
    same('s**2/(s**2 + a)**2', '-(-sqrt(a)*t*cos(sqrt(a)*t) + sin(sqrt(a)*t))*Heaviside(t)/(2*sqrt(a)) + sin(sqrt(a)*t)*Heaviside(t)/sqrt(a)');
    same('s**3/(s + 1)**2', '-t*exp(-t)*Heaviside(t) - 2*DiracDelta(t) + DiracDelta(t, 1) + 3*exp(-t)*Heaviside(t)');
    same('1/(s**2 - 2*s + 1)', 't*exp(t)*Heaviside(t)');
    same('1/(s**2 + 2*s + r)', 'exp(-t)*sin(t*sqrt(r - 1))*Heaviside(t)/sqrt(r - 1)');
    same('s/(s**2 + 2*s + r)', '(exp(-t)*cos(t*sqrt(r - 1)) - exp(-t)*sin(t*sqrt(r - 1))/sqrt(r - 1))*Heaviside(t)');
    same('1/(s*(s + 1)**3)', '-t**2*exp(-t)*Heaviside(t)/2 - t*exp(-t)*Heaviside(t) + Heaviside(t) - exp(-t)*Heaviside(t)');
    same('exp(-s)/(s*(s + 1)**3)', '(1 - t)*exp(1 - t)*Heaviside(t - 1) - (t - 1)**2*exp(1 - t)*Heaviside(t - 1)/2 - exp(1 - t)*Heaviside(t - 1) + Heaviside(t - 1)');
    same('1/(s + a)**3', 't**2*exp(-a*t)*Heaviside(t)/2');
    same('1/s**3', 't**2*Heaviside(t)/2');
    // SymPy returns a sum of gamma-function quotients from its Meijer G integration; symjs's hyperexpand
    // leaves a hypergeometric function (the same function) and Bessel functions (checked at s = 3)
    expect(String(ilt('1/(a + s**3)')[0])).toBe('2*sqrt(3)*pi*t**2*Heaviside(t)*hyper((), (4/3, 5/3), -a*t**3/27)/(27*gamma(4/3)*gamma(5/3))');
    same('1/(s**4 + 1)', '4*sqrt(2)*pi*t**3*((-1)**(3/8)*sqrt(2)*sqrt(pi)*(-3*besseli(5/2, t*exp(I*pi/4))/2 - 3*besselj(5/2, t*exp(I*pi/4))/2)/(128*t**(5/2)) + (-1)**(1/8)*sqrt(2)*sqrt(pi)*(-9*besseli(3/2, t*exp(I*pi/4))/2 + 9*besselj(3/2, t*exp(I*pi/4))/2)/(128*t**(7/2)))*Heaviside(t)/(gamma(5/4)*gamma(7/4))');
  });
});
