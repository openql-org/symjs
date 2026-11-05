// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/powsimp.ts.

import { describe, expect, it } from 'vitest';
import { Sym, SymFunction, add, float, logcombine, mul, parse, pow, powdenest, powsimp, sstr, symbol, symbols } from '../../src';
import type { Expr } from '../../src';

const P = (s: string) => parse(s);
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe('powdenest and finite differences', () => {
  it('match SymPy', async () => {
    const { powdenest, asFiniteDifference, Derivative: D } = await import('../../src');
    const [x, h] = symbols('x h');
    expect(sstr(powdenest(parse('(x**(2*i)*y**(4*i))**z'), { force: true }))).toBe('(x*y**2)**(2*i*z)');
    const f = SymFunction('f');
    const dx = SymFunction('dx');
    expect(sstr(asFiniteDifference(D(f(x), x) as never, dx(x), parse('x - h', { symbols: { x, h } } as never)))).toBe(
      '-f(-h + x - dx(-h + x)/2)/dx(-h + x) + f(-h + x + dx(-h + x)/2)/dx(-h + x)',
    );
  });
});

describe("powsimp, powdenest, logcombine: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["powsimp(Qs(\"(-1)**(3*a/2)\", [symbol(\"a\", { integer: true })]))", () => powsimp(Qs("(-1)**(3*a/2)", [symbol("a", { integer: true })])), "(-I)**a"],
    ["powsimp(Qs(\"(x*y)**2*(y*x)**2\", [symbol(\"x\", { commutative: false }), symbol(\"y\", { commutative: false })]))", () => powsimp(Qs("(x*y)**2*(y*x)**2", [symbol("x", { commutative: false }), symbol("y", { commutative: false })])), "(x*y)**2*(y*x)**2"],
    ["powsimp(P(\"2*3**x/3\"))", () => powsimp(P("2*3**x/3")), "2*3**(x - 1)"],
    ["powsimp(Qs(\"(-a**2 - 1)*sqrt(a**2 + 1)\", [symbol(\"a\", { real: true })]))", () => powsimp(Qs("(-a**2 - 1)*sqrt(a**2 + 1)", [symbol("a", { real: true })])), "-(a**2 + 1)**(3/2)"],
    ["powsimp(Qs(\"p1**z/p2**z\", [symbol(\"p1\", { positive: true }), symbol(\"p2\", { positive: true })]))", () => powsimp(Qs("p1**z/p2**z", [symbol("p1", { positive: true }), symbol("p2", { positive: true })])), "(p1/p2)**z"],
    ["powsimp(Qs(\"x**i/y**i\", [symbol(\"i\", { integer: true })]))", () => powsimp(Qs("x**i/y**i", [symbol("i", { integer: true })])), "(x/y)**i"],
    ["powsimp(P(\"x*sqrt(y)*sqrt(x*sqrt(y))\"))", () => powsimp(P("x*sqrt(y)*sqrt(x*sqrt(y))")), "(x*sqrt(y))**(3/2)"],
    ["powsimp(P(\"x**2*y**(3/2)*sqrt(x*sqrt(y))\"))", () => powsimp(P("x**2*y**(3/2)*sqrt(x*sqrt(y))")), "sqrt(y)*(x*sqrt(y))**(5/2)"],
    ["powsimp(P(\"x**2*y*(sqrt(x)*y)**(3/2)*sqrt(x*sqrt(y))\"))", () => powsimp(P("x**2*y*(sqrt(x)*y)**(3/2)*sqrt(x*sqrt(y))")), "(sqrt(x)*y)**(3/2)*(x*sqrt(y))**(5/2)"],
    ["powsimp(P(\"x*y**2*(sqrt(x)*y)**(3/2)*sqrt(x*sqrt(y))\"))", () => powsimp(P("x*y**2*(sqrt(x)*y)**(3/2)*sqrt(x*sqrt(y))")), "(sqrt(x)*y)**(7/2)*sqrt(x*sqrt(y))"],
    ["powsimp(P(\"x*y**2*(sqrt(x)*y)**(3/2)\"))", () => powsimp(P("x*y**2*(sqrt(x)*y)**(3/2)")), "(sqrt(x)*y)**(7/2)"],
    ["powsimp(P(\"x*y*(sqrt(x)*y)**(3/2)\"))", () => powsimp(P("x*y*(sqrt(x)*y)**(3/2)")), "x*y*(sqrt(x)*y)**(3/2)"],
    ["powsimp(P(\"sqrt(x)*y*(sqrt(x)*y)**(3/2)\"))", () => powsimp(P("sqrt(x)*y*(sqrt(x)*y)**(3/2)")), "(sqrt(x)*y)**(5/2)"],
    ["powsimp(P(\"sqrt(x)*sqrt(y)*(x*sqrt(y))**(3/2)\"))", () => powsimp(P("sqrt(x)*sqrt(y)*(x*sqrt(y))**(3/2)")), "sqrt(x)*sqrt(y)*(x*sqrt(y))**(3/2)"],
    ["powsimp(P(\"y*(sqrt(x)*sqrt(y)*(sqrt(x)*y)**(3/2))\"))", () => powsimp(P("y*(sqrt(x)*sqrt(y)*(sqrt(x)*y)**(3/2))")), "sqrt(x)*y**(3/2)*(sqrt(x)*y)**(3/2)"],
    ["powsimp(P(\"x**3*y**(3/2)*sqrt(x*sqrt(y))\"))", () => powsimp(P("x**3*y**(3/2)*sqrt(x*sqrt(y))")), "(x*sqrt(y))**(7/2)"],
    ["powsimp(P(\"x**y*y*sqrt(x**y*y)\"))", () => powsimp(P("x**y*y*sqrt(x**y*y)")), "(x**y*y)**(3/2)"],
    ["powsimp(P(\"x*sqrt(x*exp(2*y/3))*exp(2*y/3)\"))", () => powsimp(P("x*sqrt(x*exp(2*y/3))*exp(2*y/3)")), "(x*exp(2*y/3))**(3/2)"],
    ["powsimp(P(\"x**2*sqrt(x*exp(2*y/3))*exp(4*y/3)\"))", () => powsimp(P("x**2*sqrt(x*exp(2*y/3))*exp(4*y/3)")), "(x*exp(2*y/3))**(5/2)"],
    ["powsimp(P(\"x**2*(x*exp(2*y/3))**(1/4)*exp(4*y/3)\"))", () => powsimp(P("x**2*(x*exp(2*y/3))**(1/4)*exp(4*y/3)")), "(x*exp(2*y/3))**(9/4)"],
    ["powsimp(P(\"1/116\"))", () => powsimp(P("1/116")), "1/116"],
    ["powsimp(P(\"sqrt(58)\"))", () => powsimp(P("sqrt(58)")), "sqrt(58)"],
    ["powsimp(P(\"1/sqrt(2*sqrt(29) + 29)\"))", () => powsimp(P("1/sqrt(2*sqrt(29) + 29)")), "1/sqrt(2*sqrt(29) + 29)"],
    ["powsimp(P(\"-10*sqrt(29) + 2*sqrt(29 - 2*sqrt(29))*sqrt(2*sqrt(29) + 29)\"))", () => powsimp(P("-10*sqrt(29) + 2*sqrt(29 - 2*sqrt(29))*sqrt(2*sqrt(29) + 29)")), "0"],
    ["powsimp(P(\"sqrt(58)*(-10*sqrt(29) + 2*sqrt(29 - 2*sqrt(29))*sqrt(2*sqrt(29) + 29))/(116*sqrt(2*sqrt(29) + 29))\"))", () => powsimp(P("sqrt(58)*(-10*sqrt(29) + 2*sqrt(29 - 2*sqrt(29))*sqrt(2*sqrt(29) + 29))/(116*sqrt(2*sqrt(29) + 29))")), "0"],
    ["powsimp(P(\"sqrt(2 - sqrt(3))*sqrt(sqrt(3) + 2) + 1\"))", () => powsimp(P("sqrt(2 - sqrt(3))*sqrt(sqrt(3) + 2) + 1")), "2"],
    ["powsimp(P(\"-5*sqrt(2)/(2*sqrt(2*sqrt(29) + 29)) + sqrt(1/2 - sqrt(29)/29)\"))", () => powsimp(P("-5*sqrt(2)/(2*sqrt(2*sqrt(29) + 29)) + sqrt(1/2 - sqrt(29)/29)")), "-5*sqrt(2)/(2*sqrt(2*sqrt(29) + 29)) + sqrt(1/2 - sqrt(29)/29)"],
    ["powsimp(P(\"4**x/2**(2*x)\"))", () => powsimp(P("4**x/2**(2*x)")), "1"],
    ["powsimp(P(\"(-4)**x/((-2)**x*2**x)\"))", () => powsimp(P("(-4)**x/((-2)**x*2**x)")), "1"],
    ["powsimp(P(\"f(4**x/2**(2*x))\"))", () => powsimp(P("f(4**x/2**(2*x))")), "f(4**x/2**(2*x))"],
    ["powsimp(P(\"f(4**x/2**(2*x))\"), { deep: true })", () => powsimp(P("f(4**x/2**(2*x))"), { deep: true }), "f(1)"],
    ["powsimp(P(\"exp(x)*exp(y)\"))", () => powsimp(P("exp(x)*exp(y)")), "exp(x + y)"],
    ["powsimp(P(\"2**x*2**y*exp(x)*exp(y)\"))", () => powsimp(P("2**x*2**y*exp(x)*exp(y)")), "(2*E)**(x + y)"],
    ["powsimp(P(\"2**x*2**y*exp(x)*exp(y)\"), { combine: \"exp\" })", () => powsimp(P("2**x*2**y*exp(x)*exp(y)"), { combine: "exp" }), "2**(x + y)*exp(x + y)"],
    ["powsimp(P(\"2**x*2**y + exp(2)*exp(x)*exp(y)*sin(x) + sin(y)\"))", () => powsimp(P("2**x*2**y + exp(2)*exp(x)*exp(y)*sin(x) + sin(y)")), "2**(x + y) + exp(x + y + 2)*sin(x) + sin(y)"],
    ["powsimp(P(\"sin(exp(x)*exp(y))\"))", () => powsimp(P("sin(exp(x)*exp(y))")), "sin(exp(x)*exp(y))"],
    ["powsimp(P(\"sin(exp(x)*exp(y))\"), { deep: true })", () => powsimp(P("sin(exp(x)*exp(y))"), { deep: true }), "sin(exp(x + y))"],
    ["powsimp(P(\"x**2*x**y\"))", () => powsimp(P("x**2*x**y")), "x**(y + 2)"],
    ["powsimp(P(\"(1 + E*exp(E))*exp(-E)\"), { combine: \"exp\", deep: true })", () => powsimp(P("(1 + E*exp(E))*exp(-E)"), { combine: "exp", deep: true }), "(1 + exp(1 + E))*exp(-E)"],
    ["powsimp(P(\"(1 + E*exp(E))*exp(-E)\"), { deep: true })", () => powsimp(P("(1 + E*exp(E))*exp(-E)"), { deep: true }), "(1 + exp(1 + E))*exp(-E)"],
    ["powsimp(P(\"(1 + E*exp(E))*exp(-E)\"))", () => powsimp(P("(1 + E*exp(E))*exp(-E)")), "(1 + exp(1 + E))*exp(-E)"],
    ["powsimp(P(\"(1 + E*exp(E))*exp(-E)\"), { combine: \"exp\" })", () => powsimp(P("(1 + E*exp(E))*exp(-E)"), { combine: "exp" }), "(1 + exp(1 + E))*exp(-E)"],
    ["powsimp(P(\"(1 + E*exp(E))*exp(-E)\"), { combine: \"base\" })", () => powsimp(P("(1 + E*exp(E))*exp(-E)"), { combine: "base" }), "(1 + E*exp(E))*exp(-E)"],
    ["powsimp(Qs(\"y**n/(y/x)**n\", [symbol(\"n\", { real: true }), symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]))", () => powsimp(Qs("y**n/(y/x)**n", [symbol("n", { real: true }), symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })])), "x**n"],
    ["powsimp(Qs(\"x**(x**(x*y)*y**(x*y))*y**(x**(x*y)*y**(x*y))\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: true })", () => powsimp(Qs("x**(x**(x*y)*y**(x*y))*y**(x**(x*y)*y**(x*y))", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: true }), "(x*y)**((x*y)**(x*y))"],
    ["powsimp(Qs(\"2**(2**(2*x)*x)\", [symbol(\"x\", { nonnegative: true })]), { deep: false })", () => powsimp(Qs("2**(2**(2*x)*x)", [symbol("x", { nonnegative: true })]), { deep: false }), "2**(2**(2*x)*x)"],
    ["powsimp(Qs(\"2**(2**(2*x)*x)\", [symbol(\"x\", { nonnegative: true })]), { deep: true })", () => powsimp(Qs("2**(2**(2*x)*x)", [symbol("x", { nonnegative: true })]), { deep: true }), "2**(4**x*x)"],
    ["powsimp(Qs(\"exp(-x + exp(-x)*exp(-x*log(x)))\", [symbol(\"x\", { nonnegative: true })]), { deep: false, combine: \"exp\" })", () => powsimp(Qs("exp(-x + exp(-x)*exp(-x*log(x)))", [symbol("x", { nonnegative: true })]), { deep: false, combine: "exp" }), "exp(-x + exp(-x)*exp(-x*log(x)))"],
    ["powsimp(Qs(\"(x + y)/(3*z)\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: false, combine: \"exp\" })", () => powsimp(Qs("(x + y)/(3*z)", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: false, combine: "exp" }), "(x + y)/(3*z)"],
    ["powsimp(Qs(\"(x/3 + y/3)/z\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: true, combine: \"exp\" })", () => powsimp(Qs("(x/3 + y/3)/z", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: true, combine: "exp" }), "(x/3 + y/3)/z"],
    ["powsimp(Qs(\"exp(x)/(exp(x)*exp(y) + 1)\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: true })", () => powsimp(Qs("exp(x)/(exp(x)*exp(y) + 1)", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: true }), "exp(x)/(exp(x + y) + 1)"],
    ["powsimp(Qs(\"x*y**(z**x*z**y)\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: true })", () => powsimp(Qs("x*y**(z**x*z**y)", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: true }), "x*y**(z**(x + y))"],
    ["powsimp(Qs(\"(z**x*z**y)**x\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: true })", () => powsimp(Qs("(z**x*z**y)**x", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: true }), "(z**(x + y))**x"],
    ["powsimp(Qs(\"x*(z**x*z**y)**x\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]), { deep: true })", () => powsimp(Qs("x*(z**x*z**y)**x", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })]), { deep: true }), "x*(z**(x + y))**x"],
    ["powsimp(Qs(\"1/(p*p**log(2))\", [symbol(\"p\", { positive: true })]))", () => powsimp(Qs("1/(p*p**log(2))", [symbol("p", { positive: true })])), "p**(-1 - log(2))"],
    ["powsimp(Qs(\"2**(2*x)\", [symbol(\"x\", { nonnegative: true })]))", () => powsimp(Qs("2**(2*x)", [symbol("x", { nonnegative: true })])), "4**x"],
    ["powsimp(Qs(\"(-1)**(2*x)\", [symbol(\"x\", { nonnegative: true })]))", () => powsimp(Qs("(-1)**(2*x)", [symbol("x", { nonnegative: true })])), "(-1)**(2*x)"],
    ["powsimp(P(\"1\"))", () => powsimp(P("1")), "1"],
    ["powsimp(Qs(\"(-1)**(-x)\", [symbol(\"x\", { nonnegative: true })]))", () => powsimp(Qs("(-1)**(-x)", [symbol("x", { nonnegative: true })])), "(-1)**(-x)"],
    ["powsimp(Qs(\"(-1)**(2*x)\", [symbol(\"x\", { nonnegative: true })]), { force: true })", () => powsimp(Qs("(-1)**(2*x)", [symbol("x", { nonnegative: true })]), { force: true }), "1"],
    ["powsimp(Qs(\"m**(i/a)*n**(i/a)*w**(i/a)\", [symbol(\"w\", { negative: true }), symbol(\"n\", { negative: true }), symbol(\"i\", { integer: true }), symbol(\"m\", { negative: true })]))", () => powsimp(Qs("m**(i/a)*n**(i/a)*w**(i/a)", [symbol("w", { negative: true }), symbol("n", { negative: true }), symbol("i", { integer: true }), symbol("m", { negative: true })])), "m**(i/a)*n**(i/a)*w**(i/a)"],
    ["powsimp(Qs(\"m**((i + 3)/i)*n**((i + 3)/i)*w**((i + 3)/i)\", [symbol(\"i\", { integer: true }), symbol(\"w\", { negative: true }), symbol(\"n\", { negative: true }), symbol(\"m\", { negative: true })]))", () => powsimp(Qs("m**((i + 3)/i)*n**((i + 3)/i)*w**((i + 3)/i)", [symbol("i", { integer: true }), symbol("w", { negative: true }), symbol("n", { negative: true }), symbol("m", { negative: true })])), "(-1)**(3*(i + 3)/i)*(-m*n*w)**((i + 3)/i)"],
    ["powsimp(Qs(\"exp(p/2)\", [symbol(\"p\", { positive: true })]))", () => powsimp(Qs("exp(p/2)", [symbol("p", { positive: true })])), "exp(p/2)"],
    ["powsimp(Qs(\"sqrt(x**a)\", [symbol(\"x\", { nonnegative: true })]))", () => powsimp(Qs("sqrt(x**a)", [symbol("x", { nonnegative: true })])), "sqrt(x**a)"],
    ["powsimp(Qs(\"x\", [symbol(\"x\", { nonnegative: true })]))", () => powsimp(Qs("x", [symbol("x", { nonnegative: true })])), "x"],
    ["powsimp(P(\"(-1)**(1/3)*exp(I*pi/3)\"))", () => powsimp(P("(-1)**(1/3)*exp(I*pi/3)")), "(-1)**(2/3)"],
    ["powsimp(P(\"0\"))", () => powsimp(P("0")), "0"],
    ["powsimp(Qs(\"x**(7/2)*y**6\", [symbol(\"x\", { nonnegative: true }), symbol(\"y\", { nonnegative: true })]))", () => powsimp(Qs("x**(7/2)*y**6", [symbol("x", { nonnegative: true }), symbol("y", { nonnegative: true })])), "x**(7/2)*y**6"],
    ["powsimp(Qs(\"A**x*A**y\", [symbol(\"A\", { commutative: false })]), { combine: \"all\" })", () => powsimp(Qs("A**x*A**y", [symbol("A", { commutative: false })]), { combine: "all" }), "A**(x + y)"],
    ["powsimp(Qs(\"A**x*A**y\", [symbol(\"A\", { commutative: false })]), { combine: \"base\" })", () => powsimp(Qs("A**x*A**y", [symbol("A", { commutative: false })]), { combine: "base" }), "A**x*A**y"],
    ["powsimp(Qs(\"A**x*A**y\", [symbol(\"A\", { commutative: false })]), { combine: \"exp\" })", () => powsimp(Qs("A**x*A**y", [symbol("A", { commutative: false })]), { combine: "exp" }), "A**(x + y)"],
    ["powsimp(Qs(\"A**x*B**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]), { combine: \"all\" })", () => powsimp(Qs("A**x*B**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false })]), { combine: "all" }), "A**x*B**x"],
    ["powsimp(Qs(\"A**x*B**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]), { combine: \"base\" })", () => powsimp(Qs("A**x*B**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false })]), { combine: "base" }), "A**x*B**x"],
    ["powsimp(Qs(\"A**x*B**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]), { combine: \"exp\" })", () => powsimp(Qs("A**x*B**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false })]), { combine: "exp" }), "A**x*B**x"],
    ["powsimp(Qs(\"B**x*A**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]), { combine: \"all\" })", () => powsimp(Qs("B**x*A**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false })]), { combine: "all" }), "B**x*A**x"],
    ["powsimp(Qs(\"B**x*A**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]), { combine: \"base\" })", () => powsimp(Qs("B**x*A**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false })]), { combine: "base" }), "B**x*A**x"],
    ["powsimp(Qs(\"B**x*A**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]), { combine: \"exp\" })", () => powsimp(Qs("B**x*A**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false })]), { combine: "exp" }), "B**x*A**x"],
    ["powsimp(Qs(\"A**x*A**y*A**z\", [symbol(\"A\", { commutative: false })]), { combine: \"all\" })", () => powsimp(Qs("A**x*A**y*A**z", [symbol("A", { commutative: false })]), { combine: "all" }), "A**(x + y + z)"],
    ["powsimp(Qs(\"A**x*A**y*A**z\", [symbol(\"A\", { commutative: false })]), { combine: \"base\" })", () => powsimp(Qs("A**x*A**y*A**z", [symbol("A", { commutative: false })]), { combine: "base" }), "A**x*A**y*A**z"],
    ["powsimp(Qs(\"A**x*A**y*A**z\", [symbol(\"A\", { commutative: false })]), { combine: \"exp\" })", () => powsimp(Qs("A**x*A**y*A**z", [symbol("A", { commutative: false })]), { combine: "exp" }), "A**(x + y + z)"],
    ["powsimp(Qs(\"A**x*B**x*C**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false }), symbol(\"C\", { commutative: false })]), { combine: \"all\" })", () => powsimp(Qs("A**x*B**x*C**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false }), symbol("C", { commutative: false })]), { combine: "all" }), "A**x*B**x*C**x"],
    ["powsimp(Qs(\"A**x*B**x*C**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false }), symbol(\"C\", { commutative: false })]), { combine: \"base\" })", () => powsimp(Qs("A**x*B**x*C**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false }), symbol("C", { commutative: false })]), { combine: "base" }), "A**x*B**x*C**x"],
    ["powsimp(Qs(\"A**x*B**x*C**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false }), symbol(\"C\", { commutative: false })]), { combine: \"exp\" })", () => powsimp(Qs("A**x*B**x*C**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false }), symbol("C", { commutative: false })]), { combine: "exp" }), "A**x*B**x*C**x"],
    ["powsimp(Qs(\"B**x*A**x*C**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false }), symbol(\"C\", { commutative: false })]), { combine: \"all\" })", () => powsimp(Qs("B**x*A**x*C**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false }), symbol("C", { commutative: false })]), { combine: "all" }), "B**x*A**x*C**x"],
    ["powsimp(Qs(\"B**x*A**x*C**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false }), symbol(\"C\", { commutative: false })]), { combine: \"base\" })", () => powsimp(Qs("B**x*A**x*C**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false }), symbol("C", { commutative: false })]), { combine: "base" }), "B**x*A**x*C**x"],
    ["powsimp(Qs(\"B**x*A**x*C**x\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false }), symbol(\"C\", { commutative: false })]), { combine: \"exp\" })", () => powsimp(Qs("B**x*A**x*C**x", [symbol("A", { commutative: false }), symbol("B", { commutative: false }), symbol("C", { commutative: false })]), { combine: "exp" }), "B**x*A**x*C**x"],
    ["powsimp(P(\"(-x + y)/sqrt(x - y)\"))", () => powsimp(P("(-x + y)/sqrt(x - y)")), "-sqrt(x - y)"],
    ["powsimp(P(\"(-x + y)*(y - z)/(sqrt(x - y)*sqrt(-y + z))\"))", () => powsimp(P("(-x + y)*(y - z)/(sqrt(x - y)*sqrt(-y + z))")), "sqrt(x - y)*sqrt(-y + z)"],
    ["powsimp(Qs(\"(-p)**a/p**a\", [symbol(\"p\", { positive: true })]))", () => powsimp(Qs("(-p)**a/p**a", [symbol("p", { positive: true })])), "(-1)**a"],
    ["powsimp(Qs(\"p**a*(-p)**a\", [symbol(\"p\", { positive: true })]))", () => powsimp(Qs("p**a*(-p)**a", [symbol("p", { positive: true })])), "(-p**2)**a"],
    ["powsimp(Qs(\"(-n)**a/n**a\", [symbol(\"n\", { negative: true })]))", () => powsimp(Qs("(-n)**a/n**a", [symbol("n", { negative: true })])), "(-1)**(-a)"],
    ["powsimp(Qs(\"n**a*(-n)**a\", [symbol(\"n\", { negative: true })]))", () => powsimp(Qs("n**a*(-n)**a", [symbol("n", { negative: true })])), "(-n**2)**a"],
    ["powsimp(P(\"(-x)**a/x**a\"))", () => powsimp(P("(-x)**a/x**a")), "(-x)**a/x**a"],
    ["powsimp(P(\"sin(exp_polar(x)*exp_polar(y))\"))", () => powsimp(P("sin(exp_polar(x)*exp_polar(y))")), "sin(exp_polar(x)*exp_polar(y))"],
    ["powsimp(P('2*3**x/3'))", () => powsimp(P('2*3**x/3')), "2*3**(x - 1)"],
    ["powsimp(P('3**x/9'))", () => powsimp(P('3**x/9')), "3**(x - 2)"],
    ["powsimp(P('9*3**x'))", () => powsimp(P('9*3**x')), "3**(x + 2)"],
    ["powsimp(P('3**x/6'))", () => powsimp(P('3**x/6')), "3**(x - 1)/2"],
    ["powsimp(P('-2*2**x'))", () => powsimp(P('-2*2**x')), "-2**(x + 1)"],
    ["powsimp(P('(2/3)**x*4/9'))", () => powsimp(P('(2/3)**x*4/9')), "(2/3)**(x + 2)"],
    ["powsimp(P('(2/3)**x*9/4'))", () => powsimp(P('(2/3)**x*9/4')), "(2/3)**(x - 2)"],
    ["powsimp(P('(2/3)**x*2/9'))", () => powsimp(P('(2/3)**x*2/9')), "(2/3)**(x + 1)/3"],
    ["powsimp(P('(-2)**x*4'))", () => powsimp(P('(-2)**x*4')), "(-2)**(x + 2)"],
    ["powsimp(P('2**(1/3)*2**x/4'))", () => powsimp(P('2**(1/3)*2**x/4')), "2**(x - 5/3)"],
    ["powsimp(P('x**a*(1/x)**b'))", () => powsimp(P('x**a*(1/x)**b')), "x**a*(1/x)**b"],
    ["powsimp(Qs('p**a*(1/p)**b', [symbol('p', { positive: true })]))", () => powsimp(Qs('p**a*(1/p)**b', [symbol('p', { positive: true })])), "p**(a - b)"],
    ["powsimp(Qs('(2*p)**a*(1/(2*p))**b', [symbol('p', { positive: true })]))", () => powsimp(Qs('(2*p)**a*(1/(2*p))**b', [symbol('p', { positive: true })])), "(2*p)**(a - b)"],
    ["powsimp(Qs('(p/2)**a*(2/p)**b', [symbol('p', { positive: true })]))", () => powsimp(Qs('(p/2)**a*(2/p)**b', [symbol('p', { positive: true })])), "(p/2)**(a - b)"],
    ["powsimp(P('(x + 1)**a*(-x - 1)**b'))", () => powsimp(P('(x + 1)**a*(-x - 1)**b')), "(-x - 1)**b*(x + 1)**a"],
    ["powsimp(P('x**2*(-x)**3'))", () => powsimp(P('x**2*(-x)**3')), "-x**5"],
    ["powsimp(Qs('x**a*(-x)**b', [symbol('x', { positive: true })]))", () => powsimp(Qs('x**a*(-x)**b', [symbol('x', { positive: true })])), "(-1)**b*x**(a + b)"],
    ["powsimp(Qs('x**a*(-x)**n', [symbol('n', { integer: true })]))", () => powsimp(Qs('x**a*(-x)**n', [symbol('n', { integer: true })])), "x**a*(-x)**n"],
    ["powsimp(Qs('x**a*(-x)**b', [symbol('x', { negative: true })]))", () => powsimp(Qs('x**a*(-x)**b', [symbol('x', { negative: true })])), "(-1)**a*(-x)**(a + b)"],
    ["powsimp(P('sqrt(x)*sqrt(y)'), { combine: 'base', force: true })", () => powsimp(P('sqrt(x)*sqrt(y)'), { combine: 'base', force: true }), "sqrt(x*y)"],
    ["powsimp(P('x**(2*y)*z**(2*y)'), { combine: 'base' })", () => powsimp(P('x**(2*y)*z**(2*y)'), { combine: 'base' }), "x**(2*y)*z**(2*y)"],
    ["powsimp(P('x**(y + 1)*z**(-y - 1)'), { combine: 'base', force: true })", () => powsimp(P('x**(y + 1)*z**(-y - 1)'), { combine: 'base', force: true }), "x**(y + 1)*z**(-y - 1)"],
    ["powsimp(Qs('a**x*b**x*c**x', [symbol('a', { negative: true }), symbol('b', { negative: true })]), { combine: 'base' })", () => powsimp(Qs('a**x*b**x*c**x', [symbol('a', { negative: true }), symbol('b', { negative: true })]), { combine: 'base' }), "a**x*b**x*c**x"],
    ["powsimp(Qs('(1+p)**x*(1+p)**y*q**x*(2+q)**x', [symbol('p', { positive: true }), symbol('q', { positive: true })]), { combine: 'base' })", () => powsimp(Qs('(1+p)**x*(1+p)**y*q**x*(2+q)**x', [symbol('p', { positive: true }), symbol('q', { positive: true })]), { combine: 'base' }), "(q*(p + 1)*(q + 2))**x*(p + 1)**y"],
    ["powsimp(P('exp(x)*exp(y)*z**2*z**y'), { deep: true })", () => powsimp(P('exp(x)*exp(y)*z**2*z**y'), { deep: true }), "z**(y + 2)*exp(x + y)"],
    ["powsimp(P('sin(exp(x)*exp(y))'), { deep: true })", () => powsimp(P('sin(exp(x)*exp(y))'), { deep: true }), "sin(exp(x + y))"],
    ["powsimp(P('exp(x)**y*exp(x)'))", () => powsimp(P('exp(x)**y*exp(x)')), "exp(x)*exp(x)**y"],
    ["powsimp(P('x**(2*y)*x**(3*y)'), { combine: 'exp' })", () => powsimp(P('x**(2*y)*x**(3*y)'), { combine: 'exp' }), "x**(5*y)"],
    ["powdenest(P(\"sqrt(sin(x)**2)\"), { force: true })", () => powdenest(P("sqrt(sin(x)**2)"), { force: true }), "sin(x)"],
    ["powdenest(P(\"(x**(1/(2*y)))**(2*y)\"), { force: true })", () => powdenest(P("(x**(1/(2*y)))**(2*y)"), { force: true }), "x"],
    ["powdenest(P(\"(x**(b/(1 - a)))**(1 - a)*(y**((1 - b)/(1 - a)))**(1 - a)*exp(z/(1 - a))**(1 - a)\"), { force: true })", () => powdenest(P("(x**(b/(1 - a)))**(1 - a)*(y**((1 - b)/(1 - a)))**(1 - a)*exp(z/(1 - a))**(1 - a)"), { force: true }), "x**b*y**(1 - b)*exp(z)"],
    ["powdenest(P(\"x\"))", () => powdenest(P("x")), "x"],
    ["powdenest(P(\"x + 2*(x**(2*a/3))**(3*x)\"))", () => powdenest(P("x + 2*(x**(2*a/3))**(3*x)")), "x + 2*(x**(2*a/3))**(3*x)"],
    ["powdenest(P(\"exp(2*a/3)**(3*x)\"))", () => powdenest(P("exp(2*a/3)**(3*x)")), "exp(2*a/3)**(3*x)"],
    ["powdenest(P(\"(x**(2*a/3))**(3*x)\"))", () => powdenest(P("(x**(2*a/3))**(3*x)")), "(x**(2*a/3))**(3*x)"],
    ["powdenest(P(\"exp(3*x*log(2))\"))", () => powdenest(P("exp(3*x*log(2))")), "2**(3*x)"],
    ["powdenest(Qs(\"p\", [symbol(\"p\", { positive: true })]))", () => powdenest(Qs("p", [symbol("p", { positive: true })])), "p"],
    ["powdenest(Qs(\"p**(2*i)*q**(4*i)\", [symbol(\"p\", { positive: true }), symbol(\"q\", { positive: true }), symbol(\"i\", { integer: true })]))", () => powdenest(Qs("p**(2*i)*q**(4*i)", [symbol("p", { positive: true }), symbol("q", { positive: true }), symbol("i", { integer: true })])), "(p*q**2)**(2*i)"],
    ["powdenest(Qs(\"x**(x*(i + j))\", [symbol(\"j\", { integer: true }), symbol(\"i\", { integer: true })]))", () => powdenest(Qs("x**(x*(i + j))", [symbol("j", { integer: true }), symbol("i", { integer: true })])), "x**(x*(i + j))"],
    ["powdenest(P(\"exp(3*y*log(x))\"))", () => powdenest(P("exp(3*y*log(x))")), "x**(3*y)"],
    ["powdenest(P(\"exp(y*(log(a) + log(b)))\"))", () => powdenest(P("exp(y*(log(a) + log(b)))")), "(a*b)**y"],
    ["powdenest(P(\"a**3*b**3\"))", () => powdenest(P("a**3*b**3")), "a**3*b**3"],
    ["powdenest(Qs(\"((x**(2*i))**(3*y))**x\", [symbol(\"i\", { integer: true })]))", () => powdenest(Qs("((x**(2*i))**(3*y))**x", [symbol("i", { integer: true })])), "((x**(2*i))**(3*y))**x"],
    ["powdenest(Qs(\"((x**(2*i))**(3*y))**x\", [symbol(\"i\", { integer: true })]), { force: true })", () => powdenest(Qs("((x**(2*i))**(3*y))**x", [symbol("i", { integer: true })]), { force: true }), "x**(6*i*x*y)"],
    ["powdenest(Qs(\"((x**(2*a/3))**(3*y/i))**x\", [symbol(\"i\", { integer: true })]))", () => powdenest(Qs("((x**(2*a/3))**(3*y/i))**x", [symbol("i", { integer: true })])), "((x**(2*a/3))**(3*y/i))**x"],
    ["powdenest(Qs(\"(x**(2*i)*y**(4*i))**z\", [symbol(\"i\", { integer: true })]), { force: true })", () => powdenest(Qs("(x**(2*i)*y**(4*i))**z", [symbol("i", { integer: true })]), { force: true }), "(x*y**2)**(2*i*z)"],
    ["powdenest(Qs(\"(p**(2*i)*q**(4*i))**j\", [symbol(\"p\", { positive: true }), symbol(\"j\", { integer: true }), symbol(\"q\", { positive: true }), symbol(\"i\", { integer: true })]))", () => powdenest(Qs("(p**(2*i)*q**(4*i))**j", [symbol("p", { positive: true }), symbol("j", { integer: true }), symbol("q", { positive: true }), symbol("i", { integer: true })])), "(p*q**2)**(2*i*j)"],
    ["powdenest(Qs(\"((p**(2*a))**(3*y))**x\", [symbol(\"p\", { positive: true })]))", () => powdenest(Qs("((p**(2*a))**(3*y))**x", [symbol("p", { positive: true })])), "((p**(2*a))**(3*y))**x"],
    ["powdenest(P(\"((x**2*y**4)**a)**(x*y)\"))", () => powdenest(P("((x**2*y**4)**a)**(x*y)")), "((x**2*y**4)**a)**(x*y)"],
    ["powdenest(P(\"((x**2*y**4)**a)**(3*x*y)\"))", () => powdenest(P("((x**2*y**4)**a)**(3*x*y)")), "((x**2*y**4)**a)**(3*x*y)"],
    ["powdenest(P(\"((x**2*y**4)**a)**(x*y)\"), { force: true })", () => powdenest(P("((x**2*y**4)**a)**(x*y)"), { force: true }), "(x*y**2)**(2*a*x*y)"],
    ["powdenest(P(\"((x**2*y**4)**a)**(3*x*y)\"), { force: true })", () => powdenest(P("((x**2*y**4)**a)**(3*x*y)"), { force: true }), "(x*y**2)**(6*a*x*y)"],
    ["powdenest(Qs(\"(x**2*y**6)**i\", [symbol(\"i\", { integer: true })]))", () => powdenest(Qs("(x**2*y**6)**i", [symbol("i", { integer: true })])), "(x**2*y**6)**i"],
    ["powdenest(Qs(\"(x**2*y**6)**i\", [symbol(\"x\", { positive: true }), symbol(\"y\", { positive: true }), symbol(\"i\", { integer: true })]))", () => powdenest(Qs("(x**2*y**6)**i", [symbol("x", { positive: true }), symbol("y", { positive: true }), symbol("i", { integer: true })])), "(x*y**3)**(2*i)"],
    ["powdenest(Qs(\"(x**(2*i/3)*y**(i/2))**(2*i)\", [symbol(\"x\", { positive: true }), symbol(\"y\", { positive: true }), symbol(\"i\", { integer: true })]))", () => powdenest(Qs("(x**(2*i/3)*y**(i/2))**(2*i)", [symbol("x", { positive: true }), symbol("y", { positive: true }), symbol("i", { integer: true })])), "(x**(4/3)*y)**(i**2)"],
    ["powdenest(Qs(\"x**i*y**(3*i)\", [symbol(\"x\", { positive: true }), symbol(\"y\", { positive: true }), symbol(\"i\", { integer: true })]))", () => powdenest(Qs("x**i*y**(3*i)", [symbol("x", { positive: true }), symbol("y", { positive: true }), symbol("i", { integer: true })])), "(x*y**3)**i"],
    ["logcombine(P(\"-log(2) + log(3)\"))", () => logcombine(P("-log(2) + log(3)")), "log(3/2)"],
    ["logcombine(Qs(\"log(x) - log(y)\", [symbol(\"x\", { positive: true }), symbol(\"y\", { positive: true })]))", () => logcombine(Qs("log(x) - log(y)", [symbol("x", { positive: true }), symbol("y", { positive: true })])), "log(x/y)"],
    ["logcombine(P(\"-log(2) + log(3/2)\"))", () => logcombine(P("-log(2) + log(3/2)")), "log(3/4)"],
    ["logcombine(P(\"log(x) + 2*log(y)\"))", () => logcombine(P("log(x) + 2*log(y)")), "log(x) + 2*log(y)"],
    ["logcombine(P(\"log(x) + 2*log(y)\"), { force: true })", () => logcombine(P("log(x) + 2*log(y)"), { force: true }), "log(x*y**2)"],
    ["logcombine(Qs(\"a*log(w) + log(z)\", [symbol(\"w\", { positive: true }), symbol(\"z\", { positive: true })]))", () => logcombine(Qs("a*log(w) + log(z)", [symbol("w", { positive: true }), symbol("z", { positive: true })])), "a*log(w) + log(z)"],
    ["logcombine(Qs(\"b*log(x) + b*log(z)\", [symbol(\"b\", { real: true }), symbol(\"z\", { positive: true })]))", () => logcombine(Qs("b*log(x) + b*log(z)", [symbol("b", { real: true }), symbol("z", { positive: true })])), "b*log(x) + log(z**b)"],
    ["logcombine(Qs(\"b*log(z) - log(w)\", [symbol(\"w\", { positive: true }), symbol(\"z\", { positive: true }), symbol(\"b\", { real: true })]))", () => logcombine(Qs("b*log(z) - log(w)", [symbol("w", { positive: true }), symbol("z", { positive: true }), symbol("b", { real: true })])), "log(z**b/w)"],
    ["logcombine(Qs(\"log(x)*log(z)\", [symbol(\"z\", { positive: true })]))", () => logcombine(Qs("log(x)*log(z)", [symbol("z", { positive: true })])), "log(x)*log(z)"],
    ["logcombine(Qs(\"log(w)*log(x)\", [symbol(\"w\", { positive: true })]))", () => logcombine(Qs("log(w)*log(x)", [symbol("w", { positive: true })])), "log(w)*log(x)"],
    ["logcombine(Qs(\"cos(b*log(w) - 2*log(z))\", [symbol(\"b\", { real: true }), symbol(\"z\", { positive: true }), symbol(\"w\", { positive: true })]))", () => logcombine(Qs("cos(b*log(w) - 2*log(z))", [symbol("b", { real: true }), symbol("z", { positive: true }), symbol("w", { positive: true })])), "cos(log(w**b/z**2))"],
    ["logcombine(Qs(\"-log(z) + log(log(x) - log(y))\", [symbol(\"z\", { positive: true })]), { force: true })", () => logcombine(Qs("-log(z) + log(log(x) - log(y))", [symbol("z", { positive: true })]), { force: true }), "log(log(x/y)/z)"],
    ["logcombine(P(\"(2 + I)*log(x)\"), { force: true })", () => logcombine(P("(2 + I)*log(x)"), { force: true }), "(2 + I)*log(x)"],
    ["logcombine(P(\"(x**2 + log(x) - log(y))/(x*y)\"), { force: true })", () => logcombine(P("(x**2 + log(x) - log(y))/(x*y)"), { force: true }), "(x**2 + log(x/y))/(x*y)"],
    ["logcombine(Qs(\"2*log(x)*log(y) + log(z)\", [symbol(\"z\", { positive: true })]), { force: true })", () => logcombine(Qs("2*log(x)*log(y) + log(z)", [symbol("z", { positive: true })]), { force: true }), "log(y**log(x**2)*z)"],
    ["logcombine(P(\"(x*y + sqrt(x**4 + y**4) + log(x) - log(y))/(pi*x**(2/3)*y**(3/2))\"), { force: true })", () => logcombine(P("(x*y + sqrt(x**4 + y**4) + log(x) - log(y))/(pi*x**(2/3)*y**(3/2))"), { force: true }), "(x*y + sqrt(x**4 + y**4) + log(x/y))/(pi*x**(2/3)*y**(3/2))"],
    ["logcombine(P(\"acos(-log(x/y))*gamma(-log(x/y))\"), { force: true })", () => logcombine(P("acos(-log(x/y))*gamma(-log(x/y))"), { force: true }), "acos(-log(x/y))*gamma(-log(x/y))"],
    ["logcombine(Qs(\"2*log(w)*log(x)*log(z) + log(w) + log(z)\", [symbol(\"w\", { positive: true }), symbol(\"z\", { positive: true })]))", () => logcombine(Qs("2*log(w)*log(x)*log(z) + log(w) + log(z)", [symbol("w", { positive: true }), symbol("z", { positive: true })])), "log(x)*log(z**log(w**2)) + log(w*z)"],
    ["logcombine(Qs(\"3*log(w) + 3*log(z)\", [symbol(\"w\", { positive: true }), symbol(\"z\", { positive: true })]))", () => logcombine(Qs("3*log(w) + 3*log(z)", [symbol("w", { positive: true }), symbol("z", { positive: true })])), "log(w**3*z**3)"],
    ["logcombine(P(\"x*(y + 1) + log(2) + log(3)\"))", () => logcombine(P("x*(y + 1) + log(2) + log(3)")), "x*(y + 1) + log(6)"],
    ["logcombine(P(\"log(x) + log(2)\"))", () => logcombine(P("log(x) + log(2)")), "log(2*x)"],
    ["logcombine(P(\"log(Abs(x)) + log(Abs(y))\"))", () => logcombine(P("log(Abs(x)) + log(Abs(y))")), "log(Abs(x)) + log(Abs(y))"],
    ["logcombine(P('(2 + I)*log(x)'), { force: true })", () => logcombine(P('(2 + I)*log(x)'), { force: true }), "(2 + I)*log(x)"],
    ["logcombine(P('I*log(x) + log(y)'), { force: true })", () => logcombine(P('I*log(x) + log(y)'), { force: true }), "I*log(x) + log(y)"],
    ["logcombine(P('pi*log(x)'), { force: true })", () => logcombine(P('pi*log(x)'), { force: true }), "log(x**pi)"],
    ["logcombine(P('sqrt(2)*log(x)'), { force: true })", () => logcombine(P('sqrt(2)*log(x)'), { force: true }), "log(x**(sqrt(2)))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["powsimp(P('x*sqrt(x/y)/y**3'))", () => powsimp(PA('x*sqrt(x/y)/y**3')), "x*sqrt(x/y)/y**3"],
    ["powsimp(P('x**2*sqrt(x/y)/y**3'))", () => powsimp(PA('x**2*sqrt(x/y)/y**3')), "x**2*sqrt(x/y)/y**3"],
    ["powsimp(P('x**3*(x/y)**(1/3)*y**5'))", () => powsimp(PA('x**3*(x/y)**(1/3)*y**5')), "x**3*y**5*(x/y)**(1/3)"],
    ["powsimp(P('x**3*(x*y**2)**(1/3)*y**5'))", () => powsimp(PA('x**3*(x*y**2)**(1/3)*y**5')), "x*y*(x*y**2)**(7/3)"],
    ["powsimp(P('x**4*(x*y**2)**(1/3)*y**5*(x*y)**(1/2)'))", () => powsimp(PA('x**4*(x*y**2)**(1/3)*y**5*(x*y)**(1/2)')), "x*(x*y)**(3/2)*(x*y**2)**(7/3)"],
    ["powsimp(P('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)'))", () => powsimp(PA('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)')), "y**3*(x*sqrt(y))**(13/3)*sqrt(x*y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe("powsimp, powdenest, logcombine, expand_log (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["powsimp(P('((w**(-1)*w**(2)*w)**(-3/2)*w**(1/2))**(1/4)*w**(5/2)*(w**(-1)*w**(2)*w)**(1/2)*w**(1/2)', {n: {integer: true}}))", () => powsimp(PA('((w**(-1)*w**(2)*w)**(-3/2)*w**(1/2))**(1/4)*w**(5/2)*(w**(-1)*w**(2)*w)**(1/2)*w**(1/2)', {n: {integer: true}})), "sqrt(w**2)/(w**2*(sqrt(w)/(w**2)**(3/2))**(7/4))"],
    ["powsimp(P('(x*y**(-1))**(1/2)*x**(1)*y**(4)', {n: {integer: true}}))", () => powsimp(PA('(x*y**(-1))**(1/2)*x**(1)*y**(4)', {n: {integer: true}})), "x*y**4*sqrt(x/y)"],
    ["powsimp(P('(y**(-1/2)*w**(1/2))**(1/4)*y**(-1)*w**(3)', {n: {integer: true}}))", () => powsimp(PA('(y**(-1/2)*w**(1/2))**(1/4)*y**(-1)*w**(3)', {n: {integer: true}})), "w**2*(sqrt(w)/sqrt(y))**(9/4)"],
    ["powsimp(P('((z**(2)*y**(1/2))**(5/2)*z)**(2/3)*z**(5/2)*y**(5/2)*z**(1)', {n: {integer: true}}))", () => powsimp(PA('((z**(2)*y**(1/2))**(5/2)*z)**(2/3)*z**(5/2)*y**(5/2)*z**(1)', {n: {integer: true}})), "y**(5/2)*z**(7/2)*(z*(sqrt(y)*z**2)**(5/2))**(2/3)"],
    ["powsimp(P('(w*x**(n))**(-3/2)*w**(3/2)', {n: {integer: true}}))", () => powsimp(PA('(w*x**(n))**(-3/2)*w**(3/2)', {n: {integer: true}})), "w**(3/2)/(w*x**n)**(3/2)"],
    ["powsimp(P('(w**(-1/2)*(w**(n)*x**(-1/2))**(1/2))**(3/2)*w**(-1/2)*x**(-2)*(w**(n)*x**(-1/2))**(1/2)', {n: {integer: true}}))", () => powsimp(PA('(w**(-1/2)*(w**(n)*x**(-1/2))**(1/2))**(3/2)*w**(-1/2)*x**(-2)*(w**(n)*x**(-1/2))**(1/2)', {n: {integer: true}})), "(sqrt(w**n/sqrt(x))/sqrt(w))**(5/2)/x**2"],
    ["powsimp(P('sqrt(z*sqrt(x*sqrt(y)))*z*(x*sqrt(y))**(3/2)', {n: {integer: true}}))", () => powsimp(PA('sqrt(z*sqrt(x*sqrt(y)))*z*(x*sqrt(y))**(3/2)', {n: {integer: true}})), "x*sqrt(y)*(z*sqrt(x*sqrt(y)))**(3/2)"],
    ["powsimp(P('sqrt(z*sqrt(x*y**(1/3)))*z*(x*y**(1/3))**(3/2)', {n: {integer: true}}))", () => powsimp(PA('sqrt(z*sqrt(x*y**(1/3)))*z*(x*y**(1/3))**(3/2)', {n: {integer: true}})), "x*y**(1/3)*(z*sqrt(x*y**(1/3)))**(3/2)"],
    ["powsimp(P('(y*x**(t/2)*y**(t/2))**(5/2)', {n: {integer: true}}))", () => powsimp(PA('(y*x**(t/2)*y**(t/2))**(5/2)', {n: {integer: true}})), "(x**(t/2)*y*y**(t/2))**(5/2)"],
    ["powsimp(P('x*sqrt(x/y)/y**3', {n: {integer: true}}))", () => powsimp(PA('x*sqrt(x/y)/y**3', {n: {integer: true}})), "x*sqrt(x/y)/y**3"],
    ["powsimp(P('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)', {n: {integer: true}}))", () => powsimp(PA('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)', {n: {integer: true}})), "y**3*(x*sqrt(y))**(13/3)*sqrt(x*y)"],
    ["powsimp(P('n**(1/3)*x**(1/3)*y**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(PA('n**(1/3)*x**(1/3)*y**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "(-1)**(1/3)*x**(1/3)*y**(1/3)*(-n)**(1/3)"],
    ["powsimp(P('n**(j/3)*x**(j/3)*y**(j/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(PA('n**(j/3)*x**(j/3)*y**(j/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "(-1)**(j/3)*x**(j/3)*y**(j/3)*(-n)**(j/3)"],
    ["powsimp(P('n**(1/3)*x**(1/3)*y**(1/3)*p**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(PA('n**(1/3)*x**(1/3)*y**(1/3)*p**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "(-1)**(1/3)*p**(1/3)*x**(1/3)*y**(1/3)*(-n)**(1/3)"],
    ["powsimp(P('n**(x/3)*x**(x/3)*y**(x/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(PA('n**(x/3)*x**(x/3)*y**(x/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "n**(x/3)*x**(x/3)*y**(x/3)"],
    ["powdenest(P('8**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('8**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2**(3*x)"],
    ["powdenest(P('4**x*3', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('4**x*3', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3*2**(2*x)"],
    ["powdenest(P('sqrt(8)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('sqrt(8)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(2*sqrt(2))**x"],
    ["powdenest(P('(p**(1/2)*q**sqrt(2))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(p**(1/2)*q**sqrt(2))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(sqrt(p)*q**(sqrt(2)))**z"],
    ["powdenest(P('(p**x*q**(2*x))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(p**x*q**(2*x))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(p**x*q**(2*x))**z"],
    ["powdenest(P('(p**pi*q**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(p**pi*q**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(p**pi*q**2)**z"],
    ["powdenest(P('(n**2)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => powdenest(PA('(n**2)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "(-n)**(2*x)"],
    // SymPy 1.14 gives (p**2.5*q**3.0)**(1.0*z), the same value: its gcd of the coefficients 2.5 and 3 of the logarithms is 1.0, symjs keeps exact exponents
    ["powdenest(P('(p**2.5*q**3)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(p**2.5*q**3)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(p**2.5*q**3)**z"],
    ["logcombine(P('2*log(p)*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(PA('2*log(p)*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(q**log(p**2))"],
    ["logcombine(P('log(2)*log(3)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(PA('log(2)*log(3)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(3**log(sqrt(2)))"],
    ["logcombine(P('log(4)*log(9)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(PA('log(4)*log(9)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(9**log(2))"],
    ["logcombine(P('log(p)*log(q)*x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(PA('log(p)*log(q)*x', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "x*log(q**log(p))"],
    ["powdenest(P('(1/(p**2*q**3))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(1/(p**2*q**3))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(1/(p**2*q**3))**z"],
    ["powdenest(P('(q**3/p**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(q**3/p**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(q**3/p**2)**z"],
    ["powdenest(P('(p**(-2)*q**(-4))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(p**(-2)*q**(-4))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(1/(p*q**2))**(2*z)"],
    ["logcombine(P('x*log(p) - x*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(PA('x*log(p) - x*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "x*log(p/q)"],
    ["logcombine(P('x*log(p) - x*log(q) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('x*log(p) - x*log(q) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(p**x*y/q**x)"],
    ["logcombine(P('f(1)*log(x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('f(1)*log(x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(x**f(1))"],
    ["logcombine(P('I*log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('I*log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "I*log(y)"],
    ["logcombine(P('pi*log(x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('pi*log(x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log((x*y)**pi)"],
    ["logcombine(P('log(x) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('log(x) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(x*y)"],
    ["logcombine(P('log(x) + log(n)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('log(x) + log(n)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(n*x)"],
    ["logcombine(P('2*log(x) - log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(PA('2*log(x) - log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(x**2/y)"],
    ["logcombine(P('-log(p) + 2*x*log(q) - x*log(p)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(PA('-log(p) + 2*x*log(q) - x*log(p)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "x*log(q**2/p) - log(p)"],
    ["powdenest(P('3**x*y', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('3**x*y', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3**x*y"],
    ["powdenest(P('6**x*12**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('6**x*12**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "12**y*6**x"],
    ["powdenest(P('(3*x)**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(PA('(3*x)**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(3*x)**y"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('powsimp (cov2): an exponent that becomes symbolic while bases are combined', () => {
  it('keeps the value where SymPy 1.14 raises TypeError (cannot determine truth value of Relational: 2*n < 2)', () => {
    // sqrt(s*sqrt(s**n*y))*s*(s**n*y)**(5/2) = y**2*s**(2*n)*(s*sqrt(s**n*y))**(3/2) for an integer n
    const e = PA('sqrt(sin(x)*sqrt(sin(x)**n*y))*sin(x)*(sin(x)**n*y)**(5/2)', { n: { integer: true } });
    const r = powsimp(e);
    expect(String(r)).toBe('y**2*(sqrt(y*sin(x)**n)*sin(x))**(3/2)*sin(x)**(2*n)');
    const at = (v: Expr) => v.subs([[symbol('n', { integer: true }), 3], [symbol('x'), float(0.7)], [symbol('y'), float(1.3)]]).toNumber();
    expect(at(r)).toBeCloseTo(at(e), 12);
  });
});

describe('powsimp: SymPy 1.14 test_powsimp cases', () => {
  it('a negative exponent sum combines with the inverted base', () => {
    expect(String(powsimp(PA('x**(i + 1)*y**(-i - 1)', { i: { integer: true } })))).toBe('(x/y)**(i + 1)');
  });
  it('powers of the float 1 are 1.0', () => {
    const f = float(1);
    const x = symbol('x', { nonnegative: true });
    expect(String(powsimp(mul(pow(f, add(x, 1)), pow(pow(f, x), -1))))).toBe('1.00000000000000');
  });
});

describe('powdenest with force and a base that is not positive', () => {
  it('keeps the nested power', () => {
    const n = new Sym('n', { negative: true });
    const Qn = (s: string) => Qs(s, [n]);
    // SymPy powdenest(..., force=True)
    expect(sstr(powdenest(Qn('(n**a)**b'), { force: true }))).toBe('(n**a)**b');
    expect(sstr(powdenest(P('((-2)**a)**b'), { force: true }))).toBe('((-2)**a)**b');
    expect(sstr(powdenest(Qn('(n**a)**b*(x**a)**b'), { force: true }))).toBe('x**(a*b)*(n**a)**b');
  });
});

describe('powsimp and powdenest with polar bases (SymPy test_powsimp_polar, test_powdenest_polar)', () => {
  const pol = ['x', 'y', 'z', 'p', 'q'].map((n) => symbol(n, { polar: true }));
  const Pp = (s: string) => parse(s, { symbols: pol });
  const cases: [string, () => Expr, string][] = [
    ['powdenest((x*y*z)**a)', () => powdenest(Pp('(x*y*z)**a')), 'x**a*y**a*z**a'],
    ['powdenest((x**a*y**b)**c)', () => powdenest(Pp('(x**a*y**b)**c')), 'x**(a*c)*y**(b*c)'],
    ['powdenest(((x**a)**b*y**c)**c)', () => powdenest(Pp('((x**a)**b*y**c)**c')), 'x**(a*b*c)*y**(c**2)'],
    ['powsimp(p**a*q**a)', () => powsimp(Pp('p**a*q**a')), '(p*q)**a'],
    ['p**a*(1/p)**a', () => Pp('p**a*(1/p)**a'), '1'],
    ['powsimp(exp_polar(a)*exp_polar(b))', () => powsimp(P('exp_polar(a)*exp_polar(b)')), 'exp_polar(a + b)'],
    ['powsimp(exp_polar(a)*exp_polar(b)*p**a*p**b)', () => powsimp(Pp('exp_polar(a)*exp_polar(b)*p**a*p**b')), '(p*exp_polar(1))**(a + b)'],
    ["combine='exp'", () => powsimp(Pp('exp_polar(a)*exp_polar(b)*p**a*p**b'), { combine: 'exp' }), 'p**(a + b)*exp_polar(a + b)'],
    ['a sum', () => powsimp(Pp('exp_polar(a)*exp_polar(b)*exp_polar(2)*sin(a) + sin(b) + p**a*p**b')), 'p**(a + b) + exp_polar(a + b + 2)*sin(a) + sin(b)'],
    ['deep', () => powsimp(P('sin(exp_polar(a)*exp_polar(b))'), { deep: true }), 'sin(exp_polar(a + b))'],
    // a polar factor of a product base: SymPy _denest_pow splits it off
    ['powdenest((p*w)**a)', () => powdenest(parse('(polar_lift(w)*w)**a')), 'w**a*polar_lift(w)**a'],
    ['powdenest((p*q*w)**a)', () => powdenest(parse('(polar_lift(w)*exp_polar(v)*w)**a')), 'w**a*exp_polar(a*v)*polar_lift(w)**a'],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(String(run())).toBe(want);
  });
});
