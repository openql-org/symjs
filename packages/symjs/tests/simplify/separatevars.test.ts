// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/separatevars.ts.

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Sym, parse, separatevars, symbol } from '../../src';
import type { Expr } from '../../src';

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("simplify functions: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["separatevars(P(\"2*n*x*z + 2*x*y*z\"))", () => separatevars(P("2*n*x*z + 2*x*y*z")), "2*x*z*(n + y)"],
    ["separatevars(P(\"x*y*z + x*z\"))", () => separatevars(P("x*y*z + x*z")), "x*z*(y + 1)"],
    ["separatevars(P(\"x*y**2*sin(x) + x*sin(x)*sin(y)\"))", () => separatevars(P("x*y**2*sin(x) + x*sin(x)*sin(y)")), "x*(y**2 + sin(y))*sin(x)"],
    ["separatevars(P(\"x*E**x + x*E**(x + y)\"))", () => separatevars(P("x*E**x + x*E**(x + y)")), "x*(exp(y) + 1)*exp(x)"],
    ["separatevars(P(\"(x*(y + 1))**z\"))", () => separatevars(P("(x*(y + 1))**z")), "(x*(y + 1))**z"],
    ["separatevars(P(\"x*y + x + y + 1\"))", () => separatevars(P("x*y + x + y + 1")), "(x + 1)*(y + 1)"],
    ["separatevars(P(\"2*x + y**2 + (x - y)*(x + y) + 1\"))", () => separatevars(P("2*x + y**2 + (x - y)*(x + y) + 1")), "(x + 1)**2"],
    ["separatevars(Qs(\"sqrt(p**2*x + p**2)\", [symbol(\"p\", { positive: true })]))", () => separatevars(Qs("sqrt(p**2*x + p**2)", [symbol("p", { positive: true })])), "p*sqrt(x + 1)"],
    ["separatevars(Qs(\"sqrt(y*(p**2*x + p**2))\", [symbol(\"p\", { positive: true })]))", () => separatevars(Qs("sqrt(y*(p**2*x + p**2))", [symbol("p", { positive: true })])), "p*sqrt(y*(x + 1))"],
    ["separatevars(Qs(\"sqrt(y*(p**2*x + p**2))\", [symbol(\"p\", { positive: true })]), { force: true })", () => separatevars(Qs("sqrt(y*(p**2*x + p**2))", [symbol("p", { positive: true })]), { force: true }), "p*sqrt(y)*sqrt(x + 1)"],
    ["separatevars(P(\"sqrt(x*y)\"))", () => separatevars(P("sqrt(x*y)")), "sqrt(x*y)"],
    ["separatevars(P(\"sqrt(x*y)\"), { force: true })", () => separatevars(P("sqrt(x*y)"), { force: true }), "sqrt(x)*sqrt(y)"],
    ["separatevars(Qs(\"x + x*n\", [symbol(\"n\", { commutative: false })]))", () => separatevars(Qs("x + x*n", [symbol("n", { commutative: false })])), "x*(1 + n)"],
    ["separatevars(P(\"x*f(x) + f(x)\"))", () => separatevars(P("x*f(x) + f(x)")), "x*f(x) + f(x)"],
    ["separatevars(P(\"x*exp(x) + x*exp(x + y)\"))", () => separatevars(P("x*exp(x) + x*exp(x + y)")), "x*(exp(y) + 1)*exp(x)"],
    ["separatevars(P(\"log(x)*log(y) + log(x) + log(y) + 1\"))", () => separatevars(P("log(x)*log(y) + log(x) + log(y) + 1")), "(log(x) + 1)*(log(y) + 1)"],
    ["separatevars(P(\"-x*exp(y)*log(z) + x*exp(y) - x*log(z) + x - exp(y)*log(z) + exp(y) - log(z) + 1\"))", () => separatevars(P("-x*exp(y)*log(z) + x*exp(y) - x*log(z) + x - exp(y)*log(z) + exp(y) - log(z) + 1")), "-(x + 1)*(exp(y) + 1)*(log(z) - 1)"],
    ["separatevars(Qs(\"log(x**log(y)) + log(x*y) + 1\", [symbol(\"x\", { positive: true }), symbol(\"y\", { positive: true })]))", () => separatevars(Qs("log(x**log(y)) + log(x*y) + 1", [symbol("x", { positive: true }), symbol("y", { positive: true })])), "(log(x) + 1)*(log(y) + 1)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["separatevars(P('x*y/(x + y + 3) + x/(x + y + 3) + y/(x + y + 3) + 1/(x + y + 3)'))", () => separatevars(PA('x*y/(x + y + 3) + x/(x + y + 3) + y/(x + y + 3) + 1/(x + y + 3)')), "(x + 1)*(y + 1)/(x + y + 3)"],
    ["separatevars(P('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)'))", () => separatevars(PA('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)')), "z*(x + 1)*(y + 1)/(x + y + 3)"],
    ["separatevars(P('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)'), { force: true })", () => separatevars(PA('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)'), { force: true }), "z*(x + 1)*(y + 1)/(x + y + 3)"],
    ["separatevars(P('(2*x + 2)*y'), { dict: true, symbols: [] })", () => separatevars(PA('(2*x + 2)*y'), { dict: true, symbols: [] }), "{coeff: 1, x: 2*x + 2, y: y}"],
    ["separatevars(P('2*x + y'), { dict: true })", () => separatevars(PA('2*x + y'), { dict: true }), "NoMatch"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});
