// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/gammasimp.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Sym, combsimp, gammasimp, hypersimilar, hypersimp, parse, sstr, symbol, symbols } from '../../src';
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

describe('gammasimp and combsimp', () => {
  const n = symbols('n', { integer: true })[0];
  it('combine integer shifts', () => {
    expect(sstr(gammasimp(parse('gamma(x + 3)/gamma(x + 1)')))).toBe('(x + 1)*(x + 2)');
    expect(sstr(gammasimp(parse('gamma(x + 1)/gamma(x)/x')))).toBe('1');
    expect(sstr(combsimp(parse('factorial(n + 2)/factorial(n)', { symbols: { n } } as never)))).toBe('(n + 1)*(n + 2)');
    expect(sstr(combsimp(parse('binomial(n + 1, 2)/binomial(n, 2)', { symbols: { n } } as never)))).toBe('(n + 1)/(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)/factorial(n - 3)', { symbols: { n } } as never)))).toBe('n*(n - 2)*(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)*factorial(n + 1)', { symbols: { n } } as never)))).toBe('factorial(n)*factorial(n + 1)');
  });
});

describe("simplify functions: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["gammasimp(P(\"gamma(x)\"))", () => gammasimp(P("gamma(x)")), "gamma(x)"],
    ["gammasimp(P(\"gamma(x)*gamma(1 - x)\"))", () => gammasimp(P("gamma(x)*gamma(1 - x)")), "pi/sin(pi*x)"],
    ["gammasimp(P(\"gamma(-x)*gamma(x)\"))", () => gammasimp(P("gamma(-x)*gamma(x)")), "-pi/(x*sin(pi*x))"],
    ["gammasimp(P(\"factorial(n + 2)\"))", () => gammasimp(P("factorial(n + 2)")), "gamma(n + 3)"],
    ["gammasimp(P(\"binomial(n, k)\"))", () => gammasimp(P("binomial(n, k)")), "gamma(n + 1)/(gamma(k + 1)*gamma(-k + n + 1))"],
    ["gammasimp(P(\"gamma(-3/4)*gamma(-1/4)\"))", () => gammasimp(P("gamma(-3/4)*gamma(-1/4)")), "16*sqrt(2)*pi/3"],
    ["gammasimp(P(\"gamma(1/4)/gamma(5/4)\"))", () => gammasimp(P("gamma(1/4)/gamma(5/4)")), "4"],
    ["gammasimp(P(\"binomial(n + 2, k + 1/2)\"))", () => gammasimp(P("binomial(n + 2, k + 1/2)")), "gamma(n + 3)/(gamma(k + 3/2)*gamma(-k + n + 5/2))"],
    ["gammasimp(P(\"binomial(0, x)\"))", () => gammasimp(P("binomial(0, x)")), "sin(pi*x)/(pi*x)"],
    ["gammasimp(P(\"gamma(n + 1/3)*gamma(n + 2/3)\"))", () => gammasimp(P("gamma(n + 1/3)*gamma(n + 2/3)")), "gamma(n + 1/3)*gamma(n + 2/3)"],
    ["gammasimp(Qs(\"gamma(exp(i))\", [symbol(\"i\", { integer: true })]))", () => gammasimp(Qs("gamma(exp(i))", [symbol("i", { integer: true })])), "gamma(exp(i))"],
    ["gammasimp(Qs(\"gamma(m + 3)\", [symbol(\"m\", { integer: true })]))", () => gammasimp(Qs("gamma(m + 3)", [symbol("m", { integer: true })])), "gamma(m + 3)"],
    ["gammasimp(Qs(\"gamma(m + 1)/(gamma(i + 1)*gamma(-i + m + 1))\", [symbol(\"m\", { integer: true }), symbol(\"i\", { integer: true })]))", () => gammasimp(Qs("gamma(m + 1)/(gamma(i + 1)*gamma(-i + m + 1))", [symbol("m", { integer: true }), symbol("i", { integer: true })])), "gamma(m + 1)/(gamma(i + 1)*gamma(-i + m + 1))"],
    ["gammasimp(Qs(\"gamma(4 - p)\", [symbol(\"p\", { integer: true, positive: true })]))", () => gammasimp(Qs("gamma(4 - p)", [symbol("p", { integer: true, positive: true })])), "gamma(4 - p)"],
    ["combsimp(Qs(\"factorial(n)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("factorial(n)", [symbol("n", { integer: true })])), "factorial(n)"],
    ["combsimp(Qs(\"binomial(n, k)\", [symbol(\"n\", { integer: true }), symbol(\"k\", { integer: true })]))", () => combsimp(Qs("binomial(n, k)", [symbol("n", { integer: true }), symbol("k", { integer: true })])), "binomial(n, k)"],
    ["combsimp(Qs(\"factorial(n)/factorial(n - 3)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("factorial(n)/factorial(n - 3)", [symbol("n", { integer: true })])), "n*(n - 2)*(n - 1)"],
    ["combsimp(Qs(\"binomial(n + 1, k + 1)/binomial(n, k)\", [symbol(\"n\", { integer: true }), symbol(\"k\", { integer: true })]))", () => combsimp(Qs("binomial(n + 1, k + 1)/binomial(n, k)", [symbol("n", { integer: true }), symbol("k", { integer: true })])), "(n + 1)/(k + 1)"],
    ["combsimp(Qs(\"binomial(3*n + 4, n + 1)/binomial(3*n + 1, n)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("binomial(3*n + 4, n + 1)/binomial(3*n + 1, n)", [symbol("n", { integer: true })])), "3*(3*n + 2)*(3*n + 4)/(2*(n + 1)*(2*n + 3))"],
    ["combsimp(Qs(\"binomial(n + 1, k + 1)*factorial(n)/binomial(n, k)\", [symbol(\"n\", { integer: true }), symbol(\"k\", { integer: true })]))", () => combsimp(Qs("binomial(n + 1, k + 1)*factorial(n)/binomial(n, k)", [symbol("n", { integer: true }), symbol("k", { integer: true })])), "factorial(n + 1)/(k + 1)"],
    ["combsimp(Qs(\"6*FallingFactorial(-4, n)/factorial(n)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*FallingFactorial(-4, n)/factorial(n)", [symbol("n", { integer: true })])), "(-1)**n*(n + 1)*(n + 2)*(n + 3)"],
    ["combsimp(Qs(\"6*FallingFactorial(-4, n - 1)/factorial(n - 1)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*FallingFactorial(-4, n - 1)/factorial(n - 1)", [symbol("n", { integer: true })])), "(-1)**(n - 1)*n*(n + 1)*(n + 2)"],
    ["combsimp(Qs(\"6*FallingFactorial(-4, n - 3)/factorial(n - 3)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*FallingFactorial(-4, n - 3)/factorial(n - 3)", [symbol("n", { integer: true })])), "(-1)**(n - 3)*n*(n - 2)*(n - 1)"],
    ["combsimp(Qs(\"6*FallingFactorial(-4, -n - 1)/factorial(-n - 1)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*FallingFactorial(-4, -n - 1)/factorial(-n - 1)", [symbol("n", { integer: true })])), "-(-1)**(-n - 1)*n*(n - 2)*(n - 1)"],
    ["combsimp(Qs(\"6*RisingFactorial(4, n)/factorial(n)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*RisingFactorial(4, n)/factorial(n)", [symbol("n", { integer: true })])), "(n + 1)*(n + 2)*(n + 3)"],
    ["combsimp(Qs(\"6*RisingFactorial(4, n - 1)/factorial(n - 1)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*RisingFactorial(4, n - 1)/factorial(n - 1)", [symbol("n", { integer: true })])), "n*(n + 1)*(n + 2)"],
    ["combsimp(Qs(\"6*RisingFactorial(4, n - 3)/factorial(n - 3)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*RisingFactorial(4, n - 3)/factorial(n - 3)", [symbol("n", { integer: true })])), "n*(n - 2)*(n - 1)"],
    ["combsimp(Qs(\"6*RisingFactorial(4, -n - 1)/factorial(-n - 1)\", [symbol(\"n\", { integer: true })]))", () => combsimp(Qs("6*RisingFactorial(4, -n - 1)/factorial(-n - 1)", [symbol("n", { integer: true })])), "-n*(n - 2)*(n - 1)"],
    ["combsimp(Qs(\"factorial(2 - p)\", [symbol(\"p\", { integer: true, positive: true })]))", () => combsimp(Qs("factorial(2 - p)", [symbol("p", { integer: true, positive: true })])), "factorial(2 - p)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("ratsimpmodprime, gammasimp, signsimp, cancel, ratsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["gammasimp(P('ff(p, k)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(PA('ff(p, k)', {p: {positive: true}, n: {negative: true}})), "gamma(p + 1)/gamma(-k + p + 1)"],
    ["gammasimp(P('ff(n, k)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(PA('ff(n, k)', {p: {positive: true}, n: {negative: true}})), "(-1)**k*gamma(k - n)/gamma(-n)"],
    ["gammasimp(P('ff(-3, k)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(PA('ff(-3, k)', {p: {positive: true}, n: {negative: true}})), "(-1)**k*gamma(k + 3)/2"],
    ["gammasimp(P('gamma(x)*gamma(x + 1)/gamma(x + 2)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(PA('gamma(x)*gamma(x + 1)/gamma(x + 2)', {p: {positive: true}, n: {negative: true}})), "gamma(x)/(x + 1)"],
    ["gammasimp(P('gamma(x + 2)/(gamma(x)*x)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(PA('gamma(x + 2)/(gamma(x)*x)', {p: {positive: true}, n: {negative: true}})), "x + 1"],
    // symjs factor raises for this noncommutative sum; gammasimp and combsimp then keep it, as SymPy does
    ["gammasimp(P('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}}))", () => gammasimp(PA('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}})), "x*A + A*B - B*A"],
    // symjs factor raises for this noncommutative sum; gammasimp and combsimp then keep it, as SymPy does
    ["combsimp(P('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}}))", () => combsimp(PA('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}})), "x*A + A*B - B*A"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('hypersimp and hypersimilar (cov2): a term index that is not a symbol', () => {
  const fx = PA('f(x)');
  it.each([
    ['factorial(f(x))', 'f(x) + 1'],
  ])('hypersimp(%s, f(x)) = %s', (src, want) => {
    expect(String(hypersimp(PA(src), fx))).toBe(want);
  });
  it('is NoMatch for a term ratio that is not rational (SymPy: None)', () => {
    expect(String(hypersimp(PA('2**(f(x)**2)'), fx))).toBe('NoMatch');
  });
  it('hypersimilar(factorial(f(x)), factorial(f(x) + 1), f(x)) is true', () => {
    expect(hypersimilar(PA('factorial(f(x))'), PA('factorial(f(x) + 1)'), fx)).toBe(true);
  });
});
