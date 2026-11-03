// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/gammasimp.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Sym, combsimp, gammasimp, hypersimilar, hypersimp, isHypergeometric, parse, sstr, symbol, symbols } from '../../src';
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

describe('combsimp and gammasimp: the calls of SymPy 1.14 test_combsimp.py and test_gammasimp.py', () => {
  const cases: ['combsimp' | 'gammasimp', string, Record<string, Assume>, string][] = [
    ['combsimp', 'factorial(n)', {n: {integer: true}}, 'factorial(n)'],
    ['combsimp', 'binomial(n, k)', {k: {integer: true}, n: {integer: true}}, 'binomial(n, k)'],
    ['combsimp', 'factorial(n)/factorial(n - 3)', {n: {integer: true}}, 'n*(n - 2)*(n - 1)'],
    ['combsimp', 'binomial(n + 1, k + 1)/binomial(n, k)', {k: {integer: true}, n: {integer: true}}, '(n + 1)/(k + 1)'],
    ['combsimp', 'binomial(3*n + 4, n + 1)/binomial(3*n + 1, n)', {n: {integer: true}}, '3*(3*n + 2)*(3*n + 4)/(2*(n + 1)*(2*n + 3))'],
    ['combsimp', 'factorial(n)**2/factorial(n - 3)', {n: {integer: true}}, 'n*(n - 2)*(n - 1)*factorial(n)'],
    ['combsimp', 'binomial(n + 1, k + 1)*factorial(n)/binomial(n, k)', {k: {integer: true}, n: {integer: true}}, 'factorial(n + 1)/(k + 1)'],
    ['combsimp', 'gamma(n + 3)', {n: {integer: true}}, 'factorial(n + 2)'],
    ['combsimp', 'factorial(x)', {}, 'gamma(x + 1)'],
    ['combsimp', '(n + 1)*factorial(n)', {n: {integer: true}}, 'factorial(n + 1)'],
    ['combsimp', 'factorial(n)/n', {n: {integer: true}}, 'factorial(n - 1)'],
    ['combsimp', 'binomial(n, -k + n)', {k: {integer: true}, n: {integer: true}}, 'binomial(n, k)'],
    ['combsimp', 'factorial(n)/(factorial(k)*factorial(-k + n))', {k: {integer: true}, n: {integer: true}}, 'binomial(n, k)'],
    ['combsimp', 'factorial(k)*factorial(-k + n)/factorial(n)', {k: {integer: true}, n: {integer: true}}, '1/binomial(n, k)'],
    ['combsimp', 'factorial(2*n)/factorial(n)**2', {n: {integer: true}}, 'binomial(2*n, n)'],
    ['combsimp', 'factorial(k)*factorial(2*n)*factorial(-k + n)/factorial(n)**3', {k: {integer: true}, n: {integer: true}}, 'binomial(2*n, n)/binomial(n, k)'],
    ['combsimp', 'factorial(-n**2 + n*(n + 1) - n)', {n: {integer: true}}, '1'],
    ['combsimp', '6*FallingFactorial(-4, n)/factorial(n)', {n: {integer: true}}, '(-1)**n*(n + 1)*(n + 2)*(n + 3)'],
    ['combsimp', '6*FallingFactorial(-4, n - 1)/factorial(n - 1)', {n: {integer: true}}, '(-1)**(n - 1)*n*(n + 1)*(n + 2)'],
    ['combsimp', '6*FallingFactorial(-4, n - 3)/factorial(n - 3)', {n: {integer: true}}, '(-1)**(n - 3)*n*(n - 2)*(n - 1)'],
    ['combsimp', '6*FallingFactorial(-4, -n - 1)/factorial(-n - 1)', {n: {integer: true}}, '-(-1)**(-n - 1)*n*(n - 2)*(n - 1)'],
    ['combsimp', '6*RisingFactorial(4, n)/factorial(n)', {n: {integer: true}}, '(n + 1)*(n + 2)*(n + 3)'],
    ['combsimp', '6*RisingFactorial(4, n - 1)/factorial(n - 1)', {n: {integer: true}}, 'n*(n + 1)*(n + 2)'],
    ['combsimp', '6*RisingFactorial(4, n - 3)/factorial(n - 3)', {n: {integer: true}}, 'n*(n - 2)*(n - 1)'],
    ['combsimp', '6*RisingFactorial(4, -n - 1)/factorial(-n - 1)', {n: {integer: true}}, '-n*(n - 2)*(n - 1)'],
    ['combsimp', 'binomial(1, p)', {p: {integer: true, positive: true}}, '1/(factorial(p)*factorial(1 - p))'],
    ['combsimp', 'factorial(2 - p)', {p: {integer: true, positive: true}}, 'factorial(2 - p)'],
    ['combsimp', 'RisingFactorial(-10, n)', {n: {integer: true}}, '3628800*(-1)**n/factorial(10 - n)'],
    ['gammasimp', 'gamma(x)', {}, 'gamma(x)'],
    ['gammasimp', 'gamma(x + 1)/x', {}, 'gamma(x)'],
    ['gammasimp', 'gamma(x)/(x - 1)', {}, 'gamma(x - 1)'],
    ['gammasimp', 'x*gamma(x)', {}, 'gamma(x + 1)'],
    ['gammasimp', '(x + 1)*gamma(x + 1)', {}, 'gamma(x + 2)'],
    ['gammasimp', '(x + y)*gamma(x + y)', {}, 'gamma(x + y + 1)'],
    ['gammasimp', 'x/gamma(x + 1)', {}, '1/gamma(x)'],
    ['gammasimp', '(x + 1)**2/gamma(x + 2)', {}, '(x + 1)/gamma(x + 1)'],
    ['gammasimp', 'x*gamma(x) + gamma(x + 3)/(x + 2)', {}, '(x + 2)*gamma(x + 1)'],
    ['gammasimp', 'x*gamma(2*x)', {}, 'gamma(2*x + 1)/2'],
    ['gammasimp', 'gamma(2*x)/(x - 1/2)', {}, '2*gamma(2*x - 1)'],
    ['gammasimp', 'gamma(x)*gamma(1 - x)', {}, 'pi/sin(pi*x)'],
    ['gammasimp', 'gamma(-x)*gamma(x)', {}, '-pi/(x*sin(pi*x))'],
    ['gammasimp', '1/(gamma(1 - x)*gamma(x + 3))', {}, 'sin(pi*x)/(pi*x*(x + 1)*(x + 2))'],
    ['gammasimp', 'factorial(n + 2)', {}, 'gamma(n + 3)'],
    ['gammasimp', 'binomial(n, k)', {}, 'gamma(n + 1)/(gamma(k + 1)*gamma(-k + n + 1))'],
    ['gammasimp', 'gamma(x)*gamma(y)*gamma(x + 1/2)/gamma(x + y)', {}, '2*sqrt(2)*2**(-2*x - 1/2)*sqrt(pi)*gamma(2*x)*gamma(y)/gamma(x + y)'],
    ['gammasimp', '1/(gamma(x)*gamma(x - 1/3)*gamma(x + 1/3))', {}, '3**(3*x - 3/2)/(2*pi*gamma(3*x - 1))'],
    ['gammasimp', 'gamma(-3/4)*gamma(-1/4)', {}, '16*sqrt(2)*pi/3'],
    ['gammasimp', 'gamma(2*x)/gamma(x)', {}, '2**(2*x + 1)*gamma(x + 1/2)/(4*sqrt(pi))'],
    ['gammasimp', '(-gamma(k)*gamma(k + 2) + gamma(k + 1)**2)/gamma(k)**2', {}, '-k'],
    ['gammasimp', 'gamma(k)**2/(-gamma(k)*gamma(k + 2) + gamma(k + 1)**2)', {}, '-1/k'],
    ['gammasimp', '(gamma(x) + gamma(x + 1))/gamma(x)', {}, 'x + 1'],
    ['gammasimp', 'gamma(x)/(gamma(x) + gamma(x + 1))', {}, '1/(x + 1)'],
    ['gammasimp', '(gamma(x) + gamma(x - 1))*(gamma(x) + gamma(x + 2))/gamma(x)', {}, '(x**2 + x + 1)*gamma(x + 1)/(x - 1)'],
    ['gammasimp', '(-gamma(k)*gamma(k + 2) + gamma(k + 1)**2)**2/gamma(k)**4', {}, 'k**2'],
    ['gammasimp', '(-gamma(k)*gamma(k + 2) + gamma(k + 1)**2)**2/(gamma(k)**4*gamma(k + 1))', {}, 'k/gamma(k)'],
    ['gammasimp', 'gamma(2*k)*gamma(k + 5/6)*gamma(k + 7/6)/gamma(k)', {}, '3*2**(2*k + 1)*3**(-3*k - 2)*sqrt(pi)*gamma(3*k + 3/2)/2'],
    ['gammasimp', '(x + 1)*factorial(x)/gamma(y)', {}, 'gamma(x + 2)/gamma(y)'],
    ['gammasimp', '(-gamma(k)*gamma(k + 2) + gamma(k + 1)**2)*B*A/gamma(k)**2', {A: {commutative: false}, B: {commutative: false}}, '-k*B*A'],
    ['gammasimp', 'gamma(2*k)*gamma(-k - 1/2)/gamma(k)', {}, '-2**(2*k + 1)*sqrt(pi)/(2*(2*k + 1)*cos(pi*k))'],
    ['gammasimp', 'gamma(k)*gamma(k + 1/3)*gamma(k + 2/3)/gamma(3*k/2)', {}, '3*2**(3*k + 1)*3**(-3*k - 1/2)*sqrt(pi)*gamma(3*k/2 + 1/2)/2'],
    ['gammasimp', 'gamma(1/4)/gamma(5/4)', {}, '4'],
    ['gammasimp', 'binomial(n + 2, k + 1/2)', {}, 'gamma(n + 3)/(gamma(k + 3/2)*gamma(-k + n + 5/2))'],
    ['gammasimp', 'binomial(n + 2, k + 2.0)', {}, 'gamma(n + 3)/(gamma(k + 3.0)*gamma(-k + n + 1))'],
    ['gammasimp', 'binomial(0, x)', {}, 'sin(pi*x)/(pi*x)'],
    ['gammasimp', 'gamma(n + 1/3)*gamma(n + 2/3)', {}, 'gamma(n + 1/3)*gamma(n + 2/3)'],
    ['gammasimp', 'gamma(4*n + 1/2)/gamma(2*n - 3/4)', {}, '2**(4*n - 5/2)*(8*n - 3)*gamma(2*n + 3/4)/sqrt(pi)'],
    ['gammasimp', 'gamma(exp(i))', {i: {integer: true}}, 'gamma(exp(i))'],
    ['gammasimp', 'gamma(m + 3)', {m: {integer: true}}, 'gamma(m + 3)'],
    ['gammasimp', 'gamma(m + 1)/(gamma(i + 1)*gamma(-i + m + 1))', {i: {integer: true}, m: {integer: true}}, 'gamma(m + 1)/(gamma(i + 1)*gamma(-i + m + 1))'],
    ['gammasimp', 'gamma(4 - p)', {p: {integer: true, positive: true}}, 'gamma(4 - p)'],
    ['gammasimp', 'x + gamma(y)', {}, '(x*y + gamma(y + 1))/y'],
    ['gammasimp', 'f(x) + gamma(y)', {}, '(y*f(x) + gamma(y + 1))/y'],
    ['gammasimp', 'cos(x) + gamma(y)', {}, '(y*cos(x) + gamma(y + 1))/y'],
    ['gammasimp', '1/(x + gamma(y))', {}, 'y/(x*y + gamma(y + 1))'],
    ['gammasimp', 'f(x + gamma(y))', {}, 'f((x*y + gamma(y + 1))/y)'],
  ];
  it.each(cases)('%s(%s)', (f, src, a, want) => {
    expect(sstr((f === 'combsimp' ? combsimp : gammasimp)(PA(src, a)))).toBe(want);
  });
  it('gammasimp(rf(n + x, k)*binomial(n, k)) keeps the Piecewise of rf', () => {
    // SymPy prints the Piecewise factor first; the printed order of the factors differs, the expression is the same
    const want = 'Piecewise((gamma(k + n + x)/gamma(n + x), n + x > 0), ((-1)**k*gamma(-n - x + 1)/gamma(-k - n - x + 1), True))*gamma(n + 1)/(gamma(k + 1)*gamma(-k + n + 1))';
    expect(gammasimp(PA('RisingFactorial(n + x, k)*binomial(n, k)')).key).toBe(PA(want).key);
  });
});

describe('combsimp and gammasimp: further SymPy 1.14 cases', () => {
  const I = { n: { integer: true }, k: { integer: true }, m: { integer: true } };
  const cases: ['combsimp' | 'gammasimp', string, string][] = [
    ['gammasimp', 'beta(x, y)', 'gamma(x)*gamma(y)/gamma(x + y)'],
    ['combsimp', 'ff(n, k)', 'factorial(n)/factorial(-k + n)'],
    ['combsimp', 'Piecewise((factorial(n)/factorial(n - 1), n > 0), (1, True))', 'Piecewise((n, n > 0), (1, True))'],
    // a repeated coefficient and a run of two among the coefficients 0, 1/3, 1/2
    ['gammasimp', 'gamma(x)**2*gamma(x + 1/2)', '2*sqrt(2)*2**(-2*x - 1/2)*sqrt(pi)*gamma(x)*gamma(2*x)'],
    ['gammasimp', 'gamma(x)*gamma(x + 1/2)*gamma(x + 1/3)', '2*sqrt(2)*2**(-2*x - 1/2)*sqrt(pi)*gamma(2*x)*gamma(x + 1/3)'],
    // absorption of factors with equal functional components, and of factors without free symbols
    ['gammasimp', 'sqrt(x)*gamma(sqrt(x))', 'gamma(sqrt(x) + 1)'],
    ['gammasimp', 'x*gamma(pi)', 'x*gamma(1 + pi)/pi'],
    ['gammasimp', 'pi*gamma(pi)', 'gamma(1 + pi)'],
    // cos(t) has the bound symbol t, so it is not masked
    ['gammasimp', 'Integral(cos(t)*gamma(t)*t, (t, 0, 1)) + cos(y)*gamma(y)', '(y*Integral(cos(t)*gamma(t + 1), (t, 0, 1)) + cos(y)*gamma(y + 1))/y'],
    ['combsimp', 'factorial(n)/factorial(k)', 'factorial(n)/factorial(k)'],
    ['combsimp', 'factorial(n)**2/(factorial(k)**2*factorial(n - k)**2)', 'binomial(n, k)**2'],
    ['combsimp', 'factorial(n)/(factorial(k)*factorial(n - k)*factorial(m))', 'binomial(n, k)/factorial(m)'],
    // runs: 1/3 is not a run (3/2 is not an integer multiple of 1/3) but 1/2 is; 1/3 and 4/3 give the same difference
    ['gammasimp', 'gamma(x + 1)*gamma(x + 4/3)*gamma(x + 3/2)', 'sqrt(2)*2**(-2*x - 3/2)*sqrt(pi)*gamma(x + 4/3)*gamma(2*x + 2)'],
    ['gammasimp', 'gamma(x + 1)*gamma(x + 4/3)*gamma(x + 7/3)', 'gamma(x + 1)*gamma(x + 4/3)*gamma(x + 7/3)'],
    ['gammasimp', 'gamma(sqrt(x))/(sqrt(x) - 1)', 'gamma(sqrt(x) - 1)'],
    ['combsimp', 'factorial(n)*factorial(m)/(factorial(k)*factorial(n - k))', 'binomial(n, k)*factorial(m)'],
    // sums of gamma terms in the numerator and the denominator
    ['gammasimp', '(gamma(x) + 1)*(gamma(x + 1) + 2)/(gamma(x)*gamma(y))', '(x*gamma(x) + 2)*(gamma(x) + 1)/(gamma(x)*gamma(y))'],
    ['gammasimp', '(gamma(x) + x)*(gamma(y) + y)/(gamma(x + 1)*gamma(y + 1))', '(x + gamma(x))*(gamma(y)**2 + gamma(y + 1))/(gamma(y)*gamma(x + 1)*gamma(y + 1))'],
    ['gammasimp', 'gamma(x + 2)*gamma(y) + gamma(x + 1)**2', '(x*gamma(y + 1) + y*gamma(x + 1) + gamma(y + 1))*gamma(x + 1)/y'],
    // SymPy raises AttributeError ('Float' object has no attribute 'p') in the multiplication theorem;
    // symjs keeps a Float shift in the argument, and the product is left as it is
    ['gammasimp', 'gamma(x + 1.5)*gamma(x + 2)', 'gamma(x + 1.5)*gamma(x + 2)'],
  ];
  it.each(cases)('%s(%s)', (f, src, want) => {
    expect(sstr((f === 'combsimp' ? combsimp : gammasimp)(PA(src, I)))).toBe(want);
  });
  it('hypersimp and isHypergeometric of factorial(n)', () => {
    const n = PA('n', I);
    expect(String(hypersimp(PA('factorial(n)', I), n))).toBe('n + 1');
    expect(isHypergeometric(PA('factorial(n)', I), n)).toBe(true);
  });
});
