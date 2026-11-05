// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/radsimp.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { Wild, add, collect, dsolve, factor, mul, parse, pow, rcollect, sstr, symbol, symbols } from '../../src';
import type { Expr } from '../../src';

const Pplain = parse;
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
const [x, y, n, k, z, a, b] = symbols('x y n k z a b');
const r = symbol('r', { real: true });
const p = symbol('p', { positive: true });
const kk = symbol('kk', { integer: true });
const P = (s: string) => parse(s, { symbols: [x, y, n, k, r, p, kk, z, a, b] });
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe('rcollect, hypersimilar, number theory and matrix helpers', () => {
  it('match SymPy', async () => {
    const { rcollect, hypersimilar, legendreSymbol, motzkin, andre, Matrix, rrefRhs, rankDecomposition, invMod, permuteRows } = await import('../../src');
    const [x, y] = symbols('x y');
    expect(sstr(rcollect(parse('(x**2*y + x*y + x + y)/(x + y)'), y))).toBe('(x + y*(x**2 + x + 1))/(x + y)');
    const k = symbols('k')[0];
    expect(hypersimilar(parse('factorial(k)', { symbols: { k } } as never), parse('factorial(k + 1)', { symbols: { k } } as never), k)).toBe(true);
    expect([legendreSymbol(3, 7), legendreSymbol(2, 7)]).toEqual([-1, 1]);
    expect([2, 3, 6].map((n) => motzkin(n))).toEqual([1n, 2n, 21n]);
    expect([0, 1, 2, 3, 4, 5, 6, 7].map((n) => andre(n))).toEqual([1n, 1n, 1n, 2n, 5n, 16n, 61n, 272n]);
    const M = Matrix.of([[1, 2], [3, 4]]);
    expect(rrefRhs(M, Matrix.col(5, 6)).map(String)).toEqual(['Matrix([[1, 0], [0, 1]])', 'Matrix([[-4], [9/2]])']);
    expect(rankDecomposition(M).map(String)).toEqual(['Matrix([[1, 2], [3, 4]])', 'Matrix([[1, 0], [0, 1]])']);
    expect(String(invMod(M, 5))).toBe('Matrix([[3, 1], [4, 2]])');
    expect(String(permuteRows(M, [1, 0]))).toBe('Matrix([[3, 4], [1, 2]])');
    void x;
  });
});

describe('collect exact=None/func, deep factor with exponentials, radical content in cancel', () => {
  it('match SymPy', async () => {
    const { collect, factor, cancel, Symbol: Sym } = await import('../../src');
    const [x, y, a, b] = symbols('x y a b');
    const P = (s: string) => parse(s, { symbols: { x, y, a, b } } as never);
    expect(sstr(collect(P('x*exp(x) + sin(x)*y + sin(x)*2 + 3*x'), [x], { exact: null }))).toBe('x*exp(x) + 3*x + (y + 2)*sin(x)');
    expect(sstr(collect(P('a*x*y + x*y + b*x + x'), [x, y], { exact: null }))).toBe('x*y*(a + 1) + x*(b + 1)');
    expect(sstr(collect(P('expand((x + a + 1)**3)').subs([]) as never, [x]))).toBeTruthy();
    expect(sstr(factor(P('5*x + 3*exp(2 - 7*x)'), { deep: true }))).toBe('(5*x*exp(7*x) + 3*exp(2))*exp(-7*x)');
    expect(sstr(factor(P('5*x + 3*exp(2 - 7*x)'), { deep: true, fraction: false }))).toBe('5*x + 3*exp(2)*exp(-7*x)');
    expect(sstr(factor(P('exp(x)+exp(-x)'), { deep: true }))).toBe('(exp(2*x) + 1)*exp(-x)');
    const A = new Sym('A', { commutative: false });
    expect(sstr(cancel(parse('(sqrt(3) + sqrt(15)*A)/(sqrt(2) + sqrt(10)*A)', { symbols: { A } } as never)))).toBe('sqrt(6)/2');
  });
});

describe("collect: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["collect(P('C1 + C2*x + C3*x**2'), P('x**2'))", () => collect(Pplain('C1 + C2*x + C3*x**2'), Pplain('x**2')), "C1 + C2*x + C3*x**2"],
    ["collect(P('x + x**3 + x**4*y'), P('x**2'))", () => collect(Pplain('x + x**3 + x**4*y'), Pplain('x**2')), "x**4*y + x**3 + x"],
    ["collect(P('x**4*y + x**4 + x*a + x'), P('x**2'))", () => collect(Pplain('x**4*y + x**4 + x*a + x'), Pplain('x**2')), "a*x + x**4*(y + 1) + x"],
    ["collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)'))", () => collect(Pplain('sqrt(x)*y + sqrt(x) + x*a + x'), Pplain('sqrt(x)')), "sqrt(x)*(y + 1) + x*(a + 1)"],
    ["collect(P('a*x**2 + b*x**2 + a*x - b*x'), x)", () => collect(Pplain('a*x**2 + b*x**2 + a*x - b*x'), x), "x**2*(a + b) + x*(a - b)"],
    ["collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y'))", () => collect(Pplain('a*2**(2*y) + b*2**(2*y) + 2**y'), Pplain('2**y')), "2**(2*y)*(a + b) + 2**y"],
    ["collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)'))", () => collect(Pplain('a*exp(2*x) + b*exp(2*x)'), Pplain('exp(x)')), "(a + b)*exp(2*x)"],
    ["dsolve(P('Derivative(f(x), x, 3) - x'), P('f(x)'))", () => dsolve(Pplain('Derivative(f(x), x, 3) - x'), Pplain('f(x)')), "Eq(f(x), C1 + C2*x + C3*x**2 + x**4/24)"],
    ["collect(P('x*a + x'), P('x**2'))", () => collect(Pplain('x*a + x'), Pplain('x**2')), "a*x + x"],
    ["collect(P('x**3*a + x**3'), P('x**2'))", () => collect(Pplain('x**3*a + x**3'), Pplain('x**2')), "a*x**3 + x**3"],
    ["collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)'))", () => collect(Pplain('x**(3/2)*a + x**(3/2)'), Pplain('sqrt(x)')), "x**(3/2)*(a + 1)"],
    ["collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2'))", () => collect(Pplain('a/x**2 + 1/x**2 + 1/x'), Pplain('x**2')), "1/x + (a + 1)/x**2"],
    ["(() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })()", () => (() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })(), "p**3*(a + 1) + p*(a + 1)"],
    ["collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)'))", () => collect(Pplain('a*2**(3*y) + 2**(3*y)'), Pplain('2**(2*y)')), "2**(3*y)*a + 2**(3*y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("collect: SymPy 1.14 test_radsimp cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["collect(1, P(\"x\"))", () => collect(1, P("x")), "1"],
    ["collect(P(\"x*y + x\"), P(\"x\"))", () => collect(P("x*y + x"), P("x")), "x*(y + 1)"],
    ["collect(P(\"x**2 + x\"), P(\"x\"))", () => collect(P("x**2 + x"), P("x")), "x**2 + x"],
    ["collect(P(\"x**2*y + x**2\"), P(\"x\"))", () => collect(P("x**2*y + x**2"), P("x")), "x**2*(y + 1)"],
    ["collect(P(\"x**2 + x*y\"), P(\"x\"))", () => collect(P("x**2 + x*y"), P("x")), "x**2 + x*y"],
    ["collect(P(\"x**2*y + 2*x**2 + 3*x*y\"), [P(\"x\")])", () => collect(P("x**2*y + 2*x**2 + 3*x*y"), [P("x")]), "x**2*(y + 2) + 3*x*y"],
    ["collect(P(\"x**2*y + 2*x**2 + 3*x*y\"), [P(\"y\")])", () => collect(P("x**2*y + 2*x**2 + 3*x*y"), [P("y")]), "2*x**2 + y*(x**2 + 3*x)"],
    ["collect(P(\"x**4 + 4*x**3*y + 4*x**3 + 6*x**2*y**2 + 12*x**2*y + 6*x**2 + 4*x*y**3 + 12*x*y**2 + 12*x*y + 4*x + y**4 + 4*y**3 + 6*y**2 + 4*y + 1\"), P(\"x\"))", () => collect(P("x**4 + 4*x**3*y + 4*x**3 + 6*x**2*y**2 + 12*x**2*y + 6*x**2 + 4*x*y**3 + 12*x*y**2 + 12*x*y + 4*x + y**4 + 4*y**3 + 6*y**2 + 4*y + 1"), P("x")), "x**4 + x**3*(4*y + 4) + x**2*(6*y**2 + 12*y + 6) + x*(4*y**3 + 12*y**2 + 12*y + 4) + y**4 + 4*y**3 + 6*y**2 + 4*y + 1"],
    ["collect(P(\"x*exp(x) + 3*x + y*sin(x) + 2*sin(x)\"), P(\"x\"), { exact: null })", () => collect(P("x*exp(x) + 3*x + y*sin(x) + 2*sin(x)"), P("x"), { exact: null }), "x*exp(x) + 3*x + (y + 2)*sin(x)"],
    ["collect(P(\"x*y*exp(x) + x*y + x*exp(x) + 3*x + y*sin(x) + 2*sin(x)\"), P(\"x\"), { exact: null })", () => collect(P("x*y*exp(x) + x*y + x*exp(x) + 3*x + y*sin(x) + 2*sin(x)"), P("x"), { exact: null }), "x*(y + 1)*exp(x) + x*(y + 3) + (y + 2)*sin(x)"],
    ["collect(P(\"a*(sin(x) + cos(x)) + b*(sin(x) + cos(x))\"), P(\"sin(x) + cos(x)\"))", () => collect(P("a*(sin(x) + cos(x)) + b*(sin(x) + cos(x))"), P("sin(x) + cos(x)")), "(a + b)*(sin(x) + cos(x))"],
    ["collect(P(\"x*y - x/8\"), P(\"-x\"))", () => collect(P("x*y - x/8"), P("-x")), "x*(y - 1/8)"],
    ["collect(P(\"x*y**2 + 1\"), P(\"x*y\"))", () => collect(P("x*y**2 + 1"), P("x*y")), "x*y**2 + 1"],
    ["collect(P(\"a*x*y + x*y\"), P(\"x*y\"))", () => collect(P("a*x*y + x*y"), P("x*y")), "x*y*(a + 1)"],
    ["collect(P(\"a*x*y + x*y + 1\"), P(\"x*y\"))", () => collect(P("a*x*y + x*y + 1"), P("x*y")), "x*y*(a + 1) + 1"],
    ["collect(P(\"a*x*f(x) + b*x*f(x)\"), P(\"x*f(x)\"))", () => collect(P("a*x*f(x) + b*x*f(x)"), P("x*f(x)")), "x*(a + b)*f(x)"],
    ["collect(P(\"a*x*log(x) + b*x*log(x)\"), P(\"x*log(x)\"))", () => collect(P("a*x*log(x) + b*x*log(x)"), P("x*log(x)")), "x*(a + b)*log(x)"],
    ["collect(P(\"a*x**2*log(x)**2 + b*x**2*log(x)**2\"), P(\"x*log(x)\"))", () => collect(P("a*x**2*log(x)**2 + b*x**2*log(x)**2"), P("x*log(x)")), "x**2*(a + b)*log(x)**2"],
    ["collect(P(\"a*x*y*z + x*y*z\"), P(\"x*y*z\"))", () => collect(P("a*x*y*z + x*y*z"), P("x*y*z")), "x*y*z*(a + 1)"],
    ["collect(P(\"a*x**c + b*x**c\"), P(\"x**c\"))", () => collect(P("a*x**c + b*x**c"), P("x**c")), "x**c*(a + b)"],
    ["collect(P(\"a*x**(2*c) + b*x**(2*c)\"), P(\"x**c\"))", () => collect(P("a*x**(2*c) + b*x**(2*c)"), P("x**c")), "x**(2*c)*(a + b)"],
    ["collect(P(\"a*z + x**2*y**4*z + x**2*y**4 + z\"), [P(\"x*y**2\"), P(\"z\")])", () => collect(P("a*z + x**2*y**4*z + x**2*y**4 + z"), [P("x*y**2"), P("z")]), "x**2*y**4*(z + 1) + z*(a + 1)"],
    ["collect(P(\"x**2 + 2*x*y + x + y**2 + y + 1\"), [P(\"x\"), P(\"y\")])", () => collect(P("x**2 + 2*x*y + x + y**2 + y + 1"), [P("x"), P("y")]), "x**2 + x*(2*y + 1) + y**2 + y + 1"],
    ["collect(P(\"a*Derivative(f(x), x) + b*Derivative(f(x), x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("a*Derivative(f(x), x) + b*Derivative(f(x), x)"), P("Derivative(f(x), x)")), "(a + b)*Derivative(f(x), x)"],
    ["collect(P(\"5*f(x) + 3*Derivative(f(x), x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("5*f(x) + 3*Derivative(f(x), x)"), P("Derivative(f(x), x)")), "5*f(x) + 3*Derivative(f(x), x)"],
    ["collect(P(\"x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)"), P("Derivative(f(x), x)")), "(x*f(x) + f(x))*Derivative(f(x), x) + f(x)"],
    ["collect(P(\"x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)\"), P(\"Derivative(f(x), x)\"), { exact: true })", () => collect(P("x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)"), P("Derivative(f(x), x)"), { exact: true }), "(x*f(x) + f(x))*Derivative(f(x), x) + f(x)"],
    ["collect(P(\"x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)\"), P(\"Derivative(f(x), x)\"), { exact: true })", () => collect(P("x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)"), P("Derivative(f(x), x)"), { exact: true }), "(x/f(x) + 1/f(x))*Derivative(f(x), x) + 1/f(x)"],
    ["collect(P(\"x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)\"), P(\"Derivative(f(x), x)\"))", () => collect(P("x*Derivative(f(x), x)/f(x) + Derivative(f(x), x)/f(x) + 1/f(x)"), P("Derivative(f(x), x)")), "(x/f(x) + 1/f(x))*Derivative(f(x), x) + 1/f(x)"],
    ["collect(P(\"a**3 + 3*a**2*x + 3*a**2 + 3*a*x**2 + 6*a*x + 3*a + x**3 + 3*x**2 + 3*x + 1\"), P(\"x\"))", () => collect(P("a**3 + 3*a**2*x + 3*a**2 + 3*a*x**2 + 6*a*x + 3*a + x**3 + 3*x**2 + 3*x + 1"), P("x")), "a**3 + 3*a**2 + 3*a + x**3 + x**2*(3*a + 3) + x*(3*a**2 + 6*a + 3) + 1"],
    ["collect(P(\"f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)\"), P(\"w_\"))", () => collect(P("f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"), P("w_")), "f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"],
    ["collect(P(\"x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)\"), P(\"f(x)\"))", () => collect(P("x*f(x)*Derivative(f(x), x) + f(x)*Derivative(f(x), x) + f(x)"), P("f(x)")), "(x*Derivative(f(x), x) + Derivative(f(x), x) + 1)*f(x)"],
    ["collect(P(\"f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)\"), [P(\"f(x)\"), P(\"Derivative(f(x), x)\")])", () => collect(P("f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"), [P("f(x)"), P("Derivative(f(x), x)")]), "(Derivative(f(x), x) + 1)*f(x) + Derivative(f(x), x)"],
    ["collect(P(\"f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)\"), [P(\"Derivative(f(x), x)\"), P(\"f(x)\")])", () => collect(P("f(x)*Derivative(f(x), x) + f(x) + Derivative(f(x), x)"), [P("Derivative(f(x), x)"), P("f(x)")]), "(f(x) + 1)*Derivative(f(x), x) + f(x)"],
    ["collect(P(\"exp(3*x/4)\"), P(\"exp(x)\"))", () => collect(P("exp(3*x/4)"), P("exp(x)")), "exp(3*x/4)"],
    ["collect(P(\"D**3*a/Re + aA**3*b/Re\"), [P(\"aA**3/Re\"), P(\"a\")])", () => collect(P("D**3*a/Re + aA**3*b/Re"), [P("aA**3/Re"), P("a")]), "D**3*a/Re + aA**3*b/Re"],
    ["collect(P('x + x**3 + x**4*y'), P('x**2'))", () => collect(P('x + x**3 + x**4*y'), P('x**2')), "x**4*y + x**3 + x"],
    ["collect(P('x**4*y + x**4 + x*a + x'), P('x**2'))", () => collect(P('x**4*y + x**4 + x*a + x'), P('x**2')), "a*x + x**4*(y + 1) + x"],
    ["collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)'))", () => collect(P('sqrt(x)*y + sqrt(x) + x*a + x'), P('sqrt(x)')), "sqrt(x)*(y + 1) + x*(a + 1)"],
    ["collect(P('a*x**2 + b*x**2 + a*x - b*x'), x)", () => collect(P('a*x**2 + b*x**2 + a*x - b*x'), x), "x**2*(a + b) + x*(a - b)"],
    ["collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y'))", () => collect(P('a*2**(2*y) + b*2**(2*y) + 2**y'), P('2**y')), "2**(2*y)*(a + b) + 2**y"],
    ["collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)'))", () => collect(P('a*exp(2*x) + b*exp(2*x)'), P('exp(x)')), "(a + b)*exp(2*x)"],
    ["collect(P('x*a + x'), P('x**2'))", () => collect(P('x*a + x'), P('x**2')), "a*x + x"],
    ["collect(P('x**3*a + x**3'), P('x**2'))", () => collect(P('x**3*a + x**3'), P('x**2')), "a*x**3 + x**3"],
    ["collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)'))", () => collect(P('x**(3/2)*a + x**(3/2)'), P('sqrt(x)')), "x**(3/2)*(a + 1)"],
    ["collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2'))", () => collect(P('a/x**2 + 1/x**2 + 1/x'), P('x**2')), "1/x + (a + 1)/x**2"],
    ["(() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })()", () => (() => { const p = symbol('p', { positive: true }); return collect(add(mul(a, p), p, mul(a, pow(p, 3)), pow(p, 3)), pow(p, 2)); })(), "p**3*(a + 1) + p*(a + 1)"],
    ["collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)'))", () => collect(P('a*2**(3*y) + 2**(3*y)'), P('2**(2*y)')), "2**(3*y)*a + 2**(3*y)"],
    ["collect(P('a*x*y + b*x*y + x'), P('x*y'))", () => collect(P('a*x*y + b*x*y + x'), P('x*y')), "x*y*(a + b) + x"],
    ["collect(P('a*x*y + b*x*y + x'), P('x*y'), { exact: true })", () => collect(P('a*x*y + b*x*y + x'), P('x*y'), { exact: true }), "x*y*(a + b) + x"],
    ["collect(P('a*x**2*y + b*x**2*y'), P('x*y'), { exact: true })", () => collect(P('a*x**2*y + b*x**2*y'), P('x*y'), { exact: true }), "x*y*(a*x + b*x)"],
    ["collect(P('a/x + b/x + x'), x)", () => collect(P('a/x + b/x + x'), x), "x + (a + b)/x"],
    ["collect(P('a*x**2*y + b*x**2*y + x*y'), P('x*y'))", () => collect(P('a*x**2*y + b*x**2*y + x*y'), P('x*y')), "x*y*(a*x + b*x + 1)"],
    ["collect(P('a*x + b*x + a*y + b*y'), [x, y], { exact: null })", () => collect(P('a*x + b*x + a*y + b*y'), [x, y], { exact: null }), "x*(a + b) + y*(a + b)"],
    ["collect(P('a*x*y + b*x*y + a*y + 2*y'), [x, y], { exact: null })", () => collect(P('a*x*y + b*x*y + a*y + 2*y'), [x, y], { exact: null }), "x*y*(a + b) + y*(a + 2)"],
    ["collect(P('a*x + b*x + c'), [x], { func: factor })", () => collect(P('a*x + b*x + c'), [x], { func: factor }), "c + x*(a + b)"],
    ["collect(P('a*x**2 + 2*a*x + a + x'), [x], { exact: null, func: factor })", () => collect(P('a*x**2 + 2*a*x + a + x'), [x], { exact: null, func: factor }), "a*x**2 + a + x*(2*a + 1)"],
    ["collect(P('a*x + b*x'), [])", () => collect(P('a*x + b*x'), []), "a*x + b*x"],
    ["rcollect(P('(x + a*x)*y + (x + b*x)/y'), x)", () => rcollect(P('(x + a*x)*y + (x + b*x)/y'), x), "x*(y*(a + 1) + (b + 1)/y)"],
    ["rcollect(P('sin(a*x + b*x)'), x)", () => rcollect(P('sin(a*x + b*x)'), x), "sin(x*(a + b))"],
    ["rcollect(P('a*x + b*x + y'), x, y)", () => rcollect(P('a*x + b*x + y'), x, y), "x*(a + b) + y"],
    ["rcollect(x, x)", () => rcollect(x, x), "x"],
    ["collect(P('a*x**2/y + b*x**2/y'), P('x*y'))", () => collect(P('a*x**2/y + b*x**2/y'), P('x*y')), "a*x**2/y + b*x**2/y"],
    ["collect(P('a*x**2*y**2 + b*x**2*y**2'), P('x*y'), { exact: true })", () => collect(P('a*x**2*y**2 + b*x**2*y**2'), P('x*y'), { exact: true }), "a*x**2*y**2 + b*x**2*y**2"],
    ["collect(P('a/(x*y) + b/(x*y)'), P('x*y'))", () => collect(P('a/(x*y) + b/(x*y)'), P('x*y')), "(a + b)/(x*y)"],
    ["collect(P('a*(x + 1)**y + (x + 1)**y'), pow(new Wild('w'), y))", () => collect(P('a*(x + 1)**y + (x + 1)**y'), pow(new Wild('w'), y)), "(a + 1)*(x + 1)**y"],
    ["collect(P('a*(x + 1)**y + b'), pow(new Wild('w'), z))", () => collect(P('a*(x + 1)**y + b'), pow(new Wild('w'), z)), "a*(x + 1)**y + b"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("ratsimpmodprime, gammasimp, signsimp, cancel, ratsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["collect(P('a*x'), P('x'), { exact: null })", () => collect(PA('a*x'), PA('x'), { exact: null }), "a*x"],
    ["collect(P('x**3*y**2 + 2*x**2*y**2'), P('x*y'))", () => collect(PA('x**3*y**2 + 2*x**2*y**2'), PA('x*y')), "x**2*y**2*(x + 2)"],
    ["collect(P('x**3*y**2 + 2*x**2*y**3'), P('x*y'))", () => collect(PA('x**3*y**2 + 2*x**2*y**3'), PA('x*y')), "x**2*y**2*(x + 2*y)"],
    ["collect(P('x**-3*y**-2 + 2*x**-2*y**-3'), P('x*y'))", () => collect(PA('x**-3*y**-2 + 2*x**-2*y**-3'), PA('x*y')), "(2/y + 1/x)/(x**2*y**2)"],
    ["collect(P('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), P('Derivative(f(x), x)'))", () => collect(PA('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), PA('Derivative(f(x), x)')), "(a + b)*Derivative(f(x), (x, 2))"],
    ["collect(P('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), P('f(x)'))", () => collect(PA('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), PA('f(x)')), "(a + b)*Derivative(f(x), (x, 2))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('collectAbs (SymPy collect_abs)', () => {
  it('collects the arguments of several Abs factors under one Abs', async () => {
    const { collectAbs } = await import('../../src/simplify/radsimp');
    const cases: [string, string][] = [
      // SymPy 1.14
      ['Abs(x + 1)/Abs(x**2 - 1)', 'Abs((x + 1)/(x**2 - 1))'],
      ['1/Abs(x)', 'Abs(1/x)'],
      ['Abs(x)*Abs(y)', 'Abs(x*y)'],
      ['Abs(x)**2*Abs(y)', 'Abs(x**2*y)'],
      ['y*Abs(x)', 'y*Abs(x)'],
      ['2*Abs(x)**2', '2*Abs(x)**2'],
      ['Abs(x)*Abs(x)**y', 'Abs(x)*Abs(x)**y'],
      ['Abs(x)*Abs(y) + 1', 'Abs(x*y) + 1'],
    ];
    for (const [e, want] of cases) expect(String(collectAbs(parse(e)))).toBe(want);
    expect(String(collectAbs(parse('1/(Abs(x)*Abs(y))')))).toBe('Abs(1/(x*y))');
    // noncommutative factors stay last, in their order
    const [A, B] = [symbol('A', { commutative: false }), symbol('B', { commutative: false })];
    expect(String(collectAbs(parse('Abs(x)*Abs(y)*B*A', { symbols: [A, B] })))).toBe('Abs(x*y)*B*A');
  });
});
