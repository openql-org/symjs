// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/exprtools.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { Sum, add, collectConst, factorTerms, float, gcdTerms, keepCoeffSympy, mul, parse, pow, signsimp, symbol, symbols, unevaluatedAdd } from '../../src';
import type { Expr } from '../../src';
import { decomposePower, gcdTermsOf } from '../../src/simplify/exprtools';

const [x, y, n, k, z, a, b] = symbols('x y n k z a b');
const r = symbol('r', { real: true });
const p = symbol('p', { positive: true });
const kk = symbol('kk', { integer: true });
const P = (s: string) => parse(s, { symbols: [x, y, n, k, r, p, kk, z, a, b] });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("exprtools: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["collectConst(P('sqrt(3) + sqrt(3)*sqrt(2)'))", () => collectConst(P('sqrt(3) + sqrt(3)*sqrt(2)')), "sqrt(3) + sqrt(6)"],
    ["collectConst(P('sqrt(3) + sqrt(3)*(1 + sqrt(2))'))", () => collectConst(P('sqrt(3) + sqrt(3)*(1 + sqrt(2))')), "sqrt(3)*(sqrt(2) + 2)"],
    ["collectConst(P('x*sqrt(2) + y*sqrt(2) + x*sqrt(3) + y*sqrt(3)'))", () => collectConst(P('x*sqrt(2) + y*sqrt(2) + x*sqrt(3) + y*sqrt(3)')), "(sqrt(2) + sqrt(3))*(x + y)"],
    ["collectConst(P('2*x + 2*y + 3*z'))", () => collectConst(P('2*x + 2*y + 3*z')), "3*z + 2*(x + y)"],
    ["collectConst(P('sqrt(2)*x + sqrt(2)*y + 3*x'))", () => collectConst(P('sqrt(2)*x + sqrt(2)*y + 3*x')), "3*x + sqrt(2)*(x + y)"],
    ["collectConst(P('x + y'))", () => collectConst(P('x + y')), "x + y"],
    ["collectConst(P('3*x + 6*y'))", () => collectConst(P('3*x + 6*y')), "3*x + 6*y"],
    ["collectConst(P('x/2 + y/2 + 3'))", () => collectConst(P('x/2 + y/2 + 3')), "(x + y)/2 + 3"],
    ["collectConst(P('2*sqrt(x) + 4*sqrt(y)'))", () => collectConst(P('2*sqrt(x) + 4*sqrt(y)')), "2*sqrt(x) + 4*sqrt(y)"],
    ["collectConst(P('sqrt(2)*x**2 + sqrt(2)*x'))", () => collectConst(P('sqrt(2)*x**2 + sqrt(2)*x')), "sqrt(2)*(x**2 + x)"],
    ["collectConst(P('-x - y - 2*z'))", () => collectConst(P('-x - y - 2*z')), "-(x + y + 2*z)"],
    ["collectConst(P('x - 2*(x + 1)'))", () => collectConst(P('x - 2*(x + 1)')), "-(x + 2)"],
    ["collectConst(P('sqrt(3)*(x+1) + sqrt(3)'))", () => collectConst(P('sqrt(3)*(x+1) + sqrt(3)')), "sqrt(3)*(x + 2)"],
    ["collectConst(P('a*sqrt(5) + b*sqrt(5) + sqrt(7)'))", () => collectConst(P('a*sqrt(5) + b*sqrt(5) + sqrt(7)')), "sqrt(5)*(a + b) + sqrt(7)"],
    ["collectConst(P('x*sqrt(2)/2 + y*sqrt(2)/3'))", () => collectConst(P('x*sqrt(2)/2 + y*sqrt(2)/3')), "(sqrt(2)*x + 2*sqrt(2)*y/3)/2"],
    ["collectConst(P('2**x*3 + 2**x*y'))", () => collectConst(P('2**x*3 + 2**x*y')), "2**x*y + 3*2**x"],
    ["collectConst(P('pi*x + pi*y + E'))", () => collectConst(P('pi*x + pi*y + E')), "pi*(x + y) + E"],
    ["collectConst(P('exp(2)*x + exp(2)*y'))", () => collectConst(P('exp(2)*x + exp(2)*y')), "(x + y)*exp(2)"],
    ["collectConst(P('sqrt(3) + sqrt(3)*sqrt(2)'), [P('sqrt(3)')])", () => collectConst(P('sqrt(3) + sqrt(3)*sqrt(2)'), [P('sqrt(3)')]), "sqrt(3) + sqrt(6)"],
    ["collectConst(P('2*x + 2*y + sqrt(2)*x'), [P('2')])", () => collectConst(P('2*x + 2*y + sqrt(2)*x'), [P('2')]), "sqrt(2)*x + 2*(x + y)"],
    ["collectConst(P('2*x + 2*y + sqrt(2)*x'), [], { numbers: false })", () => collectConst(P('2*x + 2*y + sqrt(2)*x'), [], { numbers: false }), "sqrt(2)*x + 2*x + 2*y"],
    ["collectConst(P('2*x + 2*y'), [P('2')], { numbers: false })", () => collectConst(P('2*x + 2*y'), [P('2')], { numbers: false }), "2*x + 2*y"],
    ["collectConst(P('x*sqrt(2) + y*sqrt(2) + x*sqrt(3)'), [P('sqrt(2)'), P('sqrt(3)')])", () => collectConst(P('x*sqrt(2) + y*sqrt(2) + x*sqrt(3)'), [P('sqrt(2)'), P('sqrt(3)')]), "sqrt(3)*x + sqrt(2)*(x + y)"],
    ["collectConst(P('sqrt(6)*x + sqrt(6)*y'), [P('sqrt(2)')])", () => collectConst(P('sqrt(6)*x + sqrt(6)*y'), [P('sqrt(2)')]), "sqrt(6)*x + sqrt(6)*y"],
    ["collectConst(P('x**2*y + x**2'), [P('x')])", () => collectConst(P('x**2*y + x**2'), [P('x')]), "x*(x*y + x)"],
    ["collectConst(P('sqrt(x)*y + sqrt(x)'), [P('x')])", () => collectConst(P('sqrt(x)*y + sqrt(x)'), [P('x')]), "sqrt(x)*y + sqrt(x)"],
    ["collectConst(P('2/3*x + 4/3*y'), [P('2/3')])", () => collectConst(P('2/3*x + 4/3*y'), [P('2/3')]), "2*x/3 + 4*y/3"],
    ["collectConst(P('-2*x - 2*y'), [P('-1')])", () => collectConst(P('-2*x - 2*y'), [P('-1')]), "-(2*x + 2*y)"],
    ["collectConst(P('-2*x - 4*y'), [P('-2')])", () => collectConst(P('-2*x - 4*y'), [P('-2')]), "-2*x - 4*y"],
    ["collectConst(P('x'))", () => collectConst(P('x')), "x"],
    ["collectConst(P('6*x + 4*y'), [P('2')])", () => collectConst(P('6*x + 4*y'), [P('2')]), "6*x + 4*y"],
    ["factorTerms(P('9*(x + x*y + 1) + (3*x + 3)**(2 + 2*x)'))", () => factorTerms(P('9*(x + x*y + 1) + (3*x + 3)**(2 + 2*x)')), "9*x*y + 9*x + (3*(x + 1))**(2*(x + 1)) + 9"],
    ["factorTerms(P('x/2 + 1'), { clear: false })", () => factorTerms(P('x/2 + 1'), { clear: false }), "x/2 + 1"],
    ["factorTerms(P('x/2 + 1'), { clear: true })", () => factorTerms(P('x/2 + 1'), { clear: true }), "(x + 2)/2"],
    ["factorTerms(P('x/2 + y/3 + 1/6'), { clear: false })", () => factorTerms(P('x/2 + y/3 + 1/6'), { clear: false }), "(3*x + 2*y + 1)/6"],
    ["factorTerms(P('-x - y'))", () => factorTerms(P('-x - y')), "-(x + y)"],
    ["factorTerms(P('-x - y'), { sign: false })", () => factorTerms(P('-x - y'), { sign: false }), "-x - y"],
    ["factorTerms(P('x/y + y'), { fraction: true })", () => factorTerms(P('x/y + y'), { fraction: true }), "(x + y**2)/y"],
    ["factorTerms(P('2**(2*x) + 2**(2*x)*y'))", () => factorTerms(P('2**(2*x) + 2**(2*x)*y')), "2**(2*x)*(y + 1)"],
    ["factorTerms(P('exp(x*(y+1)) + exp(x*(y+1))*z'))", () => factorTerms(P('exp(x*(y+1)) + exp(x*(y+1))*z')), "(z + 1)*exp(x*(y + 1))"],
    ["factorTerms(P('x**(2*y) + x**(2*y)*z'))", () => factorTerms(P('x**(2*y) + x**(2*y)*z')), "x**(2*y)*(z + 1)"],
    ["factorTerms(P('Eq(2*x + 2, 4)'))", () => factorTerms(P('Eq(2*x + 2, 4)')), "Eq(2*(x + 1), 4)"],
    ["factorTerms(P('sin(2*x + 2*y)'))", () => factorTerms(P('sin(2*x + 2*y)')), "sin(2*(x + y))"],
    ["factorTerms(P('f(2*x + 2)'))", () => factorTerms(P('f(2*x + 2)')), "f(2*(x + 1))"],
    ["factorTerms(P('(2*x + 2)*(3*y + 3)'))", () => factorTerms(P('(2*x + 2)*(3*y + 3)')), "6*(x + 1)*(y + 1)"],
    ["factorTerms(P('x*y + x*z + 2*x'))", () => factorTerms(P('x*y + x*z + 2*x')), "x*(y + z + 2)"],
    ["factorTerms(P('x**2*sqrt(y) + x*sqrt(y)'))", () => factorTerms(P('x**2*sqrt(y) + x*sqrt(y)')), "x*sqrt(y)*(x + 1)"],
    ["factorTerms(P('x*y**(-2) + x/y'))", () => factorTerms(P('x*y**(-2) + x/y')), "x*(1 + 1/y)/y"],
    ["gcdTerms(P('x*y + x*z'))", () => gcdTerms(P('x*y + x*z')), "x*(y + z)"],
    ["gcdTerms(P('x/y + y'))", () => gcdTerms(P('x/y + y')), "(x + y**2)/y"],
    ["gcdTerms(P('x/y + y'), { fraction: false })", () => gcdTerms(P('x/y + y'), { fraction: false }), "x/y + y"],
    ["gcdTerms(P('x/2 + 1'), { clear: false })", () => gcdTerms(P('x/2 + 1'), { clear: false }), "x/2 + 1"],
    ["gcdTerms(P('x/2 + y/2'), { clear: false })", () => gcdTerms(P('x/2 + y/2'), { clear: false }), "(x + y)/2"],
    ["gcdTerms(P('(x + 1)**2*y + (x + 1)*y**2'))", () => gcdTerms(P('(x + 1)**2*y + (x + 1)*y**2')), "y*(x + 1)*(x + y + 1)"],
    ["gcdTerms(P('2*x'))", () => gcdTerms(P('2*x')), "2*x"],
    ["gcdTerms(P('0'))", () => gcdTerms(P('0')), "0"],
    ["gcdTerms(P('x/3 + 2*y/9'))", () => gcdTerms(P('x/3 + 2*y/9')), "(3*x + 2*y)/9"],
    ["gcdTerms(P('x**2*y**(1/2) + x*y**(3/2)'))", () => gcdTerms(P('x**2*y**(1/2) + x*y**(3/2)')), "x*sqrt(y)*(x + y)"],
    ["gcdTerms(P('2**(3*x) + 2**(2*x)'))", () => gcdTerms(P('2**(3*x) + 2**(2*x)')), "2**(2*x)*(2**x + 1)"],
    ["gcdTerms(P('exp(3*x) + exp(2*x)'))", () => gcdTerms(P('exp(3*x) + exp(2*x)')), "(exp(x) + 1)*exp(2*x)"],
    ["gcdTerms(P('exp(-x) + exp(-2*x)'))", () => gcdTerms(P('exp(-x) + exp(-2*x)')), "(exp(x) + 1)*exp(-2*x)"],
    ["gcdTerms(P('1/x + 1/x**2'))", () => gcdTerms(P('1/x + 1/x**2')), "(x + 1)/x**2"],
    ["gcdTerms(P('2.5*x + 5*y'))", () => gcdTerms(P('2.5*x + 5*y')), "2.5*x + 5*y"],
    ["keepCoeffSympy(P('2'), P('x + y'))", () => keepCoeffSympy(P('2'), P('x + y')), "2*(x + y)"],
    ["keepCoeffSympy(P('1/2'), P('x + 2'), false)", () => keepCoeffSympy(P('1/2'), P('x + 2'), false), "x/2 + 1"],
    ["keepCoeffSympy(P('1/2'), P('x + y'), false)", () => keepCoeffSympy(P('1/2'), P('x + y'), false), "(x + y)/2"],
    ["keepCoeffSympy(P('x'), P('2'))", () => keepCoeffSympy(P('x'), P('2')), "2*x"],
    ["keepCoeffSympy(P('x'), P('y'))", () => keepCoeffSympy(P('x'), P('y')), "x*y"],
    ["keepCoeffSympy(P('1'), P('x'))", () => keepCoeffSympy(P('1'), P('x')), "x"],
    ["keepCoeffSympy(P('3'), P('1'))", () => keepCoeffSympy(P('3'), P('1')), "3"],
    ["keepCoeffSympy(P('-1'), P('x + y'))", () => keepCoeffSympy(P('-1'), P('x + y')), "-x - y"],
    ["keepCoeffSympy(P('-1'), P('x + y'), true, true)", () => keepCoeffSympy(P('-1'), P('x + y'), true, true), "-(x + y)"],
    ["keepCoeffSympy(P('2'), P('3*x'))", () => keepCoeffSympy(P('2'), P('3*x')), "6*x"],
    ["keepCoeffSympy(P('1/3'), P('3*x'))", () => keepCoeffSympy(P('1/3'), P('3*x')), "x"],
    ["keepCoeffSympy(P('2'), P('x*y'))", () => keepCoeffSympy(P('2'), P('x*y')), "2*x*y"],
    ["keepCoeffSympy(P('2'), P('x'))", () => keepCoeffSympy(P('2'), P('x')), "2*x"],
    ["keepCoeffSympy(P('2'), P('sqrt(2)'))", () => keepCoeffSympy(P('2'), P('sqrt(2)')), "2*sqrt(2)"],
    ["unevaluatedAdd([P('2*x'), P('3'), P('x + 1')])", () => unevaluatedAdd([P('2*x'), P('3'), P('x + 1')]), "x + 2*x + 4"],
    ["unevaluatedAdd([P('1'), P('-1')])", () => unevaluatedAdd([P('1'), P('-1')]), "0"],
    ["unevaluatedAdd([P('x')])", () => unevaluatedAdd([P('x')]), "x"],
    ["unevaluatedAdd([])", () => unevaluatedAdd([]), "0"],
    ["signsimp(P('-x - y'))", () => signsimp(P('-x - y')), "-x - y"],
    ["signsimp(P('-x - y'), false)", () => signsimp(P('-x - y'), false), "-(x + y)"],
    ["signsimp(P('x - y'), false)", () => signsimp(P('x - y'), false), "x - y"],
    ["signsimp(P('(-x - y)**2'))", () => signsimp(P('(-x - y)**2')), "(x + y)**2"],
    ["signsimp(P('1/(-x - y)'))", () => signsimp(P('1/(-x - y)')), "-1/(x + y)"],
    ["signsimp(P('sin(-x - y)'))", () => signsimp(P('sin(-x - y)')), "-sin(x + y)"],
    ["signsimp(P('x'))", () => signsimp(P('x')), "x"],
    ["signsimp(P('(-x + 1)*(-x - 1)'))", () => signsimp(P('(-x + 1)*(-x - 1)')), "(x - 1)*(x + 1)"],
    ["signsimp(P('-x - y + exp(-x - 1)'), false)", () => signsimp(P('-x - y + exp(-x - 1)'), false), "-(x + y - exp(-x - 1))"],
    ["signsimp(P('(-x - y)**(-z - 1)'))", () => signsimp(P('(-x - y)**(-z - 1)')), "(-x - y)**(-z - 1)"],
    ["factorTerms(add(x, mul(x, Sum(x, [k, 1, n]))))", () => factorTerms(add(x, mul(x, Sum(x, [k, 1, n])))), "x*(x*Sum(1, (k, 1, n)) + 1)"],
    ["factorTerms(Sum(P('x*k + x'), [k, 1, n]))", () => factorTerms(Sum(P('x*k + x'), [k, 1, n])), "x*Sum(k + 1, (k, 1, n))"],
    ["factorTerms(Sum(P('x*k'), [k, 1, n]))", () => factorTerms(Sum(P('x*k'), [k, 1, n])), "x*Sum(k, (k, 1, n))"],
    ["factorTerms(Sum(P('0'), [k, 1, n]))", () => factorTerms(Sum(P('0'), [k, 1, n])), "0"],
    ["factorTerms(Sum(P('2*x*k + 2*x'), [k, 1, n]))", () => factorTerms(Sum(P('2*x*k + 2*x'), [k, 1, n])), "2*x*Sum(k + 1, (k, 1, n))"],
    ["signsimp(P('exp(-x - y)*(-x - y)**2'))", () => signsimp(P('exp(-x - y)*(-x - y)**2')), "(x + y)**2*exp(-x - y)"],
    ["signsimp(P('(-x - y)**3'))", () => signsimp(P('(-x - y)**3')), "-(x + y)**3"],
    ["signsimp(P('(-x - y)**y'))", () => signsimp(P('(-x - y)**y')), "(-x - y)**y"],
    ["signsimp(P('-x - y + exp(-x - 1)'))", () => signsimp(P('-x - y + exp(-x - 1)')), "-x - y + exp(-x - 1)"],
    ["signsimp(P('x - y + exp(-x - 1)'), false)", () => signsimp(P('x - y + exp(-x - 1)'), false), "x - y + exp(-x - 1)"],
    ["gcdTerms(P('sin(x*y + x*z)'))", () => gcdTerms(P('sin(x*y + x*z)')), "sin(x*(y + z))"],
    ["gcdTerms(P('sin(x*y + x*z)*2*cos(x*y+x)'))", () => gcdTerms(P('sin(x*y + x*z)*2*cos(x*y+x)')), "2*sin(x*(y + z))*cos(x*(y + 1))"],
    ["factorTerms(Sum(P('x + k'), [k, 1, n]))", () => factorTerms(Sum(P('x + k'), [k, 1, n])), "x*Sum(1, (k, 1, n)) + Sum(k, (k, 1, n))"],
    ["collectConst(P('x + 1'), [P('2')])", () => collectConst(P('x + 1'), [P('2')]), "x + 1"],
    ["collectConst(P('x**y*a + x**y'), [P('x')])", () => collectConst(P('x**y*a + x**y'), [P('x')]), "a*x**y + x**y"],
    ["collectConst(P('2*x*y + 2*x'), [P('2')])", () => collectConst(P('2*x*y + 2*x'), [P('2')]), "2*(x*y + x)"],
    ["collectConst(P('2*x + 2*y + 4'))", () => collectConst(P('2*x + 2*y + 4')), "2*(x + y) + 4"],
    ["collectConst(P('2*x + 2*y'), [P('2'), P('3')])", () => collectConst(P('2*x + 2*y'), [P('2'), P('3')]), "2*(x + y)"],
    ["(() => { const [A] = symbols('A B', { commutative: false }); return gcdTerms(add(mul(x, A), mul(y, A))); })()", () => (() => { const [A] = symbols('A B', { commutative: false }); return gcdTerms(add(mul(x, A), mul(y, A))); })(), "x*A + y*A"],
    ["(() => { const [A, B] = symbols('A B', { commutative: false }); return gcdTerms(add(mul(A, x), mul(A, B, x))); })()", () => (() => { const [A, B] = symbols('A B', { commutative: false }); return gcdTerms(add(mul(A, x), mul(A, B, x))); })(), "x*(A + A*B)"],
    ["signsimp(P('-x + exp(-x - y)'), false)", () => signsimp(P('-x + exp(-x - y)'), false), "-(x - exp(-x - y))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe('decomposePower: results equal SymPy 1.14 decompose_power', () => {
  const cases: [string, string][] = [
    ['x**2', '[x, 2]'],
    ['x**(2/3)', '[x**(1/3), 2]'],
    ['x**(-1)', '[x, -1]'],
    ['x**y', '[x**y, 1]'],
    ['x**(2*y)', '[x**y, 2]'],
    ['x**(-y)', '[x**y, -1]'],
    ['x**(2*y/3)', '[x**(y/3), 2]'],
    ['exp(2*x)', '[exp(x), 2]'],
    ['exp(x)', '[exp(x), 1]'],
    ['exp(x/2)', '[exp(x/2), 1]'],
    ['x', '[x, 1]'],
  ];
  it.each(cases)('%s', (src, want) => {
    expect(show(decomposePower(P(src)))).toBe(want);
  });
  it('a float exponent', () => {
    // SymPy: decompose_power(x**2.5) = (x**2.5, 1)
    const [b, e] = decomposePower(pow(x, float(2.5)));
    expect(e).toBe(1);
    expect(b.key).toBe(pow(x, float(2.5)).key);
  });
});

describe('gcdTermsOf: results equal SymPy 1.14 gcd_terms of a list', () => {
  it('empty and single-term lists', () => {
    // SymPy: gcd_terms([0, 0]) = 0, gcd_terms([2*x]) = 2*x
    expect(gcdTermsOf([P('0'), P('0')]).toString()).toBe('0');
    expect(gcdTermsOf([P('2*x')]).toString()).toBe('2*x');
    // SymPy: gcd_terms([x/2, x/3], clear=False) = 5*x/6
    expect(gcdTermsOf([P('x/2'), P('x/3')], { clear: false }).toString()).toBe('5*x/6');
  });
});

describe("ratsimpmodprime, gammasimp, signsimp, cancel, ratsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["signsimp(P('x*(-y - z) + 1'), false)", () => signsimp(PA('x*(-y - z) + 1'), false), "-(x*(y + z) - 1)"],
    ["signsimp(P('x*(-y - z) + 1'))", () => signsimp(PA('x*(-y - z) + 1')), "-x*(y + z) + 1"],
    ["signsimp(P('w + x*(-y - z)'), false)", () => signsimp(PA('w + x*(-y - z)'), false), "w - x*(y + z)"],
    ["signsimp(P('w + x*(-y - z)'))", () => signsimp(PA('w + x*(-y - z)')), "w - x*(y + z)"],
    ["signsimp(P('a*(-b - c) + d*(-u - v)'), false)", () => signsimp(PA('a*(-b - c) + d*(-u - v)'), false), "-(a*(b + c) + d*(u + v))"],
    ["signsimp(P('a*(-b - c) + d*(-u - v)'))", () => signsimp(PA('a*(-b - c) + d*(-u - v)')), "-a*(b + c) - d*(u + v)"],
    ["signsimp(P('x*(-y - z) + w*(-a - b) + 1'), false)", () => signsimp(PA('x*(-y - z) + w*(-a - b) + 1'), false), "-(w*(a + b) + x*(y + z) - 1)"],
    ["signsimp(P('x*(-y - z) + w*(-a - b) + 1'))", () => signsimp(PA('x*(-y - z) + w*(-a - b) + 1')), "-w*(a + b) - x*(y + z) + 1"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('signsimp: the second sub_pre pass', () => {
  it('extracts the sign of a sum that appears after the first replacement', () => {
    const P = (s: string) => parse(s);
    const cases: [string, string, string][] = [
      ['x*(-y - z) - w', '-w - x*(y + z)', '-(w + x*(y + z))'],
      ['-w - x*(-y - z)', '-w + x*(y + z)', '-(w - x*(y + z))'],
      ['y - x', '-x + y', '-(x - y)'],
      ['(-x - y)**3', '-(x + y)**3', '-(x + y)**3'],
      ['(-x - y)**y', '(-x - y)**y', '(-(x + y))**y'],
    ];
    cases.push(['f(x*(-y - z) + 1)', 'f(-x*(y + z) + 1)', 'f(-x*(y + z) + 1)'], ['f(x*(-y - z) + 1)*(x*(-y - z) + 1)', '-(x*(y + z) - 1)*f(-x*(y + z) + 1)', '-(x*(y + z) - 1)*f(-x*(y + z) + 1)']);
    for (const [e, ev, unev] of cases) {
      expect(String(signsimp(P(e)))).toBe(ev);
      expect(String(signsimp(P(e), false))).toBe(unev);
    }
  });
});
