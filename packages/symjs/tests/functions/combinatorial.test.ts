// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/combinatorial.ts.
//
// The combinatorial numbers and polynomials, the number-theoretic functions and helpers. Expected
// values are str() results of SymPy 1.14 unless a comment says otherwise; errors where SymPy raises.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { abs, add, andre, bell, bernoulli, binomialMod, euler, fibonacci, findCarmichaelNumbersInRange, findFirstNCarmichaels, frac, isCarmichael, isMotzkin, jacobiSymbol, kroneckerSymbol, legendreSymbol, mobius, motzkin, motzkinNumbersInRange, mul, multigamma, parse, S, sstr, Sym, symbols } from '../../src';

// ---- table harness: each case is [kind, SymPy source, str() of the SymPy 1.14 result or [re, im]] ----
type Case = [kind: string, src: string, expected: string | [number, number]];
const x = new sj.Sym('x');
const locals = {
  p: new sj.Sym('p', { positive: true }),
  q: new sj.Sym('q', { positive: true }),
  n: new sj.Sym('n', { integer: true }),
  k: new sj.Sym('k', { integer: true }),
  m: new sj.Sym('m', { integer: true, positive: true }),
  r: new sj.Sym('r', { real: true }),
  ng: new sj.Sym('ng', { negative: true }),
  nn: new sj.Sym('nn', { nonnegative: true }),
  // functions the parser does not know by name
  bernoulli: sj.bernoulli,
  euler: sj.euler,
  genocchi: sj.genocchi,
  bell: (n: sj.Expr, a?: sj.Expr) => sj.bell(n, a),
  fibonacci: sj.fibonacci,
  lucas: sj.lucas,
  tribonacci: sj.tribonacci,
  partition: sj.partition,
  mobius: sj.mobius,
  primenu: sj.primenu,
  primeomega: sj.primeomega,
  multigamma: sj.multigamma,
  frac: sj.frac,
  totient: sj.totient,
  reduced_totient: sj.reducedTotient,
  divisor_sigma: sj.divisorSigma,
  primepi: sj.primepi,
  // bell(n, k, (a, b, ...)) of SymPy
  bellx: (n: sj.Expr, k: sj.Expr, ...xs: sj.Expr[]) => sj.bell(n, k, xs),
};
/** Parse a SymPy expression with the symbols and functions above. */
const P = (src: string): sj.Expr => sj.parse(src, { locals });
/** NV sources are `expr;x=1.5;y=0.5+2i`: the numeric values of the free symbols. */
function numericValues(spec: string[]): Record<string, number | { re: number; im: number }> {
  const vals: Record<string, number | { re: number; im: number }> = {};
  for (const item of spec) {
    const [name = '', v = ''] = item.split('=');
    const c = /^([-+]?[\d.]+)([-+][\d.]+)i$/.exec(v);
    vals[name] = c ? { re: Number(c[1]), im: Number(c[2]) } : Number(v);
  }
  return vals;
}
/** str() of the SymPy operation named by the case kind, or the double-precision value for N / NV. */
function run(kind: string, src: string): string | [number, number] {
  if (kind === 'N' || kind === 'NV') {
    const [e = '', ...vals] = src.split(';');
    const c = sj.toComplex(P(e), numericValues(vals));
    return [c.re, c.im];
  }
  const e = P(src);
  switch (kind) {
    case 'D':
      return String(sj.diff(e, x));
    case 'EF':
      return String(sj.expandFunc(e));
    case 'UP':
      return String(sj.unpolarify(e));
    case 'PL':
      return String(sj.polarify(e, { subs: false }));
    case 'C':
      return String(sj.conjugate(e));
    case 'T':
      return String(sj.transpose(e));
    case 'A':
      return String(sj.adjoint(e));
    case 'E':
      return String(sj.expand(e));
    case 'EFl':
      return String(sj.evalf(e));
    default:
      return String(e);
  }
}
function check(cases: readonly Case[]): void {
  it.each(cases)('%s %s', (kind, src, expected) => {
    const got = run(kind, src);
    if (typeof expected === 'string') {
      expect(got).toBe(expected);
      return;
    }
    if (typeof got === 'string') throw new TypeError(`expected a number, got ${got}`);
    const tol = (v: number) => 1e-9 * Math.max(1, Math.abs(v));
    expect(Math.abs(got[0] - expected[0])).toBeLessThanOrEqual(tol(expected[0]));
    expect(Math.abs(got[1] - expected[1])).toBeLessThanOrEqual(tol(expected[1]));
  });
}
const COMB_CASES: Case[] = [
  ["s", "bernoulli(0)", "1"],
  ["s", "bernoulli(1)", "1/2"],
  ["s", "bernoulli(2)", "1/6"],
  ["s", "bernoulli(5)", "0"],
  ["s", "bernoulli(10)", "5/66"],
  ["s", "bernoulli(-1)", "bernoulli(-1)"],
  ["s", "bernoulli(x)", "bernoulli(x)"],
  ["s", "bernoulli(3, x)", "x**3 - 3*x**2/2 + x/2"],
  ["s", "bernoulli(0, x)", "1"],
  ["s", "bernoulli(1, x)", "x - 1/2"],
  ["s", "bernoulli(x, y)", "bernoulli(x, y)"],
  ["s", "euler(0)", "1"],
  ["s", "euler(3)", "0"],
  ["s", "euler(4)", "5"],
  ["s", "euler(10)", "-50521"],
  ["s", "euler(-1)", "pi/2"],
  ["s", "euler(x)", "euler(x)"],
  ["s", "euler(4, x)", "x**4 - 2*x**3 + x"],
  ["s", "euler(3, x)", "x**3 - 3*x**2/2 + 1/4"],
  ["s", "euler(x, y)", "euler(x, y)"],
  ["s", "genocchi(4)", "1"],
  ["s", "genocchi(1)", "-1"],
  ["s", "genocchi(6)", "-3"],
  ["s", "genocchi(-1)", "genocchi(-1)"],
  ["s", "genocchi(3, x)", "-3*x**2 + 3*x"],
  ["s", "genocchi(2*m + 1)", "0"],
  ["s", "genocchi(2*m)", "genocchi(2*m)"],
  ["s", "genocchi(x)", "genocchi(x)"],
  ["s", "bell(0)", "1"],
  ["s", "bell(5)", "52"],
  ["s", "bell(x)", "bell(x)"],
  ["s", "bell(4, x)", "x**4 + 6*x**3 + 7*x**2 + x"],
  ["s", "bell(0, x)", "1"],
  ["s", "bellx(4, 2, a, b, c)", "4*a*c + 3*b**2"],
  ["s", "bellx(3, 3, a, b, c)", "a**3"],
  ["s", "bellx(0, 0, a)", "1"],
  ["s", "bellx(3, 0, a, b, c)", "0"],
  ["s", "fibonacci(0)", "0"],
  ["s", "fibonacci(10)", "55"],
  ["s", "fibonacci(-5)", "5"],
  ["s", "fibonacci(-6)", "-8"],
  ["s", "fibonacci(x)", "fibonacci(x)"],
  ["s", "fibonacci(1, x)", "1"],
  ["s", "fibonacci(5, x)", "x**4 + 3*x**2 + 1"],
  ["s", "lucas(0)", "2"],
  ["s", "lucas(10)", "123"],
  ["s", "lucas(-1)", "-1"],
  ["s", "lucas(x)", "lucas(x)"],
  ["s", "tribonacci(0)", "0"],
  ["s", "tribonacci(1)", "1"],
  ["s", "tribonacci(2)", "1"],
  ["s", "tribonacci(10)", "149"],
  ["s", "tribonacci(x)", "tribonacci(x)"],
  ["s", "tribonacci(0, x)", "0"],
  ["s", "tribonacci(1, x)", "1"],
  ["s", "tribonacci(2, x)", "x**2"],
  ["s", "tribonacci(5, x)", "x**8 + 3*x**5 + 3*x**2"],
  ["s", "partition(0)", "1"],
  ["s", "partition(10)", "42"],
  ["s", "partition(-3)", "0"],
  ["s", "partition(x)", "partition(x)"],
  ["s", "partition(-m)", "0"],
  ["s", "totient(1)", "1"],
  ["s", "totient(36)", "12"],
  ["s", "totient(x)", "totient(x)"],
  ["s", "reduced_totient(1)", "1"],
  ["s", "reduced_totient(16)", "4"],
  ["s", "reduced_totient(15)", "4"],
  ["s", "reduced_totient(x)", "reduced_totient(x)"],
  ["s", "mobius(1)", "1"],
  ["s", "mobius(6)", "1"],
  ["s", "mobius(12)", "0"],
  ["s", "mobius(7)", "-1"],
  ["s", "mobius(x)", "mobius(x)"],
  ["s", "mobius(4*m)", "0"],
  ["s", "mobius(m)", "mobius(m)"],
  ["s", "divisor_sigma(12)", "28"],
  ["s", "divisor_sigma(12, 0)", "6"],
  ["s", "divisor_sigma(12, 2)", "210"],
  ["s", "divisor_sigma(x)", "divisor_sigma(x)"],
  ["s", "divisor_sigma(12, x)", "divisor_sigma(12, x)"],
  ["s", "primenu(1)", "0"],
  ["s", "primenu(60)", "3"],
  ["s", "primenu(x)", "primenu(x)"],
  ["s", "primeomega(1)", "0"],
  ["s", "primeomega(60)", "4"],
  ["s", "primeomega(x)", "primeomega(x)"],
  ["s", "primepi(1)", "0"],
  ["s", "primepi(100)", "25"],
  ["s", "primepi(-5)", "0"],
  ["s", "primepi(x)", "primepi(x)"],
  ["s", "multigamma(x, 1)", "gamma(x)"],
  ["s", "multigamma(x, 2)", "sqrt(pi)*gamma(x)*gamma(x - 1/2)"],
  ["s", "multigamma(x, 3)", "pi**(3/2)*gamma(x)*gamma(x - 1)*gamma(x - 1/2)"],
  ["s", "multigamma(x, y)", "pi**(y*(y - 1)/4)*Product(gamma(-_k/2 + x + 1/2), (_k, 1, y))"],
  ["s", "multigamma(x, m)", "pi**(m*(m - 1)/4)*Product(gamma(-_k/2 + x + 1/2), (_k, 1, m))"],
  ["s", "frac(0)", "0"],
  ["s", "frac(n)", "0"],
  ["s", "frac(7/3)", "1/3"],
  ["s", "frac(-7/3)", "2/3"],
  ["s", "frac(pi)", "-3 + pi"],
  ["s", "frac(oo)", "AccumBounds(0, 1)"],
  ["s", "frac(x)", "frac(x)"],
  ["s", "frac(r)", "frac(r)"],
  ["s", "frac(I*r)", "I*frac(r)"],
  ["s", "frac(7/3 + 5*I/2)", "1/3 + I/2"],
  ["s", "frac(x + I*r)", "I*frac(r) + frac(x)"],
  ["s", "frac(I*x)", "frac(I*x)"],
  ["s", "frac(I)", "0"],
  ["s", "frac(r + I*pi)", "frac(r) + I*(-3 + pi)"],
  ["s", "euler(-1, x)", "-polygamma(0, x/2) + polygamma(0, x/2 + 1/2)"],
  ["s", "lucas(-5)", "-11"],
  ["s", "lucas(-4)", "7"],
  ["s", "frac(-oo)", "AccumBounds(0, 1)"],
  ["s", "frac(zoo)", "nan"],
  ["s", "frac(nan)", "nan"],
  ["s", "frac(3/2 + x)", "frac(x + 3/2)"],
  ["s", "mobius(n**2)", "mobius(n**2)"],
  ["s", "mobius(4*n)", "mobius(4*n)"],
  ["s", "bernoulli(5, x)", "x**5 - 5*x**4/2 + 5*x**3/3 - x/6"],
  ["s", "genocchi(0)", "0"],
  ["s", "genocchi(0, x)", "0"],
  ["s", "bell(1, x)", "x"],
  ["s", "tribonacci(3, x)", "x**4 + x"],
  ["s", "mobius((m + 1)**2)", "0"],
  ["s", "mobius(9*m)", "0"],
];
const y = new Sym('y');
const z = new Sym('z');

describe('binomial modulo prime powers, pure quadratics, ImageSet parameters', () => {
  it('match SymPy', async () => {
    const { binomialMod, solveset, roots } = await import('../../src');
    expect(binomialMod(10n ** 18n, 10n ** 12n, 100003n ** 2n)).toBe(3744312326n);
    expect([binomialMod(100n, 37n, 1000n), binomialMod(50n, 20n, 97n)]).toEqual([600n, 49n]);
    const [y, c] = symbols('y c');
    expect(sstr(solveset(parse('exp(-y) - 3', { symbols: { y } } as never), y))).toBe('ImageSet(Lambda(_n, 2*_n*I*pi - log(3)), Integers)');
    expect(roots(parse('y**2 + c', { symbols: { y, c } } as never), y, { multiple: true }).map((e) => sstr(e))).toEqual(['sqrt(-c)', '-sqrt(-c)']); // SymPy: ordered() order
  });
});

describe('combinatorial numbers and number-theoretic functions (SymPy eval)', () => check(COMB_CASES));

describe('combinatorial: cases outside the table', () => {
  it('mobius of a symbolic product', () => {
    // SymPy returns 0 for mobius(m**2) and -1 for mobius(3*m) (m a positive integer); both
    // are wrong for some m (mobius(1**2) = 1, mobius(3*3) = 0), so they stay unevaluated
    expect(String(P('mobius(m**2)'))).toBe('mobius(m**2)');
    expect(String(P('mobius(3*m)'))).toBe('mobius(3*m)');
  });
  it('fibonacci(0, x) is an error', () => {
    // SymPy raises ValueError for the index 0 of the Fibonacci polynomials (the number fibonacci(0) is 0)
    expect(() => P('fibonacci(0, x)')).toThrow('Fibonacci polynomials are defined only for positive integer indices.');
    expect(String(P('fibonacci(0)'))).toBe('0');
  });
  it('Jacobi, Kronecker and Legendre symbols', () => {
    // SymPy jacobi_symbol / kronecker_symbol / legendre_symbol
    expect([[2n, 15n], [3n, 9n], [-1n, 7n], [1001n, 9907n]].map(([a, b]) => jacobiSymbol(a ?? 0n, b ?? 0n))).toEqual([1, 0, -1, -1]);
    expect(() => jacobiSymbol(3n, 8n)).toThrow(RangeError);
    expect(() => jacobiSymbol(3n, -5n)).toThrow(RangeError);
    const kr: [bigint, bigint][] = [[1n, 0n], [-1n, 0n], [2n, 0n], [3n, -5n], [-3n, -5n], [4n, 8n], [3n, 8n], [5n, 2n], [3n, 2n], [7n, 4n], [5n, 12n], [-5n, -12n], [6n, 1n]];
    expect(kr.map(([a, b]) => kroneckerSymbol(a, b))).toEqual([1, 1, 0, -1, 1, 0, -1, -1, -1, 1, -1, -1, 1]);
    expect(legendreSymbol(3, 7)).toBe(-1);
    expect(legendreSymbol(2, 7)).toBe(1);
    expect(() => legendreSymbol(2, 9)).toThrow(RangeError);
  });
  it('Motzkin and Andre numbers', () => {
    expect([1, 2, 5, 10].map(motzkin)).toEqual([1n, 1n, 9n, 835n]);
    expect(() => motzkin(0)).toThrow(RangeError);
    expect(motzkinNumbersInRange(0n, 100n)).toEqual([1n, 2n, 4n, 9n, 21n, 51n]);
    expect(motzkinNumbersInRange(5n, 100n)).toEqual([9n, 21n, 51n]);
    expect([isMotzkin(0n), isMotzkin(51n), isMotzkin(50n)]).toEqual([false, true, false]);
    expect([0, 1, 2, 5, 10].map(andre)).toEqual([1n, 1n, 1n, 16n, 50521n]);
    expect(() => andre(-1)).toThrow(RangeError);
  });
  it('binomial coefficients modulo m', () => {
    // binomial(n, k) % m in SymPy
    expect(binomialMod(5n, 7n, 11n)).toBe(0n);
    expect(binomialMod(5n, -1n, 11n)).toBe(0n);
    expect(binomialMod(20n, 7n, 1n)).toBe(0n);
    expect(binomialMod(50n, 20n, 8n)).toBe(0n);
    expect(binomialMod(50n, 20n, 1024n)).toBe(1016n);
    // a prime modulus above the table size and a square of a prime above 2000
    expect(binomialMod(10_000_003n, 12345n, 4_000_037n)).toBe(14185n);
    expect(binomialMod(30n, 12n, 3001n ** 2n)).toBe(5439216n);
    // SymPy: 4935779; prime powers p**e (e >= 3) above the table size are not supported
    expect(() => binomialMod(100n, 30n, 211n ** 3n)).toThrow(RangeError);
    expect(() => binomialMod(100n, 30n, 20_000_003n)).toThrow(RangeError);
  });
  it('Carmichael numbers', () => {
    expect(findCarmichaelNumbersInRange(561, 3000)).toEqual([561n, 1105n, 1729n, 2465n, 2821n]);
    expect(findCarmichaelNumbersInRange(562n, sj.sympify(3000))).toEqual([1105n, 1729n, 2465n, 2821n]);
    expect(findFirstNCarmichaels(2)).toEqual([561n, 1105n]);
    expect(isCarmichael(561)).toBe(true);
    expect(() => isCarmichael(sj.Rational.of(1, 2))).toThrow(TypeError);
    expect(() => findCarmichaelNumbersInRange(10, 5)).toThrow(RangeError);
  });
});

describe('combinatorial numbers and polynomials', () => {
  it('incomplete Bell polynomials', () => {
    // SymPy bell(3, 2, (x, y)), bell(4, 2, (x, y, z)), bell(3, 4, (x,))
    expect(String(bell(3, 2, [x, y]))).toBe('3*x*y');
    expect(String(bell(4, 2, [x, y, z]))).toBe('4*x*z + 3*y**2');
    expect(String(bell(3, 4, [x]))).toBe('0');
    // SymPy: IndexError (too few symbols) and TypeError (symbolic k)
    expect(() => bell(3, 1, [x])).toThrow(RangeError);
    expect(() => bell(3, x, [y])).toThrow(TypeError);
  });
  it('domain errors like SymPy', () => {
    // SymPy raises ValueError for these
    expect(() => fibonacci(-1, x)).toThrow(RangeError);
    expect(() => mobius(0)).toThrow(RangeError);
    expect(() => mobius(-3)).toThrow(RangeError);
    expect(() => multigamma(x, 0)).toThrow(RangeError);
    expect(() => multigamma(x, S.Half)).toThrow(RangeError);
    expect(() => multigamma(x, -1)).toThrow(RangeError);
  });
  it('mobius of a product with a factor that is not a positive integer', () => {
    // SymPy leaves mobius(-4*n) unevaluated for a negative integer n (the factor -4 is negative)
    const n = new Sym('n', { integer: true, negative: true });
    expect(String(mobius(mul(-4, n)))).toBe('mobius(-4*n)');
    // 4*x is a positive integer for x = 1/2, where mobius(2) = -1: unevaluated (SymPy too)
    const xp = new Sym('x', { positive: true });
    expect(String(mobius(mul(4, xp)))).toBe('mobius(4*x)');
  });
  it('indices beyond the evaluation limit stay unevaluated', () => {
    // SymPy computes these (a degree-5001 polynomial and 5000-digit numbers); symjs keeps
    // indices above 5000 unevaluated. bernoulli of an odd index above 1 is 0 in both.
    expect(String(bernoulli(5001, x))).toBe('bernoulli(5001, x)');
    expect(String(bernoulli(5002))).toBe('bernoulli(5002)');
    expect(String(bernoulli(5003))).toBe('0');
    expect(String(euler(5001, x))).toBe('euler(5001, x)');
    expect(String(euler(5002))).toBe('euler(5002)');
  });
  it('frac of an imaginary term whose imaginary part contains I', () => {
    // SymPy frac(I*Abs(x + I))
    expect(String(frac(mul(S.I, abs(add(x, S.I)))))).toBe('frac(I*Abs(x + I))');
  });
  it('binomial coefficients modulo a composite modulus', () => {
    // Python math.comb(10, 4) % 12, comb(30, 7) % 60, comb(100, 50) % 1001
    expect(binomialMod(10n, 4n, 12n)).toBe(6n);
    expect(binomialMod(30n, 7n, 60n)).toBe(2035800n % 60n);
    expect(binomialMod(100n, 50n, 1001n)).toBe(100891344545564193334812497256n % 1001n);
  });
});
