// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/recurr.ts: recurrence solving (rsolve); expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { rsolve, rsolveHyper, rsolvePoly, rsolveRatio } from '../../src/solvers/recurr';

// expected values from SymPy 1.14 (sympy.solvers.recurr, mostly its own test_recurr.py) with n = Symbol('n', integer=True)
const n = new sj.Sym('n', { integer: true });
const y = sj.SymFunction('y');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: { n }, locals: { y } } as never);
const show = (r: [sj.Expr, sj.Sym[]] | sj.Expr | undefined) => (r === undefined ? 'None' : sj.str(Array.isArray(r) ? r[0] : r));
const poly = (cs: string[], f: string) => show(rsolvePoly(cs.map(P), P(f), n));
const ratio = (cs: string[], f: string) => show(rsolveRatio(cs.map(P), P(f), n));
const hyper = (cs: string[], f: string) => show(rsolveHyper(cs.map(P), P(f), n));
const init = (pairs: [string, string][]): [sj.Expr, sj.Expr][] => pairs.map(([k, v]) => [P(k), P(v)]);
const rs = (eq: string, ini?: [string, string][]) => rsolve(P(eq), y(n), ini && init(ini));
/** Values at n = 0..5 with the constants and a fixed (a = 1/3), as complex numbers. */
function values(e: sj.Expr): [number, number][] {
  const vals: Record<string, number> = { C0: 2, C1: 3, C2: 5, a: 1 / 3 };
  return [0, 1, 2, 3, 4, 5].map((k) => {
    const z = e.subs(n, k).toComplex(vals);
    return [z.re, z.im];
  });
}
/** e has the same values as SymPy's expression (forms that differ only by automatic evaluation). */
function sameValues(e: sj.Expr | undefined, sympy: string) {
  expect(e).toBeDefined();
  const got = values(e as sj.Expr);
  const want = values(P(sympy));
  got.forEach(([re, im], i) => {
    expect(re).toBeCloseTo(at(want, i)[0], 9);
    expect(im).toBeCloseTo(at(want, i)[1], 9);
  });
}
const at = <T>(xs: T[], i: number): T => xs[i] as T;
/** sum(coeffs[i] * s(n + i)) - f is identically zero. */
function solves(cs: string[], f: string, s: sj.Expr) {
  const lhs = sj.add(...cs.map((c, i) => sj.mul(P(c), s.subs(n, sj.add(n, i)))));
  expect(sj.str(sj.simplify(sj.expand(sj.add(lhs, sj.mul(-1, P(f))))))).toBe('0');
}

describe('rsolve_poly', () => {
  it('equals SymPy', () => {
    expect(poly(['-1', '-1', '1'], '0')).toBe('0');
    expect(poly(['-1', '-1', '1'], '1')).toBe('-1');
    expect(poly(['-1', 'n + 1'], 'n')).toBe('1');
    expect(poly(['-1', '1'], 'n')).toBe('C0 + n**2/2 - n/2');
    expect(poly(['-n - 1', 'n'], '1')).toBe('C0*n - 1');
    expect(poly(['-4*n - 2', '1'], '4*n + 1')).toBe('-1');
    expect(poly(['-1', '1'], 'n**5 + n**3')).toBe('C0 + n**6/6 - n**5/2 + 2*n**4/3 - n**3/2 + n**2/6');
    expect(poly(['-1', '1'], '4*n**3')).toBe('C0 + n**4 - 2*n**3 + n**2');
    expect(poly(['-2', '1'], 'n**2')).toBe('-n**2 - 2*n - 3');
    expect(poly(['n', '1'], 'n**3')).toBe('None');
    expect(poly(['1', '-2', '1'], '0')).toBe('C0 + C1*n');
    expect(poly(['1', '-2', '1'], '1')).toBe('C0 + C1*n + n**2/2');
    expect(poly(['-1', '1'], '2**n')).toBe('None');
    expect(poly(['n**2 - n + 12', '1'], 'n*(n**2 - n + 12) + n + 1')).toBe('n');
    expect(poly(['-1', '1', '1', '-1', '1'], 'n**4 + 3*n')).toBe('n**4 - 16*n**3 + 120*n**2 - 565*n + 1364');
    expect(poly(['-n', 'n+1'], '0')).toBe('0');
    expect(poly(['n', '-2*n-2', 'n+2'], '0')).toBe('C0');
    expect(poly(['n', '-2*n-2', 'n+2'], 'n')).toBe('C0 + n**2/6 - n/2');
    expect(poly(['n**2', '1'], '0')).toBe('0');
    expect(poly(['1', '1'], '0')).toBe('0');
  });
  it('has no polynomial solution where SymPy returns one that does not solve the equation', () => {
    // SymPy returns C0 + C1*n for both, which does not satisfy y(n + 1) - n*y(n) = n**2 + 1
    // (a linear y = u*n + v gives -u*n**2 + (u - v)*n + u + v); there is no polynomial solution
    expect(poly(['-n**2 + n - 12', '1'], 'n**3')).toBe('None');
    expect(poly(['-n', '1'], 'n**2 + 1')).toBe('None');
  });
});

describe('rsolve_ratio', () => {
  it('equals SymPy', () => {
    expect(ratio(['-2*n**3 + n**2 + 2*n - 1', '2*n**3 + n**2 - 6*n', '-2*n**3 - 11*n**2 - 18*n - 9', '2*n**3 + 13*n**2 + 22*n + 8'], '0'))
      .toBe('C0*(2*n - 3)/(2*(n**2 - 1))');
    expect(ratio(['-1', '1'], '2**n')).toBe('None');
    expect(ratio(['-1', '1'], 'n')).toBe('C0 + n**2/2 - n/2');
    expect(ratio(['n', '-(n+1)'], '0')).toBe('C0/n');
  });
  it('finds the rational solutions SymPy misses', () => {
    // SymPy test_rsolve_ratio_missed (XFAIL) expects a solution here; SymPy 1.14 returns None
    const s1 = rsolveRatio([P('-n'), P('n + 2')], n, n);
    expect(show(s1)).toBe('(3*C0 + n**3 - n)/(3*n*(n + 1))');
    solves(['-n', 'n + 2'], 'n', (s1 as [sj.Expr, sj.Sym[]])[0]);
    // SymPy returns 0 (only the trivial solution), but C0*n*(n + 1)/2 solves -(n + 2)*y(n) + n*y(n + 1) = 0
    const s2 = rsolveRatio([P('-(n+2)'), P('n')], 0, n);
    expect(show(s2)).toBe('C0*n**2/2 + C0*n/2');
    solves(['-(n+2)', 'n'], '0', (s2 as [sj.Expr, sj.Sym[]])[0]);
    // SymPy returns None
    const s3 = rsolveRatio([P('n+1'), P('-(n+3)')], 1, n);
    expect(show(s3)).toBe('(2*C0 - n**2 - 3*n)/(2*(n + 1)*(n + 2))');
    solves(['n+1', '-(n+3)'], '1', (s3 as [sj.Expr, sj.Sym[]])[0]);
  });
});

describe('rsolve_hyper', () => {
  it('equals SymPy', () => {
    expect(hyper(['-1', '-1', '1'], '0')).toBe('C0*(1/2 - sqrt(5)/2)**n + C1*(1/2 + sqrt(5)/2)**n');
    expect(hyper(['n**2 - 2', '-2*n - 1', '1'], '0')).toBe('C0*RisingFactorial(-sqrt(2), n) + C1*RisingFactorial(sqrt(2), n)');
    expect(hyper(['2*n*(n + 1)', '-n**2 - 3*n + 2', 'n - 1'], '0')).toBe('2**n*C0 + C1*factorial(n)');
    expect(hyper(['n + 2', '-(2*n + 3)*(17*n**2 + 51*n + 39)', 'n + 1'], '0')).toBe('0');
    expect(hyper(['-n - 1', '-1', '1'], '0')).toBe('0');
    expect(hyper(['-1', '1'], 'n')).toBe('C0 + n*(n - 1)/2');
    expect(hyper(['-1', '1'], '1 + n')).toBe('C0 + n*(n + 1)/2');
    expect(hyper(['-a', '1'], '0')).toBe('C0*a**n');
    expect(hyper(['1', '1', '1'], '0')).toBe('C0*(-1/2 - sqrt(3)*I/2)**n + C1*(-1/2 + sqrt(3)*I/2)**n');
    expect(hyper(['1', '-2*n/a - 2/a', '1'], '0')).toBe('0');
    // test_rsolve_0_sol_homogeneous: the resultant has irreducible sextic factors next to its integer root 0
    expect(hyper(['n**2 - n + 12', '1'], 'n*(n**2 - n + 12) + n + 1')).toBe('n');
    expect(hyper(['1', '1'], '2**n + 3**n')).toBe('(-1)**n*C0 + 2**n/3 + 3**n/4');
    expect(hyper(['-1', '1'], 'gamma(n**2)')).toBe('None');
    expect(hyper(['-1', '1'], '2**n + gamma(n**2)')).toBe('None');
    expect(hyper(['-1', '1'], 'cos(n)')).toBe('None');
    expect(hyper(['-n', '1'], '0')).toBe('C0*RisingFactorial(0, n)');
    expect(hyper(['-1', '1'], 'factorial(n)')).toBe('None');
    expect(hyper(['-(n+1)', '1'], 'factorial(n)')).toBe('None');
    expect(hyper(['1', '-n'], '0')).toBe('C0/factorial(n - 1)');
    expect(hyper(['n**2+1', '-1'], '0')).toBe('0');
    // an irreducible quintic leading coefficient: its roots are not needed (SymPy roots gives none)
    expect(hyper(['n**5 - n + 1', '1'], '0')).toBe('0');
    // a non-real root in the denominator of the term ratio
    expect(hyper(['1', 'n**2 + 1'], '0')).toBe('0');
    // annihilates 1/RisingFactorial(1 - I, n + 1) and its conjugate: the ratio's denominator has the root -1 + I
    expect(hyper(['n**2 + 2*n + 2', '-(2*n + 3)*(n**2 + 2*n + 2)', '(n**2 + 2*n + 2)*(n**2 + 4*n + 5)'], '0')).toBe('None');
  });
  it('equals SymPy up to automatic evaluation', () => {
    // SymPy: C0 + n**3 - n (simplify keeps the expanded form)
    sameValues(rsolveHyper([-1, 1], P('3*(n + n**2)'), n)?.[0], 'C0 + n**3 - n');
    // SymPy writes sqrt(a)**n as a**(n/2) for integer n
    sameValues(rsolveHyper([P('-a'), 0, 1], 0, n)?.[0], 'C0*a**(n/2) + C1*(-sqrt(a))**n');
    // SymPy: 2**n*C0 + 2**(n - 1)*n + 3**n
    sameValues(rsolveHyper([-2, 1], P('2**n + 3**n'), n)?.[0], '2**n*C0 + 2**(n - 1)*n + 3**n');
    // SymPy: C0/factorial(-n) (C0 at n = 0 and 0 for n >= 1)
    expect(hyper(['n', '1'], '0')).toBe('C0/factorial(-n)');
    sameValues(rsolveHyper([n, 1], 0, n)?.[0], 'C0*(-1)**n*RisingFactorial(0, n)');
  });
  it('solves where SymPy fails', () => {
    // SymPy raises AttributeError: the similar terms 3**n and n*3**n are grouped into a sum it cannot simplify
    const s = rsolveHyper([-2, 1], P('2**n*n + 3**n + n*3**n'), n);
    expect(show(s)).toBe('2**n*C0 + 2**(n - 2)*n*(n - 1) + 3**n*(n - 2)');
    solves(['-2', '1'], '2**n*n + 3**n + n*3**n', (s as [sj.Expr, sj.Sym[]])[0]);
    // SymPy raises UnboundLocalError: the sum expands to the single term 1
    const t = rsolveHyper([-1, 1], P('(n + 1)**2 - n**2 - 2*n'), n);
    expect(show(t)).toBe('C0 + n');
  });
});

describe('rsolve', () => {
  const fib = '-sqrt(5)*(1/2 - sqrt(5)/2)**n + sqrt(5)*(1/2 + sqrt(5)/2)**n';
  it('equals SymPy', () => {
    expect(show(rs('y(n + 2) - y(n + 1) - y(n)'))).toBe('C0*(1/2 - sqrt(5)/2)**n + C1*(1/2 + sqrt(5)/2)**n');
    expect(show(rs('y(n + 2) - y(n + 1) - y(n)', [['0', '0'], ['1', '5']]))).toBe(fib);
    expect(show(rs('y(n + 2) - y(n + 1) - y(n)', [['y(0)', '0'], ['y(1)', '5']]))).toBe(fib);
    expect(show(rs('y(n) - y(n - 1) - y(n - 2)', [['0', '0'], ['1', '5']]))).toBe(fib);
    expect(show(rs('Eq(y(n), y(n - 1) + y(n - 2))', [['0', '0'], ['1', '5']]))).toBe(fib);
    const f2 = '(n - 1)*y(n + 2) - (n**2 + 3*n - 2)*y(n + 1) + 2*n*(n + 1)*y(n)';
    expect(show(rs(f2))).toBe('2**n*C0 + C1*factorial(n)');
    expect(show(rs(f2, []))).toBe('2**n*C0 + C1*factorial(n)');
    expect(show(rs(f2, [['0', '0'], ['1', '3']]))).toBe('3*2**n - 3*factorial(n)');
    expect(show(rs('y(n) - y(n - 1) - 2', [['y(0)', '0']]))).toBe('2*n');
    expect(show(rs('y(n) - y(n - 1) - 2', [['y(0)', '1']]))).toBe('2*n + 1');
    expect(show(rs('y(n) - y(n - 1) - 2', [['y(0)', '0'], ['y(1)', '1']]))).toBe('None');
    expect(show(rs('3*y(n - 1) - y(n) - 1', [['y(0)', '0']]))).toBe('1/2 - 3**n/2');
    expect(show(rs('3*y(n - 1) - y(n) - 1', [['y(0)', '2']]))).toBe('3*3**n/2 + 1/2');
    expect(show(rs('y(n) - 1/n*y(n - 1)'))).toBe('C0/factorial(n)');
    expect(show(rs('y(n) - 1/n*y(n - 1) - 1'))).toBe('None');
    expect(show(rs('2*y(n - 1) + (1 - n)*y(n)/n', [['y(1)', '1']]))).toBe('2**(n - 1)*n');
    expect(show(rs('(n - 1)*(n - 2)*y(n + 2) - (n + 1)*(n + 2)*y(n)', [['y(3)', '6'], ['y(4)', '24']]))).toBe('n*(n - 2)*(n - 1)');
    expect(show(rs('Eq(y(n + 1), a*y(n))', [['y(1)', 'a']]))).toBe('a**n');
    expect(show(rs('(n + 1)*y(n)'))).toBe('None');
    expect(show(rs('(n + 1)*y(n) + (n + 3)*y(n + 1) + (n + 5)*y(n + 2)'))).toBe('None');
    expect(show(rs('y(n) + y(n + 1) + 2**n + 3**n'))).toBe('(-1)**n*C0 - 2**n/3 - 3**n/4');
    expect(show(rs('y(n+3) - y(n+2) - y(n+1) + y(n)'))).toBe('(-1)**n*C1 + C0 + C2*n');
    expect(show(rs('y(n) - 2*y(n - 3) + 5*y(n - 2) - 4*y(n - 1)', [['0', '1'], ['1', '3'], ['2', '8']]))).toBe('3*2**n - n - 2');
    expect(show(rs('y(n+3) - 3*y(n+1) + 2*y(n)', [['y(1)', '0'], ['y(2)', '8'], ['y(3)', '-2']]))).toBe('(-2)**n + 2*n');
    expect(show(rs('y(n) - y(n - 1) - 2*y(n - 2) - 2*n'))).toBe('(-1)**n*C0 + 2**n*C1 - n - 5/2');
    expect(show(rs('y(n) - y(n - 1) - 2*y(n - 2) - 2*n', [['y(0)', '-1'], ['y(1)', '1']]))).toBe('-(-1)**n/2 + 2*2**n - n - 5/2');
    expect(show(rs('-2*y(n) + y(n + 1) + n - 1'))).toBe('2**n*C0 + n');
    expect(show(rs('Eq(y(n), 2*y(n - 1) + n)'))).toBe('2**n*C0 - n - 2');
    expect(show(rs('Eq(y(n + 1), 2*y(n) + n**2 + 1)', [['y(1)', '0']]))).toBe('7*2**n/2 - n**2 - 2*n - 4');
    expect(show(rs('Eq(y(n), 2*y(n - 1) + n)', [['y(0)', '1']]))).toBe('3*2**n - n - 2');
    expect(show(rs('y(n+1) - y(n) - 1/(n*(n+1))'))).toBe('C0 - 1/n');
    expect(show(rs('y(n+1) - y(n)/n - 1/n'))).toBe('None');
    expect(show(rs('y(n+1) - y(n) - n/(n+1)'))).toBe('None');
    expect(show(rs('y(n+1) - y(n)', [['y(0)', '1'], ['y(1)', '2']]))).toBe('None');
    expect(show(rs('y(n+1) + y(n)'))).toBe('(-1)**n*C0');
    expect(show(rs('n*y(n+1) - (n+1)*y(n)'))).toBe('C0*n');
    expect(show(rs('y(n+2) + y(n)'))).toBe('I**n*C0 + C1*(-I)**n');
  });
  it('equals SymPy up to automatic evaluation', () => {
    // SymPy: -(-1)**n*n*(n - 2)*(n - 1)
    sameValues(rs('(n - 1)*(n - 2)*y(n + 2) - (n + 1)*(n + 2)*y(n)', [['y(3)', '6'], ['y(4)', '-24']]), '-(-1)**n*n*(n - 2)*(n - 1)');
    // SymPy: C0*((-sqrt(1 - a**2) - 1)/a)**n + C1*((sqrt(1 - a**2) - 1)/a)**n (the same roots for a > 0)
    sameValues(rs('y(n) + a*(y(n + 1) + y(n - 1))/2'), 'C0*((-sqrt(1 - a**2) - 1)/a)**n + C1*((sqrt(1 - a**2) - 1)/a)**n');
    // SymPy writes (1/2)**n as 2**(-n)
    sameValues(rs('y(n + 2) - y(n + 1) + y(n)/4'), '2**(1 - n)*C1*n + C0/2**n');
    sameValues(rs('y(n + 2) - y(n + 1) + y(n)/4', [['y(0)', '0'], ['y(1)', '1']]), '2**(1 - n)*n');
    sameValues(rs('y(n+1) - y(n) - 2**(-n)'), '-2**(1 - n) + C0');
  });
  it('is Unsolved where SymPy returns an incomplete or wrong answer', () => {
    // SymPy returns 0 for both: the general solution prod(k**2 + 1) is not found, and 0 does not meet y(0) = 1
    expect(show(rs('(n**2+1)*y(n) - y(n+1)'))).toBe('None');
    expect(show(rs('(n**2+1)*y(n) - y(n+1)', [['0', '1']]))).toBe('None');
    // y(n) = 0 for n >= 1 only (y(0) is free); SymPy returns 0 for all three
    expect(show(rs('y(n+1)'))).toBe('None');
  });
  it('raises like SymPy (ValueError there)', () => {
    expect(() => rs('y(n) - y(n + 1)*y(n)')).toThrow(TypeError);
    expect(() => rs('y(n) - y(n + 1/2)')).toThrow(TypeError);
    expect(() => rs('y(n) - sqrt(n)*y(n + 1)')).toThrow(/polynomial or rational function expected/);
    expect(() => rs('y(n) + y(n + 1) + 2**n + cos(n)')).toThrow(/sum of hypergeometric functions/);
    expect(() => rs('y(n+1) - y(n) - 1/sqrt(n)')).toThrow(/sum of hypergeometric functions/);
    // SymPy fails with IndexError for a y that is not an applied function
    expect(() => rsolve(P('y(n)'), n)).toThrow(TypeError);
  });
  it('public form returns Unsolved', () => {
    expect(sj.rsolve(P('(n + 1)*y(n)'), y(n))).toBe(sj.Unsolved);
    expect(sj.str(sj.rsolve(P('y(n+1) + y(n)'), y(n)) as sj.Expr)).toBe('(-1)**n*C0');
  });
});
