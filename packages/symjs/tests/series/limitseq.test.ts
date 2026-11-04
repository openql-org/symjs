// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/limitseq.ts.
// Limits of sequences and the difference operator. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Expr } from '../../src/core/nodes';
import { dominant } from '../../src/series/limitseq';

const [n, k, m, x] = [new sj.Sym('n'), new sj.Sym('k'), new sj.Sym('m'), new sj.Sym('x')];
const P = (s: string): Expr => sj.parseExpr(s);
const div = (a: sj.ExprLike, b: sj.ExprLike): Expr => sj.mul(a, sj.pow(b, -1));
const show = (v: unknown): string => (sj.isUnsolved(v) ? 'None' : String(v));

describe('difference_delta', () => {
  it('takes differences like SymPy', () => {
    expect(show(sj.differenceDelta(P('n*(n + 1)'), n))).toBe('2*n + 2');
    expect(show(sj.differenceDelta(P('n*(n + 1)'), n, 2))).toBe('4*n + 6');
    expect(show(sj.differenceDelta(5))).toBe('0');
    expect(show(sj.differenceDelta(P('n**2')))).toBe('-n**2 + (n + 1)**2');
    expect(show(sj.differenceDelta(P('2**n'), n))).toBe('2**n');
    expect(show(sj.differenceDelta(P('x*n'), n))).toBe('x');
    expect(show(sj.differenceDelta(P('n**n'), n))).toBe('-n**n + (n + 1)**(n + 1)');
    expect(show(sj.differenceDelta(sj.Sum(k, [k, 1, n]), n))).toBe('n + 1');
    // SymPy: (n + 1)*(n**2/2 + n/2), the same polynomial
    expect(show(sj.expand(sj.differenceDelta(sj.Sum(sj.mul(k, m), [k, 1, n], [m, 1, n]), n)))).toBe('n**3/2 + n**2 + n/2');
    expect(() => sj.differenceDelta(P('x*y'))).toThrow('Since there is more than one variable in the expression, a variable must be supplied to take the difference of x*y');
    expect(() => sj.differenceDelta(n, n, x)).toThrow('Step should be a finite number.');
    expect(() => sj.differenceDelta(n, n, sj.S.Infinity)).toThrow('Step should be a finite number.');
  });
});

describe('limit_seq', () => {
  it('computes the limits of the SymPy doctests', () => {
    expect(show(sj.limitSeq(P('(5*n**3 + 3*n**2 + 4) / (3*n**3 + 4*n - 5)'), n))).toBe('5/3');
    expect(show(sj.limitSeq(div(sj.binomial(sj.mul(2, n), n), sj.Sum(sj.binomial(sj.mul(2, k), k), [k, 1, n])), n))).toBe('3/4');
    expect(show(sj.limitSeq(div(sj.Sum(sj.mul(sj.pow(k, 2), sj.Sum(div(sj.pow(2, m), m), [m, 1, k])), [k, 1, n]), sj.mul(sj.pow(2, n), n)), n))).toBe('4');
  });

  const cases: [string, string][] = [
      ['(-1)**n', 'AccumBounds(-1, 1)'],
      ['(-1)**n/n', '0'],
      ['n*(-1)**n', 'AccumBounds(-oo, oo)'],
      ['cos(pi*n)', 'AccumBounds(-1, 1)'],
      ['1/n', '0'],
      ['factorial(n)/n**n', '0'],
      ['2**n/n', 'oo'],
      ['n/2**n', '0'],
      ['(-2)**n', 'AccumBounds(-oo, oo)'],
      ['n + (-1)**n', 'oo'],
      ['n**2 - n', 'oo'],
      // sympy/series/tests/test_limitseq.py
      ['(-1)**n/n**2', '0'],
      ['(-2)**(n+1)/(n + 3**n)', '0'],
      ['(2*n + (-1)**n)/(n + 1)', '2'],
      ['sin(pi*n)', '0'],
      ['cos(2*pi*n)', '1'],
      ['(-1/5)**n', '0'],
      ['(I/3)**n', '0'],
      ['sqrt(n)*(I/2)**n', '0'],
      ['n**7*(I/3)**n', '0'],
      ['n/(n + 1) + (I/2)**n', '1'],
      ['2*(-3)**n/(n + 3**n)', 'AccumBounds(-2, 2)'],
      ['3*n/(n + 1) + 2*(-1)**n', 'AccumBounds(1, 5)'],
      ['(-1/2)**n', '0'],
      ['5**n/factorial(n)', '0'],
      ['1/gamma(n + 1/2)', '0'],
      ['sin(n)', 'AccumBounds(-1, 1)'],
      ['log(n)/n', '0'],
      ['gamma(n)', 'oo'],
      ['exp(n)*(-1)**n', 'AccumBounds(-oo, oo)'],
      ['n**(-1)**n', 'AccumBounds(0, oo)'],
      // SymPy finds AccumBounds(0, 1), exp(-1), 1 and 0 (symjs does not decide them yet)
      ['sin(pi*n/2)**2', 'None'],
      ['subfactorial(n)/factorial(n)', 'None'],
      ['harmonic(n)/log(n)', 'None'],
      ['Abs(sin(n))/n', 'None'],
      ['(1+I)**n/2**n', '0'],
      ['(-1)**(n**2)/n', '0'],
      // x is not a number: no bounds of the odd and even limits -x and x (SymPy None)
      ['(-1)**n*x', 'None'],
      // SymPy: 0, AccumBounds(0, 2), 2 and a RecursionError (its XFAIL test expects 2)
      ['(I/2)**n*harmonic(n)', 'None'],
      ['((-1)**n + 1)*harmonic(n)/log(n)', 'None'],
      ['harmonic(n)/log(n) + 1', 'None'],
      ['n**3*Sum(2**k/k**2, (k, 1, n))**2 / (2**n * Sum(2**k/k, (k, 1, n)))', 'None'],
    ];
  it.each(cases)('limit_seq(%s, n) = %s', (e, v) => {
    expect(show(sj.limitSeq(P(e), n))).toBe(v);
  });

  it('computes other limits like SymPy', () => {
    expect(show(sj.limitSeq(div(sj.fibonacci(sj.add(n, 1)), sj.fibonacci(n)), n))).toBe('GoldenRatio');
    expect(show(sj.limitSeq(div(sj.Sum(k, [k, 1, n]), sj.pow(n, 2)), n))).toBe('1/2');
    expect(show(sj.limitSeq(div(sj.Sum(div(1, k), [k, 1, n]), sj.log(n)), n))).toBe('1');
    expect(show(sj.limitSeq(sj.sub(sj.Sum(div(1, k), [k, 1, n]), div(1, n)), n))).toBe('oo');
    // SymPy: EulerGamma
    expect(show(sj.limitSeq(sj.sub(sj.Sum(div(1, k), [k, 1, n]), sj.log(n)), n))).toBe('None');
    expect(show(sj.limitSeq(5))).toBe('5');
    expect(show(sj.limitSeq(P('1/n')))).toBe('0');
    expect(show(sj.limitSeq(x, n))).toBe('x');
    expect(() => sj.limitSeq(P('x*n'))).toThrow('Expression has more than one variable. Please specify a variable.');
    // no trials: no limit (SymPy None)
    expect(show(sj.limitSeq(n, n, 0))).toBe('None');
    // the limit of |e| when the oscillation of a power is not resolved: SymPy 0
    expect(show(sj.limitSeq(P('(-2)**(n/2)/3**n'), n))).toBe('0');
    // a limit computation that fails is no result. Deliberate difference: SymPy raises
    // ValueError (Error: n should be an integer.) from laguerre(oo, 1)
    expect(show(sj.limitSeq(P('laguerre(n, 1)'), n))).toBe('None');
  });

  it('finds dominant terms like SymPy', () => {
    expect(show(dominant(P('5*n**3 + 4*n**2 + n + 1'), n))).toBe('5*n**3');
    expect(show(dominant(sj.add(sj.pow(2, n), sj.Sum(k, [k, 0, n])), n))).toBe('2**n');
    expect(show(dominant(P('n + (-1)**n*n'), n))).toBe('undefined');
    expect(show(dominant(P('gamma(n + 1) + gamma(n)'), n))).toBe('n*gamma(n)');
    expect(show(dominant(P('factorial(n) + 2**n'), n))).toBe('factorial(n)');
  });
});
