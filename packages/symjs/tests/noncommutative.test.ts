import { describe, expect, it } from 'vitest';
import { I, Rational, Sym, add, adjoint, exp, latex, mul, pow, transpose } from '../src';

const x = new Sym('x');
const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });

// expected values generated with SymPy 1.14 (str, latex)
const CASES: [unknown, string, string][] = [
    [pow(A, -1), 'A**(-1)', 'A^{-1}'],
    [pow(mul(A, B), 2), '(A*B)**2', '\\left(A B\\right)^{2}'],
    [mul(-1, A, B), '-A*B', '- A B'],
    [mul(A, Rational.of(1, 2)), 'A/2', '\\frac{A}{2}'],
    [mul(I, A, B), 'I*A*B', 'i A B'],
    [mul(x, A, pow(B, 2)), 'x*A*B**2', 'x A B^{2}'],
    [mul(adjoint(A), A), 'adjoint(A)*A', 'A^{\\dagger} A'],
    [pow(adjoint(mul(A, B)), 2), '(adjoint(B)*adjoint(A))**2', '\\left(B^{\\dagger} A^{\\dagger}\\right)^{2}'],
    [add(mul(A, B), mul(-1, B, A)), 'A*B - B*A', 'A B - B A'],
    [mul(add(A, B), add(A, mul(-1, B))), '(A + B)*(A - B)', '\\left(A + B\\right) \\left(A - B\\right)'],
    [mul(exp(A), exp(B)), 'exp(A)*exp(B)', 'e^{A} e^{B}'],
    [adjoint(mul(I, x, A)), '-I*conjugate(x)*adjoint(A)', '- i \\overline{x} A^{\\dagger}'],
    [pow(transpose(A), -1), 'transpose(A)**(-1)', '\\operatorname{transpose}^{-1}{\\left(A \\right)}'],
    [pow(A, Rational.of(1, 2)), 'sqrt(A)', '\\sqrt{A}'],
    [add(mul(2, adjoint(A)), B), 'B + 2*adjoint(A)', 'B + 2 A^{\\dagger}'],
];

describe('non-commutative printing matches SymPy', () => {
  it.each(CASES.map((c, i) => [i, ...c] as const))('case %i', (_i, e, s, l) => {
    expect(String(e)).toBe(s);
    expect(latex(e as never)).toBe(l);
  });
  it('exp(A)*exp(B) does not combine', () => {
    expect(mul(exp(A), exp(B)).toString()).toBe('exp(A)*exp(B)');
    expect(mul(pow(A, x), pow(A, new Sym('y'))).toString()).toBe('A**x*A**y');
    expect(mul(pow(A, 2), pow(A, 3)).toString()).toBe('A**5');
  });
});

import { asIndependent, coeff, symbols } from '../src';

describe('coeff and as_independent with non-commutative symbols (SymPy)', () => {
  const [n, m, n1, n2, n3] = symbols('n m n1 n2 n3', { commutative: false });
  it('coeff', () => {
    expect(String(coeff(add(mul(n, m), mul(m, n, m)), n))).toBe('1 + m');
    expect(String(coeff(add(mul(n, m), mul(m, n, m)), n, 1, true))).toBe('m');
    expect(String(coeff(add(mul(n, m), mul(m, n)), n))).toBe('0');
    expect(String(coeff(add(mul(n, m), mul(x, m, n)), mul(m, n)))).toBe('x');
    expect(String(coeff(add(mul(n, m), mul(x, m, n)), mul(m, n), 1, true))).toBe('1');
  });
  it('as_independent', () => {
    expect(asIndependent(mul(n1, n2, n3), [n1]).map(String)).toEqual(['1', 'n1*n2*n3']);
    expect(asIndependent(mul(n1, n2, n3), [n2]).map(String)).toEqual(['n1', 'n2*n3']);
  });
});

import { expand, factorNc } from '../src';

describe('factor_nc', () => {
  it('factors through commutative dummies when the expansion matches', () => {
    expect(String(factorNc(expand(pow(add(x, A), 2))))).toBe('(x + A)**2');
    expect(String(factorNc(expand(mul(add(x, A), add(x, B)))))).toBe('(x + A)*(x + B)');
  });
});
