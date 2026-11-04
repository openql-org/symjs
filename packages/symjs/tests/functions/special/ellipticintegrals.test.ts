// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/special/ellipticintegrals.ts.
//
// elliptic_k, elliptic_f, elliptic_e and elliptic_pi: special values, derivatives, series, conjugation,
// rewrites and numeric values. Expected values are str() results of SymPy 1.14 (mpmath 1.3 for the
// numerics) unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';

const locals = { gt: new sj.Sym('gt', { positive: true }) };
const P = (src: string): sj.Expr => sj.parse(src, { locals });

/** str() of the SymPy operation named by kind applied to src. */
function run(kind: string, src: string): string {
  const e = P(src);
  if (kind === 'E') return String(e);
  if (kind === 'C') return String(sj.conjugate(e));
  if (kind.startsWith('D:')) return String(sj.diff(e, new sj.Sym(kind.slice(2))));
  if (kind.startsWith('RW:')) return String(sj.rewrite(e, kind.slice(3)));
  if (kind.startsWith('S:')) {
    const [v = '', n = ''] = kind.slice(2).split(',');
    return String(sj.series(e, new sj.Sym(v), 0, Number(n)));
  }
  return String(sj.evalf(e, kind.length > 1 ? Number(kind.slice(1)) : 15));
}

type Case = [kind: string, src: string, expected: string];
const CASES: Case[] = [
    ['E', 'elliptic_k(0)', 'pi/2'],
    ['E', 'elliptic_k(1/2)', '8*pi**(3/2)/gamma(-1/4)**2'],
    ['E', 'elliptic_k(1)', 'zoo'],
    ['E', 'elliptic_k(-1)', 'sqrt(2)*gamma(1/4)**2/(8*sqrt(pi))'],
    ['E', 'elliptic_k(oo)', '0'],
    ['E', 'elliptic_k(-oo)', '0'],
    ['E', 'elliptic_k(I*oo)', '0'],
    ['E', 'elliptic_k(-I*oo)', '0'],
    ['E', 'elliptic_k(zoo)', '0'],
    ['E', 'elliptic_k(m)', 'elliptic_k(m)'],
    ['E', 'elliptic_k(1.0 + I)', '1.50923695405127 + 0.625146415202697*I'],
    ['D:m', 'elliptic_k(m)', '(-(1 - m)*elliptic_k(m) + elliptic_e(m))/(2*m*(1 - m))'],
    ['S:m,3', 'elliptic_k(m)', 'pi/2 + pi*m/8 + 9*pi*m**2/128 + O(m**3)'],
    ['RW:hyper', 'elliptic_k(m)', 'pi*hyper((1/2, 1/2), (1,), m)/2'],
    ['RW:meijerg', 'elliptic_k(m)', 'meijerg(((1/2, 1/2), ()), ((0,), (0,)), -m)/2'],
    ['C', 'elliptic_k(m)', 'conjugate(elliptic_k(m))'],
    ['C', 'elliptic_k(I)', 'elliptic_k(-I)'],
    ['C', 'elliptic_k(-gt)', 'elliptic_k(-gt)'],
    ['C', 'elliptic_k(gt + 1)', 'conjugate(elliptic_k(gt + 1))'],
    ['N', 'elliptic_k(2 + I)', '1.28298458888421 + 0.90936706093798*I'],
    ['E', 'elliptic_f(0, m)', '0'],
    ['E', 'elliptic_f(z, 0)', 'z'],
    ['E', 'elliptic_f(pi/2, m)', 'elliptic_k(m)'],
    ['E', 'elliptic_f(pi, m)', '2*elliptic_k(m)'],
    ['E', 'elliptic_f(z, oo)', '0'],
    ['E', 'elliptic_f(z, -oo)', '0'],
    ['E', 'elliptic_f(-z, m)', '-elliptic_f(z, m)'],
    ['E', 'elliptic_f(z, m)', 'elliptic_f(z, m)'],
    ['E', 'elliptic_f(3.0 + I/2, 1.0 + I)', '2.909449841483 + 1.74720545502474*I'],
    ['D:z', 'elliptic_f(z, m)', '1/sqrt(-m*sin(z)**2 + 1)'],
    ['D:m', 'elliptic_f(z, m)', '-sin(2*z)/((4 - 4*m)*sqrt(-m*sin(z)**2 + 1)) - elliptic_f(z, m)/(2*m) + elliptic_e(z, m)/(2*m*(1 - m))'],
    ['S:z,6', 'elliptic_f(z, m)', 'z + z**5*(3*m**2/40 - m/30) + m*z**3/6 + O(z**6)'],
    ['C', 'elliptic_f(z, I)', 'elliptic_f(conjugate(z), -I)'],
    ['C', 'elliptic_f(z, m)', 'conjugate(elliptic_f(z, m))'],
    ['E', 'elliptic_e(0)', 'pi/2'],
    ['E', 'elliptic_e(1)', '1'],
    ['E', 'elliptic_e(oo)', 'oo*I'],
    ['E', 'elliptic_e(-oo)', 'oo'],
    ['E', 'elliptic_e(zoo)', 'zoo'],
    ['E', 'elliptic_e(m)', 'elliptic_e(m)'],
    ['E', 'elliptic_e(2.0 - I)', '0.991052601328069 + 0.81879421395609*I'],
    ['E', 'elliptic_e(z, 0)', 'z'],
    ['E', 'elliptic_e(0, m)', '0'],
    ['E', 'elliptic_e(pi/2, m)', 'elliptic_e(m)'],
    ['E', 'elliptic_e(z, oo)', 'zoo'],
    ['E', 'elliptic_e(z, -oo)', 'zoo'],
    ['E', 'elliptic_e(-z, m)', '-elliptic_e(z, m)'],
    ['E', 'elliptic_e(z, m)', 'elliptic_e(z, m)'],
    ['D:m', 'elliptic_e(m)', '(elliptic_e(m) - elliptic_k(m))/(2*m)'],
    ['D:z', 'elliptic_e(z, m)', 'sqrt(-m*sin(z)**2 + 1)'],
    ['D:m', 'elliptic_e(z, m)', '(elliptic_e(z, m) - elliptic_f(z, m))/(2*m)'],
    ['S:m,4', 'elliptic_e(m)', 'pi/2 - pi*m/8 - 3*pi*m**2/128 - 5*pi*m**3/512 + O(m**4)'],
    ['S:z,6', 'elliptic_e(z, m)', 'z + z**5*(-m**2/40 + m/30) - m*z**3/6 + O(z**6)'],
    ['RW:hyper', 'elliptic_e(m)', 'pi*hyper((-1/2, 1/2), (1,), m)/2'],
    ['RW:meijerg', 'elliptic_e(m)', '-meijerg(((1/2, 3/2), ()), ((0,), (0,)), -m)/4'],
    ['RW:hyper', 'elliptic_e(z, m)', 'elliptic_e(z, m)'],
    ['RW:meijerg', 'elliptic_e(z, m)', 'elliptic_e(z, m)'],
    ['C', 'elliptic_e(I)', 'elliptic_e(-I)'],
    ['C', 'elliptic_e(z, I)', 'elliptic_e(conjugate(z), -I)'],
    ['C', 'elliptic_e(m)', 'conjugate(elliptic_e(m))'],
    ['N', 'elliptic_e(1 + I, 2 - I/2)', '1.55203744279187 + 0.290764986058437*I'],
    ['E', 'elliptic_pi(0, m)', 'elliptic_k(m)'],
    ['E', 'elliptic_pi(1, m)', 'zoo'],
    ['E', 'elliptic_pi(n, 0)', 'pi/(2*sqrt(1 - n))'],
    ['E', 'elliptic_pi(n, 1)', '-oo/sign(n - 1)'],
    ['E', 'elliptic_pi(m, m)', 'elliptic_e(m)/(1 - m)'],
    ['E', 'elliptic_pi(oo, m)', '0'],
    ['E', 'elliptic_pi(n, -oo)', '0'],
    ['E', 'elliptic_pi(n, m)', 'elliptic_pi(n, m)'],
    ['E', 'elliptic_pi(0, z, m)', 'elliptic_f(z, m)'],
    ['E', 'elliptic_pi(1, z, m)', 'elliptic_f(z, m) + (sqrt(-m*sin(z)**2 + 1)*tan(z) - elliptic_e(z, m))/(1 - m)'],
    ['E', 'elliptic_pi(n, pi/2, m)', 'elliptic_pi(n, m)'],
    ['E', 'elliptic_pi(n, z, 0)', 'atanh(sqrt(n - 1)*tan(z))/sqrt(n - 1)'],
    ['E', 'elliptic_pi(m, z, m)', 'tan(z)/sqrt(-m*sin(z)**2 + 1) - (sqrt(-m*sin(z)**2 + 1)*tan(z) - elliptic_e(z, m))/(1 - m)'],
    ['E', 'elliptic_pi(oo, z, m)', '0'],
    ['E', 'elliptic_pi(n, z, -oo)', '0'],
    ['E', 'elliptic_pi(n, -z, m)', '-elliptic_pi(n, z, m)'],
    ['E', 'elliptic_pi(n, z, m)', 'elliptic_pi(n, z, m)'],
    ['E', 'elliptic_pi(0, 0)', 'pi/2'],
    ['E', 'elliptic_pi(1.0 - I/3, 2.0 + I)', '3.29136443417283 + 0.32555634906645*I'],
    ['E', 'elliptic_pi(0.5 + I, 1.0 - I, 1.2)', '2.50232379629182 - 0.760939574180767*I'],
    ['D:n', 'elliptic_pi(n, z, m)', '(-n*sqrt(-m*sin(z)**2 + 1)*sin(2*z)/(-2*n*sin(z)**2 + 2) + elliptic_e(z, m) + (-m + n**2)*elliptic_pi(n, z, m)/n + (m - n)*elliptic_f(z, m)/n)/((2*m - 2*n)*(n - 1))'],
    ['D:z', 'elliptic_pi(n, z, m)', '1/(sqrt(-m*sin(z)**2 + 1)*(-n*sin(z)**2 + 1))'],
    ['D:m', 'elliptic_pi(n, z, m)', '(-m*sin(2*z)/((2*m - 2)*sqrt(-m*sin(z)**2 + 1)) + elliptic_pi(n, z, m) + elliptic_e(z, m)/(m - 1))/(-2*m + 2*n)'],
    ['D:n', 'elliptic_pi(n, m)', '(elliptic_e(m) + (-m + n**2)*elliptic_pi(n, m)/n + (m - n)*elliptic_k(m)/n)/((2*m - 2*n)*(n - 1))'],
    ['D:m', 'elliptic_pi(n, m)', '(elliptic_pi(n, m) + elliptic_e(m)/(m - 1))/(-2*m + 2*n)'],
    ['S:z,4', 'elliptic_pi(n, z, m)', 'z + z**3*(m/6 + n/3) + O(z**4)'],
    ['C', 'elliptic_pi(n, m)', 'elliptic_pi(conjugate(n), conjugate(m))'],
    ['C', 'elliptic_pi(I, z, 2*I)', 'elliptic_pi(-I, conjugate(z), -2*I)'],
    ['C', 'elliptic_pi(n, z, m)', 'conjugate(elliptic_pi(n, z, m))'],
    ['N', 'elliptic_pi(1/2, 1/3)', '2.49524604707763'],
    ['N', 'elliptic_pi(1/2, 1/3, 1/4)', '0.341152767055257'],
    ['N', 'elliptic_f(1/2, 1/3)', '0.506847756265431'],
    ['N30', 'elliptic_pi(1/2 + I, 1 - I, 6/5)', '2.5023237962918172993229246469 - 0.76093957418076725495559089176*I'],
    // mpmath 1.3 at 30 digits gives 3.29136443417283236740505753981 + 0.325556349066449821172443409897*I,
    // wrong from the 26th digit (its quadrature in elliprj stops early); the value below is mpmath.quad of
    // the defining integral 1/((1 - n*sin(t)**2)*sqrt(1 - m*sin(t)**2)) over [0, pi/2] at 40 digits
    ['N30', 'elliptic_pi(1 - I/3, 2 + I)', '3.29136443417283236740505761439 + 0.325556349066449821172443359749*I'],
];

describe('elliptic integrals (SymPy elliptic_integrals)', () => {
  it.each(CASES)('%s %s', (kind, src, expected) => {
    expect(run(kind, src)).toBe(expected);
  });
  it('builds the functions with the public constructors', () => {
    const [n, z, m] = sj.symbols('n z m') as [sj.Sym, sj.Sym, sj.Sym];
    expect(String(sj.ellipticK(m))).toBe('elliptic_k(m)');
    expect(String(sj.ellipticF(z, m))).toBe('elliptic_f(z, m)');
    expect(String(sj.ellipticE(m))).toBe('elliptic_e(m)');
    expect(String(sj.ellipticE(z, m))).toBe('elliptic_e(z, m)');
    expect(String(sj.ellipticPi(n, m))).toBe('elliptic_pi(n, m)');
    expect(String(sj.ellipticPi(n, z, m))).toBe('elliptic_pi(n, z, m)');
  });
  it('gives double-precision values (mpmath)', () => {
    expect(sj.toComplex(sj.ellipticK(sj.Rational.of(1n, 3n))).re).toBeCloseTo(1.733916885257935, 14);
  });
});
