// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/special/zetafunctions.ts.
//
// lerchphi, polylog, dirichlet_eta, riemann_xi and stieltjes, and the rewrites and expansions of the
// Riemann and Hurwitz zeta functions. Expected values are str() results of SymPy 1.14 (mpmath 1.3 for
// the numerics) unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';

const locals = {
  p: new sj.Sym('p', { positive: true }),
  ni: new sj.Sym('ni', { integer: true, negative: true }),
  nn: new sj.Sym('nn', { negative: true }),
  ip: new sj.Sym('ip', { integer: true, positive: true }),
  exp_polar: sj.expPolar,
  polar_lift: sj.polarLift,
};
const P = (src: string): sj.Expr => sj.parse(src, { locals });

/** str() of the SymPy operation named by kind applied to src. */
export function run(kind: string, src: string): string {
  const e = P(src);
  if (kind === 'E') return String(e);
  if (kind === 'F') return String(sj.expandFunc(e));
  if (kind === 'C') return String(sj.conjugate(e));
  if (kind === 'D') return String(sj.diff(e, new sj.Sym('x')));
  if (kind.startsWith('D:')) return String(sj.diff(e, new sj.Sym(kind.slice(2))));
  if (kind.startsWith('RW:')) return String(sj.rewrite(e, kind.slice(3)));
  if (kind.startsWith('S:')) {
    const [v = '', n = ''] = kind.slice(2).split(',');
    return String(sj.series(e, new sj.Sym(v), 0, Number(n)));
  }
  // N or N<digits>: evalf
  return String(sj.evalf(e, kind.length > 1 ? Number(kind.slice(1)) : 15));
}

type Case = [kind: string, src: string, expected: string];
const CASES: Case[] = [
    ['E', 'polylog(s, 0)', '0'],
    ['E', 'polylog(s, 1)', 'zeta(s)'],
    ['E', 'polylog(s, -1)', '-dirichlet_eta(s)'],
    ['E', 'polylog(2, 1/2)', '-log(2)**2/2 + pi**2/12'],
    ['E', 'polylog(2, 2)', 'pi**2/4 - I*pi*log(2)'],
    ['E', 'polylog(2, I)', '-pi**2/48 + Catalan*I'],
    ['E', 'polylog(2, -I)', '-pi**2/48 - Catalan*I'],
    ['E', 'polylog(2, 1 - I)', 'pi**2/16 - Catalan*I - I*pi*log(2)/4'],
    ['E', 'polylog(2, 1 + I)', 'pi**2/16 + I*pi*log(2)/4 + Catalan*I'],
    ['E', 'polylog(2, (1 - I)/2)', '-log(2)**2/8 + 5*pi**2/96 - Catalan*I + I*pi*log(2)/8'],
    ['E', 'polylog(2, -(sqrt(5) - 1)/2)', '-pi**2/15 + log(-1/2 + sqrt(5)/2)**2/2'],
    ['E', 'polylog(2, -(sqrt(5) + 1)/2)', '-pi**2/10 - log(1/2 + sqrt(5)/2)**2'],
    ['E', 'polylog(2, (3 - sqrt(5))/2)', '-log(-1/2 + sqrt(5)/2)**2 + pi**2/15'],
    ['E', 'polylog(2, (sqrt(5) - 1)/2)', '-log(-1/2 + sqrt(5)/2)**2 + pi**2/10'],
    ['E', 'polylog(2, 3)', 'polylog(2, 3)'],
    ['E', 'polylog(0, 3)', '-3/2'],
    ['E', 'polylog(-1, 3)', '3/4'],
    ['E', 'polylog(0, z)', 'z/(1 - z)'],
    ['E', 'polylog(s, exp_polar(I*pi)/2)', 'polylog(s, -1/2)'],
    ['E', 'polylog(s, 2*exp_polar(I*pi))', 'polylog(s, 2*exp_polar(I*pi))'],
    ['D:z', 'polylog(s, z)', 'polylog(s - 1, z)/z'],
    ['D:s', 'polylog(s, z)', 'Derivative(polylog(s, z), s)'],
    ['D', 'polylog(x**2, z)', '2*x*Subs(Derivative(polylog(_xi_1, z), _xi_1), _xi_1, x**2)'],
    ['RW:lerchphi', 'polylog(s, z)', 'z*lerchphi(z, s, 1)'],
    ['F', 'polylog(1, z)', '-log(1 - z)'],
    ['F', 'polylog(-2, z)', '2*z**3/(1 - z)**3 + 3*z**2/(1 - z)**2 + z/(1 - z)'],
    ['F', 'polylog(0, z)', 'z/(1 - z)'],
    ['F', 'polylog(s, z)', 'polylog(s, z)'],
    ['D:z', 'lerchphi(z, s, a)', '(-a*lerchphi(z, s, a) + lerchphi(z, s - 1, a))/z'],
    ['D:a', 'lerchphi(z, s, a)', '-s*lerchphi(z, s + 1, a)'],
    ['D:s', 'lerchphi(z, s, a)', 'Derivative(lerchphi(z, s, a), s)'],
    ['F', 'lerchphi(1, s, a)', 'zeta(s, a)'],
    ['F', 'lerchphi(z, -2, a)', 'a**2/(1 - z) + 2*a*z/(1 - z)**2 + z*(2*z/(1 - z)**3 + (1 - z)**(-2))'],
    ['F', 'lerchphi(z, s, 1/2)', '2**(s - 1)*(polylog(s, sqrt(z))/sqrt(z) - polylog(s, sqrt(z)*exp_polar(I*pi))/sqrt(z))'],
    ['F', 'lerchphi(z, s, 3/2)', '-2**s/z + 2**(s - 1)*(polylog(s, sqrt(z))/sqrt(z) - polylog(s, sqrt(z)*exp_polar(I*pi))/sqrt(z))/z'],
    ['F', 'lerchphi(z, s, 2)', '-1/z + polylog(s, z)/z**2'],
    ['F', 'lerchphi(z, s, -1/2)', '2**(s - 1)*z*(polylog(s, sqrt(z))/sqrt(z) - polylog(s, sqrt(z)*exp_polar(I*pi))/sqrt(z)) + (-1/2)**(-s)'],
    ['F', 'lerchphi(z, s, 0)', 'zoo**s + polylog(s, z)'],
    ['F', 'lerchphi(z, 2, 1/3)', '3*polylog(2, z**(1/3))/z**(1/3) + 3*exp(-2*I*pi/3)*polylog(2, z**(1/3)*exp_polar(2*I*pi/3))/z**(1/3) + 3*exp(2*I*pi/3)*polylog(2, z**(1/3)*exp_polar(4*I*pi/3))/z**(1/3)'],
    ['F', 'lerchphi(-1, s, a)', 'zeta(s, a/2)/2**s - zeta(s, a/2 + 1/2)/2**s'],
    ['F', 'lerchphi(I, s, a)', 'zeta(s, a/4)/4**s + I*zeta(s, a/4 + 1/4)/4**s - zeta(s, a/4 + 1/2)/4**s - I*zeta(s, a/4 + 3/4)/4**s'],
    ['F', 'lerchphi(-I, s, a)', 'zeta(s, a/4)/4**s - I*zeta(s, a/4 + 1/4)/4**s - zeta(s, a/4 + 1/2)/4**s + I*zeta(s, a/4 + 3/4)/4**s'],
    ['F', 'lerchphi(exp(I*pi/3), s, a)', 'zeta(s, a/6)/6**s + exp(I*pi/3)*zeta(s, a/6 + 1/6)/6**s + exp(2*I*pi/3)*zeta(s, a/6 + 1/3)/6**s - zeta(s, a/6 + 1/2)/6**s + exp(-2*I*pi/3)*zeta(s, a/6 + 2/3)/6**s + exp(-I*pi/3)*zeta(s, a/6 + 5/6)/6**s'],
    ['F', 'lerchphi(z, s, a)', 'lerchphi(z, s, a)'],
    ['RW:zeta', 'lerchphi(1, s, a)', 'zeta(s, a)'],
    ['RW:polylog', 'lerchphi(z, s, 1)', 'polylog(s, z)/z'],
    ['RW:zeta', 'lerchphi(z, s, a)', 'lerchphi(z, s, a)'],
    ['RW:dirichlet_eta', 'zeta(s)', 'dirichlet_eta(s)/(1 - 2**(1 - s))'],
    ['RW:dirichlet_eta', 'zeta(s, a)', 'zeta(s, a)'],
    ['RW:lerchphi', 'zeta(s)', 'lerchphi(1, s, 1)'],
    ['RW:lerchphi', 'zeta(s, a)', 'lerchphi(1, s, a)'],
    ['D:a', 'zeta(s, a)', '-s*zeta(s + 1, a)'],
    ['D:s', 'zeta(s, a)', 'Derivative(zeta(s, a), s)'],
    ['E', 'zeta(s, 1)', 'zeta(s)'],
    ['E', 'zeta(2, 3)', '-5/4 + pi**2/6'],
    ['E', 'zeta(-1, a)', '-a**2/2 + a/2 - 1/12'],
    ['E', 'zeta(0, a)', '1/2 - a'],
    ['E', 'zeta(1, a)', 'zoo'],
    ['E', 'zeta(nan, a)', 'nan'],
    ['E', 'zeta(oo)', '1'],
    ['E', 'zeta(s, oo)', '0'],
    ['E', 'zeta(s, -2)', 'zeta(s, -2)'],
    ['E', 'zeta(1/2, -2)', 'nan'],
    ['E', 'zeta(nan)', 'nan'],
    ['F', 'zeta(s, 3)', 'zeta(s) - 1 - 1/2**s'],
    ['F', 'zeta(s, a)', 'zeta(s, a)'],
    ['F', 'zeta(s)', 'zeta(s)'],
    ['F', 'zeta(p, ni)', 'nan'],
    ['F', 'zeta(s, ni)', 'zeta(s, ni)'],
    ['E', 'dirichlet_eta(s, 1)', 'dirichlet_eta(s)'],
    ['E', 'dirichlet_eta(1)', 'log(2)'],
    ['E', 'dirichlet_eta(2)', 'pi**2/12'],
    ['E', 'dirichlet_eta(s)', 'dirichlet_eta(s)'],
    ['E', 'dirichlet_eta(1, a)', '-polygamma(0, a) + polygamma(0, a/2 + 1/2) + log(2)'],
    ['E', 'dirichlet_eta(2, 3)', '-3/4 + pi**2/12'],
    ['E', 'dirichlet_eta(s, a)', 'dirichlet_eta(s, a)'],
    ['RW:zeta', 'dirichlet_eta(s)', 'Piecewise((log(2), Eq(s, 1)), ((1 - 2**(1 - s))*zeta(s), True))'],
    ['RW:zeta', 'dirichlet_eta(s, a)', 'Piecewise((-polygamma(0, a) + polygamma(0, a/2 + 1/2) + log(2), Eq(s, 1)), (-2**(1 - s)*zeta(s, a/2 + 1/2) + zeta(s, a), True))'],
    ['N', 'dirichlet_eta(2, 1/3)', '8.56365942074773'],
    ['N', 'dirichlet_eta(3)', '0.901542677369696'],
    ['N30', 'dirichlet_eta(1/2)', '0.604898643421630370247265914236'],
    ['E', 'riemann_xi(0)', '1/2'],
    ['E', 'riemann_xi(1)', '1/2'],
    ['E', 'riemann_xi(2)', 'pi/6'],
    ['E', 'riemann_xi(s)', 'riemann_xi(s)'],
    ['RW:zeta', 'riemann_xi(s)', 's*(s - 1)*gamma(s/2)*zeta(s)/(2*pi**(s/2))'],
    // riemann_xi has no numeric implementation: evalf leaves it (as SymPy does) unless zeta evaluates
    ['N', 'riemann_xi(3)', 'riemann_xi(3)'],
    ['N30', 'riemann_xi(5/2)', 'riemann_xi(5/2)'],
    ['N', 'riemann_xi(3.0)', '0.573939894046755'],
    ['N', 'polylog(2, 1/3)', '0.366213229977064'],
    ['N', 'polylog(3, 1 + 2*I)', '0.436491807899422 + 2.1831024188651*I'],
    ['N', 'lerchphi(1/2, 2, 3)', '0.157924211720100'],
    ['E', 'stieltjes(n)', 'stieltjes(n)'],
    ['E', 'stieltjes(0)', 'EulerGamma'],
    ['E', 'stieltjes(0, 1)', 'EulerGamma'],
    ['E', 'stieltjes(n, m)', 'stieltjes(n, m)'],
    ['E', 'stieltjes(-1)', 'zoo'],
    ['E', 'stieltjes(1/2)', 'zoo'],
    ['E', 'stieltjes(nan)', 'nan'],
    ['E', 'stieltjes(1, nan)', 'nan'],
    ['E', 'stieltjes(1, -2)', 'zoo'],
    ['E', 'stieltjes(0, 2)', 'stieltjes(0, 2)'],
    ['E', 'stieltjes(nn)', 'zoo'],
    ['E', 'stieltjes(1)', 'stieltjes(1)'],
    ['F', 'zeta(s, p)', 'zeta(s, p)'],
    ['F', 'zeta(s, ip)', '-harmonic(ip - 1, s) + zeta(s)'],
    ['E', 'polylog(-1, z)', 'z/(1 - z)**2'],
    ['E', 'polylog(0, stieltjes(1))', 'stieltjes(1)/(1 - stieltjes(1))'],
    ['E', 'polylog(0.0, z)', 'z/(1 - z)'],
    ['E', 'polylog(s, 0.0)', '0'],
    ['E', 'stieltjes(I)', 'zoo'],
    ['E', 'stieltjes(0.0)', 'zoo'],
    ['E', 'stieltjes(pi)', 'zoo'],
    ['E', 'polylog(0, oo)', 'nan'],
    ['E', 'polylog(s, polar_lift(1/3 + I/2))', 'polylog(s, 1/3 + I/2)'],
    ['F', 'lerchphi(exp(I*x), s, a)', 'lerchphi(exp(I*x), s, a)'],
    ['F', 'lerchphi(-1, 2, 1/2)', '2*I*(-pi**2/48 - Catalan*I) - 2*I*(-pi**2/48 + Catalan*I)'],
    ['F', 'lerchphi(z, s, 7/3)', '-3**s/z**2 + 3**(s - 1)*(polylog(s, z**(1/3))/z**(1/3) + exp(-2*I*pi/3)*polylog(s, z**(1/3)*exp_polar(2*I*pi/3))/z**(1/3) + exp(2*I*pi/3)*polylog(s, z**(1/3)*exp_polar(4*I*pi/3))/z**(1/3))/z**2 - 1/((4/3)**s*z)'],
    ['F', 'lerchphi(z, s, -5/3)', '3**(s - 1)*z**2*(polylog(s, z**(1/3))/z**(1/3) + exp(-2*I*pi/3)*polylog(s, z**(1/3)*exp_polar(2*I*pi/3))/z**(1/3) + exp(2*I*pi/3)*polylog(s, z**(1/3)*exp_polar(4*I*pi/3))/z**(1/3)) + (-5/3)**(-s) + z/(-2/3)**s'],
    ['E', 'polylog(s, exp_polar(2*I*pi))', 'zeta(s)'],
    ['E', 'polylog(s, cos(1)**2 + sin(1)**2)', 'zeta(s)'],
    ['E', 'polylog(0, 1.0)', '-1/2'],
];

describe('zeta functions (SymPy zeta_functions)', () => {
  it.each(CASES)('%s %s', (kind, src, expected) => {
    expect(run(kind, src)).toBe(expected);
  });
});

describe('constructors and numeric values', () => {
  const [s, z, a] = sj.symbols('s z a') as [sj.Sym, sj.Sym, sj.Sym];
  it('builds the functions like SymPy', () => {
    expect(String(sj.lerchphi(z, s, a))).toBe('lerchphi(z, s, a)');
    expect(String(sj.polylog(s, z))).toBe('polylog(s, z)');
    expect(String(sj.dirichletEta(s))).toBe('dirichlet_eta(s)');
    expect(String(sj.dirichletEta(s, a))).toBe('dirichlet_eta(s, a)');
    expect(String(sj.riemannXi(s))).toBe('riemann_xi(s)');
    expect(String(sj.stieltjes(s))).toBe('stieltjes(s)');
    expect(String(sj.stieltjes(s, a))).toBe('stieltjes(s, a)');
    expect(String(sj.zeta(s, a))).toBe('zeta(s, a)');
  });
  it('evaluates dirichlet_eta(1, a) = log(2) - digamma(a) + digamma((a + 1)/2) numerically', () => {
    // (dirichlet_eta(1, a) evaluates symbolically; the numeric rule is reached by an unevaluated node)
    expect(String(sj.evalf(new sj.Fn('dirichlet_eta', [sj.S.One, sj.Rational.of(1n, 3n)])))).toBe('2.50694654479416');
  });
  it('gives double-precision values (mpmath)', () => {
    const v = (e: sj.Expr) => sj.toComplex(e).re;
    expect(v(sj.polylog(2, sj.Rational.of(1n, 3n)))).toBeCloseTo(0.3662132299770635, 14);
    expect(v(sj.lerchphi(sj.Rational.of(1n, 2n), 2, 3))).toBeCloseTo(0.15792421172010004, 14);
    expect(v(new sj.Fn('dirichlet_eta', [sj.Rational.of(3n)]))).toBeCloseTo(0.9015426773696957, 14);
    // no numeric riemann_xi (SymPy's lambdify raises NameError: mpmath has none)
    expect(() => v(new sj.Fn('riemann_xi', [sj.Rational.of(3n)]))).toThrow('Cannot evaluate riemann_xi numerically');
  });
});
