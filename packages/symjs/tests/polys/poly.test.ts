// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/poly.ts: roots, UPoly and univariate factorization; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { add, factorPoly, mul, pow, roots, solve, symbols, UPoly } from '../../src';

const { parse } = sj;
const [x] = symbols('x');
const E = sj.parse;
// the multiset of roots (the order of SymPy's dict is not part of the comparison)
const roots2 = (e: string) => sj.roots(E(e), x, { multiple: true }).map(String).sort();
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
const [a] = symbols('a b theta', { real: true });

describe('roots', () => {
  it('cubics by Cardano', () => {
    expect(roots2('x**3 + 3*x**2 + 3*x - 1')).toEqual(['-1 + 2**(1/3)', '-1 + 2**(1/3)*(-1/2 + sqrt(3)*I/2)', '-1 + 2**(1/3)*(-1/2 - sqrt(3)*I/2)']);
    expect(roots2('x**3 + 3*x**2 + 3*x + 3')).toEqual(['-1 - 2**(1/3)*(-1/2 + sqrt(3)*I/2)', '-1 - 2**(1/3)*(-1/2 - sqrt(3)*I/2)', '-2**(1/3) - 1']);
    expect(roots2('x**3 + x - 1')).toEqual(['(-1/2 - sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3) - 1/(3*(-1/2 - sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3))', '-1/(3*(-1/2 + sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3)', '-1/(3*(1/2 + sqrt(93)/18)**(1/3)) + (1/2 + sqrt(93)/18)**(1/3)']);
  });
  it('binomials and symbolic coefficients', () => {
    expect(roots2('2*x**2 + 1')).toEqual(['-sqrt(2)*I/2', 'sqrt(2)*I/2']);
    expect(roots2('2*x**4 + 1')).toEqual(['-2**(1/4)/2 + 2**(1/4)*I/2', '-2**(1/4)/2 - 2**(1/4)*I/2', '2**(1/4)/2 + 2**(1/4)*I/2', '2**(1/4)/2 - 2**(1/4)*I/2']);
    expect(roots2('x**2 + a*x + b')).toEqual(['-a/2 + sqrt(a**2 - 4*b)/2', '-a/2 - sqrt(a**2 - 4*b)/2']);
    expect(roots2('x**3 + a*x**2')).toEqual(['-a', '0', '0']);
    expect(roots2('x**2 - a')).toEqual(['-sqrt(a)', 'sqrt(a)']);
    expect(roots2('a*x + b')).toEqual(['-b/a']);
    expect(roots2('3*x**4 - x**2')).toEqual(['-sqrt(3)/3', '0', '0', 'sqrt(3)/3']);
    // SymPy roots_quartic answers with a Piecewise; not supported here
    expect(() => roots2('x**4 + a*x + b')).toThrow(sj.NotImplementedError);
    expect(() => sj.roots(E('sin(x)'), x)).toThrow(sj.PolynomialError);
  });
  it('quintics without radicals', () => {
    expect(sj.roots(E('x**5 - x - 1'), x, { multiple: true, skipQuintic: true })).toEqual([]);
    expect(() => sj.roots(E('x**5 - x - 1'), x, { multiple: true })).toThrow(sj.NotImplementedError);
  });
});

describe('UPoly and factorPoly', () => {
  it('dense rational polynomials', () => {
    const P = (e: string) => {
      const q = sj.UPoly.fromExpr(E(e), x);
      if (!q) throw new TypeError('not a polynomial');
      return q;
    };
    const zero = P('0');
    const p = P('2*x**2 + 4');
    expect(String(p.mul(zero).toExpr(x))).toBe('0');
    expect(() => p.divmod(zero)).toThrow(RangeError);
    expect(zero.monic().isZero).toBe(true);
    expect(P('3').squareFree()).toEqual([]);
    expect(String(P('5').factor().factors.length)).toBe('0');
    expect(String(zero.factor().content)).toBe('0');
    expect(String(sj.factorPoly(E('sin(x)'), x))).toBe('sin(x)');
    expect(String(sj.factorPoly(E('2*x**2 - 2'), x))).toBe('2*(x - 1)*(x + 1)');
    expect(String(sj.factorPoly(E('3*x**2 + 6'), x))).toBe('3*(x**2 + 2)');
  });
});

describe('roots with symbolic coefficients (str as in SymPy)', () => {
  const cases: [string, string[]][] = [
    ['a*x**2 + b*x + c', ['-b/(2*a) - sqrt(-4*a*c + b**2)/(2*a)', '-b/(2*a) + sqrt(-4*a*c + b**2)/(2*a)']],
    ['-a*x**2 + b*x + 1', ['b/(2*a) - sqrt(4*a + b**2)/(2*a)', 'b/(2*a) + sqrt(4*a + b**2)/(2*a)']],
    ['a*x**2 - b', ['sqrt(b/a)', '-sqrt(b/a)']],
    ['a*x**3 + x', ['0', 'sqrt(-1/a)', '-sqrt(-1/a)']],
    ['x**2 - a**2*b', ['a*sqrt(b)', '-a*sqrt(b)']],
    [
      'x**3 + a*x + b',
      [
        'a/(27*b/2 + sqrt(108*a**3 + 729*b**2)/2)**(1/3) - (27*b/2 + sqrt(108*a**3 + 729*b**2)/2)**(1/3)/3',
        'a/((-1/2 + sqrt(3)*I/2)*(27*b/2 + sqrt(108*a**3 + 729*b**2)/2)**(1/3)) - (-1/2 + sqrt(3)*I/2)*(27*b/2 + sqrt(108*a**3 + 729*b**2)/2)**(1/3)/3',
        'a/((-1/2 - sqrt(3)*I/2)*(27*b/2 + sqrt(108*a**3 + 729*b**2)/2)**(1/3)) - (-1/2 - sqrt(3)*I/2)*(27*b/2 + sqrt(108*a**3 + 729*b**2)/2)**(1/3)/3',
      ],
    ],
    [
      'x**3 + a*x**2 + b*x + c',
      [
        '-a/3 - (a**2 - 3*b)/(3*(a**3 - 9*a*b/2 + 27*c/2 + sqrt(-4*(a**2 - 3*b)**3 + (2*a**3 - 9*a*b + 27*c)**2)/2)**(1/3)) - (a**3 - 9*a*b/2 + 27*c/2 + sqrt(-4*(a**2 - 3*b)**3 + (2*a**3 - 9*a*b + 27*c)**2)/2)**(1/3)/3',
        '-a/3 - (a**2 - 3*b)/(3*(-1/2 + sqrt(3)*I/2)*(a**3 - 9*a*b/2 + 27*c/2 + sqrt(-4*(a**2 - 3*b)**3 + (2*a**3 - 9*a*b + 27*c)**2)/2)**(1/3)) - (-1/2 + sqrt(3)*I/2)*(a**3 - 9*a*b/2 + 27*c/2 + sqrt(-4*(a**2 - 3*b)**3 + (2*a**3 - 9*a*b + 27*c)**2)/2)**(1/3)/3',
        '-a/3 - (a**2 - 3*b)/(3*(-1/2 - sqrt(3)*I/2)*(a**3 - 9*a*b/2 + 27*c/2 + sqrt(-4*(a**2 - 3*b)**3 + (2*a**3 - 9*a*b + 27*c)**2)/2)**(1/3)) - (-1/2 - sqrt(3)*I/2)*(a**3 - 9*a*b/2 + 27*c/2 + sqrt(-4*(a**2 - 3*b)**3 + (2*a**3 - 9*a*b + 27*c)**2)/2)**(1/3)/3',
      ],
    ],
    [
      'x**3 + a*x - 1',
      [
        '-a/(3*(sqrt(a**3/27 + 1/4) + 1/2)**(1/3)) + (sqrt(a**3/27 + 1/4) + 1/2)**(1/3)',
        '-a/(3*(-1/2 - sqrt(3)*I/2)*(sqrt(a**3/27 + 1/4) + 1/2)**(1/3)) + (-1/2 - sqrt(3)*I/2)*(sqrt(a**3/27 + 1/4) + 1/2)**(1/3)',
        '-a/(3*(-1/2 + sqrt(3)*I/2)*(sqrt(a**3/27 + 1/4) + 1/2)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(sqrt(a**3/27 + 1/4) + 1/2)**(1/3)',
      ],
    ],
    ['x**3 + 3*a*x**2 + 3*a**2*x + b', ['-a + (a**3 - b)**(1/3)', '-a + (-1/2 - sqrt(3)*I/2)*(a**3 - b)**(1/3)', '-a + (-1/2 + sqrt(3)*I/2)*(a**3 - b)**(1/3)']],
    ['x**3 + 3*a*x**2 + 3*a**2*x + a**3 + 2', ['-a - 2**(1/3)', '-a - 2**(1/3)*(-1/2 - sqrt(3)*I/2)', '-a - 2**(1/3)*(-1/2 + sqrt(3)*I/2)']],
    ['x**3 + 3*x**2 + b*x + b - 2', ['-1', 'sqrt(3 - b) - 1', '-sqrt(3 - b) - 1']],
    ['x**3 - a', ['a**(1/3)', '-a**(1/3)/2 - sqrt(3)*I*a**(1/3)/2', '-a**(1/3)/2 + sqrt(3)*I*a**(1/3)/2']],
    ['x**3 + a', ['(-a)**(1/3)', '-(-a)**(1/3)/2 - sqrt(3)*I*(-a)**(1/3)/2', '-(-a)**(1/3)/2 + sqrt(3)*I*(-a)**(1/3)/2']],
    ['2*x**3 - a', ['2**(2/3)*a**(1/3)/2', '-2**(2/3)*a**(1/3)/4 - 2**(2/3)*sqrt(3)*I*a**(1/3)/4', '-2**(2/3)*a**(1/3)/4 + 2**(2/3)*sqrt(3)*I*a**(1/3)/4']],
    ['x**4 - a', ['-a**(1/4)', 'a**(1/4)', '-I*a**(1/4)', 'I*a**(1/4)']],
    [
      'x**5 - a',
      [
        'a**(1/5)',
        '-sqrt(5)*a**(1/5)/4 - a**(1/5)/4 - I*a**(1/5)*sqrt(5/8 - sqrt(5)/8)',
        '-sqrt(5)*a**(1/5)/4 - a**(1/5)/4 + I*a**(1/5)*sqrt(5/8 - sqrt(5)/8)',
        '-a**(1/5)/4 + sqrt(5)*a**(1/5)/4 - I*a**(1/5)*sqrt(sqrt(5)/8 + 5/8)',
        '-a**(1/5)/4 + sqrt(5)*a**(1/5)/4 + I*a**(1/5)*sqrt(sqrt(5)/8 + 5/8)',
      ],
    ],
    ['x**4 + a*x**2 + b', ['sqrt(-a/2 - sqrt(a**2 - 4*b)/2)', 'sqrt(-a/2 + sqrt(a**2 - 4*b)/2)', '-sqrt(-a/2 - sqrt(a**2 - 4*b)/2)', '-sqrt(-a/2 + sqrt(a**2 - 4*b)/2)']],
  ];
  it.each(cases)('roots(%s)', (e, r) => {
    expect(roots2(e)).toEqual([...r].sort());
  });
});

describe('UPoly (deprecated dense univariate polynomial)', () => {
  const U = (e: string) => {
    const p = sj.UPoly.fromExpr(parse(e), x);
    if (!p) throw new TypeError('not a polynomial');
    return p;
  };
  it('leading coefficient, sums, values and rational roots', () => {
    // Poly(0, x).LC() -> 0
    expect(String(new sj.UPoly([]).lc)).toBe('0');
    expect(String(U('x**3 + 1').add(U('2*x')).toExpr(x))).toBe('x**3 + 2*x + 1');
    expect(String(U('2*x').add(U('x**3 + 1')).toExpr(x))).toBe('x**3 + 2*x + 1');
    expect(String(U('2*x**3 - x + 5').evalAt(sj.Rational.of(1n, 2n)))).toBe('19/4');
    // roots(f, filter='Q'): {-3: 1, 1/2: 1, 0: 1} and {2/3: 1}
    expect(show(U('(2*x - 1)*(x + 3)*(x**2 + 1)*x').rationalRoots())).toBe('[-3, 0, 1/2]');
    expect(show(U('(x**2 - 2)**2*(3*x - 2)').rationalRoots())).toBe('[2/3]');
    expect(show(U('5').rationalRoots())).toBe('[]');
  });
});

describe('roots with symbolic coefficients (SymPy roots(f, x))', () => {
  const a = new sj.Sym('a', { positive: true });
  const c = (s: string) => sj.subs(parse(s), [[new sj.Sym('a'), a]]);
  const keys = (f: string) => [...sj.roots(c(f), x).keys()];
  it('binomials and quadratics', () => {
    expect(show(keys('x**2 + a'))).toBe('[-I*sqrt(a), I*sqrt(a)]');
    expect(show(keys('-a*x**2 + b*x + c'))).toBe('[b/(2*a) - sqrt(4*a*c + b**2)/(2*a), b/(2*a) + sqrt(4*a*c + b**2)/(2*a)]');
    // multiple=True lists the roots in ordered() order
    expect(show(sj.roots(c('x**2 + a'), x, { multiple: true }))).toBe('[I*sqrt(a), -I*sqrt(a)]');
    expect(show(sj.roots(parse('(x - 1)**2*(x + 2)'), x, { multiple: true }))).toBe('[-2, 1, 1]');
  });
  it.each([
    // SymPy writes (-1)**(5/6)*sqrt(3) and (-1)**(3/4) where symjs keeps I*(-1)**(1/3) and I*(-1)**(1/4)
    // (the core does not merge I with powers of -1), so the roots are compared at a = 2
    ['x**3 + a', '[-1.25992104989487, 0.629960524947437 - 1.09112363597172*I, 0.629960524947437 + 1.09112363597172*I]'],
    [
      'x**4 + a',
      '[-0.840896415253715 - 0.840896415253715*I, -0.840896415253715 + 0.840896415253715*I, 0.840896415253715 - 0.840896415253715*I, 0.840896415253715 + 0.840896415253715*I]',
    ],
  ])('roots(%s) at a = 2', (f, expected) => {
    expect(show(keys(f).map((r) => sj.evalf(sj.subs(r, [[a, sj.Rational.of(2n)]]), 15)))).toBe(expected);
  });
});

describe('deprecated factorPoly', () => {
  it('a single factor', () => {
    const x = new sj.Sym('x');
    expect(String(sj.factorPoly(parse('(x + 1)**2'), x))).toBe('(x + 1)**2');
    expect(String(sj.factorPoly(parse('x**2 - 1'), x))).toBe('(x - 1)*(x + 1)');
  });
});

describe('polynomials', () => {
  it('finds roots', () => {
    expect(roots(add(pow(x, 2), -1), x, { multiple: true }).map(String)).toEqual(['-1', '1']);
    // SymPy roots(..., multiple=True) lists the roots in ordered() order: [sqrt(2), -sqrt(2)], [I, -I]
    expect(roots(add(pow(x, 2), -2), x, { multiple: true }).map(String)).toEqual(['sqrt(2)', '-sqrt(2)']);
    expect(roots(add(pow(x, 2), 1), x, { multiple: true }).map(String)).toEqual(['I', '-I']);
    expect(solve(add(pow(x, 3), mul(-6, pow(x, 2)), mul(11, x), -6), x).map(String)).toEqual(['1', '2', '3']);
    expect(solve(add(mul(a, pow(x, 2)), mul(-1, a)), x).map(String)).toEqual(['-1', '1']);
  });

  it('computes gcd and factors', () => {
    const p = UPoly.fromExpr(add(pow(x, 2), -1), x)!;
    const q = UPoly.fromExpr(add(pow(x, 2), mul(2, x), 1), x)!;
    expect(p.gcd(q).toExpr(x).toString()).toBe('x + 1');
    expect(factorPoly(add(pow(x, 3), mul(-1, x)), x).toString()).toBe('x*(x - 1)*(x + 1)');
  });
});
