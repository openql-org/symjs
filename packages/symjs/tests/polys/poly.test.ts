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

describe('roots of symbolic quartics (SymPy roots_quartic)', () => {
  const items = (f: string) => `[${[...sj.roots(sj.expand(parse(f)), x).entries()].map(([r, k]) => `(${String(r)}, ${k})`).join(', ')}]`;
  // SymPy roots(f, x).items()
  it.each([
    ["x**4 + a*x + 1", "[(-sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2 + sqrt(2*a/sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3))) - 2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) - 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2, 1), (-sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2 - sqrt(2*a/sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3))) - 2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) - 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2, 1), (sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2 + sqrt(-2*a/sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3))) - 2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) - 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2, 1), (sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2 - sqrt(-2*a/sqrt(2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) + 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3))) - 2*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3) - 2/(3*(a**2/16 + sqrt(a**4/256 - 1/27))**(1/3)))/2, 1)]"],
    ["x**4 + a*x + b", "[(Piecewise((-sqrt(-(-a**2)**(1/3))/2 + sqrt(2*a/sqrt(-(-a**2)**(1/3)) + (-a**2)**(1/3))/2, Eq(b, 0)), (-sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2 + sqrt(2*a/sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2, True)), 1), (Piecewise((-sqrt(-(-a**2)**(1/3))/2 - sqrt(2*a/sqrt(-(-a**2)**(1/3)) + (-a**2)**(1/3))/2, Eq(b, 0)), (-sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2 - sqrt(2*a/sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2, True)), 1), (Piecewise((sqrt(-(-a**2)**(1/3))/2 + sqrt(-2*a/sqrt(-(-a**2)**(1/3)) + (-a**2)**(1/3))/2, Eq(b, 0)), (sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2 + sqrt(-2*a/sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2, True)), 1), (Piecewise((sqrt(-(-a**2)**(1/3))/2 - sqrt(-2*a/sqrt(-(-a**2)**(1/3)) + (-a**2)**(1/3))/2, Eq(b, 0)), (sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2 - sqrt(-2*a/sqrt(2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) + 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*b/(3*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3)) - 2*(a**2/16 + sqrt(a**4/256 - b**3/27))**(1/3))/2, True)), 1)]"],
    ["x**4 + 4*x**3 + (6+b)*x**2 + (5+2*b)*x + b + 2", "[(-1, 1), (b/(sqrt(108*b**3 + 729)/2 + 27/2)**(1/3) - (sqrt(108*b**3 + 729)/2 + 27/2)**(1/3)/3 - 1, 1), (b/((-1/2 + sqrt(3)*I/2)*(sqrt(108*b**3 + 729)/2 + 27/2)**(1/3)) - (-1/2 + sqrt(3)*I/2)*(sqrt(108*b**3 + 729)/2 + 27/2)**(1/3)/3 - 1, 1), (b/((-1/2 - sqrt(3)*I/2)*(sqrt(108*b**3 + 729)/2 + 27/2)**(1/3)) - (-1/2 - sqrt(3)*I/2)*(sqrt(108*b**3 + 729)/2 + 27/2)**(1/3)/3 - 1, 1)]"],
    ["x**4 + 6*x**2 + a*x - 3", "[(-sqrt(-2*(-a**2/8 - 8)**(1/3) - 4)/2 + sqrt(2*a/sqrt(-2*(-a**2/8 - 8)**(1/3) - 4) + 2*(-a**2/8 - 8)**(1/3) - 8)/2, 1), (-sqrt(-2*(-a**2/8 - 8)**(1/3) - 4)/2 - sqrt(2*a/sqrt(-2*(-a**2/8 - 8)**(1/3) - 4) + 2*(-a**2/8 - 8)**(1/3) - 8)/2, 1), (sqrt(-2*(-a**2/8 - 8)**(1/3) - 4)/2 + sqrt(-2*a/sqrt(-2*(-a**2/8 - 8)**(1/3) - 4) + 2*(-a**2/8 - 8)**(1/3) - 8)/2, 1), (sqrt(-2*(-a**2/8 - 8)**(1/3) - 4)/2 - sqrt(-2*a/sqrt(-2*(-a**2/8 - 8)**(1/3) - 4) + 2*(-a**2/8 - 8)**(1/3) - 8)/2, 1)]"],
    ["x**4 - 2*x**2 + a*x", "[(-(27*a/2 + sqrt(729*a**2 - 864)/2)**(1/3)/3 - 2/(27*a/2 + sqrt(729*a**2 - 864)/2)**(1/3), 1), (-(-1/2 + sqrt(3)*I/2)*(27*a/2 + sqrt(729*a**2 - 864)/2)**(1/3)/3 - 2/((-1/2 + sqrt(3)*I/2)*(27*a/2 + sqrt(729*a**2 - 864)/2)**(1/3)), 1), (-(-1/2 - sqrt(3)*I/2)*(27*a/2 + sqrt(729*a**2 - 864)/2)**(1/3)/3 - 2/((-1/2 - sqrt(3)*I/2)*(27*a/2 + sqrt(729*a**2 - 864)/2)**(1/3)), 1), (0, 1)]"],
    ["x**4 + a*x**2 + x + 1", "[(Piecewise((-sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3))/2 + sqrt(-4*a/3 + 2*(-a**3/108 + a/3 - 1/8)**(1/3) + 2/sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3)))/2, Eq(a**2, -12)), (-sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3))/2 + sqrt(-4*a/3 + 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) - 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3) + 2/sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)))/2, True)), 1), (Piecewise((-sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3))/2 - sqrt(-4*a/3 + 2*(-a**3/108 + a/3 - 1/8)**(1/3) + 2/sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3)))/2, Eq(a**2, -12)), (-sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3))/2 - sqrt(-4*a/3 + 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) - 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3) + 2/sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)))/2, True)), 1), (Piecewise((sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3))/2 + sqrt(-4*a/3 + 2*(-a**3/108 + a/3 - 1/8)**(1/3) - 2/sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3)))/2, Eq(a**2, -12)), (sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3))/2 + sqrt(-4*a/3 + 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) - 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3) - 2/sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)))/2, True)), 1), (Piecewise((sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3))/2 - sqrt(-4*a/3 + 2*(-a**3/108 + a/3 - 1/8)**(1/3) - 2/sqrt(-2*a/3 - 2*(-a**3/108 + a/3 - 1/8)**(1/3)))/2, Eq(a**2, -12)), (sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3))/2 - sqrt(-4*a/3 + 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) - 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3) - 2/sqrt(-2*a/3 - 2*(-a**2/12 - 1)/(3*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)) + 2*(a**3/216 - a/6 + sqrt((-a**2/12 - 1)**3/27 + (-a**3/108 + a/3 - 1/8)**2/4) + 1/16)**(1/3)))/2, True)), 1)]"],
  ])('roots(%s)', (f, expected) => {
    expect(items(f)).toBe(expected);
  });
  // the same roots as SymPy in another order or form (compared at a = 3/2, b = 5/7)
  const at = (r: sj.Expr) => sj.evalf(sj.subs(r, [[new sj.Sym('a'), sj.Rational.of(3n, 2n)], [new sj.Sym('b'), sj.Rational.of(5n, 7n)]]), 12);
  const numeric = (f: string) => [...sj.roots(sj.expand(parse(f)), x).keys()].map((r) => String(at(r))).sort();
  it('the biquadratic shift, the quasisymmetric case and a rational resolvent root', () => {
    // SymPy: -a - sqrt(-sqrt(-b)), -a + sqrt(-sqrt(-b)), -a - (-b)**(1/4), -a + (-b)**(1/4)
    expect(numeric('x**4 + 4*a*x**3 + 6*a**2*x**2 + 4*a**3*x + a**4 + b')).toEqual(
      ['-a - sqrt(-sqrt(-b))', '-a + sqrt(-sqrt(-b))', '-a - (-b)**(1/4)', '-a + (-b)**(1/4)'].map((r) => String(at(parse(r)))).sort(),
    );
    // SymPy: -a/4 -+ sqrt((a +- sqrt(a**2 - 4*b + 8))**2/4 - 4)/2 -+ sqrt(a**2 - 4*b + 8)/4
    const s = 'sqrt(a**2 - 4*b + 8)';
    expect(numeric('x**4 + a*x**3 + b*x**2 + a*x + 1')).toEqual(
      [`-a/4 - sqrt((a + ${s})**2/4 - 4)/2 - ${s}/4`, `-a/4 + sqrt((a + ${s})**2/4 - 4)/2 - ${s}/4`, `-a/4 - sqrt((a - ${s})**2/4 - 4)/2 + ${s}/4`, `-a/4 + sqrt((a - ${s})**2/4 - 4)/2 + ${s}/4`]
        .map((r) => String(at(parse(r))))
        .sort(),
    );
    // SymPy: {1 - a: 1, -a - 1: 1, -a - I: 1, -a + I: 1} (it factors over ZZ[a]; symjs finds the roots by Descartes-Euler)
    expect(numeric('x**4 + 4*a*x**3 + 6*a**2*x**2 + 4*a**3*x + a**4 - 1')).toEqual(['1 - a', '-a - 1', '-a - I', '-a + I'].map((r) => String(at(parse(r)))).sort());
    // a rational resolvent root after the shift (SymPy _roots_quartic_euler)
    expect(items('(x + a)**4 - 64*(x + a)**2/5 - 512*(x + a)/125 - 1024/3125')).toBe(
      '[(-a - sqrt(32*sqrt(5)/125 + 16/5) + 4*sqrt(5)/5, 1), (-a - 4*sqrt(5)/5 - sqrt(16/5 - 32*sqrt(5)/125), 1), (-a - 4*sqrt(5)/5 + sqrt(16/5 - 32*sqrt(5)/125), 1), (-a + 4*sqrt(5)/5 + sqrt(32*sqrt(5)/125 + 16/5), 1)]',
    );
    // SymPy roots(x**4 + x - a, x): Piecewise((..., Eq(a, 0)), (..., True)) for every root
    expect([...sj.roots(parse('x**4 + x - a'), x).keys()].map((r) => String(at(r)))).toHaveLength(4);
    expect([...sj.roots(parse('x**4 + x - a'), x).keys()].every((r) => r instanceof sj.Piecewise && String(r.args[1]) === 'Eq(a, 0)')).toBe(true);
    // roots at -a/4 (cubic) and -a/3 (quadratic) that factor() does not split off; SymPy factors them:
    // {-a: 1, -a - sqrt(-a**3 + a**2 - 1): 1, -a + sqrt(-a**3 + a**2 - 1): 1}
    expect(numeric('(t + a)*(t**2 + 2*a*t + a**3 + 1)'.replace(/t/g, 'x'))).toEqual(['-a', '-a - sqrt(-a**3 + a**2 - 1)', '-a + sqrt(-a**3 + a**2 - 1)'].map((r) => String(at(parse(r)))).sort());
    expect(numeric('(x + a)*(x**3 + 3*a*x**2 + x + a**3 + 1)')).toContain(String(at(parse('-a'))));
    // a rational resolvent without a rational root: Ferrari's method (SymPy: the same four roots)
    const s687 = '(1/16 + sqrt(687)*I/144)**(1/3)';
    const w = `sqrt(2/(3*${s687}) + 2*${s687})`;
    expect(numeric('(x + a)**4 + (x + a) + 1')).toEqual(
      [`-a + sqrt(-2*${s687} + 2/${w} - 2/(3*${s687}))/2 - ${w}/2`, `-a - ${w}/2 - sqrt(-2*${s687} + 2/${w} - 2/(3*${s687}))/2`, `-a + sqrt(-2*${s687} - 2/${w} - 2/(3*${s687}))/2 + ${w}/2`, `-a + ${w}/2 - sqrt(-2*${s687} - 2/${w} - 2/(3*${s687}))/2`]
        .map((r) => String(at(parse(r))))
        .sort(),
    );
    // SymPy roots(x**5 + a*x + 1, x) = {} (no formula)
    expect(() => sj.roots(parse('x**5 + a*x + 1'), x)).toThrow(sj.NotImplementedError);
  });
});

describe('roots over composite and EX coefficient domains (SymPy roots_linear, roots_quadratic)', () => {
  const [t] = symbols('t');
  const keys = (e: string, v = t) => show([...sj.roots(parse(e), v).keys()]);
  it('a linear root is factored over a polynomial ring and simplified over EX', () => {
    expect(keys('2.0*x*y - 1', x)).toBe('[0.5/y]');
    expect(keys('x*(exp(y) + 1)**2 - 1', x)).toBe('[(exp(y) + 1)**(-2)]');
    // gens x and f(x) are related: EX
    expect(keys('x*t + f(x) - x**2*f(x)**3')).toBe('[x*f(x)**3 - f(x)/x]');
    expect(keys('t - f(x) - x*f(x)**2')).toBe('[(x*f(x) + 1)*f(x)]');
    expect(keys('t + 2*x*f(x) - x')).toBe('[x*(1 - 2*f(x))]');
    expect(keys('t - exp(x - f(x))')).toBe('[exp(x - f(x))]');
    expect(keys('x*t + Derivative(f(x), x) + f(x)**2')).toBe('[(-f(x)**2 - Derivative(f(x), x))/x]');
    expect(keys('sqrt(2)*t - y')).toBe('[sqrt(2)*y/2]');
    expect(keys('t*f(x) - f(x)*sin(x)**2 - f(x)*cos(x)**2')).toBe('[1]');
    expect(keys('t - x*exp(f(x))')).toBe('[x*exp(f(x))]');
    expect(keys('t - exp(x)*exp(f(x))')).toBe('[exp(x + f(x))]');
  });
  it('a quadratic over EX', () => {
    // SymPy roots(t**2 - (1 + sqrt(2)), t): {-sqrt(1 + sqrt(2)): 1, sqrt(1 + sqrt(2)): 1}
    expect(keys('t**2 - 1 - sqrt(2)')).toBe('[-sqrt(1 + sqrt(2)), sqrt(1 + sqrt(2))]');
    expect(keys('t**2 - 2*f(x)*t + f(x)**2 - x')).toBe('[-sqrt(x) + f(x), sqrt(x) + f(x)]');
    expect(keys('-t**2 + 2*f(x)*t - x*f(x)')).toBe('[-sqrt((-x + f(x))*f(x)) + f(x), sqrt((-x + f(x))*f(x)) + f(x)]');
  });
  it('polynomials that factor are solved factor by factor, the roots at zero last', () => {
    // SymPy roots(t**2 - (f(1) + 2)*t + 2*f(1), t) = {2: 1, f(1): 1}
    expect(keys('t**2 - (f(1) + 2)*t + 2*f(1)')).toBe('[2, f(1)]');
    expect(keys('t**3 + a*t**2 + t')).toBe('[-a/2 - sqrt((a - 2)*(a + 2))/2, -a/2 + sqrt((a - 2)*(a + 2))/2, 0]');
    expect(keys('t**2 + a*t')).toBe('[-a, 0]');
    expect(keys('t**2 - a**2')).toBe('[-a, a]');
    expect(show(sj.roots(sj.expand(parse('(t - a)*(t + a)**2')), t, { multiple: true }))).toBe('[a, -a, -a]');
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
  it('symbolic coefficients removed by scaling x (SymPy preprocess_roots and _integer_basis)', () => {
    // the roots as a set (SymPy returns a dict)
    const keys = (s: string): string[] => [...(sj.roots(E(s), x) as unknown as Map<sj.Expr, number>).keys()].map(String).sort();
    const cases: [string, string[]][] = [
      ['x**3 - a**3', ['a', 'a*(-1/2 + sqrt(3)*I/2)', 'a*(-1/2 - sqrt(3)*I/2)']],
      ['x**2 - a**2', ['-a', 'a']],
      ['x**4 - a**4', ['-I*a', '-a', 'I*a', 'a']],
      ['x**3 + 8*a**3', ['-2*a', '2*a*(1/2 + sqrt(3)*I/2)', '2*a*(1/2 - sqrt(3)*I/2)']],
      ['x**2 - a', ['-sqrt(a)', 'sqrt(a)']],
      ['x**3 - a', ['-a**(1/3)/2 + sqrt(3)*I*a**(1/3)/2', '-a**(1/3)/2 - sqrt(3)*I*a**(1/3)/2', 'a**(1/3)']],
      ['x**4 - a**2*b**2', ['(a**2*b**2)**(1/4)', '-(a**2*b**2)**(1/4)', '-I*(a**2*b**2)**(1/4)', 'I*(a**2*b**2)**(1/4)']],
      ['x**6 - a**6', ['-a', 'a', 'a*(-1/2 + sqrt(3)*I/2)', 'a*(-1/2 - sqrt(3)*I/2)', 'a*(1/2 + sqrt(3)*I/2)', 'a*(1/2 - sqrt(3)*I/2)']],
      ['x**2 + a*x + a**2', ['a*(-1/2 + sqrt(3)*I/2)', 'a*(-1/2 - sqrt(3)*I/2)']],
      ['x**3 + a*x**2 + a**2*x + a**3', ['-I*a', '-a', 'I*a']],
      ['a*x**2 + b', ['-sqrt(-b/a)', 'sqrt(-b/a)']],
      ['x**2 - a**2*b**4', ['-a*b**2', 'a*b**2']],
      ['x**3 - a**6', ['a**2', 'a**2*(-1/2 + sqrt(3)*I/2)', 'a**2*(-1/2 - sqrt(3)*I/2)']],
      ['2*x**3 - 16*a**3', ['2*a', '2*a*(-1/2 + sqrt(3)*I/2)', '2*a*(-1/2 - sqrt(3)*I/2)']],
      ['x**4 + a**4', ['a*(-sqrt(2)/2 + sqrt(2)*I/2)', 'a*(-sqrt(2)/2 - sqrt(2)*I/2)', 'a*(sqrt(2)/2 + sqrt(2)*I/2)', 'a*(sqrt(2)/2 - sqrt(2)*I/2)']],
      ['x**3 - a**3*x', ['-sqrt(a**3)', '0', 'sqrt(a**3)']],
      ['x**2 + 2*a*x - 3*a**2', ['-3*a', 'a']],
      ['x**3 + 2*a*x**2 + 4*a**2*x + 8*a**3', ['-2*I*a', '-2*a', '2*I*a']],
      ['x**3 + 2*a**3', ['-2**(1/3)*a', 'a*(2**(1/3)/2 + 2**(1/3)*sqrt(3)*I/2)', 'a*(2**(1/3)/2 - 2**(1/3)*sqrt(3)*I/2)']],
      ['x**3 + 3*a*x**2 + 3*a**2*x + x + a**3 + a', ['-a', '-a + I', '-a - I']],
    ];
    for (const [s, r] of cases) expect(keys(s)).toEqual(r);
  });
});
