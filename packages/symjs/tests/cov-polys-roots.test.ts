// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** roots (polys/poly), UPoly and real root isolation (polys/rootisolation); expected values from SymPy 1.14. */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const [x] = sj.symbols('x') as [sj.Sym];
const E = sj.parse;
const R = (p: number, q = 1) => sj.Rational.of(BigInt(p), BigInt(q));
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
// the multiset of roots (the order of SymPy's dict is not part of the comparison)
const roots = (e: string) => sj.roots(E(e), x, { multiple: true }).map(String).sort();

describe('roots', () => {
  it('cubics by Cardano', () => {
    expect(roots('x**3 + 3*x**2 + 3*x - 1')).toEqual(['-1 + 2**(1/3)', '-1 + 2**(1/3)*(-1/2 + sqrt(3)*I/2)', '-1 + 2**(1/3)*(-1/2 - sqrt(3)*I/2)']);
    expect(roots('x**3 + 3*x**2 + 3*x + 3')).toEqual(['-1 - 2**(1/3)*(-1/2 + sqrt(3)*I/2)', '-1 - 2**(1/3)*(-1/2 - sqrt(3)*I/2)', '-2**(1/3) - 1']);
    expect(roots('x**3 + x - 1')).toEqual(['(-1/2 - sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3) - 1/(3*(-1/2 - sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3))', '-1/(3*(-1/2 + sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3)) + (-1/2 + sqrt(3)*I/2)*(1/2 + sqrt(93)/18)**(1/3)', '-1/(3*(1/2 + sqrt(93)/18)**(1/3)) + (1/2 + sqrt(93)/18)**(1/3)']);
  });
  it('binomials and symbolic coefficients', () => {
    expect(roots('2*x**2 + 1')).toEqual(['-sqrt(2)*I/2', 'sqrt(2)*I/2']);
    expect(roots('2*x**4 + 1')).toEqual(['-2**(1/4)/2 + 2**(1/4)*I/2', '-2**(1/4)/2 - 2**(1/4)*I/2', '2**(1/4)/2 + 2**(1/4)*I/2', '2**(1/4)/2 - 2**(1/4)*I/2']);
    expect(roots('x**2 + a*x + b')).toEqual(['-a/2 + sqrt(a**2 - 4*b)/2', '-a/2 - sqrt(a**2 - 4*b)/2']);
    expect(roots('x**3 + a*x**2')).toEqual(['-a', '0', '0']);
    expect(roots('x**2 - a')).toEqual(['-sqrt(a)', 'sqrt(a)']);
    expect(roots('a*x + b')).toEqual(['-b/a']);
    expect(roots('3*x**4 - x**2')).toEqual(['-sqrt(3)/3', '0', '0', 'sqrt(3)/3']);
    // SymPy roots_quartic answers with a Piecewise; not supported here
    expect(() => roots('x**4 + a*x + b')).toThrow(sj.NotImplementedError);
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

describe('real root isolation with large roots', () => {
  const I = (e: string, eps?: sj.Rational) => show(sj.Poly.from(E(e), [x]).intervals(eps));
  it('Poly.intervals', () => {
    expect(I('(x - 10)*(x - 11)*(x - 100)')).toBe('[[[10, 10], 1], [[11, 11], 1], [[100, 100], 1]]');
    expect(I('(x - 1000)*(x - 1001)')).toBe('[[[1000, 1000], 1], [[1001, 1001], 1]]');
    expect(I('(x - 1000)*(x - 1001)', R(1, 10))).toBe('[[[1000, 1000], 1], [[1001, 1001], 1]]');
    expect(I('(x**2 - 200)*(x - 50)')).toBe('[[[-15, -14], 1], [[14, 15], 1], [[50, 50], 1]]');
    expect(I('x**3 - 1000*x + 1')).toBe('[[[-32, -31], 1], [[0, 1], 1], [[31, 32], 1]]');
    expect(I('(x**2 - 2)*(x - 3)*(x - 4)*(x - 5)*(x - 6)*(x - 7)')).toBe('[[[-2, -1], 1], [[1, 2], 1], [[3, 3], 1], [[4, 4], 1], [[5, 5], 1], [[6, 6], 1], [[7, 7], 1]]');
    expect(I('(x - 10)*(x**2 - 300)')).toBe('[[[-18, -17], 1], [[10, 10], 1], [[17, 18], 1]]');
    expect(I('(x - 20)*(x**2 - 500)*(x - 30)')).toBe('[[[-23, -22], 1], [[20, 20], 1], [[22, 23], 1], [[30, 30], 1]]');
    expect(I('(x**2 - 150)*(x**2 - 170)')).toBe('[[[-14, -13], 1], [[-13, -12], 1], [[12, 13], 1], [[13, 14], 1]]');
    expect(I('(x - 7)*(x**2 - 60)*(x - 9)')).toBe('[[[-8, -7], 1], [[7, 7], 1], [[7, 8], 1], [[9, 9], 1]]');
    expect(I('x**2 - 2001*x + 1000001')).toBe('[[[968, 969], 1], [[1032, 1033], 1]]');
    expect(I('x**4 - 100*x**3 + 3500*x**2 - 50000*x + 240001')).toBe('[[[10, 11], 1], [[19, 20], 1], [[30, 31], 1], [[39, 40], 1]]');
    expect(I('(x - 1000)*(x**2 - 3000*x + 2250001)')).toBe('[[[1000, 1000], 1]]');
    expect(I('(x - 10)*(x**2 - 30*x + 226)')).toBe('[[[10, 10], 1]]');
    expect(I('(x - 100)*(x - 101)*(x**2 + 1)')).toBe('[[[100, 100], 1], [[101, 101], 1]]');
    expect(I('(x**2 - 4*x + 5)*(x - 3)*(x - 50)')).toBe('[[[3, 3], 1], [[50, 50], 1]]');
    expect(I('(x - 1000)*(x - 1001)*(x - 1002)')).toBe('[[[1000, 1000], 1], [[1001, 1001], 1], [[1002, 1002], 1]]');
    expect(I('(x**2 - 1000000)*(x**2 - 2000000)')).toBe('[[[-1415, -1414], 1], [[-1000, -1000], 1], [[1000, 1000], 1], [[1414, 1415], 1]]');
    expect(I('(x - 100)*(x - 200)*(x - 300)*(x - 400)')).toBe('[[[100, 100], 1], [[200, 200], 1], [[300, 300], 1], [[400, 400], 1]]');
    expect(I('(x**2 - 1000001)*(x - 2000)*(x - 3000)')).toBe('[[[-1001, -1000], 1], [[1000, 1001], 1], [[2000, 2000], 1], [[3000, 3000], 1]]');
    expect(I('x**4 - 1000*x**2 + 1')).toBe('[[[-32, -31], 1], [[-1, 0], 1], [[0, 1], 1], [[31, 32], 1]]');
    expect(I('(x - 1/3)*(x - 1/2)*(x - 2/3)*(x**2 - 3)')).toBe('[[[-2, -1], 1], [[0, 1/2], 1], [[1/2, 1/2], 1], [[1/2, 1], 1], [[1, 2], 1]]');
  });
  it('Poly.refineRoot', () => {
    const p = sj.Poly.from(E('x**2 - 200'), [x]);
    expect(show(p.refineRoot(R(14), R(15), R(1, 1000)))).toBe('[2093/148, 99/7]');
    expect(show(p.refineRoot(R(1), R(100), R(1, 10)))).toBe('[1385/98, 71/5]');
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
    expect(roots(e)).toEqual([...r].sort());
  });
});

