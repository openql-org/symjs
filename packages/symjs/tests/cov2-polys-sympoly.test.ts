// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Poly methods and polynomial functions (polys/sympoly); expected values from SymPy 1.14. */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const { Poly, parse } = sj;
const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];
const P = (e: string, ...g: sj.Expr[]) => Poly.from(parse(e), g);
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('square-free decomposition with symbolic coefficients (Yun over ZZ[a])', () => {
  it('contents and multiplicities', () => {
    // SymPy: (a, [(Poly(x**2 + 1, x, domain='ZZ[a]'), 1)]); symjs lists the symbolic content as a factor of degree 0
    expect(show(P('a*x**2 + a', x).sqfList())).toBe("[1, [[Poly(a, x, domain='ZZ[a]'), 1], [Poly(x**2 + 1, x, domain='ZZ[a]'), 1]]]");
    // SymPy: (1, [(Poly(x, x, domain='ZZ[a]'), 1), (Poly(x + a, x, domain='ZZ[a]'), 3)])
    expect(show(P('x*(x + a)**3', x).sqfList())).toBe("[1, [[Poly(x, x, domain='ZZ[a]'), 1], [Poly(x + a, x, domain='ZZ[a]'), 3]]]");
  });
});

describe('Poly methods', () => {
  it('diff with respect to the first generator', () => {
    expect(String(P('x**2*y', x, y).diff())).toBe("Poly(2*x*y, x, y, domain='ZZ')");
  });
});

describe('eject', () => {
  const z = new sj.Sym('z');
  it('generators into the ground domain', () => {
    expect(String(P('x*y*z + 1', x, y, z).eject(z))).toBe("Poly(z*x*y + 1, x, y, domain='ZZ[z]')");
    expect(String(P('x*y*z + 1', x, y, z).eject(y, z))).toBe("Poly(y*z*x + 1, x, domain='ZZ[y,z]')");
    // SymPy: DomainError Cannot eject generators over ZZ[z]
    expect(() => P('x*y*z + 1', x, y, z).eject(z).eject(y)).toThrow('Cannot eject generators over ZZ[z]');
  });
});

describe('norms, denominators, ground roots and root counting', () => {
  it('maxNorm and clearDenoms', () => {
    expect(String(P('x**2 + 3*x + 1', x).maxNorm())).toBe('3');
    // SymPy: (1, Poly(a/2*x + 1, x, domain='QQ[a]'))
    expect(show(P('a*x/2 + 1', x).clearDenoms())).toBe("[1, Poly(a/2*x + 1, x, domain='QQ[a]')]");
  });
  it('groundRoots with symbolic coefficients', () => {
    // SymPy: {0: 1} and {a: 1, -a: 1}
    expect(show(P('x**3 + a*x', x).groundRoots())).toBe('[[0, 1]]');
    expect(show(P('x**2 - a**2', x).groundRoots())).toBe('[[a, 1], [-a, 1]]');
  });
  it('countRoots bounds', () => {
    // SymPy converts the bounds to QQ: count_roots(1.0, 2.0) -> 1, count_roots(-2, 3/2) -> 2
    expect(P('x**2 - 2', x).countRoots(1.0, 2.0)).toBe(1);
    expect(P('x**2 - 2', x).countRoots(-2, parse('3/2'))).toBe(2);
    // SymPy: CoercionFailed expected `Rational` object, got pi
    expect(() => P('x**2 - 2', x).countRoots(parse('pi'), 4)).toThrow('expected a Rational, got pi');
    // SymPy raises TypeError over RR (mpf times PythonMPQ); the count is 2
    expect(P('x**2 - 2.0', x).countRoots()).toBe(2);
  });
});

describe('factor and terms_gcd', () => {
  it('factor', () => {
    expect(String(sj.factor(parse('2*x**2 - 2')))).toBe('2*(x - 1)*(x + 1)');
    expect(String(sj.factor(parse('x/((x + 1)**2 - x**2 - 2*x)')))).toBe('x');
  });
  it.each([
    ['x*y**2/2 + x**2*y/2', 'x*y*(x + y)/2'],
    ['x/2 + 1', 'x/2 + 1'],
    ['x*y/2 + y**2', 'y*(x/2 + y)'],
    ['(x + 1)*(x*y/3 + y/6)', 'y*(2*x**2 + 3*x + 1)/6'],
    ['2*x*(x + 1) + 2*x*z', '2*x*(x + z + 1)'],
    ['x*z/2 + x*y/3', 'x*(2*y + 3*z)/6'],
  ])('terms_gcd(%s, clear=False)', (f, expected) => {
    expect(String(sj.termsGcd(parse(f), { clear: false }))).toBe(expected);
  });
});

describe('roots over extensions and generator order', () => {
  it('complex conjugate roots', () => {
    // Poly(x**2 + 1).all_roots() -> [-I, I]
    expect(show(P('x**2 + 1', x).allRoots({ extension: true }))).toBe('[-I, I]');
    expect(show(P('x**2 + 2*x + 5', x).allRoots({ extension: true }))).toBe('[-1 - 2*I, -1 + 2*I]');
    // roots(x**2 + sqrt(2)): {-2**(1/4)*I: 1, 2**(1/4)*I: 1}, ordered by the imaginary part
    expect(show(P('x**2 + sqrt(2)', x).allRoots({ extension: true }))).toBe('[-2**(1/4)*I, 2**(1/4)*I]');
  });
  it('generators with equal sort keys keep their order', () => {
    const d = new sj.Sym('x', { positive: true });
    expect(sj.sortGens([x, d])).toEqual([x, d]);
    expect(sj.sortGens([d, x])).toEqual([d, x]);
  });
});

describe('factor over an extension', () => {
  it.each([
    ['x**2 - sqrt(2)', 'sqrt(2)', 'x**2 - sqrt(2)'],
    ['x**3 - 2', '2**(1/3)', '(x - 2**(1/3))*(x**2 + 2**(1/3)*x + 2**(2/3))'],
    ['x**4 - 2', '2**(1/4)', '(x - 2**(1/4))*(x + 2**(1/4))*(x**2 + sqrt(2))'],
  ])('factor(%s, extension=%s)', (f, ext, expected) => {
    expect(String(sj.factor(parse(f), { extension: [parse(ext)] }))).toBe(expected);
  });
});
