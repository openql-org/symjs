// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/groebner.ts: Groebner bases; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { leadingMonomial } from '../../src/polys/groebner';

const { parse } = sj;
const [x, y, z] = sj.symbols('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('Groebner bases', () => {
  const F = [parse('x**3 - 2*x*y'), parse('x**2*y - 2*y**2 + x')];
  it('orders and domains', () => {
    expect(String(sj.groebner(F, [x, y], 'lex'))).toBe("GroebnerBasis([x - 2*y**2, y**3], x, y, domain='ZZ', order='lex')");
    expect(String(sj.groebner(F, [x, y], 'grlex'))).toBe("GroebnerBasis([x**2, x*y, 2*y**2 - x], x, y, domain='ZZ', order='grlex')");
    expect(String(sj.groebner(F, [x, y], 'grevlex'))).toBe("GroebnerBasis([x**2, x*y, 2*y**2 - x], x, y, domain='ZZ', order='grevlex')");
    expect(String(sj.groebner([parse('x/2 + y'), parse('y**2 - 1/3')], [x, y]))).toBe("GroebnerBasis([x + 2*y, y**2 - 1/3], x, y, domain='QQ', order='lex')");
    expect(String(sj.groebner([parse('x*y - 1'), parse('x**2 + y**2')], [x, y], 'grevlex'))).toBe(
      "GroebnerBasis([y**3 + x, x**2 + y**2, x*y - 1], x, y, domain='ZZ', order='grevlex')",
    );
    expect(String(sj.groebner([parse('x**2*y**3 - x*y**4'), parse('x**3*y - x*y**3'), parse('x*z - y*z')], [x, y, z], 'grevlex'))).toBe(
      "GroebnerBasis([x**2*y**3 - x*y**4, x**3*y - x*y**3, x*z - y*z], x, y, z, domain='ZZ', order='grevlex')",
    );
    // the terms are printed in the basis order over the sorted generators
    expect(String(sj.groebner([parse('x - y**2'), parse('x*y - 1')], [y, x]))).toBe("GroebnerBasis([-x**2 + y, x**3 - 1], y, x, domain='ZZ', order='lex')");
    expect(String(sj.groebner([parse('x - y**2'), parse('x*y - 1')], [y, x], 'grlex'))).toBe("GroebnerBasis([y**2 - x, x*y - 1, x**2 - y], y, x, domain='ZZ', order='grlex')");
    expect(String(sj.groebner([parse('x**3 - y'), parse('x*y - 1')], [y, x], 'grevlex'))).toBe("GroebnerBasis([x**3 - y, -x**2 + y**2, x*y - 1], y, x, domain='ZZ', order='grevlex')");
    expect(String(sj.groebner([parse('x**3 - y'), parse('x*y - 1')], [x, y], 'grevlex'))).toBe("GroebnerBasis([y**3 - x, x**2 - y**2, x*y - 1], x, y, domain='ZZ', order='grevlex')");
    expect(String(sj.groebner([0, x], [x]))).toBe("GroebnerBasis([x], x, domain='ZZ', order='lex')");
    expect(String(sj.groebner([parse('2*x + 4'), parse('6*y')], [x, y]))).toBe("GroebnerBasis([x + 2, y], x, y, domain='ZZ', order='lex')");
  });
  it('coefficients outside QQ and leading monomials', () => {
    // SymPy computes over ZZ[a]: GroebnerBasis([1], x, domain='ZZ[a]', order='lex');
    // symjs supports rational coefficients only
    expect(() => sj.groebner([parse('a*x - 1'), parse('x**2')], [x])).toThrow(sj.DomainError);
    expect(leadingMonomial(parse('x**2*y + y**3'), [x, y], 'grevlex')).toEqual([2, 1]);
    expect(leadingMonomial(parse('x**2*y + y**3'), [y, x], 'grevlex')).toEqual([3, 0]);
    expect(leadingMonomial(parse('x*y**2 + x**2*y'), [x, y], 'grevlex')).toEqual([2, 1]);
    expect(leadingMonomial(parse('x*y**2 + x**2*y'), [x, y])).toEqual([2, 1]);
    expect(() => leadingMonomial(0, [x, y])).toThrow(sj.PolynomialError);
  });
  it('membership and reduction', () => {
    const G = sj.groebner([parse('x**2 + y**2 - 1'), parse('x - y')], [x, y]);
    expect(G.contains(parse('x**2 - y**2 + x - y'))).toBe(true);
    expect(G.contains(parse('x + 1'))).toBe(false);
    expect(G.contains(5)).toBe(false);
    expect(G.contains(0)).toBe(true);
    expect(show(G.reduce(5))).toBe('[[0, 0], 5]');
    // SymPy: ([x**2 + x*y + y**2, y/2], 3*y/2)
    expect(show(G.reduce(parse('x**3 + y')))).toBe('[[x**2 + x*y + y**2, y/2], 3*y/2]');
    expect(show(sj.reduced(parse('x**2*y + x*y**2'), [parse('x*y - 1'), parse('y**2 - 1')], [x, y]))).toBe('[[x + y, 0], x + y]');
    expect(show(sj.reduced(parse('x**2*y + x*y**2'), [parse('x*y - 1'), parse('y**2 - 1')], [x, y], 'grevlex'))).toBe('[[x + y, 0], x + y]');
  });
});
