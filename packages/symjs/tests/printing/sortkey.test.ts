// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/sortkey.ts.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Add, Float, Rational, S, WildFunction } from '../../src/core/nodes';
import { asOrderedTerms, compareKeys, sortKey } from '../../src/printing/sortkey';
import { str } from '../../src/printing/str';

const [x, y] = sj.symbols('x y');
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));
const ONE_KEY = [[1, 0, 'Number'], [0, []], [], 1];

/**
 * Coverage of the str printer and the printing sort keys: expected
 * values are SymPy 1.14 `str(expr)`, `latex(expr)` and
 * `expr.as_ordered_terms()` / `sorted(..., key=default_sort_key)`.
 */

describe('sort keys', () => {
  it('sorted([exp(x), x, sin(x), x**2, exp(2), 2**x], key=default_sort_key)', () => {
    const es = [sj.exp(x), x, sj.sin(x), sj.pow(x, 2), sj.exp(2), sj.pow(2, x)];
    expect(es.sort((a, b) => compareKeys(sortKey(a), sortKey(b))).map(str)).toEqual(['2**x', 'x', 'x**2', 'exp(2)', 'exp(x)', 'sin(x)']);
  });
  it('Add(exp(x), x, exp(y)).as_ordered_terms()', () => {
    expect(asOrderedTerms(new Add([sj.exp(x), x, sj.exp(y)])).map(str)).toEqual(['x', 'exp(x)', 'exp(y)']);
  });
  it('(x**2.0 + x**3 + x).as_ordered_terms()', () => {
    expect(asOrderedTerms(sj.add(sj.pow(x, new Float(2)), sj.pow(x, 3), x)).map(str)).toEqual(['x**3', 'x', 'x**2.0']);
  });
  it('(x**(I*y) + x**(2*y) + x**(-y) + x**(y/2)).as_ordered_terms()', () => {
    const e = sj.add(sj.pow(x, sj.mul(S.I, y)), sj.pow(x, sj.mul(2, y)), sj.pow(x, sj.neg(y)), sj.pow(x, sj.mul(R(1, 2), y)));
    expect(asOrderedTerms(e).map(str)).toEqual(['x**(y/2)', 'x**(2*y)', 'x**(I*y)', 'x**(-y)']);
  });
  it('keys of different kinds order by kind', () => {
    // not produced by well-formed expressions; numbers before strings before lists
    expect(compareKeys(1, 'a')).toBeLessThan(0);
    expect(compareKeys('a', [1])).toBeLessThan(0);
    expect(compareKeys([1], 1)).toBeGreaterThan(0);
  });
});

/**
 * Coverage of printing/sets.ts, sortkey.ts, str.ts and the pretty printer
 * (pretty.ts, stringpict.ts, symbology.ts). Expected strings from SymPy 1.14
 * (str, pretty with and without unicode, latex, default_sort_key).
 */

describe('sort keys', () => {
  it('gives a WildFunction the class key of a Function', () => {
    // SymPy WildFunction('F').sort_key()
    expect(sortKey(new WildFunction('F'))).toEqual([[4, 0, 'WildFunction'], [1, ['F_']], ONE_KEY, 1]);
  });
  it('takes oo, -oo as the coefficient of a product', () => {
    // SymPy: sorted([oo*x, x, -oo*x, 2*x], key=default_sort_key) = [-oo*x, x, 2*x, oo*x]
    const xs = [sj.mul(sj.oo, x), x, sj.mul(-1, sj.oo, x), sj.mul(2, x)];
    expect(xs.sort((a, b) => compareKeys(sortKey(a), sortKey(b))).map(str)).toEqual(['-oo*x', 'x', '2*x', 'oo*x']);
    expect(sj.str(sj.add(sj.mul(sj.oo, x), sj.mul(sj.zoo, y), sj.sin(x)))).toBe('oo*x + zoo*y + sin(x)');
  });
  it('keys the booleans by their class', () => {
    // SymPy: S.true.sort_key() = ((5, 0, 'BooleanTrue'), (0, ()), ((1, 0, 'Number'), (0, ()), (), 1), 1)
    expect(sortKey(sj.S.true)).toEqual([[5, 0, 'BooleanTrue'], [0, []], ONE_KEY, 1]);
    expect(sortKey(sj.S.false)).toEqual([[5, 0, 'BooleanFalse'], [0, []], ONE_KEY, 1]);
  });
  it('orders powers with a Float in the exponent', () => {
    // SymPy decompose_power(x**(2.5*y)) = (x**(2.5*y), 1)
    expect(sj.str(sj.add(sj.pow(x, sj.mul(2.5, y)), sj.pow(x, 2), x))).toBe('x**2 + x + x**(2.5*y)');
  });
  it('as_ordered_terms of a single term', () => {
    expect(asOrderedTerms(x)).toEqual([x]);
  });
});

describe('as_ordered_terms with a monomial ordering (SymPy Expr.as_ordered_terms(order))', () => {
  const f = sj.parse('x**2*y + x*y**3 + 1 + x');
  it.each([
    ['lex', ['x**2*y', 'x*y**3', 'x', '1']],
    ['rev-lex', ['1', 'x', 'x*y**3', 'x**2*y']],
    ['grlex', ['x*y**3', 'x**2*y', 'x', '1']],
    ['grevlex', ['x*y**3', 'x**2*y', 'x', '1']],
    ['rev-grlex', ['1', 'x', 'x**2*y', 'x*y**3']],
    ['ilex', ['1', 'x', 'x*y**3', 'x**2*y']],
    ['igrlex', ['1', 'x', 'x**2*y', 'x*y**3']],
    ['igrevlex', ['1', 'x', 'x**2*y', 'x*y**3']],
    ['rev-ilex', ['x**2*y', 'x*y**3', 'x', '1']],
    ['rev-grevlex', ['1', 'x', 'x**2*y', 'x*y**3']],
  ] as const)('%s', (order, want) => expect(asOrderedTerms(f, order).map(str)).toEqual(want));
  it('other expressions and an unknown ordering', () => {
    expect(asOrderedTerms(sj.add(x, sj.pow(x, -1)), 'rev-lex').map(str)).toEqual(['1/x', 'x']);
    expect(asOrderedTerms(sj.parse('2 + 3*I + x'), 'rev-lex').map(str)).toEqual(['3*I', '2', 'x']);
    expect(asOrderedTerms(x, 'lex').map(str)).toEqual(['x']);
    expect(() => asOrderedTerms(f, 'bogus' as 'lex')).toThrow(RangeError);
  });
});

describe('sort keys of Indexed', () => {
  it('sort by the printed form, an Atom in SymPy', () => {
    const X = new sj.Sym('x');
    const i = sj.Idx(new sj.Sym('i', { integer: true }));
    const at = (j: number): sj.Expr => new sj.Indexed([X, sj.add(i, j)]);
    // SymPy: sorted([x[i], x[i+1], x[i-1]], key=default_sort_key) == [x[i + 1], x[i - 1], x[i]]
    expect(String([at(0), at(1), at(-1)].sort((a, b) => compareKeys(sortKey(a), sortKey(b))))).toBe('x[i + 1],x[i - 1],x[i]');
    expect(str(sj.sub(at(1), at(0)))).toBe('x[i + 1] - x[i]');
    expect(str(sj.sub(at(0), at(-1)))).toBe('-x[i - 1] + x[i]');
  });
});

describe('class keys of the functions whose nargs is Naturals0 in SymPy', () => {
  it('order before the other functions', () => {
    // SymPy str(exp_polar(1)*sin(y)), str(lerchphi(x, y, 2)*sin(y)), str(LeviCivita(x, y)*sin(y));
    // their class_key is (4, 0, name)
    expect(str(sj.mul(sj.sin(y), sj.expPolar(1)))).toBe('exp_polar(1)*sin(y)');
    expect(str(sj.mul(sj.cos(y), sj.expPolar(x)))).toBe('exp_polar(x)*cos(y)');
    expect(str(sj.mul(sj.sin(y), sj.lerchphi(x, y, 2)))).toBe('lerchphi(x, y, 2)*sin(y)');
    expect(JSON.stringify(sortKey(sj.expPolar(x)))).toContain('[4,0,"exp_polar"]');
  });
});

describe('class keys of matrix sums and products, sums and products', () => {
  it('as in SymPy', () => {
    const d = new sj.Sym('d');
    const k = new sj.Sym('k');
    const X = sj.MatrixSymbol('X', 2, 2);
    expect(JSON.stringify(sortKey(sj.MatAdd(X, sj.MatrixSymbol('Y', 2, 2))))).toContain('[3,1,"MatAdd"]');
    expect(JSON.stringify(sortKey(sj.MatMul(X, sj.MatrixSymbol('Y', 2, 2))))).toContain('[3,0,"MatMul"]');
    expect(JSON.stringify(sortKey(sj.Product(k, [k, 1, d])))).toContain('[5,0,"Product"]');
    // SymPy: Determinant(SM)**a*Product(gamma(k), (k, 1, d))
    expect(str(sj.mul(sj.Product(sj.gamma(k), [k, 1, d]), sj.pow(sj.Determinant(sj.MatrixSymbol('SM', d, d)), new sj.Sym('a'))))).toBe('Determinant(SM)**a*Product(gamma(k), (k, 1, d))');
  });
});
