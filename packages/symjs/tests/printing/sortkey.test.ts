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
