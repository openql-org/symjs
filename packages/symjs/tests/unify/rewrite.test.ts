// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/unify/rewrite.ts (SymPy sympy/unify/rewrite.py).
// Cases from sympy/unify/tests/test_rewrite.py and the doctests; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Basic, Lt, Q, Rational, S, add, isIntegerValued, mul, pow, sin, str, symbol, symbols } from '../../src';
import type { Expr } from '../../src';
import { rebuild } from '../../src/strategies';
import { rewriterule } from '../../src/unify/rewrite';

const [p, q, w, x, y, z] = symbols('p q w x y z');
const N = (v: number): Expr => Rational.of(v);
const strs = (xs: Iterable<Expr>): string[] => [...xs].map(str);

describe('rewriterule', () => {
  it('simple', () => {
    const rl = rewriterule(Basic(p, 1), Basic(p, 2), [p]);
    expect(strs(rl(Basic(3, 1)))).toEqual(['Basic(3, 2)']);
    const rl2 = rewriterule(pow(p, 2), pow(p, 3), [p]);
    expect(strs(rl2(pow(x, 2)))).toEqual(['x**3']);
  });

  it('simple variables', () => {
    const rl = rewriterule(Basic(x, 1), Basic(x, 2), [x]);
    expect(strs(rl(Basic(3, 1)))).toEqual(['Basic(3, 2)']);
    const rl2 = rewriterule(pow(x, 2), pow(x, 3), [x]);
    expect(strs(rl2(pow(y, 2)))).toEqual(['y**3']);
  });

  it('moderate', () => {
    const rl = rewriterule(add(pow(p, 2), pow(q, 3)), pow(mul(p, q), 4), [p, q]);
    expect(strs(rl(add(pow(x, 2), pow(y, 3))))).toEqual(['x**4*y**4']);
  });

  it('sincos', () => {
    const p1 = add(pow(sin(p), 2), pow(sin(p), 2));
    const rl = rewriterule(p1, 1, [p, q]);
    expect(strs(rl(add(pow(sin(x), 2), pow(sin(x), 2))))).toEqual(['1']);
    expect(strs(rl(add(pow(sin(y), 2), pow(sin(y), 2))))).toEqual(['1']);
  });

  it('Exprs ok', () => {
    const rl = rewriterule(add(p, q), add(q, p), [p, q]);
    const r = rl(add(x, y)).next().value as Expr;
    expect(r.isCommutative).toBe(true);
    expect(str(r)).toBe('x + y');
    expect(strs(rl(add(x, y)))).toEqual(['x + y', 'x + y']);
  });

  it('condition simple', () => {
    const rl = rewriterule(x, add(x, 1), [x], (v) => Lt(v, 10));
    expect(strs(rl(N(15)))).toEqual([]);
    // SymPy yields the unevaluated 1 + 5
    const r = rl(N(5)).next().value as Expr;
    expect(str(r)).toBe('1 + 5');
    expect(str(rebuild(r))).toBe('6');
  });

  it('condition multiple', () => {
    const rl = rewriterule(add(x, y), pow(x, y), [x, y], (v) => isIntegerValued(v));
    const a = symbol('a');
    const b = symbol('b', { integer: true });
    expect(strs(rl(add(a, b)))).toEqual(['b**a']);
    const c = symbol('c', { integer: true });
    const d = symbol('d', { integer: true });
    expect(new Set(strs(rl(add(c, d))))).toEqual(new Set(['c**d', 'd**c']));
  });

  it('assumptions', () => {
    const rl = rewriterule(add(x, y), pow(x, y), [x, y], null, Q.integer(x));
    const [a, b] = symbols('a b');
    expect(strs(rl(add(a, b), Q.integer(b)))).toEqual(['b**a']);
    // doctests
    const rl2 = rewriterule(add(x, y), pow(x, y), [x, y]);
    expect(strs(rl2(add(z, 3))).sort()).toEqual(['3**z', 'z**3']);
    const rl3 = rewriterule(add(x, y), pow(x, y), [x, y], (v) => isIntegerValued(v));
    expect(strs(rl3(add(z, 3)))).toEqual(['3**z']);
    const rl4 = rewriterule(add(x, y), pow(x, y), [x, y], null, Q.integer(x));
    expect(strs(rl4(add(z, 3)))).toEqual(['3**z']);
    expect(strs(rl4(add(w, z), Q.integer(z)))).toEqual(['z**w']);
  });

  it('condition results that are not true', () => {
    expect(strs(rewriterule(x, x, [x], () => S.false)(N(1)))).toEqual([]);
    expect(strs(rewriterule(x, x, [x], () => 'unknown')(N(1)))).toEqual([]);
    expect(strs(rewriterule(x, x, [x], () => true)(N(1)))).toEqual(['1']);
    // a variable the match does not bind is passed as itself
    expect(strs(rewriterule(N(1), N(2), [x], (v) => v.equals(x))(N(1)))).toEqual(['2']);
  });
});
