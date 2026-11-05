// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/satask.ts. Expected values are those of SymPy 1.14
// (sympy/assumptions/tests/test_satask.py and the doctests).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { CNF, EncodedCNF, classFactRegistry, checkSatisfiability, extractPredargs, findSymbols, getAllRelevantFacts, getRelevantClsfacts, satask } from '../../src/assumptions';

const { Q } = sj;
const [x, y, z] = sj.symbols('x y z') as [sj.Expr, sj.Expr, sj.Expr];
const U = 'unknown';
const strs = (s: Iterable<unknown>): string[] => [...s].map(String).sort();

describe('satask', () => {
  it('doctest and no relevant facts', () => {
    expect(satask(Q.zero(sj.abs(x)), Q.zero(x))).toBe(true);
    expect(satask(Q.real(x), Q.real(x))).toBe(true);
    expect(satask(Q.real(x), sj.not(Q.real(x)))).toBe(false);
    expect(satask(Q.real(x))).toBe(U);
    expect(satask(Q.real(x), Q.positive(x))).toBe(true);
    expect(satask(Q.positive(x), Q.real(x))).toBe(U);
    expect(satask(Q.positive(x), sj.not(Q.real(x)))).toBe(false);
    expect(() => satask(Q.real(x), sj.And(Q.real(x), sj.not(Q.real(x))))).toThrow(RangeError);
    expect(() => satask(Q.real(x), false)).toThrow('Inconsistent assumptions');
    expect(satask(Q.zero(x), Q.zero(sj.mul(x, y)))).toBe(U);
    expect(satask(Q.zero(sj.mul(x, y)), Q.zero(x))).toBe(true);
  });
  it('context', () => {
    sj.assuming(Q.positive(x), () => {
      expect(satask(Q.real(x))).toBe(true);
      expect(satask(sj.not(Q.positive(x)))).toBe(false);
    });
    expect(satask(Q.real(x), true, { context: [Q.positive(x)] })).toBe(true);
    expect(satask(Q.zero(sj.mul(x, y)), Q.zero(x), { useKnownFacts: false, iterations: 1 })).toBe(true);
  });
  it('zero, positive and powers', () => {
    expect(satask(sj.Or(Q.zero(x), Q.zero(y)), Q.zero(sj.mul(x, y)))).toBe(true);
    expect(satask(sj.Or(Q.zero(x), Q.zero(y)), Q.nonzero(sj.mul(x, y)))).toBe(false);
    expect(satask(Q.zero(x), Q.zero(sj.pow(x, 2)))).toBe(true);
    expect(satask(Q.zero(sj.add(x, y)), sj.And(Q.positive(x), Q.positive(y)))).toBe(false);
    expect(satask(Q.positive(sj.add(sj.mul(sj.pi, x, y), 1)), sj.And(Q.positive(x), Q.positive(y)))).toBe(true);
    expect(satask(Q.zero(sj.pow(x, y)), sj.And(Q.zero(x), Q.positive(y)))).toBe(true);
    expect(satask(Q.negative(sj.pow(x, 2)), Q.positive(x))).toBe(false);
    expect(satask(Q.nonpositive(sj.pow(x, 3)), Q.negative(x))).toBe(true);
    expect(satask(Q.real(sj.pow(x, -2)), Q.nonpositive(x))).toBe(U);
    expect(sj.str(sj.Implies(Q.zero(x), Q.zero(sj.mul(x, y))))).toBe('Implies(Q.zero(x), Q.zero(x*y))');
    expect(satask(sj.Implies(Q.zero(x), Q.zero(sj.mul(x, y))))).toBe(true);
  });
  it('numbers (old assumptions)', () => {
    expect(satask(Q.positive(1))).toBe(true);
    expect(satask(Q.positive(sj.I))).toBe(false);
    expect(satask(Q.positive(sj.pi))).toBe(true);
    expect(satask(Q.nonpositive(0))).toBe(true);
    expect(satask(Q.irrational(sj.pi))).toBe(true);
    expect(satask(Q.rational(sj.Rational.of(1n, 2n)))).toBe(true);
    expect(satask(Q.prime(5))).toBe(true);
    expect(satask(Q.prime(6))).toBe(false);
    expect(satask(Q.even(2))).toBe(true);
    expect(satask(Q.imaginary(sj.mul(2, sj.I)))).toBe(true);
  });
  it('products, sums, Abs', () => {
    expect(satask(Q.even(sj.mul(x, y)), sj.And(Q.even(x), Q.odd(y)))).toBe(true);
    expect(satask(Q.odd(sj.mul(x, y)), sj.And(Q.odd(x), Q.odd(y)))).toBe(true);
    expect(satask(Q.even(sj.abs(x)), Q.odd(x))).toBe(false);
    expect(satask(Q.integer(sj.add(x, y)), sj.And(Q.integer(x), sj.not(Q.integer(y))))).toBe(false);
    expect(satask(Q.integer(sj.mul(x, y)), sj.And(Q.integer(x), Q.irrational(y)))).toBe(false);
    expect(satask(Q.irrational(sj.add(x, y, z)), sj.And(Q.irrational(x), Q.rational(y), Q.rational(z)))).toBe(true);
    expect(satask(Q.prime(sj.mul(x, y)), sj.And(Q.prime(x), Q.prime(y)))).toBe(false);
    expect(satask(Q.imaginary(sj.mul(x, y)), sj.And(Q.imaginary(x), Q.real(y)))).toBe(true);
    expect(satask(Q.positive(sj.abs(x)), sj.not(Q.zero(x)))).toBe(true);
    expect(satask(Q.nonzero(x), sj.not(Q.zero(sj.abs(x))))).toBe(U);
    expect(satask(Q.prime(x), Q.composite(x))).toBe(false);
  });
  it('matrices (the known matrix facts)', () => {
    const A = new sj.MatrixSymbol('A', 2, 2) as unknown as sj.Expr;
    expect(satask(Q.square(A), Q.invertible(A))).toBe(true);
  });
});

describe('the relevant facts', () => {
  it('extract_predargs', () => {
    const xy = sj.mul(x, y);
    expect(strs(extractPredargs(CNF.fromProp(Q.zero(sj.abs(xy))), CNF.fromProp(sj.And(Q.zero(x), Q.zero(y)))))).toEqual(['Abs(x*y)', 'x', 'y']);
    const props = CNF.fromProp(sj.And(Q.zero(sj.abs(xy)), Q.zero(xy)));
    expect(strs(extractPredargs(props))).toEqual(['Abs(x*y)', 'x*y']);
    expect(strs(extractPredargs(props, CNF.fromProp(Q.zero(x))))).toEqual(['Abs(x*y)', 'x', 'x*y']);
    expect(strs(extractPredargs(props, CNF.fromProp(Q.zero(x)), CNF.fromProp(Q.zero(y))))).toEqual(['Abs(x*y)', 'x', 'x*y', 'y']);
    expect(strs(extractPredargs(CNF.fromProp(sj.Eq(x, y)), CNF.fromProp(sj.Gt(y, z))))).toEqual(['x', 'y', 'z']);
    // a bare symbol and an unapplied predicate as literals
    expect(strs(extractPredargs(CNF.fromProp(sj.Or(z, Q.even(x))), CNF.fromProp(true)))).toEqual(['x', 'z']);
    expect(strs(extractPredargs(new CNF([[new sj.Literal(Q.even)]])))).toEqual([]);
    expect(findSymbols(Q.even).size).toBe(0);
  });
  it('get_relevant_clsfacts', () => {
    const xy = sj.mul(x, y);
    const [exprs, facts] = getRelevantClsfacts([sj.abs(xy)]);
    expect(strs(exprs)).toEqual(['x*y']);
    expect(facts.size).toBe(7);
    const [exprs2, facts2] = getRelevantClsfacts(exprs, facts);
    expect(strs(exprs2)).toEqual(['x', 'y']);
    expect(getRelevantClsfacts(exprs2, facts2)[0].size).toBe(0);
    // a class fact whose literal is not an applied predicate introduces no expression
    classFactRegistry.register('satask_test_f', (e) => sj.Or(z, Q.even(e)));
    const fz = sj.SymFunction('satask_test_f')(x);
    expect(strs(getRelevantClsfacts([fz])[0])).toEqual([]);
    expect(satask(Q.even(fz), sj.not(z))).toBe(true);
  });
  it('get_all_relevant_facts and check_satisfiability', () => {
    const enc = getAllRelevantFacts(CNF.fromProp(Q.nonzero(sj.mul(x, y))), CNF.fromProp(Q.nonzero(x)), CNF.fromProp(Q.nonzero(y)));
    expect(enc).toBeInstanceOf(EncodedCNF);
    expect(checkSatisfiability(CNF.fromProp(Q.zero(x)), CNF.fromProp(sj.not(Q.zero(x))), new EncodedCNF())).toBe(U);
  });
});
