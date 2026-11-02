// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Poly, evalf, factor, parse, rootOf, solve, symbols } from '../src';

const [x] = symbols('x');
const P = (s: string) => Poly.from(parse(s), [x]);

// expected values from SymPy 1.14
describe('factorization over ZZ (Zassenhaus)', () => {
  it('splits polynomials without rational roots', () => {
    expect(String(factor(parse('x**5 + x + 1')))).toBe('(x**2 + x + 1)*(x**3 - x**2 + 1)');
    expect(String(factor(parse('x**4 + 4')))).toBe('(x**2 - 2*x + 2)*(x**2 + 2*x + 2)');
    expect(String(factor(parse('x**8 - 1')))).toBe('(x - 1)*(x + 1)*(x**2 + 1)*(x**4 + 1)');
    expect(String(factor(parse('6*x**4 - 5*x**3 + 7*x**2 - 5*x + 1')))).toBe('(2*x - 1)*(3*x - 1)*(x**2 + 1)');
    expect(String(factor(parse('x**4 - 10*x**2 + 1')))).toBe('x**4 - 10*x**2 + 1');
  });
});

describe('CRootOf', () => {
  it('all_roots and real_roots order', () => {
    expect(P('x**5 + x + 1').allRoots().map(String)).toEqual([
      'CRootOf(x**3 - x**2 + 1, 0)',
      '-1/2 - sqrt(3)*I/2',
      '-1/2 + sqrt(3)*I/2',
      'CRootOf(x**3 - x**2 + 1, 1)',
      'CRootOf(x**3 - x**2 + 1, 2)',
    ]);
    expect(P('(x**2 - 2)*(x**3 + x + 1)').realRoots().map(String)).toEqual(['-sqrt(2)', 'CRootOf(x**3 + x + 1, 0)', 'sqrt(2)']);
  });
  it('numeric values', () => {
    expect(String(evalf(rootOf(parse('x**3 + x + 1'), 0), 30))).toBe('-0.682327803828019327369483739711');
    expect(String(evalf(rootOf(parse('x**3 + x + 1'), 1)))).toBe('0.34116390191401 - 1.16154139999725*I');
  });
  it('solve falls back to CRootOf', () => {
    expect(solve(parse('x**5 - x - 1'), x).map(String)).toEqual([0, 1, 2, 3, 4].map((i) => `CRootOf(x**5 - x - 1, ${i})`));
    expect(solve(parse('x**3 - x + 1'), x, { cubics: false }).map(String)).toEqual([0, 1, 2].map((i) => `CRootOf(x**3 - x + 1, ${i})`));
  });
});

import { Rational } from '../src';

describe('real root isolation (SymPy intervals / refine_root)', () => {
  const show = (iv: [[Rational, Rational], number][]) => iv.map(([[s, t], k]) => `((${s}, ${t}), ${k})`).join(', ');
  it('isolates and refines', () => {
    expect(show(P('x**2 - 3').intervals())).toBe('((-2, -1), 1), ((1, 2), 1)');
    expect(show(P('x**2 - 3').intervals(Rational.of(1, 100)))).toBe('((-26/15, -19/11), 1), ((19/11, 26/15), 1)');
    expect(P('x**2 - 3').refineRoot(Rational.of(1), Rational.of(2), Rational.of(1, 100)).map(String)).toEqual(['19/11', '26/15']);
    expect(show(P('(x - 1)**2*(x + 2)*x').intervals())).toBe('((-2, -2), 1), ((0, 0), 1), ((1, 1), 2)');
  });
});

import { Reals, solveset, sin } from '../src';

describe('solveset with ImageSet and ConditionSet', () => {
  it('periodic, complex exponential and unsolvable equations', () => {
    expect(String(solveset(sin(x), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi), Integers), ImageSet(Lambda(_n, 2*_n*pi + pi), Integers))');
    expect(String(solveset(parse('sin(x) + cos(x)'), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi + 3*pi/4), Integers), ImageSet(Lambda(_n, 2*_n*pi + 7*pi/4), Integers))');
    expect(String(solveset(parse('exp(x) + 1'), x))).toBe('ImageSet(Lambda(_n, I*(2*_n*pi + pi)), Integers)');
    expect(String(solveset(parse('cos(x) - 2'), x, Reals))).toBe('EmptySet');
    expect(String(solveset(parse('x**2 + x*sin(x) - 1'), x, Reals))).toBe('ConditionSet(x, Eq(x**2 + x*sin(x) - 1, 0), Reals)');
  });
});
