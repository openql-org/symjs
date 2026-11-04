// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/diophantine.ts: Diophantine equations; expected values from SymPy 1.14
// (sympy.solvers.diophantine.diophantine, its doctests and test_diophantine.py).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import type { Expr } from '../../src';
import * as D from '../../src/solvers/diophantine';

const p = new sj.Sym('p', { positive: true });
const q = new sj.Sym('q', { nonpositive: true });
const P = (s: string): Expr => sj.parse(s, { symbols: { p, q } } as never);
const [x, y, z, t] = sj.symbols('x y z t');
/** A tuple printed like Python. */
const tup = (v: readonly unknown[]): string => (v.length === 1 ? `(${String(v[0])},)` : `(${v.map(String).join(', ')})`);
/** A set of tuples printed like sorted(map(str, s)) in Python. */
const sset = (s: Iterable<readonly unknown[]>): string[] => [...s].map(tup).sort();
const dio = (eq: string, opts: D.DiophantineOptions = {}) => sset(D.diophantine(P(eq), opts));
const show = (v: unknown): string => (sj.isNoMatch(v) ? 'None' : v === sj.EmptySet ? 'EmptySet' : Array.isArray(v) ? tup(v) : String(v));

describe('diophantine', () => {
  it('solves the doctest equations', () => {
    expect(dio('a**4 + b**4 - 97')).toEqual(['(2, 3)']);
    expect(dio('a**4 + b**4 - 97', { permute: true })).toEqual(['(-2, -3)', '(-2, 3)', '(-3, -2)', '(-3, 2)', '(2, -3)', '(2, 3)', '(3, -2)', '(3, 2)']);
    expect(dio('x**2 - y**2')).toEqual(['(t_0, -t_0)', '(t_0, t_0)']);
    expect(dio('x*(2*x + 3*y - z)')).toEqual(['(0, n1, n2)', '(t_0, t_1, 2*t_0 + 3*t_1)']);
    expect(dio('x**2 + 3*x*y + 4*x')).toEqual(['(-3*t_0 - 4, t_0)', '(0, n1)']);
  });

  it('linear, univariate and factored equations', () => {
    expect(dio('2*x + 4*y - 6')).toEqual(['(3 - 2*t_0, t_0)']);
    expect(sset(D.diophantine(sj.Eq(sj.add(x, y), 3)))).toEqual(['(t_0, 3 - t_0)']);
    expect(dio('x + y - 3', { syms: [y, x] })).toEqual(['(3 - t_0, t_0)']);
    expect(dio('x**2 + y**2 + z**2 - 14', { syms: [z, y, x] })).toEqual(['(3, 2, 1)']);
    expect(dio('x**2 - 15*x + 56')).toEqual(['(7,)', '(8,)']);
    expect(dio('x**4 - 2*x**2 + 1')).toEqual(['(-1,)', '(1,)']);
    expect(dio('x/2 + y - 1')).toEqual(['(2 - 2*t_0, t_0)']);
    expect(dio('x - y + 0*z')).toEqual(['(t_0, t_0)']);
    expect(dio('x + y - 3', { permute: true })).toEqual(['(t_0, 3 - t_0)']);
    expect(dio('x + y - 3', { syms: [x, y] })).toEqual(['(t_0, 3 - t_0)']);
    expect(dio('x**2 + 1')).toEqual([]);
    expect(dio('x**2 - 3*x*y + 2*y**2')).toEqual(['(2*t_0, t_0)', '(t_0, t_0)']);
    expect(dio('x**2 - x*y')).toEqual(['(0, n1)', '(t_0, t_0)']);
    expect(dio('x*y + x + y + 1')).toEqual(['(-1, n1)', '(n1, -1)']);
    expect(dio('x*y + 2*y*z')).toEqual(['(-2*t_0, n1, t_0)', '(n1, 0, n2)']);
    // a custom parameter
    expect(sset(D.diophantine(P('2*x + 3*y - 5'), { param: new sj.Sym('s', { integer: true }) }))).toEqual(['(3*s_0 - 5, 5 - 2*s_0)']);
  });

  it('numerators, denominators and invalid input', () => {
    expect(dio('(x - y)/(x + y)')).toEqual(['(t_0, t_0)']);
    expect(dio('(x**2 - 1)/(x - 1)')).toEqual(['(-1,)']);
    expect(dio('x**2/y')).toEqual([]);
    expect(dio('(x**2 + x*y)/x')).toEqual(['(t_0, -t_0)']);
    expect(dio('3')).toEqual([]);
    expect(() => D.diophantine(P('sqrt(x) + y'))).toThrow(TypeError);
    expect(() => D.diophantine(P('sin(x) + y'))).toThrow('Equation should be a polynomial with Rational coefficients.');
    expect(() => D.diophantine(P('x*sqrt(2) + y'))).toThrow(TypeError);
    expect(() => D.diophantine(P('x*y*z - 1'))).toThrow(sj.NotImplementedError);
    // SymPy: NotImplementedError: No solver has been written for inhomogeneous_general_quadratic.
    expect(() => D.diophantine(P('x**2 + y**2 + z + 1'))).toThrow(sj.NotImplementedError);
  });

  it('symbol assumptions', () => {
    expect(dio('p**2 + y**2 - 25')).toEqual(['(3, -4)', '(3, 4)', '(4, -3)', '(4, 3)', '(5, 0)']);
    expect(dio('x*p')).toEqual(['(n1, 0)']);
    expect(dio('p + y')).toEqual(['(t_0, -t_0)']);
    expect(dio('q**2 + y**2 + z**2 - 14')).toEqual(['(-1, 2, 3)']);
    // the trivial solution is excluded when a symbol must be positive
    expect(dio('p**2 + y**2')).toEqual([]);
    expect(dio('x**2 + y**2 + z**2 + 1')).toEqual([]);
  });

  it('binary quadratic equations', () => {
    expect(dio('x*y - 1')).toEqual(['(-1, -1)', '(1, 1)']);
    expect(dio('x*y + 3*x')).toEqual(['(0, n1)', '(n1, -3)']);
    expect(dio('2*x*y + 3*y')).toEqual(['(n1, 0)']);
    expect(dio('x*y - 2*y')).toEqual(['(2, n1)', '(n1, 0)']);
    expect(dio('3*x*y + 4*x - 5*y - 7')).toEqual(['(2, -1)']);
    expect(dio('x**2 - 4*x*y + 4*y**2 - 3*x + 7*y - 5')).toEqual(['(-2*t**2 - 7*t + 10, -t**2 - 3*t + 5)']);
    expect(dio('x**2 - 2*x*y + y**2 + x - 3')).toEqual(['(3 - t**2, -t**2 + t + 3)']);
    expect(dio('2*x**2 + 4*x*y + 2*y**2 + x - 3*y')).toEqual(['(-8*t**2 + 3*t, 8*t**2 + t)']);
    expect(dio('4*x**2 - 4*x*y + y**2 + 2*x - y - 2')).toEqual(['(t_0, 2*t_0 + 2)', '(t_0, 2*t_0 - 1)']);
    expect(dio('x**2 - y**2 - 2*x + 3')).toEqual([]);
    expect(dio('3*x**2 - 5*x*y + 2*y**2 + 4')).toEqual(['(-6, -7)', '(-6, -8)', '(-9, -13)', '(6, 7)', '(6, 8)', '(9, 13)']);
    expect(dio('y**2 - 5*x*y + 6*x**2 + 3')).toEqual(['(-4, -11)', '(-4, -9)', '(4, 11)', '(4, 9)']);
    expect(dio('x**2 - 7*y**2 - 2*x + 1')).toEqual(['(1, 0)']);
    expect(dio('x**2 + 2*x*y - 2*y**2 - 3')).toEqual([]);
    expect(dio('x**2 + y**2 - 5*x + 1')).toEqual([]);
    expect(dio('2*x**2 + 3*y**2 + 2*x - 7')).toEqual(['(-2, -1)', '(-2, 1)', '(1, -1)', '(1, 1)']);
    expect(dio('x**2 + 5*y**2 + 3*y - 7')).toEqual([]);
    expect(dio('x**2 - 6*y**2 + 4*y - 5')).toEqual([]);
    expect(dio('x**2 + y**2 + 2*x + 2*y + 2', { permute: true })).toEqual(['(-1, -1)']);
    expect(dio('x*y + x + y', { permute: true })).toEqual(['(-2, -2)', '(0, 0)']);
    // an x*y term without linear terms: the signs are permuted keeping the sign of x*y
    expect(dio('x**2 + x*y + y**2 - 7', { permute: true })).toEqual(['(-1, -2)', '(-1, 3)', '(-2, -1)', '(-2, 3)', '(-3, 1)', '(-3, 2)', '(1, -3)', '(1, 2)', '(2, -3)', '(2, 1)', '(3, -1)', '(3, -2)']);
    expect(dio('2*x**2 + 2*y**2 - 50', { permute: true })).toEqual([
      '(-3, -4)',
      '(-3, 4)',
      '(-4, -3)',
      '(-4, 3)',
      '(-5, 0)',
      '(0, -5)',
      '(0, 5)',
      '(3, -4)',
      '(3, 4)',
      '(4, -3)',
      '(4, 3)',
      '(5, 0)',
    ]);
  });

  /** The integer values of the parametric solutions at t = 0 and t = 1. */
  const pellValues = (eq: string, opts: D.DiophantineOptions = {}): string[] => {
    const ti = new sj.Sym('t', { integer: true });
    return D.diophantine(P(eq), opts)
      .flatMap((s) => [0, 1].map((k) => tup(s.map((e) => sj.nsimplify(sj.expand(sj.subs(e, [[ti, k]])))))))
      .sort();
  };
  const sortedValues = (vs: [number, number][]) => vs.map((v) => tup(v)).sort();

  it('Pell-type binary quadratics (values of the parametric solutions)', () => {
    expect(pellValues('x**2 - 2*y**2 - 1')).toEqual(sortedValues([[-17, 12], [-3, 2], [3, -2], [17, -12]]));
    expect(pellValues('x**2 - 3*y**2 + 2*x - 5')).toEqual(sortedValues([[-4, -1], [-4, 1], [2, -1], [2, 1]]));
    expect(pellValues('x**2 - 3*x*y + y**2 - 5')).toEqual(
      sortedValues([[-199, -76], [-76, -29], [-29, -11], [-11, -4], [-4, -1], [-1, 1], [1, -1], [4, 1], [11, 4], [29, 11], [76, 29], [199, 76]]),
    );
    // the transformation has rational coefficients: the solutions of every residue class modulo the period
    expect(pellValues('x**2 - 2*y**2 + 3*y - 1')).toEqual(
      sortedValues([
        [-9228778026, 6525731525],
        [-271669860, 192099601],
        [-7997214, 5654885],
        [-235416, 166465],
        [-6930, 4901],
        [-204, 145],
        [-6, 5],
        [0, 1],
        [1, 0],
        [35, -24],
        [1189, -840],
        [40391, -28560],
        [1372105, -970224],
        [46611179, -32959080],
        [1583407981, -1119638520],
        [53789260175, -38034750624],
      ]),
    );
    // permute=True with an x*y term but no linear terms keeps the sign of x*y
    expect(pellValues('x**2 + 3*x*y - y**2 - 1', { permute: true })).toEqual(
      sortedValues([[-141481, -467280], [-12970, -42837], [-1189, -3927], [-109, -360], [-10, -33], [-1, -3], [1, 3], [10, 33], [109, 360], [1189, 3927], [12970, 42837], [141481, 467280]]),
    );
  });

  it('ternary quadratics and sums of squares', () => {
    expect(dio('x**2 + y**2 + z**2 - 14')).toEqual(['(1, 2, 3)']);
    expect(dio('x**2 + y**2 + z**2 - 14', { permute: true })).toHaveLength(48);
    expect(dio('x**2 + y**2 + z**2 - 7')).toEqual([]);
    expect(dio('x**4 + y**4 + z**4 - 18', { permute: true })).toHaveLength(24);
    expect(dio('x**2 + y**2 - z**2')).toEqual(['(2*p*q, p**2 - q**2, p**2 + q**2)']);
    expect(dio('x**2 + y**2 - z**2', { permute: true })).toEqual(['(2*p*q, p**2 - q**2, p**2 + q**2)']);
    expect(dio('x**2 + y**2 - 2*z**2', { permute: true })).toEqual(['(p**2 - 2*q**2, -p**2 + 4*p*q - 2*q**2, p**2 - 2*p*q + 2*q**2)']);
    expect(dio('x*y - z**2', { permute: true })).toEqual(['(-q**2, -p**2 + 2*p*q - q**2, -p*q + q**2)']);
    expect(dio('x**2 + y**2 - z**2 + x*y', { permute: true })).toEqual(['(p**2 - q**2, -p**2 + 2*p*q, p**2 - p*q + q**2)']);
    expect(dio('x**2 + 2*y**2 - 3*z**2 + 6*x*z', { permute: true })).toEqual(['(-2*p**2 + 3*q**2, -4*p**2 + 12*p*q - 6*q**2, 2*p**2 - 8*p*q + 9*q**2)']);
    expect(dio('4*x**2 + 9*y**2 - z**2 - 2*x*z', { permute: true })).toEqual(['(27*p**2 - 3*q**2, -18*p**2 + 18*p*q - 2*q**2, 54*p**2 - 36*p*q + 12*q**2)']);
    expect(dio('3*x**2 + 4*y**2 - 5*z**2 + 4*x*y - 7*y*z + 7*x*z')).toEqual(['(-16*p**2 + 28*p*q + 20*q**2, 3*p**2 + 38*p*q - 25*q**2, 4*p**2 - 24*p*q + 68*q**2)']);
    expect(dio('x**2 + y**2 + z**2 - x*y')).toEqual(['(0, 0, 0)']);
    expect(dio('x*y + y*z + x*z')).toEqual(['(0, 0, 0)']);
    expect(dio('2*x**2 + y**2 + z**2 - 2*x*y')).toEqual(['(0, 0, 0)']);
    expect(dio('y*z - x**2')).toEqual(['(-p*q, p**2, q**2)']);
    expect(dio('x**2 - y*z + z**2')).toEqual(['(-p*q + q**2, p**2 - 2*p*q + 2*q**2, q**2)']);
    expect(dio('x**2 + 3*y**2 + 2*y*z - z**2')).toEqual(['(4*p*q, p**2 - q**2, 3*p**2 + q**2)']);
    expect(dio('y**2 - 3*x*z + z**2')).toEqual(['(2*p**2 + 2*q**2, -3*p**2 + 3*q**2, 3*p**2 - 6*p*q + 3*q**2)']);
    expect(dio('z**2 + x*y - 2*y**2')).toEqual(['(-4*p**2 + 2*q**2, q**2, 2*p*q)']);
    expect(dio('9*a**2 + 4*b**2 + 16*c**2 - 25*d**2')).toEqual(['(10*t1**2 + 10*t2**2 - 10*t3**2, 30*t1*t3, 15*t2*t3, 6*t1**2 + 6*t2**2 + 6*t3**2)']);
  });
});

describe('equation types', () => {
  it('matches and solves the doctests', () => {
    expect(new D.BinaryQuadratic(P('x**3 + y**2 + 1')).matches()).toBe(false);
    expect(new D.BinaryQuadratic(P('x**2 + y**2 + 2*x + 2*y + 2')).matches()).toBe(true);
    expect(String(new D.BinaryQuadratic(P('x**2 + y**2 + 2*x + 2*y + 2')).solve())).toBe('DiophantineSolutionSet({(-1, -1)})');
    expect(new D.CubicThue(P('x**3 + y**2 + 1')).matches()).toBe(true);
    expect(new D.Linear(P('2*x - 3*y - 5')).matches()).toBe(true);
    expect(sset(new D.Linear(P('2*x - 3*y - 5')).solve())).toEqual(['(3*t_0 - 5, 2*t_0 - 5)']);
    expect(sset(new D.Linear(P('2*x - 3*y - 4*z -3')).solve())).toEqual(['(t_0, 2*t_0 + 4*t_1 + 3, -t_0 - 3*t_1 - 3)']);
    expect(String(new D.Univariate(P('(x - 2)*(x - 3)**2')).solve())).toBe('DiophantineSolutionSet({(2,), (3,)})');
    expect(sset(new D.GeneralPythagorean(P('a**2 + b**2 + c**2 - d**2')).solve())).toEqual(['(t_0**2 + t_1**2 - t_2**2, 2*t_0*t_2, 2*t_1*t_2, t_0**2 + t_1**2 + t_2**2)']);
    expect(sset(new D.GeneralPythagorean(P('9*a**2 - 4*b**2 + 16*c**2 + 25*d**2 + e**2')).solve({ parameters: [x, y, z, t] }))).toEqual([
      '(-10*t**2 + 10*x**2 + 10*y**2 + 10*z**2, 15*t**2 + 15*x**2 + 15*y**2 + 15*z**2, 15*t*x, 12*t*y, 60*t*z)',
    ]);
    expect(sset(new D.GeneralSumOfEvenPowers(P('a**4 + b**4 - (2**4 + 3**4)')).solve())).toEqual(['(2, 3)']);
    expect(sset(new D.GeneralSumOfSquares(P('a**2 + b**2 + c**2 + d**2 + e**2 - 2345')).solve())).toEqual(['(15, 22, 22, 24, 24)']);
    expect(sset(new D.GeneralSumOfSquares(P('a**2 + b**2 + c**2 + d**2 + e**2 - 2345')).solve({ limit: 3 }))).toEqual(['(15, 22, 22, 24, 24)', '(16, 19, 24, 24, 24)', '(16, 20, 22, 23, 26)']);
    expect(sset(new D.HomogeneousTernaryQuadratic(P('x**2 + y**2 - 3*z**2 + x*y')).solve())).toEqual(['(-1, 2, 1)']);
    expect(sset(new D.HomogeneousTernaryQuadratic(P('3*x**2 + y**2 - 3*z**2 + 5*x*y + y*z')).solve())).toEqual(['(3, 12, 13)']);
    expect(sset(new D.HomogeneousTernaryQuadraticNormal(P('4*x**2 - 5*y**2 + z**2')).solve())).toEqual(['(1, 2, 4)']);
  });

  it('binary quadratics of each case', () => {
    const bq = (eq: string, opts: D.DiophantineSolveOptions = {}) => sset(new D.BinaryQuadratic(P(eq)).solve(opts));
    // simple hyperbolic
    expect(bq('x*y + 2*x')).toEqual(['(0, t_0)', '(t_0, -2)']);
    expect(bq('2*x*y + 3*x')).toEqual(['(0, t_0)']);
    expect(bq('2*x*y + 3*y')).toEqual(['(t_0, 0)']);
    expect(bq('48*x*y')).toEqual(['(0, t_0)', '(t_0, 0)']);
    expect(bq('3*x*y + 34*x - 12*y + 1')).toEqual(['(-133, -11)', '(5, -57)']);
    expect(bq('6*x*y + 2*x + 3*y + 1')).toEqual([]);
    expect(bq('2*x*y + 5*x + 56*y + 7')).toEqual(['(-161, -3)', '(-21, 7)', '(-27, 64)', '(-29, -69)', '(-35, -12)', '(-47, -6)', '(-9, 1)', '(105, -2)']);
    // parabolic
    expect(bq('y**2 - x - 3')).toEqual(['(t_0**2 - 3, t_0)']);
    expect(bq('y**2 - 41*x + 40')).toEqual(['(41*t_0**2 + 2*t_0 + 1, 41*t_0 + 1)', '(41*t_0**2 + 80*t_0 + 40, 41*t_0 + 40)']);
    expect(bq('x**2 + 2*x*y + y**2 + 3*x + 3*y + 2')).toEqual(['(t_0, -t_0 - 1)', '(t_0, -t_0 - 2)']);
    expect(bq('x**2 - y + 1')).toEqual(['(t_0, t_0**2 + 1)']);
    expect(bq('8*x**2 - 24*x*y + 18*y**2 + 5*x + 7*y + 16')).toEqual(['(-174*t_0**2 + 17*t_0 - 2, -116*t_0**2 + 21*t_0 - 2)', '(-174*t_0**2 + 41*t_0 - 4, -116*t_0**2 + 37*t_0 - 4)']);
    expect(bq('8*x**2 - 24*x*y + 18*y**2 + 6*x + 12*y - 6')).toEqual(['(-63*t_0**2 + 12*t_0, -42*t_0**2 + 15*t_0 - 1)', '(-63*t_0**2 + 30*t_0 - 3, -42*t_0**2 + 27*t_0 - 4)']);
    expect(bq('8*x**2 + 24*x*y + 18*y**2 + 4*x + 6*y - 7')).toEqual([]);
    expect(bq('-4*x**2 + 4*x*y - y**2 + 2*x - 3')).toEqual(['(2*t_0**2 - 2*t_0 + 2, 4*t_0**2 - 2*t_0 + 3)']);
    expect(bq('x**2 + 2*x*y + y**2 + 2*x + 2*y + 1')).toEqual(['(t_0, -t_0 - 1)']);
    expect(bq('x**2 - 2*x*y + y**2 + 2*x + 2*y + 1')).toEqual(['(-4*t_0**2 + 4*t_0 - 1, -4*t_0**2 + 8*t_0 - 4)', '(-4*t_0**2, -4*t_0**2 + 4*t_0 - 1)']);
    // the discriminant is a square
    expect(bq('x**2 - 3*x*y + 2*y**2')).toEqual(['(2*t_0, t_0)', '(t_0, t_0)']);
    expect(bq('x**2 - 3*x*y + 2*y**2 - 2')).toEqual(['(-3, -1)', '(0, -1)', '(0, 1)', '(3, 1)']);
    expect(bq('x*y + y**2 - 2')).toEqual(['(-1, -1)', '(-1, 2)', '(1, -2)', '(1, 1)']);
    expect(bq('4*x**2 - 5*x*y + y**2 + 2')).toEqual(['(-1, -2)', '(-1, -3)', '(1, 2)', '(1, 3)']);
    expect(bq('-2*x**2 - 3*x*y + 2*y**2 -2*x - 17*y + 25')).toEqual(['(4, 15)']);
    expect(bq('12*x**2 + 13*x*y + 3*y**2 - 2*x + 3*y - 12')).toEqual(['(-2, 5)', '(-6, 16)', '(-6, 9)', '(4, -4)']);
    expect(bq('8*x**2 + 10*x*y + 2*y**2 - 32*x - 13*y - 23')).toEqual(['(-44, 47)', '(22, -85)']);
    expect(bq('4*x**2 - 4*x*y - 3*y- 8*x - 3')).toEqual(['(-1, -9)', '(-6, -9)', '(0, -1)', '(1, -1)']);
    expect(bq('- 4*x*y - 4*y**2 - 3*y- 5*x - 10')).toEqual(['(-11, -1)', '(-2, 0)', '(-5, 5)']);
    expect(bq('x**2 - y**2 - 2*x - 2*y')).toEqual(['(t_0, -t_0)', '(t_0, t_0 - 2)']);
    expect(bq('x**2 - y**2 - 2*x - 2*y', { parameters: [t, P('u')] })).toEqual(['(t, -t)', '(t, t - 2)']);
    expect(bq('x**2 - 9*y**2 - 2*x - 6*y')).toEqual(['(-3*t_0, t_0)', '(3*t_0 + 2, t_0)']);
    expect(bq('4*x**2 - 9*y**2 - 4*x - 12*y - 3')).toEqual(['(3*t_0 + 1, -2*t_0 - 1)', '(3*t_0 - 3, 2*t_0 - 3)']);
    // parametric solutions made integral (check_param), with their fixed parts and signs
    expect(bq('3*x**2 - 5*x*y - 3*x - 5*y - 6')).toEqual(['(-10*t_0 - 7, t_0)', '(5*t_0 + 12, 3*t_0 + 6)']);
    expect(bq('-7*x**2 + 8*x*y - 5*x')).toEqual(['(16*t_0, t_0)', '(8*t_0 + 5, 7*t_0 + 5)']);
    expect(bq('x**2 + 3*x*y + 3*x + 2*y**2 + 6*y')).toEqual(['(-2*t_0, t_0)', '(t_0, -t_0 - 3)']);
    expect(bq('-x**2 + 10*x*y + 11*y**2')).toEqual(['(11*t_0, t_0)', '(t_0, -t_0)']);
    // SymPy raises ValueError here (check_param builds a solution set with parameters None); with parameters it gives
    // diop_quadratic(eq, t) = {(t, 1 - t)}
    expect(bq('-4*x**2 - 4*x*y + 2*x - 2*y + 2')).toEqual(['(t_0, 1 - t_0)']);
    expect(sset(D.diopQuadratic(P('-4*x**2 - 4*x*y + 2*x - 2*y + 2'), t) as Expr[][])).toEqual(['(t, 1 - t)']);
    expect(sset(D.diopQuadratic(P('9*x**2 - 3*x*y - y - 1'), t) as Expr[][])).toEqual(['(t, 3*t - 1)']);
    // elliptic
    expect(bq('42*x**2 + 8*x*y + 15*y**2 + 23*x + 17*y - 4915')).toEqual(['(-11, -1)']);
    expect(bq('10*x**2 + 12*x*y + 12*y**2 - 34')).toEqual(['(-1, -1)', '(-1, 2)', '(1, -2)', '(1, 1)']);
  });

  it('attributes, errors and the types without a solver', () => {
    const l = new D.Linear(P('2*x - 3*y - 5'));
    expect([l.name, l.totalDegree, l.homogeneous, l.homogeneousOrder, l.dimension, l.nParameters]).toEqual(['linear', 1, false, false, 2, 2]);
    expect(l.parameters.map(String)).toEqual(['t_0', 't_1']);
    expect(String(l.equation)).toBe('2*x - 3*y - 5');
    expect(new D.DiophantineEquationType(P('x')).matches()).toBe(false);
    expect(() => new D.DiophantineEquationType(P('x')).solve()).toThrow(sj.NotImplementedError);
    expect(() => new D.CubicThue(P('x**3 + y**2 + 1')).solve()).toThrow('No solver has been written for cubic_thue.');
    expect(() => new D.Linear(P('3'))).toThrow(RangeError);
    expect(() => new D.Linear(P('x/2 + y'))).toThrow('Coefficients should be Integers');
    expect(() => new D.Linear(P('x**2 + y')).solve()).toThrow('This equation does not match the linear equation type.');
    expect(() => new D.Linear(P('x + y')).solve({ parameters: [x] })).toThrow('Expected 2 parameter(s) but got 1');
    expect(new D.InhomogeneousTernaryQuadratic(P('x*y + z**2 + x')).matches()).toBe(true);
    expect(new D.InhomogeneousTernaryQuadratic(P('x*y + z**2 + 1')).matches()).toBe(false);
    expect(new D.InhomogeneousTernaryQuadratic(P('x*y + z**2')).matches()).toBe(false);
    expect(new D.InhomogeneousTernaryQuadratic(P('x + y + z')).matches()).toBe(false);
    expect(new D.HomogeneousTernaryQuadraticNormal(P('x**2 + y**2 + z**2 + 1')).matches()).toBe(false);
    expect(new D.HomogeneousTernaryQuadraticNormal(P('x**2 + y**2 + z')).matches()).toBe(false);
    expect(new D.HomogeneousTernaryQuadratic(P('x**2 + y**2 + z**2 + 1')).matches()).toBe(false);
    expect(new D.HomogeneousTernaryQuadratic(P('x**2 + y**2 + z')).matches()).toBe(false);
    expect(new D.HomogeneousGeneralQuadratic(P('x**2 + y')).matches()).toBe(false);
    expect(new D.HomogeneousGeneralQuadratic(P('w**2 + x**2 + y**2 + z')).matches()).toBe(false);
    expect(new D.GeneralSumOfSquares(P('x**2 + y')).matches()).toBe(false);
    expect(new D.GeneralSumOfSquares(P('x**2 + y**2 + z')).matches()).toBe(false);
    expect(new D.GeneralSumOfSquares(P('x**2 + y**2 + x*z')).matches()).toBe(false);
    expect(new D.GeneralPythagorean(P('x**2 + y')).matches()).toBe(false);
    expect(new D.GeneralPythagorean(P('x**2 + y**2 + z')).matches()).toBe(false);
    expect(new D.GeneralPythagorean(P('x**2 + y**2 - x*z')).matches()).toBe(false);
    expect(new D.GeneralPythagorean(P('x**2 + 2*y**2 - z**2')).matches()).toBe(false);
    expect(new D.GeneralPythagorean(P('x**2 + 4*y**2 + z**2')).matches()).toBe(false);
    expect(new D.GeneralSumOfEvenPowers(P('x**2 + y**2')).matches()).toBe(false);
    expect(new D.GeneralSumOfEvenPowers(P('x**5 + y**5')).matches()).toBe(false);
    expect(new D.GeneralSumOfEvenPowers(P('x**4 + y**3*x')).matches()).toBe(false);
    expect(new D.GeneralSumOfEvenPowers(P('x**4 + 2*y**4')).matches()).toBe(false);
    // the variables assumed nonpositive get negative values
    expect(sset(new D.GeneralSumOfEvenPowers(P('q**4 + b**4 - 97')).solve())).toEqual(['(2, -3)']);
    expect(sset(new D.GeneralSumOfEvenPowers(P('a**4 + b**4 - 97')).solve({ limit: 0 }))).toEqual([]);
    expect(sset(new D.GeneralSumOfEvenPowers(P('a**4 + b**4 + 5')).solve())).toEqual([]);
    expect(sset(new D.GeneralSumOfSquares(P('a**2 + b**2 + c**2 + 5')).solve())).toEqual([]);
    expect(sset(new D.GeneralSumOfSquares(P('a**2 + b**2 + c**2 - 5')).solve({ limit: 0 }))).toEqual([]);
    // the trivial solutions of the homogeneous ternary quadratics without squares
    expect(sset(new D.HomogeneousTernaryQuadratic(P('x*y + y*z')).solve())).toEqual(['(-1, 0, n1)']);
    expect(sset(new D.HomogeneousTernaryQuadratic(P('x*z + y*z')).solve())).toEqual(['(n1, -1, 0)']);
    expect(new D.GeneralPythagorean(P('x**2 + y**2 + z**2')).matches()).toBe(false);
  });

  it('classifyDiop', () => {
    const c = (s: string) => {
      const [v, cd, name] = D.classifyDiop(P(s));
      return `${tup(v)} ${[...cd].map(([k, w]) => `${String(k)}: ${String(w)}`).sort().join(', ')} ${name}`;
    };
    expect(c('4*x + 6*y - 4')).toBe('(x, y) 1: -4, x: 4, y: 6 linear');
    expect(c('x**2 + y**2 - x*y + x + 5')).toBe('(x, y) 1: 5, x**2: 1, x*y: -1, x: 1, y**2: 1 binary_quadratic');
    expect(c('x**2 + y**2 + z**2 + x*y + 1').endsWith('inhomogeneous_general_quadratic')).toBe(true);
    expect(c('x**2 + y**2 + z**2 + x + 1').endsWith('inhomogeneous_general_quadratic')).toBe(true);
    expect(c('x**2 + y**2 + z**2 + w**2 + x*y').endsWith(' homogeneous_general_quadratic')).toBe(true);
    expect(c('x**2 + y**2 + z**2 + w**2 + x*y + 3').endsWith('inhomogeneous_general_quadratic')).toBe(true);
    expect(c('x**3 + 2*y**3').endsWith('cubic_thue')).toBe(true);
    for (const s of ['x**3 + y**3 - z**3', 'x**2 + y**2 + 2*z**2 + w**2 - 3', 'x**2 + y**2 - z**2 + 3', 'x**4 + 2*y**4', 'x**4 + y**3 + z**4', 'x**5 + y**5 - 1', 'x**4*y**4 - 1']) {
      expect(() => D.classifyDiop(P(s)), s).toThrow(sj.NotImplementedError);
    }
    expect(() => D.classifyDiop(P('x/2 + y'))).toThrow(TypeError);
  });
});

describe('DiophantineSolutionSet', () => {
  const [u] = sj.symbols('u');
  it('adds, substitutes and evaluates solutions', () => {
    const s1 = new D.DiophantineSolutionSet([x, y], [t, u!]);
    expect(String(s1)).toBe('DiophantineSolutionSet()');
    s1.add([2, 3]);
    s1.add([-1, u!]);
    const s2 = new D.DiophantineSolutionSet([x, y], [t, u!]);
    s2.add([3, 4]);
    s1.update(...s2);
    expect(sset(s1)).toEqual(['(-1, u)', '(2, 3)', '(3, 4)']);
    expect(s1.size).toBe(3);
    expect(s1.has([2, 3])).toBe(true);
    expect([...s1.dictIterator()].map((m) => [...m].map(([k, v]) => `${String(k)}: ${String(v)}`).join(', '))).toEqual(['x: -1, y: u', 'x: 2, y: 3', 'x: 3, y: 4']);
    const s3 = new D.DiophantineSolutionSet([x, y], [t, u!]);
    s3.add([sj.pow(t, 2), sj.add(t, u!)]);
    expect(String(s3.subs(new Map([[t, 2], [u!, 3]])))).toBe('DiophantineSolutionSet({(4, 5)})');
    expect(String(s3.subs(t, -1))).toBe('DiophantineSolutionSet({(1, u - 1)})');
    expect(String(s3.subs(t, 3))).toBe('DiophantineSolutionSet({(9, u + 3)})');
    expect(String(s3.call(-2, 3))).toBe('DiophantineSolutionSet({(4, 1)})');
    expect(String(s3.call(5))).toBe('DiophantineSolutionSet({(25, u + 5)})');
    expect(String(s3.call(null, 2))).toBe('DiophantineSolutionSet({(t**2, t + 2)})');
    expect(() => s3.call(1, 2, 3)).toThrow('Evaluation should have at most 2 values, not 3');
    expect(() => s3.add([1])).toThrow('Solution should have a length of 2, not 1');
  });

  it('makes solutions canonical with respect to sign', () => {
    const s = new D.DiophantineSolutionSet([x, y], [t]);
    s.add([sj.neg(t), sj.neg(t)]);
    s.add([t, sj.neg(t)]);
    expect(sset(s)).toEqual(['(t, -t)', '(t, t)']);
  });
});

describe('diopSolve and the solvers of each type', () => {
  it('diopSolve', () => {
    expect(show(D.diopSolve(P('2*x + 3*y - 5')))).toBe('(3*t_0 - 5, 5 - 2*t_0)');
    expect(show(D.diopSolve(P('4*x + 3*y - 4*z + 5')))).toBe('(t_0, 8*t_0 + 4*t_1 + 5, 7*t_0 + 3*t_1 + 5)');
    expect(show(D.diopSolve(P('x + 3*y - 4*z + w - 6')))).toBe('(t_0, t_0 + t_1, 6*t_0 + 5*t_1 + 4*t_2 - 6, 5*t_0 + 4*t_1 + 3*t_2 - 6)');
    expect(sset(D.diopSolve(P('x**2 + y**2 - 5')) as Expr[][])).toEqual(['(-1, -2)', '(-1, 2)', '(-2, -1)', '(-2, 1)', '(1, -2)', '(1, 2)', '(2, -1)', '(2, 1)']);
    expect(show(D.diopSolve(P('2*x + 4*y - 3')))).toBe('EmptySet');
    expect(() => D.diopSolve(P('x**3 + y**3 - 2'))).toThrow('No solver has been written for cubic_thue.');
    expect(sset(D.diopSolve(P('x**2 - 4')) as Expr[][])).toEqual(['(-2,)', '(2,)']);
  });

  it('linear and univariate equations', () => {
    expect(show(D.diopLinear(P('2*x - 3*y - 5')))).toBe('(3*t_0 - 5, 2*t_0 - 5)');
    expect(show(D.diopLinear(P('2*x - 3*y - 4*z -3')))).toBe('(t_0, 2*t_0 + 4*t_1 + 3, -t_0 - 3*t_1 - 3)');
    expect(show(D.diopLinear(P('2*x + 4*y - 3')))).toBe('EmptySet');
    expect(show(D.diopLinear(P('2*x - 3*y - 5'), null))).toBe('(-5, -5)');
    expect(show(D.diopLinear(P('x**2 - y')))).toBe('None');
    expect(show(D.baseSolutionLinear(5, 2, 3))).toBe('(-5, 5)');
    expect(show(D.baseSolutionLinear(0, 5, 7))).toBe('(0, 0)');
    expect(show(D.baseSolutionLinear(5, 2, 3, t))).toBe('(3*t - 5, 5 - 2*t)');
    expect(show(D.baseSolutionLinear(0, 5, 7, t))).toBe('(7*t, -5*t)');
    expect(show(D.baseSolutionLinear(0, 5, -7, t))).toBe('(7*t, 5*t)');
    expect(show(D.baseSolutionLinear(3, 2, 4))).toBe('EmptySet');
    expect(show(D.baseSolutionLinear(5n, 2n, -3n, t))).toBe(show(D.baseSolutionLinear(5, 2, -3, t)));
    expect(() => D.baseSolutionLinear(P('1/2'), 1, 1)).toThrow(RangeError);
    expect(sset(D.diopUnivariate(P('(x - 2)*(x - 3)**2')) as Expr[][])).toEqual(['(2,)', '(3,)']);
    expect(sset(D.diopUnivariate(P('x**3 - 4*x')) as Expr[][])).toEqual(['(-2,)', '(0,)', '(2,)']);
    expect(show(D.diopUnivariate(P('x + y')))).toBe('None');
    expect(sset(D.diopUnivariate(P('(x - 2)*(x**2 + 1)')) as Expr[][])).toEqual(['(2,)']);
    expect(sset(D.diopUnivariate(P('(x - 1)*(x**2 + x + 1)')) as Expr[][])).toEqual(['(1,)']);
    expect(sset(D.diopUnivariate(P('(2*x - 1)*(x - 3)')) as Expr[][])).toEqual(['(3,)']);
  });

  it('binary quadratics, Pell equations and Cornacchia', () => {
    expect(sset(D.diopQuadratic(P('x**2 + y**2 + 2*x + 2*y + 2'), t) as Expr[][])).toEqual(['(-1, -1)']);
    expect(show(D.diopQuadratic(P('x + y')))).toBe('None');
    expect(sset(D.diopQuadratic(P('x**2 + y**2 - 5'), null) as Expr[][])).toEqual(['(-1, -2)', '(-1, 2)', '(-2, -1)', '(-2, 1)', '(1, -2)', '(1, 2)', '(2, -1)', '(2, 1)']);
    const dn = (d: number, n: number) => D.diopDN(d, n).map(tup).join(' ');
    expect(dn(13, -4)).toBe('(3, 1) (393, 109) (36, 10)');
    expect(dn(986, 1)).toBe('(49299, 1570)');
    expect(dn(13, -3)).toBe('(7, 2) (137, 38)');
    expect(dn(2445, -20)).toBe('(445, 9) (17625560, 356454) (698095554475, 14118073569)');
    expect(dn(-1, 5)).toBe('(2, 1) (1, 2)');
    expect(dn(-3, 0)).toBe('(0, 0)');
    expect(dn(-3, -5)).toBe('');
    expect(dn(-2, 9)).toBe('(1, 2) (3, 0)');
    expect(dn(0, -1)).toBe('');
    expect(dn(0, 0)).toBe('(0, t)');
    expect(dn(0, 4)).toBe('(2, t)');
    expect(dn(0, 5)).toBe('');
    expect(dn(4, 0)).toBe('(2*t, t)');
    expect(dn(4, 12)).toBe('(4, 1)');
    expect(dn(4, -12)).toBe('(2, 2)');
    expect(dn(1, 0)).toBe('(t, t)');
    expect(dn(1, 5)).toBe('(3, 2)');
    expect(dn(1, -3)).toBe('(1, 2)');
    expect(dn(9, 7)).toBe('(4, 1)');
    expect(dn(13, 0)).toBe('(0, 0)');
    expect(dn(2, -1)).toBe('(1, 1)');
    expect(dn(3, -1)).toBe('');
    expect(dn(13, -1)).toBe('(18, 5)');
    expect(dn(13, 1)).toBe('(649, 180)');
    expect(dn(3, 1)).toBe('(2, 1)');
    expect(dn(41, -1)).toBe('(32, 5)');
    expect(dn(61, 1)).toBe('(1766319049, 226153980)');
    expect(dn(13, 27)).toBe('(220, 61) (40, 11) (768, 213) (12, 3)');
    expect(dn(5, 44)).toBe('(-7, 1) (13, 5) (17, 7) (7, 1) (-8, 2) (8, 2)');
    expect(dn(7, 36)).toBe('(-8, 2) (8, 2) (48, 18)');
    expect(dn(2, 7)).toBe('(-3, 1) (3, 1)');
    expect(dn(5, -4)).toBe('(-1, 1) (1, 1) (4, 2)');
    expect(dn(10, 9)).toBe('(7, 2) (13, 4) (57, 18)');
    expect(dn(10, -9)).toBe('(-1, 1) (1, 1) (9, 3)');
    expect(dn(17, 16)).toBe('(13, 3) (21, 5) (132, 32)');
    expect(dn(3, 24)).toBe('(-6, 2)');
    expect(dn(3, -24)).toBe('');
    expect(dn(5, 20)).toBe('(-5, 1) (5, 1) (10, 4)');
    expect(dn(6, -15)).toBe('(3, 2) (9, 4)');
    const bf = (d: number, n: number) => D.diopBfDN(d, n).map(tup).join(' ');
    expect(bf(13, -4)).toBe('(3, 1) (-3, 1) (36, 10)');
    expect(bf(986, 1)).toBe('(49299, 1570)');
    expect(bf(13, 0)).toBe('(0, 0)');
    expect(bf(-3, 0)).toBe('(0, 0)');
    expect(bf(0, 0)).toBe('(0, t)');
    expect(bf(4, 0)).toBe('(2*t, t) (-2*t, t)');
    expect(bf(13, 27)).toBe('(12, 3) (-12, 3) (40, 11) (-40, 11)');
    expect(bf(13, -27)).toBe('(5, 2) (-5, 2) (21, 6) (-21, 6)');
    expect(bf(2, 2)).toBe('(2, 1)');
    expect(bf(5, -4)).toBe('(1, 1) (-1, 1) (4, 2)');
    expect(bf(5, 11)).toBe('(4, 1) (-4, 1)');
    const co = (a: number, b: number, m: number) => sset(D.cornacchia(a, b, m));
    expect(co(2, 3, 35)).toEqual(['(2, 3)', '(4, 1)']);
    expect(co(1, 1, 25)).toEqual(['(4, 3)']);
    expect(co(1, 1, 1)).toEqual(['(1, 0)']);
    expect(co(1, 2, 2)).toEqual(['(0, 1)']);
    expect(co(3, 5, 4)).toEqual([]);
    expect(co(1, 3, 1)).toEqual(['(1, 0)']);
    expect(co(1, 1, 2)).toEqual(['(1, 1)']);
    expect(co(1, 1, 5)).toEqual(['(2, 1)']);
    expect(co(2, 1, 1)).toEqual(['(0, 1)']);
    expect(co(1, 5, 9)).toEqual(['(2, 1)']);
    expect(co(1, 4, 8)).toEqual(['(2, 1)']);
    expect(co(3, 1, 3)).toEqual([]);
    expect(co(1, 1, 3)).toEqual([]);
    expect(co(1, 1, 50)).toEqual(['(7, 1)']);
    expect(co(1, 2, 9)).toEqual(['(1, 2)']);
    expect(co(1, 1, 4)).toEqual([]);
    expect([co(1, 1, 13), co(1, 1, 65), co(1, 3, 13), co(1, 3, 19), co(3, 4, 19), co(2, 5, 13), co(1, 7, 23), co(5, 3, 17), co(1, 2, 11), co(2, 3, 5)]).toEqual([
      ['(3, 2)'],
      ['(7, 4)', '(8, 1)'],
      ['(1, 2)'],
      ['(4, 1)'],
      ['(1, 2)'],
      ['(2, 1)'],
      ['(4, 1)'],
      ['(1, 2)'],
      ['(3, 1)'],
      ['(1, 1)'],
    ]);
    const g = D.PQa(13n, 4n, 5n);
    expect([g.next().value, g.next().value].map(tup)).toEqual(['(13, 4, 3, 3, 1, -1)', '(-1, 1, 1, 4, 1, 3)']);
  });

  it('the transformation to x**2 - D*y**2 = N', () => {
    const tr = (s: string) => {
      const r = D.transformationToDN(P(s));
      return sj.isNoMatch(r) ? 'None' : r.map(String).join(' ');
    };
    expect(tr('x**2 - 3*x*y - y**2 - 2*y + 1')).toBe('Matrix([[1/26, 3/26], [0, 1/13]]) Matrix([[-6/13], [-4/13]])');
    expect(tr('x**2 + 3*x - y**2 + 5*y')).toBe('Matrix([[1/2, 0], [0, -1/2]]) Matrix([[-3/2], [5/2]])');
    expect(tr('x**2 - 5*y**2 + 3*y')).toBe('Matrix([[1/20, 0], [0, -1/10]]) Matrix([[0], [3/10]])');
    expect(tr('x + y')).toBe('None');
    expect(show(D.findDN(P('x**2 - 3*x*y - y**2 - 2*y + 1')))).toBe('(13, -884)');
    expect(show(D.findDN(P('x**2 + 3*x - y**2 + 5*y')))).toBe('(1, -16)');
    expect(show(D.findDN(P('x + y')))).toBe('None');
  });

  it('ternary quadratics', () => {
    const tq = (s: string, param = false) => show(D.diopTernaryQuadratic(P(s), param));
    expect(tq('x**2 + 3*y**2 - z**2')).toBe('(1, 0, 1)');
    expect(tq('4*x**2 + 5*y**2 - z**2')).toBe('(1, 0, 2)');
    expect(tq('45*x**2 - 7*y**2 - 8*x*y - z**2')).toBe('(28, 45, 105)');
    expect(tq('x**2 - 49*y**2 - z**2 + 13*z*y -8*x*y')).toBe('(9, 1, 5)');
    expect(tq('x + y')).toBe('None');
    expect(tq('x**2 + y**2 + z**2')).toBe('EmptySet');
    expect(tq('x**2 + y**2 - z**2', true)).toBe('(2*p*q, p**2 - q**2, p**2 + q**2)');
    expect(tq('x*y + y*z + 3*x*z')).toBe('(0, -1, 0)');
    expect(tq('x*y + y*z')).toBe('(-1, 0, n1)');
    expect(tq('y**2 + x*z')).toBe('(1, -1, -1)');
    expect(tq('z**2 + x*y')).toBe('(-1, 1, -1)');
    expect(tq('3*x**2 + 2*y*z')).toBe('(-2, 3, -2)');
    expect(tq('x**2 + y*z + 2*z**2')).toBe('(0, 1, 0)');
    expect(tq('x**2 + 2*y**2 + 2*y*z - z**2')).toBe('(1, 0, 1)');
    expect(tq('x**2 + 2*x*y + 2*y**2 + z**2')).toBe('EmptySet');
    expect(tq('x**2 + x*y + y**2 + z**2 + y*z')).toBe('EmptySet');
    // SymPy fails with a TypeError: the transformed form (x + y)**2 + z**2 has two variables
    expect(() => D.diopTernaryQuadratic(P('x**2 + 2*x*y + y**2 + z**2'))).toThrow(sj.NotImplementedError);
    const pt = (s: string) => show(D.parametrizeTernaryQuadratic(P(s)));
    expect(pt('2*x**2 + y**2 - 2*z**2')).toBe('(p**2 - 2*q**2, -2*p**2 + 4*p*q - 4*p*r - 4*q**2, p**2 - 4*p*q + 2*q**2 - 4*q*r)');
    expect(pt('4*x**2 + 2*y**2 - 3*z**2')).toBe('(2*p**2 - 3*q**2, -4*p**2 + 12*p*q - 6*q**2, 4*p**2 - 8*p*q + 6*q**2)');
    expect(pt('x + y')).toBe('None');
    expect(pt('x**2 - y**2')).toBe('None');
    expect(pt('y**2 - 2*z**2 + x*y')).toBe('EmptySet');
    expect(pt('x*y - z**2')).toBe('(-q**2, -p**2 + 2*p*q - q**2, -p*q + q**2)');
    expect(pt('3*x**2 + 3*y**2 - 3*z**2')).toBe('(2*p*q, p**2 - q**2, p**2 + q**2)');
    expect(pt('x**2 + y**2 - 4*z**2')).toBe('(8*p*q, 2*p**2 - 8*q**2, p**2 + 4*q**2)');
    expect(pt('x**2 - 2*y**2')).toBe('None');
    // SymPy raises IndexError (no solution to parametrize)
    expect(pt('x**2 + y**2 + z**2')).toBe('EmptySet');
    const tn = (s: string, param = false) => show(D.diopTernaryQuadraticNormal(P(s), param));
    expect(tn('x**2 + 3*y**2 - z**2')).toBe('(1, 0, 1)');
    expect(tn('4*x**2 + 5*y**2 - z**2')).toBe('(1, 0, 2)');
    expect(tn('34*x**2 - 3*y**2 - 301*z**2')).toBe('(4, 9, 1)');
    expect(tn('x**2 + y**2 + z**2')).toBe('EmptySet');
    expect(tn('x**2 + y**2 - z**2 + x*y')).toBe('None');
    expect(tn('x**2 - 5*y**2 + 3*z**2')).toBe('EmptySet');
    expect(tn('x**2 + 2*y**2 - 3*z**2')).toBe('(1, 1, 1)');
    expect(tn('-x**2 + 2*y**2 + 3*z**2')).toBe('EmptySet');
    expect(tn('5*x**2 - 3*y**2 + 2*z**2')).toBe('EmptySet');
    expect(tn('x**2 + 3*y**2 - 7*z**2')).toBe('(5, 1, 2)');
    expect(tn('2*x**2 + 3*y**2 - 5*z**2', true)).toBe('(3*p**2 - 5*q**2, -3*p**2 + 10*p*q - 5*q**2, 3*p**2 - 6*p*q + 5*q**2)');
    expect(tn('9*x**2 + 4*y**2 - 25*z**2')).toBe('(0, 5, 2)');
    expect(tn('18*x**2 + 50*y**2 - 98*z**2')).toBe('(0, 7, 5)');
    expect(tn('x**2 + 6*y**2 - 15*z**2')).toBe('(3, 1, 1)');
    expect(tn('x**2 + 2*y**2 - 7*z**2')).toBe('EmptySet');
  });

  it('the helpers of the ternary solver', () => {
    expect(show(D.sqfNormal(2 * 3 ** 2 * 5, 2 * 5 * 11, 2 * 7 ** 2 * 11))).toBe('(11, 1, 5)');
    expect(show((D.sqfNormal(2 * 3 ** 2 * 5, 2 * 5 * 11, 2 * 7 ** 2 * 11, true) as bigint[][]).map(tup))).toBe('((3, 1, 7), (5, 55, 11), (11, 1, 5))');
    expect(show(D.sqfNormal(4, 9, -1))).toBe('(1, 1, -1)');
    expect(show((D.sqfNormal(6, 10, 15, true) as bigint[][]).map(tup))).toBe('((1, 1, 1), (6, 10, 15), (5, 1, 6))');
    expect([D.squareFactor(24), D.squareFactor(-36 * 3), D.squareFactor(1), D.squareFactor(new Map([[3, 2], [2, 1], [-1, 1]]))]).toEqual([2n, 6n, 1n, 3n]);
    const ld = (a: number, b: number) => show(D.ldescent(a, b));
    expect(ld(1, 1)).toBe('(1, 1, 0)');
    expect(ld(4, -7)).toBe('(2, -1, 0)');
    expect(ld(5, -1)).toBe('(2, 1, -1)');
    expect(ld(-1, -1)).toBe('EmptySet');
    expect(ld(3, 7)).toBe('EmptySet');
    expect(ld(2, 3)).toBe('EmptySet');
    expect(ld(2, 7)).toBe('(3, -1, 1)');
    expect(ld(-2, 7)).toBe('EmptySet');
    expect(ld(-7, 2)).toBe('(1, 1, 2)');
    expect(ld(6, 3)).toBe('(3, 1, -1)');
    expect(ld(7, -10)).toBe('EmptySet');
    expect(ld(13, 3)).toBe('(4, 1, -1)');
    expect(ld(-3, 13)).toBe('(-1, -2, 1)');
    // SymPy fails with a TypeError (ldescent(3, 7) has no solution, so neither has ldescent(7, 3))
    expect(ld(7, 3)).toBe('EmptySet');
    // SymPy fails with a TypeError: the descent reaches ldescent(3, 2), which has no solution
    expect(() => D.ldescent(3, 11)).toThrow(sj.NotImplementedError);
    expect(() => D.ldescent(0, 1)).toThrow('A and B must be non-zero integers');
    const de = (a: number, b: number) => show(D.descent(a, b));
    expect(de(3, 1)).toBe('(1, 0, 1)');
    expect(de(41, -113)).toBe('(-16, -3, 1)');
    expect(de(1, 5)).toBe('(1, 1, 0)');
    expect(de(-1, 1)).toBe('(1, 0, 1)');
    expect(de(1, -1)).toBe('(1, 1, 0)');
    expect(de(2, 2)).toBe('(2, 1, 1)');
    expect(de(5, -1)).toBe('(2, 1, 1)');
    expect(de(-7, 2)).toBe('(-1, 1, 2)');
    expect(de(6, 3)).toBe('(-3, -1, -1)');
    expect(de(2, 7)).toBe('(-3, -1, -1)');
    // SymPy fails with a TypeError (no square root of A modulo B)
    expect(() => D.descent(3, -13)).toThrow(RangeError);
    const gr = (w: bigint | sj.NoMatchResult, a: number, b: number) => show(D.gaussianReduce(w as bigint, a, b));
    expect(gr(sj.sqrtMod(19, 101), 19, 101)).toBe('(1, -4)');
    expect(gr(sj.sqrtMod(11, 14), 11, 14)).toBe('(5, 1)');
    expect(gr(sj.sqrtMod(6, 95), 6, 95)).toBe('(14, 1)');
    expect(gr(3n, -2, -7)).toBe('(-1, 2)');
    expect(gr(4n, 3, 13)).toBe('(4, 1)');
    expect(gr(5n, 30, 7)).toBe('(-2, 1)');
    expect(gr(2n, 3, 7)).toBe('(2, 1)');
    const ho = (...v: number[]) => show(D.holzer(...(v as [number, number, number, number, number, number])));
    expect(ho(2, 7, 13, 4, 79, 23)).toBe('(2, 7, 13)');
    expect(ho(2, 6, 2, 1, 1, 10)).toBe('(2, 6, 2)');
    expect(ho(1, 0, 1, 1, 1, 1)).toBe('(1, 0, 1)');
    expect(ho(3, 4, 5, 1, 1, 1)).toBe('(3, 4, 5)');
    expect(ho(4, 5, 1, 1, 1, 41)).toBe('(4, 5, 1)');
    expect(() => ho(1, 1, 1, 1, 1, 1)).toThrow('bad starting solution');
    expect(ho(4, 3, 5, 1, 1, 1)).toBe('(4, 3, 5)');
    expect(ho(1, 7, 5, 1, 1, 2)).toBe('(1, 7, 5)');
    // reductions that do not give a smaller solution keep the starting one
    for (const v of [[20, 21, 29, 1, 1, 1], [7, 1, 5, 1, 1, 2], [17, 7, 13, 1, 1, 2], [41, 1, 29, 1, 1, 2], [119, 120, 169, 1, 1, 1], [3, 1, 2, 1, 3, 3]]) {
      expect(ho(...v)).toBe(tup(v.slice(0, 3)));
    }
  });

  it('Pythagorean equations and sums of powers', () => {
    expect(show(D.diopGeneralPythagorean(P('a**2 + b**2 + c**2 - d**2')))).toBe('(m1**2 + m2**2 - m3**2, 2*m1*m3, 2*m2*m3, m1**2 + m2**2 + m3**2)');
    expect(show(D.diopGeneralPythagorean(P('9*a**2 - 4*b**2 + 16*c**2 + 25*d**2 + e**2')))).toBe(
      '(10*m1**2 + 10*m2**2 + 10*m3**2 - 10*m4**2, 15*m1**2 + 15*m2**2 + 15*m3**2 + 15*m4**2, 15*m1*m4, 12*m2*m4, 60*m3*m4)',
    );
    expect(show(D.diopGeneralPythagorean(P('a**2 + b**2 + c**2 - d**2'), null))).toBe('(t_0**2 + t_1**2 - t_2**2, 2*t_0*t_2, 2*t_1*t_2, t_0**2 + t_1**2 + t_2**2)');
    expect(show(D.diopGeneralPythagorean(P('-a**2 - b**2 - c**2 + 4*d**2')))).toBe('(2*m1**2 + 2*m2**2 - 2*m3**2, 4*m1*m3, 4*m2*m3, m1**2 + m2**2 + m3**2)');
    expect(show(D.diopGeneralPythagorean(P('-9*a**2 + b**2 + c**2 + d**2')))).toBe('(m1**2 + m2**2 + m3**2, 3*m1**2 + 3*m2**2 - 3*m3**2, 6*m1*m3, 6*m2*m3)');
    expect(show(D.diopGeneralPythagorean(P('a**2 - 4*b**2 + 9*c**2 + 16*d**2')))).toBe('(6*m1**2 + 6*m2**2 - 6*m3**2, 3*m1**2 + 3*m2**2 + 3*m3**2, 4*m1*m3, 3*m2*m3)');
    expect(show(D.diopGeneralPythagorean(P('x + y')))).toBe('None');
    expect(sset(D.diopGeneralSumOfSquares(P('a**2 + b**2 + c**2 + d**2 + e**2 - 2345')) as Expr[][])).toEqual(['(15, 22, 22, 24, 24)']);
    expect(sset(D.diopGeneralSumOfSquares(P('a**2 + b**2 + c**2 + d**2 + e**2 - 2345'), 3) as Expr[][])).toHaveLength(3);
    expect(show(D.diopGeneralSumOfSquares(P('x + y')))).toBe('None');
    expect(sset(D.diopGeneralSumOfEvenPowers(P('a**4 + b**4 - (2**4 + 3**4)')) as Expr[][])).toEqual(['(2, 3)']);
    expect(show(D.diopGeneralSumOfEvenPowers(P('x + y')))).toBe('None');
    const ps = (n: number) => show(D.primeAsSumOfTwoSquares(n));
    expect([7, 5, 13, 29, 41, 1009, 241, 2, 17, 73, 409, 3361, 1201].map(ps)).toEqual(
      ['EmptySet', '(1, 2)', '(2, 3)', '(2, 5)', '(4, 5)', '(15, 28)', '(4, 15)', 'EmptySet', '(1, 4)', '(3, 8)', '(3, 20)', '(15, 56)', '(24, 25)'],
    );
    expect(() => D.primeAsSumOfTwoSquares(9)).toThrow('p should be a prime number');
    const s3 = (n: number) => show(D.sumOfThreeSquares(n));
    expect([9, 25].map(s3)).toEqual(['(0, 0, 3)', '(0, 0, 5)']);
    expect([44542, 0, 7, 28, 34, 16, 11, 5, 1414 * 4, 27, 3, 24, 19, 51, 6, 41].map(s3)).toEqual([
      '(18, 37, 207)',
      '(0, 0, 0)',
      'EmptySet',
      'EmptySet',
      '(3, 3, 4)',
      '(0, 0, 4)',
      '(1, 1, 3)',
      '(0, 1, 2)',
      '(12, 34, 66)',
      '(1, 1, 5)',
      '(1, 1, 1)',
      '(2, 2, 4)',
      '(1, 3, 3)',
      '(1, 5, 5)',
      '(1, 1, 2)',
      '(1, 2, 6)',
    ]);
    expect(() => D.sumOfThreeSquares(-1)).toThrow('n should be a non-negative integer');
    const s4 = (n: number | bigint) => show(D.sumOfFourSquares(n));
    expect([3456, 1294585930293n, 0, 7, 6, 5, 4 * 7, 15, 31].map(s4)).toEqual([
      '(8, 8, 32, 48)',
      '(0, 1234, 2161, 1137796)',
      '(0, 0, 0, 0)',
      '(1, 1, 1, 2)',
      '(0, 1, 1, 2)',
      '(0, 0, 1, 2)',
      '(2, 2, 2, 4)',
      '(1, 1, 2, 3)',
      '(1, 1, 2, 5)',
    ]);
    expect(() => D.sumOfFourSquares(-1)).toThrow('n should be a non-negative integer');
  });

  it('powerRepresentation and sumOfSquares', () => {
    const pr = (n: number, pw: number, k: number, zeros = false) => [...D.powerRepresentation(n, pw, k, { zeros })].map(tup).join(' ');
    expect(pr(1729, 3, 2)).toBe('(9, 10) (1, 12)');
    expect(pr(125, 2, 3, true)).toBe('(5, 6, 8) (3, 4, 10) (0, 5, 10) (0, 2, 11)');
    expect(pr(-8, 3, 1)).toBe('(-2,)');
    expect(pr(-8, 2, 1)).toBe('');
    expect(pr(0, 2, 2, true)).toBe('(0, 0)');
    expect(pr(0, 2, 2)).toBe('');
    expect(pr(7, 1, 1)).toBe('(7,)');
    expect(pr(1, 3, 1)).toBe('(1,)');
    expect(pr(27, 3, 1)).toBe('(3,)');
    expect(pr(16, 3, 1)).toBe('');
    expect(pr(15, 2, 1)).toBe('');
    expect(pr(5, 1, 2)).toBe('(1, 4) (2, 3)');
    expect(pr(5, 1, 3, true)).toBe('(0, 0, 5) (0, 1, 4) (0, 2, 3) (1, 1, 3) (1, 2, 2)');
    expect(pr(4 * 14, 2, 3)).toBe('(2, 4, 6)');
    expect(pr(7, 2, 3)).toBe('');
    expect(pr(40, 2, 6)).toBe('(1, 1, 2, 3, 3, 4)');
    expect(pr(11, 2, 4)).toBe('');
    expect(pr(24, 2, 4)).toBe('');
    expect(pr(13, 2, 3)).toBe('');
    expect(pr(13, 2, 2)).toBe('(2, 3)');
    expect(pr(7, 2, 2)).toBe('');
    expect(pr(2, 2, 2)).toBe('(1, 1)');
    expect(pr(21, 2, 2)).toBe('');
    expect(pr(25, 2, 2)).toBe('(3, 4)');
    expect(pr(8, 3, 2)).toBe('');
    expect(pr(3, 2, 5)).toBe('');
    expect(pr(10, 2, 3, true)).toBe('(0, 1, 3)');
    expect(pr(-8, 3, 2)).toBe('');
    expect(pr(4, 3, 2)).toBe('');
    expect(pr(2, 4, 2)).toBe('(1, 1)');
    expect(pr(39, 2, 5)).toBe('(1, 2, 3, 3, 4)');
    expect(pr(100, 2, 4)).toBe('(5, 5, 5, 5) (1, 5, 5, 7) (1, 1, 7, 7) (2, 4, 4, 8) (1, 3, 3, 9)');
    expect(pr(1, 2, 4)).toBe('');
    expect(pr(14, 2, 4)).toBe('');
    expect(pr(40, 2, 35)).toBe('');
    expect(pr(3, 2, 2, true)).toBe('');
    expect(pr(9, 2, 2)).toBe('');
    expect(pr(18, 2, 2)).toBe('(3, 3)');
    expect(pr(17, 4, 2)).toBe('(1, 2)');
    expect(pr(16 * 4, 2, 3)).toBe('');
    expect(pr(1, 2, 3)).toBe('');
    expect(pr(13, 2, 3, true)).toBe('(0, 2, 3)');
    expect(pr(29, 2, 4, true)).toBe('(0, 0, 2, 5) (0, 2, 3, 4)');
    expect(pr(4, 2, 1)).toBe('(2,)');
    expect(pr(32, 5, 1)).toBe('(2,)');
    expect(pr(64, 6, 1)).toBe('(2,)');
    expect(pr(2, 2, 3)).toBe('');
    expect(pr(4, 1, 2, true)).toBe('(0, 4) (1, 3) (2, 2)');
    expect(() => [...D.powerRepresentation(0, 2, 0)]).toThrow('Expecting positive integers for `(p, k)`, but got `(2, 0)`');
    expect(() => [...D.powerRepresentation(1, 0, 1)]).toThrow(RangeError);
    expect([...D.powerRepresentation(1729n, 3n, 2n)].map(tup)).toEqual(['(9, 10)', '(1, 12)']);
    const sq = (n: number, k: number, zeros = false) => [...D.sumOfSquares(n, k, { zeros })].map(tup).join(' ');
    expect(sq(25, 2)).toBe('(3, 4)');
    expect(sq(25, 2, true)).toBe('(3, 4) (0, 5)');
    expect(sq(25, 4)).toBe('(1, 2, 2, 4)');
    expect([...D.sumOfSquares(25, 2)].map(tup)).toEqual(['(3, 4)']);
  });
});
