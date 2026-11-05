// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Cases of sympy/stats/tests/test_stochastic_process.py replayed on
// src/stats/stochasticprocesstypes.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Ge, Gt, Le, Lt, Ne, Matrix, MatrixSymbol, Rational, S, Sym, and, exp, not, or, round, simplify, str, symbols, sympify } from '../../src';
import type { Expr } from '../../src';
import { P, RandomIndexedSymbol, expectation as E, variance } from '../../src/stats';
import { Contains, Lopen, Naturals0, Range, Ropen, interval } from '../../src/sets/sets';
import { ExpectationNode, ProbabilityNode } from '../../src/stats/symbolicprobability';
import {
  BernoulliProcess,
  ContinuousMarkovChain,
  DiscreteMarkovChain,
  GammaProcess,
  PoissonProcess,
  StochasticStateSpaceOf,
  TransitionMatrixOf,
  WienerProcess,
} from '../../src/stats/stochasticprocesstypes';

const r = (n: number, d: number) => Rational.of(n, d);
const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : e instanceof Matrix ? e.toString() : str(e as Expr));
const sym = (names: string, a?: Record<string, boolean>) => symbols(names, a) as [Sym, Sym, Sym, Sym, Sym, Sym];
const m = (rows: (number | Expr)[][]) => Matrix.of(rows);

describe('DiscreteMarkovChain', () => {
  it('symbolic chain', () => {
    const X = DiscreteMarkovChain('X');
    expect(X.stateSpace).toBeInstanceOf(Range);
    expect(X.indexSet).toBe(Naturals0);
    expect(s(X.transitionProbabilities)).toBe('_T');
    const [t] = sym('t', { positive: true, integer: true });
    expect(X.at(t)).toBeInstanceOf(RandomIndexedSymbol);
    expect(s(E(X.at(0)))).toBe('Expectation(X[0])');
    expect(() => DiscreteMarkovChain(1 as unknown as string)).toThrow(TypeError);
    expect(() => X.call(t)).toThrow('Use []');
    expect(() => X.communicationClasses()).toThrow('symbolic matrix');
    expect(() => X.canonicalForm()).toThrow('symbolic matrix');
    expect(() => X.decompose()).toThrow('symbolic matrix');
    const [nz] = sym('n', { integer: true });
    const TZ = MatrixSymbol('M', nz, nz);
    const YZ = DiscreteMarkovChain('Y', Range.of(nz) as Range, TZ);
    expect(s(P(Eq(YZ.at(2), 1), Eq(YZ.at(1), 0)))).toBe('M[0, 1]');
  });
  it('state spaces', () => {
    const [a, rainy, cloudy, sunny] = sym('a Rainy Cloudy Sunny', { real: true });
    const spaces: [unknown, string][] = [
      [[1, 2, 3], '{1, 2, 3}'],
      [Range.of(-1, 5, 2), '{-1, 1, 3}'],
      [[rainy, cloudy, sunny], '{Cloudy, Rainy, Sunny}'],
      [[a, exp(a), 1], '{1, a, exp(a)}'],
    ];
    for (const [ss, out] of spaces) {
      const Y = DiscreteMarkovChain('Y', ss as Expr[]);
      expect(s(Y.transitionProbabilities)).toBe('_T');
      expect(s(Y.stateSpace)).toBe(out);
      expect(s(Y.numberOfStates)).toBe('3');
      expect(s(P(Eq(Y.at(2), 1), Eq(Y.at(0), 2), { evaluate: false }))).toBe('Probability(Eq(Y[2], 1), Eq(Y[0], 2))');
      expect(s(E(Y.at(0)))).toBe('Expectation(Y[0])');
    }
    expect(() => DiscreteMarkovChain('Y', { 1: 1 } as unknown as Expr[])).toThrow(TypeError);
    expect(() => DiscreteMarkovChain('Y', [1, 1])).toThrow('unique');
    const [t] = sym('t', { positive: true, integer: true });
    expect(s(DiscreteMarkovChain('Y', Range.of(1, t, 2) as Range).numberOfStates)).toBe('ceiling(t/2 - 1/2)');
  });
  it('transition matrices', () => {
    const [a] = sym('a', { real: true });
    for (const T of [Matrix.zeros(0, 0), m([[0, 1], [1, 0]]), m([[S.Pi, sympify(1).sub(S.Pi)], [a, sympify(1).sub(a)]])]) {
      const Z = DiscreteMarkovChain('Y', undefined, T);
      expect(s(Z.numberOfStates)).toBe(String(T.rows));
    }
    const T = m([[0.5, 0.2, 0.3], [0.2, 0.5, 0.3], [0.2, 0.3, 0.5]]);
    const TS = MatrixSymbol('T', 3, 3);
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], T);
    const YS = DiscreteMarkovChain('Y', ['One', 'Two', 3], TS);
    expect(s(Y.jointDistribution(1, Y.at(2), 3))).toBe('JointDistribution(Y[1], Y[2], Y[3])');
    expect(() => Y.jointDistribution(Y.at(1).indexedSymbol, Y.at(2).indexedSymbol)).toThrow('Expected a RandomIndexedSymbol');
    expect(s(round(P(Eq(Y.at(3), 2), Eq(Y.at(1), 1)), 2))).toBe('0.36');
    expect(s(P(Eq(YS.at(1), 1), Eq(YS.at(2), 2)))).toBe('Probability(Eq(Y[1], 1))');
    expect(s(P(Eq(YS.at(3), 3), Eq(YS.at(1), 1)))).toBe('T[0, 2]*T[1, 0] + T[1, 1]*T[1, 2] + T[1, 2]*T[2, 2]');
    const TO = m([[0.25, 0.75, 0], [0, 0.25, 0.75], [0.75, 0, 0.25]]);
    expect(s(round(P(Eq(Y.at(3), 2), and(Eq(Y.at(1), 1), TransitionMatrixOf(Y, TO))), 3))).toBe('0.375');
    expect(s(E(Y.at(3), undefined, { evaluate: false }))).toBe('Expectation(Y[3])');
    expect(s(round(E(Y.at(3), Eq(Y.at(2), 1)), 2))).toBe('1.10');
    const TSO = MatrixSymbol('T', 4, 4);
    expect(() => P(Eq(YS.at(3), 2), and(Eq(YS.at(1), 1), TransitionMatrixOf(YS, TSO)))).toThrow('not compatible');
    expect(() => DiscreteMarkovChain('Z', [0, 1, 2], new Sym('M') as unknown as Matrix)).toThrow(TypeError);
    expect(() => DiscreteMarkovChain('Z', [0, 1, 2], MatrixSymbol('T', 3, 4))).toThrow('square');
    expect(() => E(Y.at(3), Eq(Y.at(2), 6))).toThrow('not in the state space');
    expect(() => E(Y.at(2), Eq(Y.at(3), 1))).toThrow('Incorrect given condition');
  });
  it('extended probability queries', () => {
    const X = DiscreteMarkovChain('X');
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], m([[0.5, 0.2, 0.3], [0.2, 0.5, 0.3], [0.2, 0.3, 0.5]]));
    const TO1 = m([[r(1, 4), r(3, 4), 0], [r(1, 3), r(1, 3), r(1, 3)], [0, r(1, 4), r(3, 4)]]);
    const cond3 = and(Eq(Y.at(2), 1), Eq(Y.at(1), 1), Eq(Y.at(0), 0));
    expect(s(P(cond3, and(Eq(P(Eq(Y.at(0), 0)), r(1, 4)), TransitionMatrixOf(Y, TO1))))).toBe('1/16');
    expect(s(P(cond3, TransitionMatrixOf(Y, TO1)))).toBe('Probability(Eq(Y[0], 0))/4');
    const ss1 = and(Eq(X.at(0), 2), StochasticStateSpaceOf(X, [0, 1, 2]), TransitionMatrixOf(X, TO1));
    expect(s(P(and(Lt(X.at(1), 2), Gt(X.at(1), 0)), ss1))).toBe('1/4');
    const ss2 = and(Eq(X.at(0), 2), StochasticStateSpaceOf(X, [0, '_zero', 1]), TransitionMatrixOf(X, TO1));
    expect(s(P(and(Lt(X.at(1), 2), Gt(X.at(1), 0)), ss2))).toBe('1/4');
    expect(s(P(and(Ne(X.at(1), 2), Ne(X.at(1), 1)), ss1))).toBe('0');
    expect(s(P(cond3, Eq(Y.at(1), 1)))).toBe('0.1*Probability(Eq(Y[0], 0))');
  });
  it('properties', () => {
    const TO2 = m([[1, 0, 0], [r(1, 3), r(1, 3), r(1, 3)], [0, r(1, 4), r(3, 4)]]);
    const TO3 = m([[r(1, 4), r(3, 4), 0], [r(1, 3), r(1, 3), r(1, 3)], [0, r(1, 4), r(3, 4)]]);
    const Y2 = DiscreteMarkovChain('Y', undefined, TO2);
    const Y3 = DiscreteMarkovChain('Y', undefined, TO3);
    expect(s(Y3.fundamentalMatrix())).toBe('Matrix([[176/125, 81/125, -132/125], [36/125, 141/125, -52/125], [-44/125, -39/125, 208/125]])');
    expect(Y2.isAbsorbingChain()).toBe(S.true);
    expect(Y3.isAbsorbingChain()).toBe(S.false);
    expect(s(Y2.canonicalForm())).toBe(`[[0, 1, 2], ${s(TO2)}]`);
    expect(s(Y2.decompose())).toBe('[[0, 1, 2], Matrix([[1]]), Matrix([[1/3], [0]]), Matrix([[1/3, 1/3], [1/4, 3/4]])]');
    expect(s(Y3.decompose())).toBe(`[[0, 1, 2], ${s(TO3)}, Matrix(0, 3, []), Matrix(0, 0, [])]`);
    const TO4 = m([[r(1, 5), r(2, 5), r(2, 5)], [r(1, 10), r(1, 2), r(2, 5)], [r(3, 5), r(3, 10), r(1, 10)]]);
    const Y4 = DiscreteMarkovChain('Y', undefined, TO4);
    expect(s(Y4.limitingDistribution)).toBe('Matrix([[11/39, 16/39, 4/13]])');
    expect(Y4.isRegular()).toBe(S.true);
    expect(Y4.isErgodic()).toBe(S.true);
    const Y5 = DiscreteMarkovChain('Y', undefined, MatrixSymbol('T', 3, 3));
    expect(s(Y5.limitingDistribution)).toBe('Lambda((wm, T), Eq(wm*T, wm))');
    const TO6 = m([[1, 0, 0, 0, 0], [r(1, 2), 0, r(1, 2), 0, 0], [0, r(1, 2), 0, r(1, 2), 0], [0, 0, r(1, 2), 0, r(1, 2)], [0, 0, 0, 0, 1]]);
    const Y6 = DiscreteMarkovChain('Y', undefined, TO6);
    expect(s(Y6.fundamentalMatrix())).toBe('Matrix([[3/2, 1, 1/2], [1, 2, 1], [1/2, 1, 3/2]])');
    expect(s(Y6.absorbingProbabilities())).toBe('Matrix([[3/4, 1/4], [1/2, 1/2], [1/4, 3/4]])');
    expect(s(Y6.absorbingProbabilites())).toBe('Matrix([[3/4, 1/4], [1/2, 1/2], [1/4, 3/4]])');
    expect(Y6.isAbsorbingState(0)).toBe(true);
    expect(Y6.isAbsorbingState(1)).toBe(false);
    expect(Y6.isAbsorbingState(9)).toBe('unknown');
    const TO7 = m([[r(1, 2), r(1, 4), r(1, 4)], [r(1, 2), 0, r(1, 2)], [r(1, 4), r(1, 4), r(1, 2)]]);
    const Y7 = DiscreteMarkovChain('Y', undefined, TO7);
    expect(Y7.isAbsorbingChain()).toBe(S.false);
    expect(s(Y7.fundamentalMatrix())).toBe('Matrix([[86/75, 1/25, -14/75], [2/25, 21/25, 2/25], [-14/75, 1/25, 86/75]])');
    // zero-sized matrix
    const X0 = DiscreteMarkovChain('X', undefined, Matrix.zeros(0, 0));
    expect(s(X0.numberOfStates)).toBe('0');
    expect(s(X0.stationaryDistribution())).toBe('Matrix(1, 0, [])');
    expect(X0.communicationClasses()).toEqual([]);
    expect(s(X0.canonicalForm())).toBe('[[], Matrix(0, 0, [])]');
    expect(X0.isRegular()).toBe(S.false);
    expect(X0.isErgodic()).toBe(S.false);
  });
  it('fundamental matrix errors', () => {
    expect(s(DiscreteMarkovChain('Y', undefined, m([[0, 1], [1, 0]])).fundamentalMatrix())).toBe('Matrix([[3/4, 1/4], [1/4, 3/4]])');
    expect(s(DiscreteMarkovChain('Y', undefined, m([[1, 0, 0], [0, 1, 0], [r(1, 2), 0, r(1, 2)]])).fundamentalMatrix())).toBe('Matrix([[2]])');
    expect(() => DiscreteMarkovChain('Y', undefined, m([[1, 0], [0, 1]])).fundamentalMatrix()).toThrow("doesn't exist");
  });
  it('communication classes', () => {
    const cls = (T: Matrix) => DiscreteMarkovChain('Y', undefined, T).communicationClasses().map(([c, rec, p]) => `${s(c)} ${s(rec)} ${s(p)}`);
    const TO7 = m([[0, 5, 5, 0, 0], [0, 0, 0, 10, 0], [5, 0, 5, 0, 0], [0, 10, 0, 0, 0], [0, 3, 0, 3, 4]]).scale(r(1, 10));
    expect(cls(TO7)).toEqual(['[1, 3] True 2', '[0, 2] False 1', '[4] False 1']);
    const TO8 = m([[0, 0, 0, 10, 0, 0], [5, 0, 5, 0, 0, 0], [0, 4, 0, 0, 0, 6], [10, 0, 0, 0, 0, 0], [0, 10, 0, 0, 0, 0], [0, 0, 0, 5, 5, 0]]).scale(r(1, 10));
    expect(cls(TO8)).toEqual(['[0, 3] True 2', '[1, 2, 5, 4] False 2']);
    const TO9 = m([
      [2, 0, 0, 3, 0, 0, 3, 2, 0, 0], [0, 10, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 3, 3], [0, 0, 0, 3, 0, 0, 6, 1, 0, 0], [0, 0, 0, 0, 5, 5, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 10, 0, 0, 0, 0], [4, 0, 0, 5, 0, 0, 1, 0, 0, 0], [2, 0, 0, 4, 0, 0, 2, 2, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 4, 2], [0, 0, 4, 0, 0, 0, 0, 0, 3, 3],
    ]).scale(r(1, 10));
    expect(cls(TO9)).toEqual(['[0, 3, 6, 7] True 1', '[1] True 1', '[2, 8, 9] False 1', '[5] True 1', '[4] False 1']);
    const T = m([[1, 0, 0, 0, 0], [r(1, 2), 0, r(1, 2), 0, 0], [0, r(1, 2), 0, r(1, 2), 0], [0, 0, r(1, 2), 0, r(1, 2)], [0, 0, 0, 0, 1]]);
    const DW = DiscreteMarkovChain('DW', [0, 1, 2, 3, 4], T);
    expect(s(DW.decompose())).toBe('[[0, 4, 1, 2, 3], Matrix([[1, 0], [0, 1]]), Matrix([[1/2, 0], [0, 0], [0, 1/2]]), Matrix([[0, 1/2, 0], [1/2, 0, 1/2], [0, 1/2, 0]])]');
    expect(s(DW.canonicalForm())).toBe('[[0, 4, 1, 2, 3], Matrix([[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1/2, 0, 0, 1/2, 0], [0, 0, 1/2, 0, 1/2], [0, 1/2, 0, 1/2, 0]])]');
  });
  it('regular, ergodic and absorbing chains', () => {
    const X = (T: Matrix) => DiscreteMarkovChain('X', undefined, T);
    const T1 = m([[0, 4, 0, 0, 0], [1, 0, 3, 0, 0], [0, 2, 0, 2, 0], [0, 0, 3, 0, 1], [0, 0, 0, 4, 0]]).scale(r(1, 4));
    expect([X(T1).isRegular(), X(T1).isErgodic()]).toEqual([S.false, S.true]);
    expect([X(m([[0, 1], [1, 0]])).isRegular(), X(m([[0, 1], [1, 0]])).isErgodic()]).toEqual([S.false, S.true]);
    const T3 = m([[2, 1, 1], [2, 0, 2], [1, 1, 2]]).scale(r(1, 4));
    expect([X(T3).isRegular(), X(T3).isErgodic()]).toEqual([S.true, S.true]);
    expect(X(m([[1, 1], [1, 1]]).scale(r(1, 2))).isRegular()).toBe(S.true);
    expect(X(m([[0, 1, 0], [1, 0, 0], [0, 0, 1]])).isAbsorbingChain()).toBe(S.false);
    expect(X(m([[1, 1, 0, 0], [0, 1, 1, 0], [1, 0, 0, 1], [0, 0, 0, 2]]).scale(r(1, 2))).isAbsorbingChain()).toBe(S.true);
    const TO2 = m([[1, 0, 0], [r(1, 3), r(1, 3), r(1, 3)], [0, r(1, 4), r(3, 4)]]);
    const Y10 = DiscreteMarkovChain('Y', [1, 2, 3], TO2);
    expect(Y10.communicationClasses().map(([c, rec, p]) => `${s(c)} ${s(rec)} ${s(p)}`)).toEqual(['[1] True 1', '[2, 3] False 1']);
    expect(s(Y10.canonicalForm())).toBe(`[[1, 2, 3], ${s(TO2)}]`);
  });
  it('miscellaneous queries', () => {
    const T = m([[r(1, 2), r(1, 4), r(1, 4)], [r(1, 3), 0, r(2, 3)], [r(1, 2), r(1, 2), 0]]);
    for (const ss of [[0, 1, 2], ['A', 'B', 'C']]) {
      const X = DiscreteMarkovChain('X', ss, T);
      expect(s(P(and(Eq(X.at(1), 2), Eq(X.at(2), 1), Eq(X.at(3), 0)), and(Eq(P(Eq(X.at(1), 0)), r(1, 4)), Eq(P(Eq(X.at(1), 1)), r(1, 4)))))).toBe('1/12');
      expect(s(P(or(Eq(X.at(2), 1), Eq(X.at(2), 2)), Eq(X.at(1), 1)))).toBe('2/3');
      expect(s(P(and(Eq(X.at(2), 1), Eq(X.at(2), 2)), Eq(X.at(1), 1)))).toBe('0');
      expect(s(P(Ne(X.at(2), 2), Eq(X.at(1), 1)))).toBe('1/3');
      expect(() => E(X.at(1), Eq(X.at(2), 1))).toThrow('Incorrect given condition');
    }
    const X = DiscreteMarkovChain('X', [0, 1, 2], T);
    expect(s(E(X.at(1).pow(2), Eq(X.at(0), 1)))).toBe('8/3');
    expect(s(variance(X.at(1), Eq(X.at(0), 1)))).toBe('8/9');
    expect(() => DiscreteMarkovChain('X', [0, 1], T)).toThrow('must be the same');
    const XA = DiscreteMarkovChain('X', ['A', 'B', 'C'], T);
    const [a, , c] = (XA.stateSpace as Expr).args as [Expr, Expr, Expr];
    expect(s(simplify(E(XA.at(1).pow(2), Eq(XA.at(0), 1)).sub(a.pow(2).div(3).add(c.pow(2).mul(r(2, 3))))))).toBe('0');
  });
  it('queries with several random indexed symbols', () => {
    const T = m([[r(5, 10), r(3, 10), r(2, 10)], [r(2, 10), r(7, 10), r(1, 10)], [r(3, 10), r(3, 10), r(4, 10)]]);
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], T);
    const f = (e: Expr) => s(round(e, 14));
    expect(s(round(P(Eq(Y.at(7), Y.at(5)), Eq(Y.at(2), 0)), 5))).toBe('0.44428');
    expect(s(round(P(Le(Y.at(5), Y.at(10)), Eq(Y.at(4), 2)), 6))).toBe('0.583120');
    expect(f(P(Eq(Y.at(10), Y.at(5)), Eq(Y.at(4), 1)))).toBe(f(sympify(1).sub(P(Ne(Y.at(10), Y.at(5)), Eq(Y.at(4), 1)))));
    expect(f(P(Gt(Y.at(8), Y.at(9)), Eq(Y.at(3), 2)))).toBe(f(sympify(1).sub(P(Le(Y.at(8), Y.at(9)), Eq(Y.at(3), 2)))));
    expect(f(P(Lt(Y.at(1), Y.at(4)), Eq(Y.at(0), 0)))).toBe(f(sympify(1).sub(P(Ge(Y.at(1), Y.at(4)), Eq(Y.at(0), 0)))));
    expect(s(P(Ge(Y.at(7), Y.at(6)), Eq(Y.at(4), 1)))).toBe(s(P(Le(Y.at(6), Y.at(7)), Eq(Y.at(4), 1))));
  });
  it('symbolic queries', () => {
    const [a, b, c, d] = sym('a b c d');
    const T = m([[r(1, 10), r(4, 10), r(5, 10)], [r(3, 10), r(4, 10), r(3, 10)], [r(7, 10), r(2, 10), r(1, 10)]]);
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], T);
    const sub4 = (e: Expr, v: number[]) => e.subs([[a, v[0] ?? 0], [b, v[1] ?? 0], [c, v[2] ?? 0], [d, v[3] ?? 0]]).evalf();
    expect(s(round(sub4(P(Eq(Y.at(a), b), Eq(Y.at(c), d)), [15, 0, 10, 1]), 4))).toBe(s(round(P(Eq(Y.at(15), 0), Eq(Y.at(10), 1)), 4)));
    const sumGtLe = add2(sub4(P(Gt(Y.at(a), b), Eq(Y.at(c), d)), [5, 2, 1, 0]), sub4(P(Le(Y.at(a), b), Eq(Y.at(c), d)), [5, 2, 1, 0]));
    expect(s(round(sumGtLe, 10))).toBe('1.00000000000000');
    const sumGeLt = add2(sub4(P(Ge(Y.at(a), b), Eq(Y.at(c), d)), [4, 1, 0, 2]), sub4(P(Lt(Y.at(a), b), Eq(Y.at(c), d)), [4, 1, 0, 2]));
    expect(s(round(sumGeLt, 10))).toBe('1.00000000000000');
    // SymPy: 1 - Matrix(...)[d, b] with the explicit power of the matrix
    expect(s(round(P(Ne(Y.at(a), b), Eq(Y.at(c), d)).subs([[a, 2], [c, 1], [d, 0], [b, 1]]), 2))).toBe('0.60');
  });
});

const add2 = (x: Expr, y: Expr): Expr => x.add(y);

describe('ContinuousMarkovChain', () => {
  it('limiting distribution and transition probabilities', () => {
    const T1 = m([[-2, 2, 0], [0, -1, 1], [r(3, 2), r(3, 2), -3]]);
    expect(s(ContinuousMarkovChain('C', [0, 1, 2], T1).limitingDistribution())).toBe('Matrix([[3/19, 12/19, 4/19]])');
    const T2 = m([[-1, 1, 0], [1, -1, 0], [0, 1, -1]]);
    const C2 = ContinuousMarkovChain('C', [0, 1, 2], T2);
    const [t] = sym('t', { positive: true });
    expect(s(C2.transitionProbabilities(C2.generatorMatrix).call(t))).toBe('Matrix([[1/2 + exp(-2*t)/2, 1/2 - exp(-2*t)/2, 0], [1/2 - exp(-2*t)/2, 1/2 + exp(-2*t)/2, 0], [1/2 - exp(-t) + exp(-2*t)/2, 1/2 - exp(-2*t)/2, exp(-t)]])');
    expect(s(P(Eq(C2.call(1), 1), Eq(C2.call(0), 1), { evaluate: false }))).toBe('Probability(Eq(C(1), 1), Eq(C(0), 1))');
    expect(s(P(Eq(C2.call(1), 1), Eq(C2.call(0), 1)))).toBe('exp(-2)/2 + 1/2');
    expect(s(P(and(Eq(C2.call(1), 0), Eq(C2.call(2), 1), Eq(C2.call(3), 1)), Eq(P(Eq(C2.call(1), 0)), r(1, 2))))).toBe('(1/4 - exp(-2)/4)*(exp(-2)/2 + 1/2)');
    const c3 = and(Eq(C2.call(1), 0), Eq(C2.call(2), 1), Eq(C2.call(3), 2));
    expect(s(P(or(not(c3), c3), and(Eq(P(Eq(C2.call(1), 0)), r(1, 4)), Eq(P(Eq(C2.call(1), 1)), r(1, 4)))))).toBe('1');
    expect(s(E(C2.call(r(3, 2)), Eq(C2.call(0), 2)))).toBe('-exp(-3)/2 + 2*exp(-3/2) + 1/2');
    expect(s(variance(C2.call(r(3, 2)), Eq(C2.call(0), 1)))).toBe('(1/2 - exp(-3)/2)**2*(exp(-3)/2 + 1/2) + (-1/2 - exp(-3)/2)**2*(1/2 - exp(-3)/2)');
    expect(() => P(Eq(C2.call(1), 0), Eq(P(Eq(C2.call(1), 1)), r(1, 2)))).toThrow('KeyError');
    expect(s(P(Eq(C2.call(1), 0), Eq(P(Eq(C2.call(5), 1)), r(1, 2))))).toBe('Probability(Eq(C(1), 0))');
    const G = MatrixSymbol('G', 3, 3);
    const CS1 = ContinuousMarkovChain('C', [0, 1, 2], G);
    expect(s(CS1.transitionProbabilities().call(t))).toBe('exp(t*G)');
    expect(s(CS1.limitingDistribution())).toBe('Lambda((wm, G), Eq(wm*G, wm))');
    const C3 = ContinuousMarkovChain('C', [new Sym('0'), new Sym('1'), new Sym('2')], T2);
    expect(s(P(Eq(C3.call(1), 1), Eq(C3.call(0), 1)))).toBe('exp(-2)/2 + 1/2');
    expect(s(P(Eq(C3.call(1), new Sym('1')), Eq(C3.call(0), new Sym('1'))))).toBe('exp(-2)/2 + 1/2');
  });
  it('probability queries', () => {
    const G = m([[-1, r(1, 10), r(9, 10)], [r(2, 5), -1, r(3, 5)], [r(1, 2), r(1, 2), -1]]);
    const C = ContinuousMarkovChain('C', [0, 1, 2], G);
    expect(s(round(P(Eq(C.call(7.385), C.call(3.19)), Eq(C.call(0.862), 0)), 5))).toBe('0.35469');
    expect(s(round(P(Gt(C.call(98.715), C.call(19.807)), Eq(C.call(11.314), 2)), 5))).toBe('0.32452');
    expect(s(round(P(Le(C.call(5.9), C.call(10.112)), Eq(C.call(4), 1)), 6))).toBe('0.675214');
    const [a, b, c, d] = sym('a b c d');
    const q = (e: Expr, v: number[]) => e.subs([[a, v[0] ?? 0], [b, v[1] ?? 0], [c, v[2] ?? 0], [d, v[3] ?? 0]]).evalf();
    const sum1 = add2(q(P(Gt(C.call(a), b), Eq(C.call(c), d)), [13.2, 0, 3.29, 2]), q(P(Le(C.call(a), b), Eq(C.call(c), d)), [13.2, 0, 3.29, 2]));
    expect(s(round(sum1, 10))).toBe('1.00000000000000');
    const sum2 = add2(q(P(Ge(C.call(a), b), Eq(C.call(c), d)), [7.43, 1, 1.45, 0]), q(P(Lt(C.call(a), b), Eq(C.call(c), d)), [7.43, 1, 1.45, 0]));
    expect(s(round(sum2, 10))).toBe('1.00000000000000');
    expect(s(P(Eq(C.call(1), 5), Eq(C.call(0), 1)))).toBe('0');
    expect(() => P(Eq(C.call(1), 1), Eq(C.call(0), 7))).toThrow('No information');
  });
});

describe('BernoulliProcess', () => {
  const B = BernoulliProcess('B', 0.6, 1, 0);
  it('basics', () => {
    expect(s(B.stateSpace)).toBe('{0, 1}');
    expect(B.indexSet).toBe(Naturals0);
    expect([s(B.success), s(B.failure)]).toEqual(['1', '0']);
    const X = BernoulliProcess('X', r(1, 3), 'H', 'T');
    expect(s(X.stateSpace)).toBe('{H, T}');
    expect(s(E(X.at(1).add(X.at(2).mul(X.at(3)))))).toBe('H**2/9 + 4*H*T/9 + H/3 + 4*T**2/9 + 2*T/3');
    const [t, x] = sym('t x', { positive: true, integer: true });
    expect(B.at(t)).toBeInstanceOf(RandomIndexedSymbol);
    expect(() => BernoulliProcess('X', 1.1, 1, 0)).toThrow('between 0 and 1');
    expect(() => B.call(t)).toThrow('Use []');
    expect(() => B.at(-3)).toThrow('not in the index set');
    expect(() => B.at(r(1, 2))).toThrow('not in the index set');
    expect(s(B.jointDistribution(B.at(3), B.at(9)))).toBe('JointDistributionHandmade(Lambda((B[3], B[9]), Piecewise((0.6, Eq(B[3], 1)), (0.4, Eq(B[3], 0)), (0, True))*Piecewise((0.6, Eq(B[9], 1)), (0.4, Eq(B[9], 0)), (0, True))))');
    expect(s(B.jointDistribution(2, B.at(4)))).toBe('JointDistributionHandmade(Lambda((B[2], B[4]), Piecewise((0.6, Eq(B[2], 1)), (0.4, Eq(B[2], 0)), (0, True))*Piecewise((0.6, Eq(B[4], 1)), (0.4, Eq(B[4], 0)), (0, True))))');
    expect([...B.at(sympify(2).mul(t)).freeSymbols()].map(s).sort()).toEqual(['B[2*t]', 't']);
    expect([...B.at(4).freeSymbols()].map(s)).toEqual(['B[4]']);
    expect([...B.at(x.mul(t)).freeSymbols()].map(s).sort()).toEqual(['B[t*x]', 't', 'x']);
  });
  it('probabilities and expectations', () => {
    const Y = B.at(1).add(B.at(2)).add(B.at(3));
    const r2 = (e: Expr) => s(round(e, 2));
    expect(r2(P(Eq(Y, 0)))).toBe('0.06');
    expect(r2(P(Eq(Y, 2)))).toBe('0.43');
    expect(r2(P(Gt(Y, 1)))).toBe('0.65');
    expect(r2(P(and(Eq(B.at(1), 0), Eq(B.at(2), 1), Eq(B.at(3), 0), Eq(B.at(4), 1))))).toBe('0.06');
    expect(r2(E(B.at(1).mul(2).add(B.at(2)).add(5)))).toBe('6.80');
    expect(r2(E(B.at(2).mul(B.at(4)).add(B.at(10))))).toBe('0.96');
    expect(r2(E(Gt(B.at(2), 0), and(Eq(B.at(1), 1), Eq(B.at(2), 1))))).toBe('0.60');
    expect(s(E(B.at(1)))).toBe('0.600000000000000');
    expect(r2(P(Gt(B.at(1), 0)))).toBe('0.60');
    expect(r2(P(Gt(B.at(1), 0), Le(B.at(2), 1)))).toBe('0.60');
    expect(r2(P(Gt(B.at(12).mul(B.at(5)), 0)))).toBe('0.36');
    expect(r2(P(Gt(B.at(12).mul(B.at(5)), 0), Lt(B.at(4), 1)))).toBe('0.36');
    expect(s(P(Eq(B.at(2), 1), Gt(B.at(2), 0)))).toBe('1.00000000000000');
    expect(s(P(Eq(B.at(5), 3)))).toBe('0');
    expect(s(P(Eq(B.at(1), 1), Lt(B.at(1), 0)))).toBe('0');
    expect(s(P(Gt(B.at(2), 0), Eq(B.at(2), 1)))).toBe('1');
    expect(s(P(Lt(B.at(2), 0), Eq(B.at(2), 1)))).toBe('0');
    // SymPy B[2]==7 is the structural comparison, False
    expect(s(P(Gt(B.at(2), 0), S.false))).toBe('0');
    expect(s(P(Gt(B.at(5), 0), B.at(5)))).toBe('BernoulliDistribution(0.6, 0, 1)');
    expect(() => P(Gt(B.at(3), 0), 3)).toThrow('not a relational');
  });
  it('the substitution of simple random symbols', async () => {
    const { substituteProbability, substituteExpectation } = await import('../../src/stats/stochasticprocesstypes');
    expect(() => substituteProbability(sympify(3))).toThrow('not a relational');
    expect(s(substituteProbability(S.true))).toBe('1');
    expect(s(substituteExpectation(sympify(5)))).toBe('5');
    expect(s(substituteProbability(Gt(B.at(1), 0), undefined, { evaluate: false }))).toBe('0.600000000000000');
    expect(s(substituteProbability(Gt(B.at(1), 0), B.at(2)))).toBe('0.600000000000000');
    expect(s(substituteProbability(Gt(B.at(1).add(B.at(2)), 0), B.at(2)))).toBe('Probability(B[1] + B[2] > 0, B[2])');
  });
});

describe('PoissonProcess', () => {
  const X = PoissonProcess('X', 3);
  const [t, d, x, y] = sym('t d x y', { positive: true });
  it('basics', () => {
    expect(s(X.stateSpace)).toBe('Naturals0');
    expect(s(X.indexSet)).toBe('Interval(0, oo)');
    expect(X.call(t)).toBeInstanceOf(RandomIndexedSymbol);
    expect(s(X.distribution(t))).toBe('PoissonDistribution(3*t)');
    expect(s(X.distribution(X.call(t)))).toBe('PoissonDistribution(3*t)');
    expect(() => PoissonProcess('X', -1)).toThrow('positive');
    expect(() => X.at(t)).toThrow('Use ()');
    expect(() => X.call(-5)).toThrow('not in the index set');
    expect(s(X.jointDistribution(X.call(2), X.call(3)))).toBe('JointDistributionHandmade(Lambda((X(2), X(3)), 6**X(2)*9**X(3)*exp(-15)/(factorial(X(2))*factorial(X(3)))))');
    expect(s(X.jointDistribution(4, 6))).toBe('JointDistributionHandmade(Lambda((X(4), X(6)), 12**X(4)*18**X(6)*exp(-30)/(factorial(X(4))*factorial(X(6)))))');
  });
  it('probabilities', () => {
    expect(s(P(Lt(X.call(t), 1)))).toBe('exp(-3*t)');
    expect(s(P(Eq(X.call(t), 0), new Contains(t, Lopen(3, 5))))).toBe('exp(-6)');
    const res = P(Eq(X.call(t), 1), new Contains(t, Lopen(3, 4)));
    expect(s(res)).toBe('3*exp(-3)');
    const c4 = and(new Contains(t, Lopen(0, 1)), new Contains(d, Lopen(1, 2)), new Contains(x, Lopen(2, 3)), new Contains(y, Lopen(3, 4)));
    expect(s(P(and(Eq(X.call(t), 1), Eq(X.call(d), 1), Eq(X.call(x), 1), Eq(X.call(y), 1)), c4))).toBe(s(res.pow(4)));
    const overlap = and(new Contains(t, Lopen(0, 2)), new Contains(d, Ropen(2, 4)));
    expect(s(P(and(Eq(X.call(t), 2), Eq(X.call(d), 3)), overlap))).toBe('Probability(Eq(X(d), 3) & Eq(X(t), 2), Contains(d, Interval.Ropen(2, 4)) & Contains(t, Interval.Lopen(0, 2)))');
    expect(() => P(and(Eq(X.call(t), 2), Eq(X.call(d), 3)), and(new Contains(t, Lopen(0, 4)), new Contains(d, Lopen(3, S.Infinity))))).toThrow('finite bounds');
    expect(s(P(Eq(X.call(3), 2)))).toBe('81*exp(-9)/2');
    expect(s(P(Eq(X.call(t), 2), new Contains(t, Lopen(0, 5))))).toBe('225*exp(-15)/2');
    const res1 = P(Le(X.call(t), 3), new Contains(t, Lopen(0, 5)));
    const res2 = P(Gt(X.call(t), 3), new Contains(t, Lopen(0, 5)));
    expect(s(res1)).toBe('691*exp(-15)');
    expect(s(simplify(res1.add(res2)))).toBe('1');
    expect(s(simplify(P(not(and(Eq(X.call(t), 2), Gt(X.call(d), 3))), and(new Contains(t, Ropen(2, 4)), new Contains(d, Lopen(7, 8))))))).toBe('-18*exp(-6) + 234*exp(-9) + 1');
    expect(() => P(Gt(X.call(t), 2), X.call(t).add(X.call(d)))).toThrow('If given condition is passed with `Contains`');
    expect(s(P(and(Eq(X.call(1), 2), Eq(X.call(t), 3)), new Contains(t, Lopen(1, 2))))).toBe('81*exp(-6)/4');
    expect(() => P(Eq(X.call(t), 0), and(new Contains(t, Lopen(1, 3)), Eq(X.call(1), 0)))).toThrow('If given condition is passed with `Contains`');
    expect(s(P(or(Eq(X.call(1), 2), Eq(X.call(1), 3)), Eq(X.call(0.5), 1)))).toBe('0.585716670389628');
    expect(s(P(Eq(X.call(2), 2), or(Eq(X.call(1), 1), Eq(X.call(1), 2))))).toBe('4*exp(-3)');
  });
  it('expectations', () => {
    expect(s(E(X.call(t)))).toBe('3*t');
    const c3 = and(new Contains(t, Lopen(0, 1)), new Contains(d, Lopen(1, 2)), new Contains(y, Ropen(3, 4)));
    expect(s(E(X.call(t).pow(2).add(X.call(d).mul(2)).add(X.call(y).pow(3)), c3))).toBe('75');
    expect(s(E(X.call(t).pow(2), new Contains(t, Lopen(0, 1))))).toBe('12');
    const ov = and(new Contains(t, Lopen(0, 1)), new Contains(d, Ropen(1, 2)));
    const e1 = x.mul(X.call(t).add(X.call(d))).mul(X.call(t).pow(2).add(X.call(d).pow(2)));
    expect(E(e1, ov)).toBeInstanceOf(ExpectationNode);
    expect(() => E(X.call(t).pow(3), new Contains(t, Lopen(1, S.Infinity)))).toThrow('finite bounds');
    expect(s(E(X.call(t).add(X.call(d)).mul(X.call(t).sub(X.call(d))), and(new Contains(t, Lopen(0, 1)), new Contains(d, Lopen(1, 2)))))).toBe('0');
    expect(s(E(X.call(2).add(x.mul(E(X.call(5))))))).toBe('15*x + 6');
    expect(s(E(x.mul(X.call(1)).add(y)))).toBe('3*x + y');
    expect(s(E(X.call(t), new Contains(t, interval(2, 2))))).toBe('6');
    expect(() => E(X.call(t), 3)).toThrow('not a relational');
  });
  it('merging, splitting and increments', () => {
    const Y = PoissonProcess('Y', 6);
    const Z = X.add(Y);
    expect(s(Z.lamda)).toBe('9');
    expect(() => X.add(5)).toThrow('Only instances of Poisson Process');
    const [N, M] = Z.split(4, 5);
    expect([s(N.lamda), s(M.lamda)]).toEqual(['4', '5']);
    expect(() => Z.split(3, 2)).toThrow('Sum of l1 and l2');
    expect(s(P(Eq(N.call(3), N.call(5))))).toBe(s(P(Eq(N.call(t), 0), new Contains(t, interval(3, 5)))));
    expect(s(P(Gt(N.call(3), N.call(1))))).toBe(s(P(Gt(N.call(t), 0), new Contains(t, interval(1, 3)))));
    expect(s(P(Lt(N.call(3), N.call(1))))).toBe('0');
    expect(s(P(Le(N.call(3), N.call(1))))).toBe(s(P(Eq(N.call(t), 0), new Contains(t, interval(1, 3)))));
    expect(s(P(Lt(N.call(1), N.call(3))))).toBe(s(P(Lt(N.call(2), 0))));
    const X10 = PoissonProcess('X', 10);
    expect(s(P(and(Eq(X10.call(r(1, 3)), 3), Eq(X10.call(1), 10))))).toBe('8000000000*exp(-10)/11160261');
    expect(s(P(Eq(X10.call(1), 1), Eq(X10.call(r(1, 3)), 3)))).toBe('0');
    expect(s(P(Eq(X10.call(1), 10), Eq(X10.call(r(1, 3)), 3)))).toBe(s(P(Eq(X10.call(r(2, 3)), 7))));
    const X2 = PoissonProcess('X', 2);
    expect(s(P(Lt(X2.call(r(1, 2)), 1)))).toBe('exp(-1)');
    expect(s(P(Lt(X2.call(3), 1), Eq(X2.call(1), 0)))).toBe('exp(-4)');
    expect(s(P(Eq(X2.call(4), 3), Eq(X2.call(2), 3)))).toBe('exp(-4)');
    expect(s(P(and(Eq(X.call(2), 5), Eq(X.call(1), 2))))).toBe('81*exp(-6)/4');
    expect(s(P(Le(X.call(2), 3), Ge(X.call(1), 1)))).toBe(s(P(Eq(X.call(1), 0)).mul(3).add(P(Eq(X.call(1), 1)).mul(2)).add(P(Eq(X.call(1), 2)))));
    expect(s(P(Le(X.call(2), 3), Gt(X.call(1), 1)))).toBe(s(P(Eq(X.call(1), 0)).mul(2).add(P(Eq(X.call(1), 1)))));
    expect(s(P(Eq(X.call(3), 4), Eq(X.call(1), 3)))).toBe(s(P(Eq(X.call(2), 1))));
  });
});

describe('WienerProcess and GammaProcess', () => {
  const [t, d, x, y] = sym('t d x y', { positive: true });
  it('WienerProcess', () => {
    const X = WienerProcess('X');
    expect(s(X.indexSet)).toBe('Interval(0, oo)');
    expect(s(X.distribution(t))).toBe('NormalDistribution(0, sqrt(t))');
    expect(s(X.distribution(X.call(t)))).toBe('NormalDistribution(0, sqrt(t))');
    expect(() => X.at(t)).toThrow('Use ()');
    expect(() => X.call(-2)).toThrow('not in the index set');
    expect(s(X.jointDistribution(X.call(2), X.call(3)))).toBe('JointDistributionHandmade(Lambda((X(2), X(3)), sqrt(6)*exp(-X(2)**2/4)*exp(-X(3)**2/6)/(12*pi)))');
    expect(s(simplify(P(Lt(X.call(t), 3))))).toBe('erf(3*sqrt(2)/(2*sqrt(t)))/2 + 1/2');
    expect(s(simplify(P(Gt(X.call(t), 2), new Contains(t, Lopen(3, 7)))))).toBe('1/2 - erf(sqrt(2)/2)/2');
    const ov = and(new Contains(t, Lopen(0, 2)), new Contains(d, Ropen(2, 4)));
    expect(P(and(Lt(X.call(t), 2), Gt(X.call(d), 3)), ov)).toBeInstanceOf(ProbabilityNode);
    expect(s(E(X.call(t)))).toBe('0');
    expect(s(E(X.call(t).add(x.mul(E(X.call(3))))))).toBe('0');
  });
  it('GammaProcess', () => {
    const [g, l] = sym('g l', { positive: true });
    const X = GammaProcess('X', l, g);
    expect(() => X.at(t)).toThrow('Use ()');
    expect(() => X.call(-1)).toThrow('not in the index set');
    expect(s(X.stateSpace)).toBe('Interval(0, oo)');
    expect(s(X.distribution(t))).toBe('GammaDistribution(g*t, 1/l)');
    expect(s(X.distribution(X.call(t)))).toBe('GammaDistribution(g*t, 1/l)');
    expect(s(X.jointDistribution(5, X.call(3)))).toBe('JointDistributionHandmade(Lambda((X(5), X(3)), l**(8*g)*exp(-l*X(3))*exp(-l*X(5))*X(3)**(3*g - 1)*X(5)**(5*g - 1)/(gamma(3*g)*gamma(5*g))))');
    const c3 = and(new Contains(t, Lopen(0, 1)), new Contains(d, Lopen(1, 2)), new Contains(y, Ropen(3, 4)));
    expect(s(E(X.call(t).pow(2).add(X.call(d).mul(2)).add(X.call(y).pow(3)), c3))).toBe('2*g/l + (g**2 + g)/l**2 + (g**3 + 3*g**2 + 2*g)/l**3');
    // SymPy 1.14
    expect(s(simplify(P(Gt(X.call(t), 3), new Contains(t, Lopen(3, 4)))))).toBe('1 - lowergamma(g, 3*l)/gamma(g)');
    const X2 = GammaProcess('X', 1, 2);
    expect(s(X2.lamda)).toBe('1');
    expect(s(X2.gamma)).toBe('2');
    expect(() => GammaProcess('X', -1, 2)).toThrow('lamda');
    expect(() => GammaProcess('X', 1, -2)).toThrow('gamma');
    const c4 = and(new Contains(t, Lopen(0, 1)), new Contains(d, Lopen(1, 2)), new Contains(x, Lopen(2, 3)), new Contains(y, Lopen(3, 4)));
    expect(s(simplify(P(and(Gt(X2.call(t), 4), Gt(X2.call(d), 3), Gt(X2.call(x), 2), Gt(X2.call(y), 1)), c4)))).toBe('120*exp(-10)');
    expect(s(simplify(P(or(Gt(X2.call(t), 2), Lt(X2.call(t), 4)), new Contains(t, Ropen(1, 4)))))).toBe('-643*exp(-4)/15 + 109*exp(-2)/15 + 1');
    expect(s(E(X2.call(t)))).toBe('2*t');
  });
});
