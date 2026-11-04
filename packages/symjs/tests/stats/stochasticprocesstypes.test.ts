// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/stochasticprocesstypes.ts (SymPy
// sympy/stats/stochastic_process_types.py and
// sympy/stats/tests/test_stochastic_process.py). Expected values are those
// of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Gt, Le, Lt, Ne, Matrix, MatrixSymbol, NotImplementedError, Rational, S, Sym, TupleNode, and, not, or, round, simplify, str, sub, symbols, sympify } from '../../src';
import type { Expr } from '../../src';
import { Normal, P, expectation as E, variance } from '../../src/stats';
import { Contains, Lopen, Ropen, finiteSet } from '../../src/sets/sets';
import { Str } from '../../src/matrices/expressions/matexpr';
import {
  BernoulliProcess,
  ContinuousMarkovChain,
  ContinuousTimeStochasticProcess,
  DiscreteMarkovChain,
  DiscreteTimeStochasticProcess,
  GammaProcess,
  GeneratorMatrixOf,
  PoissonProcess,
  StochasticProcess,
  StochasticStateSpaceOf,
  TransitionMatrixOf,
  WienerProcess,
  getTimervSwaps,
  setConverter,
} from '../../src/stats/stochasticprocesstypes';

const r = (n: number, d: number) => Rational.of(n, d);
const s = (e: unknown): string => (Array.isArray(e) ? (e.length === 3 && typeof e[1] === 'object' && !Array.isArray(e[1]) && Array.isArray(e[0]) ? `(${e.map(s).join(', ')})` : `[${e.map(s).join(', ')}]`) : str(e as Expr));
const sym = (names: string, a?: Record<string, boolean>) => symbols(names, a) as [Sym, Sym, Sym, Sym, Sym, Sym];

describe('BernoulliProcess doctests', () => {
  const B = BernoulliProcess('B', 0.7, 1, 0);
  it('basics', () => {
    expect(s(B.stateSpace)).toBe('{0, 1}');
    expect(s(round(B.p, 2))).toBe('0.70');
    const X = B.at(1).add(B.at(2)).add(B.at(3));
    expect(s(round(P(Eq(X, 0)), 2))).toBe('0.03');
    expect(s(round(P(Eq(X, 2)), 2))).toBe('0.44');
    expect(s(round(P(Eq(X, 4)), 2))).toBe('0');
    expect(s(round(P(Gt(X, 1)), 2))).toBe('0.78');
    expect(s(round(P(and(Eq(B.at(1), 0), Eq(B.at(2), 1), Eq(B.at(3), 0), Eq(B.at(4), 1))), 2))).toBe('0.04');
    expect(s(B.jointDistribution(B.at(1), B.at(2)))).toBe('JointDistributionHandmade(Lambda((B[1], B[2]), Piecewise((0.7, Eq(B[1], 1)), (0.3, Eq(B[1], 0)), (0, True))*Piecewise((0.7, Eq(B[2], 1)), (0.3, Eq(B[2], 0)), (0, True))))');
    expect(s(round(E(B.at(1).mul(2).add(B.at(2))), 2))).toBe('2.10');
    expect(s(round(P(Lt(B.at(1), 1)), 2))).toBe('0.30');
  });
});

describe('DiscreteMarkovChain doctests', () => {
  const T = Matrix.of([[0.5, 0.2, 0.3], [0.2, 0.5, 0.3], [0.2, 0.3, 0.5]]);
  it('queries', () => {
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], T);
    const YS = DiscreteMarkovChain('Y');
    expect(s(Y.stateSpace)).toBe('{0, 1, 2}');
    const TS = MatrixSymbol('T', 3, 3);
    expect(s(P(Eq(YS.at(3), 2), and(Eq(YS.at(1), 1), TransitionMatrixOf(YS, TS))))).toBe('T[0, 2]*T[1, 0] + T[1, 1]*T[1, 2] + T[1, 2]*T[2, 2]');
    expect(s(round(P(Eq(Y.at(3), 2), Eq(Y.at(1), 1)), 2))).toBe('0.36');
    const [sunny, cloudy, rainy] = sym('Sunny Cloudy Rainy');
    const Y2 = DiscreteMarkovChain('Y', [sunny, cloudy, rainy], T);
    expect(s(round(P(Eq(Y2.at(3), rainy), Eq(Y2.at(1), cloudy)), 2))).toBe('0.36');
    expect(s(E(Y2.at(3), Eq(Y2.at(1), cloudy)))).toBe('0.38*Cloudy + 0.36*Rainy + 0.26*Sunny');
  });
  it('two random indexed symbols', () => {
    const T2 = Matrix.of([[r(5, 10), r(3, 10), r(2, 10)], [r(2, 10), r(7, 10), r(1, 10)], [r(3, 10), r(3, 10), r(4, 10)]]);
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], T2);
    expect(s(round(P(Eq(Y.at(3), Y.at(1)), Eq(Y.at(0), 0)), 3))).toBe('0.409');
    expect(s(round(P(Gt(Y.at(3), Y.at(1)), Eq(Y.at(0), 0)), 2))).toBe('0.36');
    expect(s(round(P(Le(Y.at(15), Y.at(10)), Eq(Y.at(8), 2)), 7))).toBe('0.6963328');
  });
  it('symbolic queries', () => {
    const [a, b, c, d] = sym('a b c d');
    const T3 = Matrix.of([[r(1, 10), r(4, 10), r(5, 10)], [r(3, 10), r(4, 10), r(3, 10)], [r(7, 10), r(2, 10), r(1, 10)]]);
    const Y = DiscreteMarkovChain('Y', [0, 1, 2], T3);
    const query = P(Eq(Y.at(a), b), Eq(Y.at(c), d));
    expect(s(round(query.subs([[a, 10], [b, 2], [c, 5], [d, 1]]), 4))).toBe('0.3096');
    expect(s(round(P(Eq(Y.at(10), 2), Eq(Y.at(5), 1)).evalf(), 4))).toBe('0.3096');
    const queryGt = P(Gt(Y.at(a), b), Eq(Y.at(c), d));
    expect(s(round(queryGt.subs([[a, 21], [b, 0], [c, 5], [d, 0]]).evalf(), 5))).toBe('0.64705');
    expect(s(round(P(Gt(Y.at(21), 0), Eq(Y.at(5), 0)), 5))).toBe('0.64705');
    const [n] = sym('n', { nonnegative: true, integer: true });
    const Tn = MatrixSymbol('T', n, n);
    const Yn = DiscreteMarkovChain('Y', undefined, Tn);
    expect(s(Yn.stateSpace)).toBe('Range(0, n, 1)');
    const q2 = P(Eq(Yn.at(a), b), Eq(Yn.at(c), d));
    expect(s(q2.subs([[a, 10], [b, 2], [c, 5], [d, 1]]))).toBe('(T**5)[1, 2]');
  });
  it('canonical form, decompose, stationary distribution', () => {
    const T1 = Matrix.of([[r(1, 2), r(1, 2), 0, 0, 0], [r(2, 5), r(1, 5), r(2, 5), 0, 0], [0, 0, 1, 0, 0], [0, 0, r(1, 2), r(1, 2), 0], [r(1, 2), 0, 0, 0, r(1, 2)]]);
    const X = DiscreteMarkovChain('X', [1, 2, 3, 4, 5], T1);
    const [states, m] = X.canonicalForm();
    expect(s(states)).toBe('[3, 1, 2, 4, 5]');
    expect(s(m)).toBe('Matrix([[1, 0, 0, 0, 0], [0, 1/2, 1/2, 0, 0], [2/5, 2/5, 1/5, 0, 0], [1/2, 0, 0, 1/2, 0], [0, 1/2, 0, 0, 1/2]])');
    const X2 = DiscreteMarkovChain('X', undefined, T1);
    const [st2, A, B, C] = X2.decompose();
    expect(s(st2)).toBe('[2, 0, 1, 3, 4]');
    expect([s(A), s(B), s(C)]).toEqual(['Matrix([[1]])', 'Matrix([[0], [2/5], [1/2], [0]])', 'Matrix([[1/2, 1/2, 0, 0], [2/5, 1/5, 0, 0], [0, 0, 1/2, 0], [1/2, 0, 0, 1/2]])']);
    const T4 = Matrix.of([[0, 5, 5, 0, 0], [0, 0, 0, 10, 0], [5, 0, 5, 0, 0], [0, 10, 0, 0, 0], [0, 3, 0, 3, 4]]).scale(r(1, 10));
    const [st4, m4] = DiscreteMarkovChain('X', undefined, T4).canonicalForm();
    expect(s(st4)).toBe('[1, 3, 0, 2, 4]');
    expect(s(m4)).toBe('Matrix([[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1/2, 0, 0, 1/2, 0], [0, 0, 1/2, 1/2, 0], [3/10, 3/10, 0, 0, 2/5]])');
    const Tc = Matrix.of([[0, 1, 0], [1, 0, 0], [1, 0, 0]]);
    expect(DiscreteMarkovChain('X', [1, 2, 3], Tc).communicationClasses().map(s)).toEqual(['([1, 2], True, 2)', '([3], False, 1)']);
    const Ts = Matrix.of([[r(1, 2), r(1, 2), 0], [r(4, 5), r(1, 5), 0], [1, 0, 0]]);
    expect(s(DiscreteMarkovChain('X', undefined, Ts).stationaryDistribution())).toBe('Matrix([[8/13, 5/13, 0]])');
    const Ts2 = Matrix.of([[r(1, 2), r(1, 2), 0], [r(4, 5), r(1, 5), 0], [0, 0, 1]]);
    expect(s(DiscreteMarkovChain('X', undefined, Ts2).stationaryDistribution())).toBe('Matrix([[8/13 - 8*tau0/13, 5/13 - 5*tau0/13, tau0]])');
    const Ys = DiscreteMarkovChain('Y');
    expect(s(Ys.stationaryDistribution())).toBe('Lambda((wm, _T), Eq(wm*_T, wm))');
    expect(s(Ys.stationaryDistribution({ conditionSet: true }))).toBe('ConditionSet(wm, Eq(wm*_T, wm))');
  });
});

describe('ContinuousMarkovChain doctests', () => {
  it('queries', () => {
    const G = Matrix.of([[-1, 1], [1, -1]]);
    const C = ContinuousMarkovChain('C', [0, 1], G);
    expect(s(C.limitingDistribution())).toBe('Matrix([[1/2, 1/2]])');
    expect(s(C.stateSpace)).toBe('{0, 1}');
    expect(s(round(P(Eq(C.call(1.96), 0), Eq(C.call(0.78), 1)), 5))).toBe('0.45279');
    expect(s(round(P(Gt(C.call(1.7), 0), Eq(C.call(0.82), 1)), 5))).toBe('0.58602');
    const G2 = Matrix.of([[-1, r(1, 10), r(9, 10)], [r(2, 5), -1, r(3, 5)], [r(1, 2), r(1, 2), -1]]);
    const C2 = ContinuousMarkovChain('C', [0, 1, 2], G2);
    expect(s(round(P(Eq(C2.call(3.92), C2.call(1.75)), Eq(C2.call(0.46), 0)), 5))).toBe('0.37933');
    expect(s(round(P(Gt(C2.call(3.92), C2.call(1.75)), Eq(C2.call(0.46), 0)), 5))).toBe('0.34211');
    expect(s(round(P(Le(C2.call(1.57), C2.call(3.14)), Eq(C2.call(1.22), 1)), 4))).toBe('0.7143');
    const [a, b, c, d] = sym('a b c d');
    const query = P(Eq(C2.call(a), b), Eq(C2.call(c), d));
    expect(s(round(query.subs([[a, 3.65], [b, 2], [c, 1.78], [d, 1]]).evalf(), 10))).toBe('0.4002723175');
    expect(s(round(P(Eq(C2.call(3.65), 2), Eq(C2.call(1.78), 1)), 10))).toBe('0.4002723175');
    const queryGt = P(Gt(C2.call(a), b), Eq(C2.call(c), d));
    expect(s(round(queryGt.subs([[a, 43.2], [b, 0], [c, 3.29], [d, 2]]).evalf(), 10))).toBe('0.6832579186');
    expect(s(round(P(Gt(C2.call(43.2), 0), Eq(C2.call(3.29), 2)), 10))).toBe('0.6832579186');
  });
});

describe('counting process doctests', () => {
  it('GammaProcess', () => {
    const [t, d, x, l, g] = sym('t d x l g', { positive: true });
    const X = GammaProcess('X', l, g);
    expect(s(E(X.call(t)))).toBe('g*t/l');
    expect(s(simplify(variance(X.call(t))))).toBe('g*t/l**2');
    const X2 = GammaProcess('X', 1, 2);
    expect(s(simplify(P(Lt(X2.call(t), 1))))).toBe('lowergamma(2*t, 1)/gamma(2*t)');
    expect(s(simplify(P(not(and(Lt(X2.call(t), 5), Gt(X2.call(d), 3))), and(new Contains(t, Ropen(2, 4)), new Contains(d, Lopen(7, 8))))))).toBe('-4*exp(-3) + 472*exp(-8)/3 + 1');
    expect(s(E(X2.call(2).add(x.mul(E(X2.call(5))))))).toBe('10*x + 4');
  });
  it('PoissonProcess', () => {
    const X = PoissonProcess('X', 3);
    expect(s(X.stateSpace)).toBe('Naturals0');
    expect(s(X.lamda)).toBe('3');
    const [t1, t2] = sym('t1 t2', { positive: true });
    // SymPy: (9*t1**3/2 + 9*t1**2/2 + 3*t1 + 1)*exp(-3*t1), the same value expanded (the probability of the Poisson distribution)
    expect(s(P(Lt(X.call(t1), 4)))).toBe('9*t1**3*exp(-3*t1)/2 + 9*t1**2*exp(-3*t1)/2 + 3*t1*exp(-3*t1) + exp(-3*t1)');
    expect(s(P(or(Eq(X.call(t1), 2), Ne(X.call(t1), 4)), new Contains(t1, Ropen(2, 4))))).toBe('1 - 36*exp(-6)');
    expect(s(P(and(Eq(X.call(t1), 2), Eq(X.call(t2), 3)), and(new Contains(t1, Lopen(0, 2)), new Contains(t2, Lopen(2, 4)))))).toBe('648*exp(-12)');
    expect(s(E(X.call(t1)))).toBe('3*t1');
    expect(s(E(X.call(t1).pow(2).add(X.call(t2).mul(2)), and(new Contains(t1, Lopen(0, 1)), new Contains(t2, Lopen(1, 2)))))).toBe('18');
    expect(s(P(Lt(X.call(3), 1), Eq(X.call(1), 0)))).toBe('exp(-6)');
    expect(s(P(Eq(X.call(4), 3), Eq(X.call(2), 3)))).toBe('exp(-6)');
    expect(s(P(Le(X.call(2), 3), Gt(X.call(1), 1)))).toBe('5*exp(-3)');
    const Z = X.add(PoissonProcess('Y', 4));
    expect(s(Z.lamda)).toBe('7');
    const [N, M] = Z.split(2, 5);
    expect([s(N.lamda), s(M.lamda)]).toEqual(['2', '5']);
  });
  it('WienerProcess', () => {
    const X = WienerProcess('X');
    expect(s(X.stateSpace)).toBe('Reals');
    const [t1, t2] = sym('t1 t2', { positive: true });
    expect(s(simplify(P(Lt(X.call(t1), 7))))).toBe('erf(7*sqrt(2)/(2*sqrt(t1)))/2 + 1/2');
    expect(s(simplify(P(or(Gt(X.call(t1), 2), Lt(X.call(t1), 4)), new Contains(t1, Ropen(2, 4)))))).toBe('-erf(1)/2 + erf(2)/2 + 1');
    expect(s(E(X.call(t1)))).toBe('0');
    expect(s(E(X.call(t1).add(X.call(t2).mul(2)), and(new Contains(t1, Lopen(0, 1)), new Contains(t2, Lopen(1, 2)))))).toBe('0');
  });
});

describe('the remaining paths of the processes', () => {
  const T = Matrix.of([[0.5, 0.2, 0.3], [0.2, 0.5, 0.3], [0.2, 0.3, 0.5]]);
  const Y = DiscreteMarkovChain('Y', [0, 1, 2], T);
  it('Markov chain probability queries', () => {
    // SymPy: 0.360000000000000, conditioned on Y[1] = 0 only (the time it takes from the set of the given
    // symbols); by the Markov property the probability given Y[2] = 1 is T[1, 2] = 0.3
    expect(s(P(Eq(Y.at(3), 2), and(Eq(Y.at(2), 1), Eq(Y.at(1), 0))))).toBe('0.300000000000000');
    expect(s(P(Eq(Y.at(3), 2), Eq(1, Y.at(1))))).toBe('0.360000000000000');
    expect(s(P(Eq(Y.at(3), 2), and(Eq(2, Y.at(2)), Eq(0, Y.at(1)))))).toBe('0.500000000000000');
    expect(s(Y.expectation(Y.at(2), Eq(Y.at(0), 2)))).toBe('1.14000000000000');
    // SymPy: IndexError (no information for the state Y[1])
    expect(() => P(Eq(Y.at(3), 2), Eq(Y.at(2), Y.at(1)))).toThrow('No information');
    expect(s(P(and(Eq(Y.at(2), 1), or(Eq(Y.at(1), 0), Eq(Y.at(1), 1))), Eq(Y.at(0), 0)))).toBe('0.203000000000000');
    expect(() => P(and(Eq(Y.at(1), 0), Gt(Y.at(2), 0)), Eq(Y.at(0), 0))).toThrow('multiple states at Y[2]');
    expect(s(P(Eq(Y.at(1), 1), StochasticStateSpaceOf(Y, [0, 1, 2])))).toBe('Probability(Eq(Y[1], 1))');
    const T4 = Matrix.of([[r(1, 4), r(1, 4), r(1, 4), r(1, 4)], [r(1, 4), r(1, 4), r(1, 4), r(1, 4)], [r(1, 4), r(1, 4), r(1, 4), r(1, 4)], [r(1, 4), r(1, 4), r(1, 4), r(1, 4)]]);
    const X4 = DiscreteMarkovChain('X', [0, 1, 2, 3], T4);
    expect(() => P(Eq(X4.at(2), 1), and(Eq(P(Eq(X4.at(1), 0)), r(1, 4)), Eq(P(Eq(X4.at(1), 1)), r(1, 4))))).toThrow('Conflicting information');
    const Tb = Matrix.of([[0.5, 0.2, 0.2], [0.2, 0.5, 0.3], [0.2, 0.3, 0.5]]);
    const Yb = DiscreteMarkovChain('Y', [0, 1, 2], Tb);
    expect(() => P(Eq(Yb.at(1), 0), Eq(Yb.at(0), 0))).toThrow('Values in a row must sum to 1');
    // SymPy: TypeError (len of an Interval), the state index of the random symbol of the condition
    expect(() => P(Eq(Y.at(3), 2), and(Eq(Y.at(1), 1), Eq(Normal('N', 0, 1), 1)))).toThrow();
    // SymPy: TypeError (t in Naturals0 did not evaluate to a bool)
    const [t] = sym('t');
    expect(() => P(Eq(Y.at(3), 1), Eq(Y.at(t), 0))).toThrow('index set');
    expect(s(Y.probability(Eq(Y.at(2), 1), Eq(Y.at(0), 2), { evaluate: false }))).toBe('Probability(Eq(Y[2], 1), Eq(Y[0], 2))');
    expect(() => Y.probability(TransitionMatrixOf(Y, T), Eq(Y.at(0), 2))).toThrow('Mechanism for handling');
    expect(s(Y.expectation(Y.at(2), Eq(Y.at(0), 2), { evaluate: false }))).toBe('Expectation(Y[2], Eq(Y[0], 2))');
    expect(() => E(Y.at(2).mul(Y.at(3)), Eq(Y.at(1), 0))).toThrow('Mechanism for handling');
    const [a] = sym('a', { real: true });
    expect(DiscreteMarkovChain('Y', undefined, Matrix.of([[S.Pi, sub(1, S.Pi)], [a, sub(1, a)]])).communicationClasses().map(s)).toEqual(['([0, 1], True, 1)']);
  });
  it('conditions on Markov chains', () => {
    const C = ContinuousMarkovChain('C', [0, 1], Matrix.of([[-1, 1], [1, -1]]));
    const B = BernoulliProcess('B', 0.5);
    expect(() => TransitionMatrixOf(C, Matrix.of([[-1, 1], [1, -1]]))).toThrow('Currently only DiscreteMarkovChain support');
    expect(() => GeneratorMatrixOf(Y, T)).toThrow('Currently only ContinuousMarkovChain support');
    expect(() => StochasticStateSpaceOf(B, [0, 1])).toThrow('Currently only DiscreteMarkovChain and');
    const g = GeneratorMatrixOf(C, Matrix.of([[-2, 2], [2, -2]]));
    expect(s(g)).toBe('GeneratorMatrixOf(ContinuousMarkovChain(C, (0, 1), Matrix([[-1, 1], [1, -1]])), Matrix([[-2, 2], [2, -2]]))');
    expect(g.process).toBe(C);
    expect(s(g.withArgs(g.args))).toBe(s(g));
    const ss = StochasticStateSpaceOf(Y, [0, 1, 2]);
    expect(s(ss)).toBe(`StochasticStateSpaceOf(${s(Y)}, Range(0, 3, 1))`);
    expect(ss.process).toBe(Y);
    expect(s(ss.withArgs(ss.args))).toBe(s(ss));
    expect(s(P(Eq(C.call(2), 0), and(Eq(C.call(1), 1), g)))).toBe(s(P(Eq(C.call(2), 0), Eq(C.call(1), 1))).replace(/-2\)/g, '-4)'));
  });
  it('generic processes', () => {
    const X = new StochasticProcess([new Sym('X'), finiteSet(1, 2)]);
    expect(s(X.stateSpace)).toBe('{1, 2}');
    expect(s(new StochasticProcess([new Sym('X'), new TupleNode([sympify(1), sympify(2)])]).stateSpace)).toBe('{1, 2}');
    expect(s(X.indexSet)).toBe('Reals');
    expect(s(X.distribution())).toBe('Distribution()');
    expect(s(X.density(new Sym('x')))).toBe('Density()');
    expect(() => X.probability(S.true)).toThrow(NotImplementedError);
    expect(() => X.expectation(S.true)).toThrow('Abstract method for expectation queries.');
    expect(s(X.withArgs([new Sym('Z'), finiteSet(3)]))).toBe('StochasticProcess(Z, {3})');
    const D = new DiscreteTimeStochasticProcess([new Sym('D'), finiteSet(0, 1)]);
    expect(s(D.at(new Sym('n')))).toBe('D[n]');
    expect(s(D.jointDistribution(D.at(1), D.at(2)))).toBe('JointDistribution(D[1], D[2])');
    const Ct = new ContinuousTimeStochasticProcess([new Sym('W')]);
    expect(s(Ct.call(2))).toBe('W(2)');
    const jd = D.jointDistribution(D.at(1));
    expect(() => jd.pdf(1)).toThrow('not specified');
    expect(() => jd.set).toThrow('not specified');
    expect(() => setConverter(5)).toThrow('is not an instance of list/tuple/set');
    expect(() => DiscreteMarkovChain('Y', [{} as Expr])).toThrow('is not a state');
    const [y] = sym('y', { real: true });
    // SymPy: TypeError (y + 1 in Naturals0 did not evaluate to a bool)
    expect(() => BernoulliProcess('B', 0.5).at(y.add(1))).toThrow(TypeError);
  });
  it('counting processes', () => {
    const X = PoissonProcess('X', 3);
    expect(s(P(Eq(X.call(3), 2), and(Eq(X.call(1), 0), Eq(X.call(2), 1))))).toBe('9*exp(-6)');
    expect(s(P(Le(X.call(2), 3), Eq(X.call(1), 1)))).toBe('4*exp(-3)');
    const W = WienerProcess('W');
    // SymPy: -sqrt(2)*(-sqrt(2)*pi*exp(2) - sqrt(2)*pi*exp(2)*erf(sqrt(2)))*exp(-2)/(4*pi)
    expect(s(simplify(P(Lt(W.call(2), 3), Gt(W.call(1), 1))))).toBe('erf(sqrt(2))/2 + 1/2');
    const [x, t] = sym('x t', { positive: true });
    expect(s(getTimervSwaps(x.mul(X.call(t)), new Contains(t, Lopen(0, 1))))).toBe('[[Interval.Lopen(0, 1)], [[X(t), X(1)]]]');
    expect(() => getTimervSwaps(X.call(t), sympify(3))).toThrow('not a relational');
  });
});

describe('states that are strings', () => {
  it('Str states (SymPy Str)', () => {
    const T = Matrix.of([[0.5, 0.2, 0.3], [0.2, 0.5, 0.3], [0.2, 0.3, 0.5]]);
    const Y = DiscreteMarkovChain('Y', [new Str('Sunny'), new Str('Cloudy'), new Str('Rainy')], T);
    expect(s(round(P(Eq(Y.at(3), 2), Eq(Y.at(1), 1)), 2))).toBe('0.36');
    expect(s(round(P(Eq(new Str('Rainy'), Y.at(3)), Eq(Y.at(1), new Str('Cloudy'))), 2))).toBe('0.36');
  });
});
