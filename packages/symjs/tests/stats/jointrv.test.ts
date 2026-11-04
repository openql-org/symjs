// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/jointrv.ts (SymPy sympy/stats/joint_rv.py and the
// joint parts of sympy/stats/tests/test_joint_rv.py). Expected values are
// those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Gt, Indexed, Integral, interval, Lambda, NotImplementedError, ProductSet, Reals, Sym, TupleNode, Union, doit, mul, str, sympify } from '../../src';
import type { Expr } from '../../src';
import {
  JointDistributionHandmade,
  JointPSpace,
  JointRV,
  JointRandomSymbol,
  MarginalDistribution,
  Normal,
  NormalDistribution,
  Poisson,
  PoissonDistribution,
  RandomSymbol,
  density,
  marginalDistribution,
} from '../../src/stats';
import { jointPSpace, makeMarginalDistribution } from '../../src/stats/jointrv';

const [x, y] = [new Sym('x'), new Sym('y')];
const s = (e: unknown): string => str(e as Expr);
const m = Normal('A', [x, y], [[1, 0], [0, 1]]) as JointRandomSymbol;
const ps = m.pspace as JointPSpace;

describe('JointPSpace', () => {
  it('has the joint random symbol and its components', () => {
    expect(m).toBeInstanceOf(JointRandomSymbol);
    expect(s(ps.componentCount)).toBe('2');
    expect(s(ps.pdf)).toBe('exp(-x**2/2 + x*A[0] - y**2/2 + y*A[1] - A[0]**2/2 - A[1]**2/2)/(2*pi)');
    expect(s(ps.componentDomain(0))).toBe('Reals');
    expect(s(ps.set)).toBe('ProductSet(Reals, Reals)');
    expect(ps.symbols.map(s)).toEqual(['A']);
    expect(ps.values.map(s)).toEqual(['A']);
    expect(s(ps.domain)).toBe('Domain: {A} in ProductSet(Reals, Reals)');
    expect(s(ps.symbol)).toBe('A');
    expect(ps.hasValueDensity).toBe(true);
    expect(ps.sharesSymbols).toBe(false);
    expect(s(m.at(1))).toBe('A[1]');
    expect(() => m.at(2)).toThrow('Index keys for A can only up to 1.');
    // a joint random symbol of the empty space
    expect(s(new JointRandomSymbol('V').at(5))).toBe('V[5]');
  });
  it('computes expectations as integrals over the components', () => {
    expect(s(ps.computeExpectation(m.at(0).add(m.at(1))))).toBe(
      'Integral((A[0] + A[1])*exp(-x**2/2 + x*A[0] - y**2/2 + y*A[1] - A[0]**2/2 - A[1]**2/2)/(2*pi), (A[0], -oo, oo), (A[1], -oo, oo))',
    );
    expect(s(ps.computeExpectation(x))).toBe('Integral(x*exp(-x**2/2 + x*A[0] - y**2/2 + y*A[1] - A[0]**2/2 - A[1]**2/2)/(2*pi), (A[0], -oo, oo), (A[1], -oo, oo))');
    expect(() => ps.computeExpectation(m)).toThrow(NotImplementedError);
    // random symbols of another space are expected separately (SymPy returns the expression)
    const Z = Normal('Z', 0, 1);
    expect(s(ps.computeExpectation(mul(Z, m.at(0)), [Z]))).toBe('A[0]*Z');
    expect(s(ps.computeExpectation(mul(Z, m.at(0)), [Z, m.at(0)]))).toBe(
      'Integral(Z*exp(-x**2/2 + x*A[0] - y**2/2 + y*A[1] - A[0]**2/2 - A[1]**2/2)*A[0]/(2*pi), (A[0], -oo, oo), (A[1], -oo, oo))',
    );
    for (const f of [() => ps.where(Gt(m.at(0), 1)), () => ps.computeDensity(m.at(0)), () => ps.probability(Gt(m.at(0), 1))]) expect(f).toThrow(NotImplementedError);
  });
  it('gives single spaces for single-variable distributions', () => {
    expect(s(jointPSpace('W', new NormalDistribution([sympify(0), sympify(1)])))).toBe('SingleContinuousPSpace(W, NormalDistribution(0, 1))');
    expect(s(jointPSpace(new Sym('W'), new PoissonDistribution([sympify(1)])))).toBe('SingleDiscretePSpace(W, PoissonDistribution(1))');
  });
  it('marginal distributions', () => {
    expect(s(marginalDistribution(Normal('B', [1, 2, 3], [[1, 0, 0], [0, 1, 0], [0, 0, 1]]), 0, 1))).toBe('Lambda((B[0], B[1]), exp(-B[0]**2/2 + B[0] - B[1]**2/2 + 2*B[1] - 5/2)/(2*pi))');
    expect(() => marginalDistribution(m)).toThrow('At least one component for marginal density is needed.');
    // a component set that is neither an interval nor a range
    const U = new JointPSpace([new Sym('U'), new JointDistributionHandmade([Lambda([x, y], 1), ProductSet(Union(interval(0, 1), interval(2, 3)), Reals)])]);
    expect(() => U.marginalDistribution(1)).toThrow('integration or summation over Union(Interval(0, 1), Interval(2, 3)) is not implemented');
    // a distribution of one component
    const one = new JointPSpace([new Sym('S'), new SymbolicCount()]);
    expect(s(one.componentCount)).toBe('1');
    expect(s(one.pdf)).toBe('sqrt(2)*exp(-(-n + S[0])**2/2)/(2*sqrt(pi))');
    expect(() => one.marginalDistribution(0)).toThrow('joint distribution');
  });
});

/** A distribution whose set is not a product (one component). */
class SymbolicCount extends NormalDistribution {
  constructor() {
    super([new Sym('n'), sympify(1)]);
  }
}

describe('MarginalDistribution', () => {
  const Z = Normal('Z', 0, 1);
  it('marginalises out the random parameters', () => {
    expect(s(makeMarginalDistribution(new NormalDistribution([sympify(0), sympify(1)]), [Z]))).toBe('NormalDistribution(0, 1)');
    const md = makeMarginalDistribution(new NormalDistribution([Z, sympify(1)]), [Z]) as MarginalDistribution;
    expect(s(md)).toBe('MarginalDistribution(NormalDistribution(Z, 1), (Z,))');
    expect(s(md.set)).toBe('ProductSet(Interval(-oo, oo))');
    expect(md.symbols.map(s)).toEqual(['Z']);
    // SymPy gives NormalDistribution(x, 1): its Lambda renames the symbol inside the random symbol Z to x;
    // the random parameter Z is kept
    expect(s(md.call(x))).toBe('NormalDistribution(Z, 1)');
    expect(() => makeMarginalDistribution(new NormalDistribution([sympify(0), sympify(1)]), [x])).toThrow('Marginal distribution can be intitialised only in terms of random variables or indexed random variables');
    const P_ = Poisson('P_', 2);
    // SymPy: PoissonDistribution(y + 1) (the random symbol renamed, as above)
    expect(s((makeMarginalDistribution(new PoissonDistribution([P_.add(1)]), [P_]) as MarginalDistribution).call(y))).toBe('PoissonDistribution(P_ + 1)');
    // a component of a joint random symbol as the variable (SymPy: AttributeError for symbols)
    const W = new MarginalDistribution([new NormalDistribution([sympify(0), sympify(1)]), new TupleNode([new Indexed([m, sympify(0)])])]);
    expect(W.symbols.map(s)).toEqual(['A']);
    expect(s(W.pdf(y))).toBe('NormalDistribution(0, 1)');
  });
  it('marginal densities of random parameters are integrals and sums', () => {
    const md = new MarginalDistribution([new NormalDistribution([sympify(0), sympify(1)]), new TupleNode([Z])]);
    expect(s(md.marginaliseOut(mul(Z, x), Z))).toBe('Integral(Z*x, (Z, -oo, oo))');
    const P_ = Poisson('P_', 2);
    expect(s(md.marginaliseOut(mul(P_, x), P_))).toBe('Sum(P_*x, (P_, 0, oo))');
  });
  it('a handmade joint density with random parameters (SymPy: AttributeError)', () => {
    // SymPy fails on density(X)(1, 2) ('JointDistributionHandmade' object has no attribute 'domain');
    // the random parameter is marginalised out: E(1*2*Z) = 0
    const X = JointRV('x', mul(new Indexed([x, sympify(0)]), new Indexed([x, sympify(1)]), Z));
    expect(s(X.pspace)).toBe('JointPSpace(x, MarginalDistribution(JointDistributionHandmade(Lambda((x[0], x[1]), x[0]*x[1]*Z), ProductSet(Reals, Reals)), (x,)))');
    expect(s(X.pspace.domain)).toBe('Domain: (-oo < Z) & (Z < oo)');
    expect((X.pspace as JointPSpace).sharesSymbols).toBe(true);
    const d = (density(X) as MarginalDistribution).call(1, 2);
    expect(d).toBeInstanceOf(Integral);
    expect(s(doit(d))).toBe('0');
    expect(X).toBeInstanceOf(RandomSymbol);
  });
});
