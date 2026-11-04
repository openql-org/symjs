// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/stochasticprocess.ts (SymPy sympy/stats/stochastic_process.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Sym, str } from '../../src';
import { StochasticPSpace, UnspecifiedDistribution } from '../../src/stats/stochasticprocess';
import { BernoulliProcess, DiscreteMarkovChain } from '../../src/stats/stochasticprocesstypes';
import { NormalDistribution } from '../../src/stats/crvtypes';

describe('StochasticPSpace', () => {
  it('the space of a process', () => {
    const Y = DiscreteMarkovChain('Y', [0, 1]);
    const ps = new StochasticPSpace([new Sym('Y'), Y]);
    expect(ps.isStochastic).toBe(true);
    expect(ps.process).toBe(Y);
    expect(str(ps.symbol)).toBe('Y');
    expect(str(ps.distribution)).toBe('Distribution()');
    expect(ps.domain.args.map(str)).toEqual(['Naturals0', '{0, 1}']);
    const B = BernoulliProcess('B', 0.5);
    expect(str(B.at(1).pspace)).toBe('StochasticPSpace(B, BernoulliProcess(B, 0.5, 1, 0), BernoulliDistribution(0.5, 1, 0))');
    // SymPy: TypeError("`process` must be an instance of StochasticProcess.")
    expect(() => new StochasticPSpace([new Sym('Y'), new NormalDistribution([new Sym('a'), new Sym('b')])])).toThrow('`process` must be an instance of StochasticProcess.');
  });
  it('the unspecified distribution', () => {
    const d = new UnspecifiedDistribution();
    expect(() => d.pdf()).toThrow('not specified');
    expect(() => d.set).toThrow('not specified');
  });
});
