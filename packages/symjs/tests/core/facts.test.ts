// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/facts.ts. Expected values from SymPy 1.14 StdFactKB(facts).

import { describe, expect, it } from 'vitest';
import { deduceAllFacts } from '../../src/core/facts';

const sorted = (m: Map<string, boolean>): [string, boolean][] => [...m].sort(([a], [b]) => (a < b ? -1 : 1));

describe('deduceAllFacts (SymPy FactKB.deduce_all_facts)', () => {
  it('the implications of the facts and the rules with several conditions', () => {
    expect(sorted(deduceAllFacts({ integer: true, odd: false }))).toEqual([
      ['algebraic', true], ['commutative', true], ['complex', true], ['even', true], ['extended_real', true], ['finite', true], ['hermitian', true], ['imaginary', false],
      ['infinite', false], ['integer', true], ['irrational', false], ['noninteger', false], ['odd', false], ['rational', true], ['real', true], ['transcendental', false],
    ]);
    expect(sorted(deduceAllFacts({ even: true, positive: true, prime: false })).filter(([k]) => ['composite', 'odd', 'zero'].includes(k))).toEqual([
      ['composite', true], ['odd', false], ['zero', false],
    ]);
    expect(deduceAllFacts({ prime: true }).get('composite')).toBe(false);
  });
  it('contradicting facts throw (SymPy InconsistentAssumptions)', () => {
    expect(() => deduceAllFacts({ positive: true, negative: true })).toThrow(RangeError);
  });
  it('a fact implied by another one given with it', () => {
    expect(deduceAllFacts({ positive: true, real: true }).get('nonzero')).toBe(true);
  });
  it('a fact without implications', () => {
    expect(sorted(deduceAllFacts({ unknownfact: true }))).toEqual([['unknownfact', true]]);
  });
});
