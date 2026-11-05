// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/facts.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import {
  askFullInference,
  generateKnownFactsDict,
  getCompositePredicates,
  getKnownFacts,
  getKnownFactsKeys,
  getMatrixFacts,
  getNumberFacts,
  predicateNamed,
  singleFactLookup,
} from '../../src/assumptions';

const { Q } = sj;
const x = sj.symbol('x');
const show = (d: Map<unknown, [Set<unknown>, Set<unknown>]>): string =>
  [...d].map(([k, [i, r]]) => `${String(k)}: ({${[...i].map(String).sort().join(', ')}}, {${[...r].map(String).sort().join(', ')}})`).join(', ');

describe('known facts', () => {
  it('generate_known_facts_dict (doctest)', () => {
    const keys = [Q.even(x), Q.odd(x), Q.zero(x)];
    const fact = sj.And(sj.Implies(Q.even(x), sj.not(Q.odd(x))), sj.Implies(Q.zero(x), Q.even(x)));
    expect(show(generateKnownFactsDict(keys, fact))).toBe('Q.even: ({Q.even}, {Q.odd}), Q.odd: ({Q.odd}, {Q.even, Q.zero}), Q.zero: ({Q.even, Q.zero}, {Q.odd})');
    expect(generateKnownFactsDict([x], true).size).toBe(0);
  });
  it('facts and keys', () => {
    expect(getCompositePredicates().get(Q.real)).toEqual([Q.negative, Q.zero, Q.positive]);
    expect(sj.str(getNumberFacts()).length).toBeGreaterThan(100);
    expect(sj.str(getMatrixFacts(sj.symbol('A')))).toContain('Q.diagonal(A)');
    expect(sj.str(getKnownFacts())).toContain('Q.orthogonal(x)');
    const keys = getKnownFactsKeys();
    expect(keys).toContain(Q.even);
    expect(keys).not.toContain(Q.eq);
    expect(predicateNamed('no_such_predicate').predicateName).toBe('no_such_predicate');
  });
  it('single_fact_lookup and ask_full_inference', () => {
    const fact = sj.Implies(Q.zero(x), Q.even(x));
    expect(askFullInference(Q.even(x), Q.zero(x), fact)).toBe(true);
    expect(askFullInference(Q.zero(x), sj.not(Q.even(x)), fact)).toBe(false);
    expect(askFullInference(Q.zero(x), Q.even(x), fact)).toBe('unknown');
    const m = singleFactLookup([Q.even(x), Q.zero(x)], fact);
    expect(m.get(Q.zero(x))?.map(String)).toEqual(['Q.zero(x)', 'Q.even(x)']);
    expect(m.get(Q.even(x))?.map(String)).toEqual(['Q.even(x)']);
  });
});
