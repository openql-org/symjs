// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/askgenerated.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { getAllKnownFacts, getAllKnownMatrixFacts, getAllKnownNumberFacts, getKnownFactsDict } from '../../src/assumptions';

const { Q } = sj;

describe('ask_generated', () => {
  it('the clauses', () => {
    expect(getAllKnownNumberFacts().length).toBe(47);
    expect(getAllKnownMatrixFacts().length).toBe(24);
    expect(getAllKnownFacts().length).toBe(71);
    expect(getAllKnownNumberFacts()[0]!.map(String)).toEqual(['Literal(Q.algebraic, False)', 'Literal(Q.imaginary, True)', 'Literal(Q.transcendental, False)']);
  });
  it('the dict', () => {
    const d = getKnownFactsDict();
    const [implied, rejected] = d.get(Q.invertible)!;
    expect([...implied].map(String).sort()).toEqual(['Q.fullrank', 'Q.invertible', 'Q.square']);
    expect([...rejected].map(String)).toEqual(['Q.singular']);
    expect(d.get(Q.commutative)![1].size).toBe(0);
  });
});
