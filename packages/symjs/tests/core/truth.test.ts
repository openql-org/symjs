// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/truth.ts. The expected values of the fuzzy functions are SymPy 1.14's
// (sympy.core.logic), with 'unknown' for None.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

describe('fuzzy logic (SymPy sympy.core.logic)', () => {
  it('fuzzyBool', () => {
    expect([sj.fuzzyBool(true), sj.fuzzyBool(false), sj.fuzzyBool(1), sj.fuzzyBool(0), sj.fuzzyBool(2), sj.fuzzyBool(null), sj.fuzzyBool('unknown')]).toEqual([true, false, true, false, 'unknown', 'unknown', 'unknown']);
  });
  it('fuzzyAnd and fuzzyOr', () => {
    expect([sj.fuzzyAnd([]), sj.fuzzyAnd([true, null]), sj.fuzzyAnd([null, false]), sj.fuzzyAnd([true, true]), sj.fuzzyAnd([false, true])]).toEqual([true, 'unknown', false, true, false]);
    // a generator (SymPy fuzzy_and(s.is_commutative for s in syms))
    expect(sj.fuzzyAnd((function* () {
      yield 'unknown';
      yield true;
    })())).toBe('unknown');
    expect([sj.fuzzyOr([]), sj.fuzzyOr([null, true]), sj.fuzzyOr([true, false]), sj.fuzzyOr([false, false]), sj.fuzzyOr([false, null]), sj.fuzzyOr([null, false])]).toEqual([false, true, true, false, 'unknown', 'unknown']);
  });
  it('fuzzyNot, fuzzyXor and fuzzyNand', () => {
    expect([sj.fuzzyNot(true), sj.fuzzyNot(false), sj.fuzzyNot(null), sj.fuzzyNot(undefined), sj.fuzzyNot('unknown')]).toEqual([false, true, 'unknown', 'unknown', 'unknown']);
    expect([sj.fuzzyXor([true, true, true]), sj.fuzzyXor([true, false]), sj.fuzzyXor([true, null]), sj.fuzzyXor([])]).toEqual([true, true, 'unknown', false]);
    expect([sj.fuzzyNand([true, true]), sj.fuzzyNand([true, null]), sj.fuzzyNand([false])]).toEqual([false, 'unknown', true]);
  });
});
