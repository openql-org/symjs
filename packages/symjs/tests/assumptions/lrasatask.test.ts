// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/lrasatask.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { UnhandledInput, extractPredFromOldAssum } from '../../src/logic';

describe('extract_pred_from_old_assum', () => {
  it('doctest', () => {
    const [x, y] = sj.symbols('x y', { positive: true });
    expect(extractPredFromOldAssum([x!, y!, 2]).map(String)).toEqual(['Q.positive(x)', 'Q.positive(y)']);
  });
  it('each predicate and the unhandled input', () => {
    const s = (name: string, a: sj.Assumptions) => sj.symbol(name, a);
    expect(extractPredFromOldAssum([s('n', { negative: true }), s('a', { real: true, zero: false }), s('b', { nonpositive: true }), s('c', { nonnegative: true }), s('r', { real: true })]).map(String)).toEqual([
      'Q.negative(n)',
      'Q.nonzero(a)',
      'Q.nonpositive(b)',
      'Q.nonnegative(c)',
    ]);
    expect(extractPredFromOldAssum([s('z', { zero: true })]).map(String)).toEqual(['Q.zero(z)']);
    expect(() => extractPredFromOldAssum([sj.symbol('w')])).toThrow(UnhandledInput);
    expect(() => extractPredFromOldAssum([s('k', { integer: true })])).toThrow('is an integer');
    expect(() => extractPredFromOldAssum([sj.add(s('n', { integer: true }), sj.Rational.of(1n, 2n))])).toThrow("can't be an integer");
  });
});
