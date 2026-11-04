// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/sequences.ts.
//
// The terms the printers show for a sequence (SymPy _print_SeqFormula); the printed forms are tested
// with the LaTeX and pretty printers.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { S } from '../../src/core/nodes';
import { DOTS } from '../../src/printing/sets';
import { hasSymbolicBounds, isSequence, sequencePrintset } from '../../src/printing/sequences';

const [a, n] = sj.symbols('a n');
const show = (ts: unknown[]) => ts.map((t) => (t === DOTS ? '...' : String(t)));

describe('sequences as the printers see them', () => {
  it('isSequence', () => {
    expect(isSequence(sj.SeqFormula(sj.pow(n, 2), [n, 0, 5]))).toBe(true);
    expect(isSequence(sj.SeqPer([1, 2], [n, 0, 3]))).toBe(true);
    expect(isSequence(sj.EmptySequence)).toBe(false);
    expect(isSequence(n)).toBe(false);
  });
  it('the terms shown', () => {
    // SymPy latex(SeqFormula(n**2, (n, 0, oo))), (n, 0, 5), (n, 0, 3), (n, -oo, 0)
    const f = (start: sj.ExprLike, stop: sj.ExprLike) => sj.SeqFormula(sj.pow(n, 2), [n, start, stop]);
    const terms = (s: sj.Expr) => (isSequence(s) ? show(sequencePrintset(s)) : []);
    expect(terms(f(0, S.Infinity))).toEqual(['0', '1', '4', '9', '...']);
    expect(terms(f(0, 5))).toEqual(['0', '1', '4', '9', '...']);
    expect(terms(f(0, 3))).toEqual(['0', '1', '4', '9']);
    expect(terms(f(S.NegativeInfinity, 0))).toEqual(['...', '9', '4', '1', '0']);
  });
  it('symbolic bounds', () => {
    const s = sj.SeqFormula(sj.pow(n, 2), [n, a, S.Infinity]);
    expect(isSequence(s) && hasSymbolicBounds(s)).toBe(true);
    const t = sj.SeqFormula(sj.pow(n, 2), [n, 0, a]);
    expect(isSequence(t) && hasSymbolicBounds(t)).toBe(true);
  });
});
