// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/residues.ts.
// Residues of expressions at points. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const x = new sj.Sym('x');
const P = (s: string) => sj.parseExpr(s);

describe('residue', () => {
  const cases: [string, string, string][] = [
    ['1/x', '0', '1'],
    ['1/x**2', '0', '0'],
    ['2/sin(x)', '0', '2'],
    ['1/(x**2 + 1)', 'I', '-I/2'],
    ['cos(x)/x**3', '0', '-1/2'],
    ['x**2 + 1', '0', '0'],
    ['1/(x - 1)', '1', '1'],
    ['a/x', '0', 'a'],
    ['1/x**30', '0', '0'],
    ['sin(x)/x**33', '0', '0'],
    ['1/(x*(x - a))', 'a', '1/a'],
    ['gamma(x)', '0', '1'],
    ['gamma(x)', '-2', '1/2'],
    ['1/tan(x)**3', '0', '-1'],
  ];
  it.each(cases)('residue(%s, x, %s) = %s', (e, p, v) => {
    expect(String(sj.residue(P(e), x, P(p)))).toBe(v);
  });

  it('rejects terms that are not integer powers', () => {
    expect(() => sj.residue(P('log(x)/x'), x)).toThrow('term of unexpected form: log(x)/x');
    expect(() => sj.residue(P('1/sqrt(x)'), x, 0)).toThrow('term of unexpected form: 1/sqrt(x)');
  });
});
