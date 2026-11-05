// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/utilities/dimacs.ts.
// Formulas from DIMACS CNF text. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { load } from '../../../src/logic';

describe('dimacs load', () => {
  it('reads clauses', () => {
    expect(sj.str(load('1'))).toBe('cnf_1');
    expect(sj.str(load('1 2'))).toBe('cnf_1 | cnf_2');
    expect(sj.str(load('1 \n 2'))).toBe('cnf_1 & cnf_2');
    expect(sj.str(load('1 2 \n 3'))).toBe('cnf_3 & (cnf_1 | cnf_2)');
    expect(sj.str(load('c comment\np cnf 3 2\n1 -2 0\n2 3 0'))).toBe('(cnf_2 | cnf_3) & (cnf_1 | ~cnf_2)');
    expect(sj.str(load('1\n0\n2'))).toBe('cnf_1 & cnf_2');
    expect(() => load('1 x')).toThrow(RangeError);
  });
});
