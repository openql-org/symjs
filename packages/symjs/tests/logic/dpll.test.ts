// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/dpll.ts.
// The DPLL satisfiability solver. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import '../../src';
import { SATSolver } from '../../src/logic/dpll';

// Coverage of logic/*.ts. Expected values are the str() of SymPy 1.14.

describe('inference and dpll', () => {
  it('SATSolver with an empty clause or without variables', () => {
    expect([...new SATSolver([[]], 1).findModels()]).toEqual([]);
    expect([...new SATSolver([[1, 2], []], 2).findModels()]).toEqual([]);
    expect([...new SATSolver([], 0).findModels()]).toEqual([[]]);
  });
});
