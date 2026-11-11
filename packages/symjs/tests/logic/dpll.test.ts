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

it('restores independent SAT checkpoints and resumes model enumeration', () => {
  const original = new SATSolver([[1], [-1, 2], [2, 3]], 3);
  const state = original.toState();
  const restored = SATSolver.fromState(state);
  expect(restored.toState()).toEqual(state);
  expect(restored.litHeap).toEqual(state.heap);
  expect([...restored.litScores]).toEqual(state.scores);
  expect([...restored.findModels()]).toEqual([...original.findModels()]);
  expect(state.settings).toEqual([]);
  expect(state.variableSet).toEqual([false, false, false, false]);
  const modelState = original.toState();
  const atModel = SATSolver.fromState(modelState);
  expect(atModel.varSettings).toEqual(original.varSettings);
  expect(atModel.toState()).toEqual(modelState);
  const clone = SATSolver.fromState({ ...state, learned: 2 });
  clone.clauses[0]?.push(2);
  clone.sentinels.clear();
  clone.litScores.clear();
  clone.litHeap.pop();
  expect(clone.numLearnedClauses).toBe(2);
  expect(state.clauses[0]).toEqual([1]);
  expect(clone.litScores.size).toBe(6);
  expect(clone.litHeap.length).toBe(6);
  expect([...SATSolver.fromState(new SATSolver([[]], 1).toState()).findModels()]).toEqual([]);
  expect(() => SATSolver.fromState({ ...state, levels: [] })).toThrow(RangeError);
  expect(() => SATSolver.fromState({ ...state, variables: 9 })).toThrow(RangeError);
});
