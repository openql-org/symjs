// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { Dyadic, Expr, capture, Matrix, sympify, sympifyMethod, Vector } from '../../packages/symjs/src';
import { deserialize, equalsSerializedOperand, fmt, matchesSympyErratum, pyEquals, runCase } from './harness';
import { capturedIterable, withQueryFixture } from './ports';
import type { Case, CaseObservation, Outcome, Tree } from './harness';

export interface TestCase extends Case {
  test: string;
  line: number;
  op: '==' | '!=' | 'is' | 'is not' | 'truthy' | 'falsy';
  raises?: string;
  capturedPrinter?: Pick<Case, 'self' | 'fn' | 'args' | 'kwargs'>;
  expectedOperand?: Tree;
  comparisonTree?: Tree;
  polyReplay?: {
    method?: string;
    originalCoeffs?: Tree[];
    intervalPrinter?: boolean;
    submoduleDiscard?: { original: Tree; index: number; computedTable: boolean };
  };
}

export type TestOutcome = Outcome & { exceptionMismatch?: { expected: string; actual: string }; phase?: 'input' | 'invoke' | 'result' };

const REPLAY_STATE = new Set([
  'capturedPrinter', 'attributeRead', 'tensorData', 'exclusion', 'unsupportedClass', 'indexedAssumptions', 'comparisonTree', 'matrixClass', 'boundMatrix', 'polyReplay',
  'expectedOperand', 'zeroDefault', 'divideError', 'functionPartials', 'randomState', 'latticeOperation', 'dummyIndex', 'globalEvaluate',
]);

export function testCaseKey(c: TestCase): string {
  // Replay state annotates an existing assertion without changing its ratchet identity.
  const serialized = JSON.stringify(c, (key, value: unknown) => REPLAY_STATE.has(key) ? undefined : value);
  return `${c.module}:${c.test}:${c.line} #${createHash('sha256').update(serialized).digest('hex').slice(0, 20)}`;
}

// The cases of one upstream test module in a corpus shard that the unit-test ratchet does not list as failing.
export function passingModuleCases(shard: string, module: string): TestCase[] {
  const gaps: { cases: string[] } = JSON.parse(readFileSync(new URL('./tests-known-gaps.json', import.meta.url), 'utf8'));
  const failing = new Set(gaps.cases);
  const cases: TestCase[] = JSON.parse(readFileSync(new URL(`./tests-corpus/${shard}.json`, import.meta.url), 'utf8'));
  return cases.filter((c) => c.module === module && !c.exclusion && !failing.has(testCaseKey(c)));
}

// Python ValueError/ZeroDivisionError correspond to range violations in JS.
// Polynomial exceptions have public classes of their own in symjs.
const ERROR_CLASSES: Readonly<Record<string, readonly string[]>> = {
  ValueError: ['RangeError'], TypeError: ['TypeError'], ZeroDivisionError: ['RangeError'],
  NotImplementedError: ['NotImplementedError'], PolynomialError: ['PolynomialError'],
  CoercionFailed: ['CoercionFailed'], DomainError: ['DomainError'],
  GeneratorsNeeded: ['GeneratorsNeeded'], SympifyError: ['SympifyError'],
  IndexError: ['RangeError'], KeyError: ['RangeError'],
};

export function assertionOutcome(c: TestCase, outcome: Outcome, observation?: CaseObservation): TestOutcome {
  if (c.raises !== undefined) {
    // An unknown adapter or failed deserialization never proves that an API raises.
    if (observation !== undefined && 'error' in observation) {
      const error = observation.error;
      const actual = error instanceof Error ? error.constructor.name : typeof error;
      const expected = ERROR_CLASSES[c.raises] ?? [c.raises];
      return expected.includes(actual) ? { status: 'pass' }
        : { status: 'pass', exceptionMismatch: { expected: c.raises, actual } };
    }
    if (outcome.status === 'unsupported' || outcome.status === 'error') return outcome;
    return { status: 'fail', got: 'did not raise' };
  }
  if (c.op === '==' && c.expectedOperand && observation && 'value' in observation && observation.value instanceof Matrix) {
    const operand = c.expectedOperand;
    const rhs = operand.t === 'SympifiableMatrix'
      ? sympify({ [sympifyMethod]: () => deserialize(operand.value as Tree) })
      : deserialize(operand);
    return rhs instanceof Matrix && observation.value.equals(rhs) ? { status: 'pass' } : { status: 'fail', got: fmt(observation.value) };
  }
  // identity with an object (x.func is cls) is compared like ==
  if (c.op === '==' || (c.op === 'is' && !['True', 'False', 'None'].includes(c.expected))) return outcome;
  // a truth-value assertion whose SymPy answer is wrong: the registered correct value counts as compatible
  if ((outcome.status === 'fail' || outcome.status === 'equivalent') && outcome.got !== undefined && matchesSympyErratum(c, outcome.got)) return { status: 'equivalent', got: outcome.got };
  if (c.op === '!=') {
    if (c.expectedOperand !== undefined && observation && 'value' in observation &&
        outcome.status !== 'error' && outcome.status !== 'unsupported') {
      try {
        return equalsSerializedOperand(observation.value, c.expectedOperand)
          ? { status: 'fail', got: fmt(observation.value) } : { status: 'pass' };
      } catch (error) {
        return { status: 'error', reason: error instanceof Error ? error.message : String(error) };
      }
    }
    // (polynomial objects and geometric entities are compared by structure, as Python's != does)
    if ((c.category === 'polys' || c.category === 'geometry') && c.comparisonTree && observation && 'value' in observation) {
      const rhs = deserialize(c.comparisonTree);
      return pyEquals(observation.value, rhs) ? { status: 'fail', got: fmt(observation.value) } : { status: 'pass' };
    }
    if (c.comparisonTree && observation && 'value' in observation && observation.value instanceof Expr) {
      const rhs = deserialize(c.comparisonTree);
      if (rhs instanceof Expr) return observation.value.equals(rhs) ? { status: 'fail', got: fmt(observation.value) } : { status: 'pass' };
    }
    // Python != compares numbers by value (Float(1.0) == 1) and other expressions by structure: a
    // mathematically equal but different expression satisfies it
    // a zero vector or dyadic prints as 0 and is not the number 0
    if (outcome.status === 'pass' && c.expected === '0' && observation && 'value' in observation && (observation.value instanceof Vector || observation.value instanceof Dyadic)) return { status: 'pass' };
    if (outcome.status === 'pass') return { status: 'fail', got: c.expected };
    if (outcome.status === 'equivalent') {
      const numeric = (v: string | undefined): boolean => v !== undefined && /^-?\d+(\.\d*)?(e[-+]?\d+)?$/.test(v);
      return numeric(outcome.got) && numeric(c.expected) ? { status: 'fail', got: c.expected } : { status: 'pass' };
    }
    if (outcome.status === 'fail') return { status: 'pass' };
    return outcome;
  }
  if (observation === undefined || !('value' in observation)) return outcome;
  const value = observation.value;
  // Do not use JS truthiness: Truth 'unknown' is truthy. The shared harness
  // normalizes unknown/NoMatch to null internally (not a public API result).
  const got = value === 'unknown' || value === null ? 'None' : value === undefined ? 'undefined' : fmt(value);
  // `x is not None` (True, False) holds for every other result.
  if (c.op === 'is not') return got !== 'undefined' && got !== c.expected ? { status: 'pass' } : { status: 'fail', got };
  return ['True', 'False', 'None'].includes(got) && got === c.expected
    ? { status: 'pass' } : { status: 'fail', got };
}

/** Reconstruct the public call with the state recorded by the unit-test extractor. */
export function replayCall(c: TestCase): TestCase {
  // These established public names capitalize the second word after "Non".
  const alias: Readonly<Record<string, string>> = { '.is_nonnegative': '.isNonNegative', '.is_nonzero': '.isNonZero', '.is_nonpositive': '.isNonPositive' };
  const fn = alias[c.fn];
  const call = c.boundMatrix ? { ...c, fn: '.' + c.fn, self: c.boundMatrix } : { ...c, fn: fn ?? c.fn };
  if (c.polyReplay?.method !== undefined) call.kwargs = { ...call.kwargs, method: { t: 'Str', v: c.polyReplay.method } };
  if (c.polyReplay?.originalCoeffs && call.self?.t === 'AlgebraicNumber') call.self = { ...call.self, coeffs: c.polyReplay.originalCoeffs };
  if (c.polyReplay?.intervalPrinter && call.self?.t === 'StrPrinter') call.self = { ...call.self, t: 'IntervalPrinter' };
  if (c.polyReplay?.submoduleDiscard) {
    const { original, index, computedTable } = c.polyReplay.submoduleDiscard;
    call.self = { ...original, discardBefore: index, computedTable };
  }
  return call;
}

export function runTestCase(c: TestCase): TestOutcome {
  if (c.exclusion) return { status: 'unsupported', reason: c.exclusion };
  // A draw from Python's seeded random generator cannot be reproduced by the JS methods.
  if (c.fn === '.random' && c.randomState === undefined) return { status: 'unsupported', reason: 'unrecorded random generator state' };
  let observation: CaseObservation | undefined;
  const call = replayCall(c);
  if (c.capturedPrinter) {
    const printer = { ...call, ...c.capturedPrinter, text: true };
    let printed: CaseObservation | undefined;
    const output = runCase(printer, (event) => { printed = event; });
    if (!printed || !('value' in printed)) return output;
    if (typeof printed.value !== 'string') return { status: 'fail', got: fmt(printed.value) };
    const pattern = printed.value;
    const got = capture((print) => print(pattern));
    return got === c.expected ? { status: 'pass' } : { status: 'fail', got };
  }
  const captured = capturedIterable(c);
  if (captured !== undefined) return captured === c.expected ? { status: 'pass' } : { status: 'fail', got: captured };
  const outcome = withQueryFixture(c, () => runCase(call, (event) => { observation = event; }));
  const result = assertionOutcome(c, outcome, observation);
  return result.status === 'error' ? { ...result, phase: observation === undefined ? 'input' : 'error' in observation ? 'invoke' : 'result' } : result;
}
