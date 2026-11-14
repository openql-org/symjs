// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { createHash } from 'node:crypto';
import { fmt, runCase } from './harness';
import type { Case, CaseObservation, Outcome } from './harness';

export interface TestCase extends Case {
  test: string;
  line: number;
  op: '==' | '!=' | 'is' | 'is not' | 'truthy' | 'falsy';
  raises?: string;
}

export type TestOutcome = Outcome & { exceptionMismatch?: { expected: string; actual: string }; phase?: 'input' | 'invoke' | 'result' };

export function testCaseKey(c: TestCase): string {
  return `${c.module}:${c.test}:${c.line} #${createHash('sha256').update(JSON.stringify(c)).digest('hex').slice(0, 20)}`;
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
  // identity with an object (x.func is cls) is compared like ==
  if (c.op === '==' || (c.op === 'is' && !['True', 'False', 'None'].includes(c.expected))) return outcome;
  if (c.op === '!=') {
    if (outcome.status === 'pass' || outcome.status === 'equivalent') return { status: 'fail', got: c.expected };
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

export function runTestCase(c: TestCase): TestOutcome {
  // Upstream tests inject exact random draws through a private keyword. The
  // public JS methods have no such input; dropping it would measure a random
  // experiment instead of the captured assertion.
  if (c.kwargs && '_random_prec' in c.kwargs) return { status: 'unsupported', reason: 'upstream private random fixture _random_prec' };
  let observation: CaseObservation | undefined;
  // These established public names capitalize the second word after "Non".
  const alias: Readonly<Record<string, string>> = { '.is_nonnegative': '.isNonNegative', '.is_nonzero': '.isNonZero', '.is_nonpositive': '.isNonPositive' };
  const fn = alias[c.fn];
  const outcome = runCase(fn === undefined ? c : { ...c, fn }, (event) => { observation = event; });
  const result = assertionOutcome(c, outcome, observation);
  return result.status === 'error' ? { ...result, phase: observation === undefined ? 'input' : 'error' in observation ? 'invoke' : 'result' } : result;
}
