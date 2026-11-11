// SPDX-License-Identifier: MIT
import { runTestCase } from '../tests-harness';
import type { TestCase, TestOutcome } from '../tests-harness';

/** Preserve Python exception-class checks when reporting unit assertions. */
export function runDiffgeomTestCase(c: TestCase): TestOutcome {
  const result = runTestCase(c);
  return result.exceptionMismatch === undefined
    ? result
    : { status: 'fail', got: `${result.exceptionMismatch.actual}; expected ${result.exceptionMismatch.expected}` };
}
