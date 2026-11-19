// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { failureKind, ratchetDifferences, replayDeadlineMs } from './tests-report';

it('validates optional replay deadlines while preserving category defaults', () => {
  expect(replayDeadlineMs('core', '')).toBe(30_000);
  expect(replayDeadlineMs('polys', '')).toBe(30_000);
  expect(replayDeadlineMs('tensor', '')).toBe(5000);
  expect(replayDeadlineMs('tensor', '30000')).toBe(30_000);
  for (const invalid of ['0', '-1', '1.5', 'NaN', 'Infinity']) {
    expect(() => replayDeadlineMs('tensor', invalid)).toThrow(RangeError);
  }
});

it('ratchets completed assertions strictly and keeps incomplete observations separate', () => {
  expect(ratchetDifferences({ cases: ['old'] }, ['new'], [])).toEqual({ regressions: ['new'], fixed: ['old'] });
  expect(ratchetDifferences({ cases: ['old'] }, ['old', 'unfinished'], ['unfinished'])).toEqual({ regressions: [], fixed: [] });
  expect(ratchetDifferences({ cases: ['old', 'unfinished'], timeouts: ['unfinished'] }, ['old'], [])).toEqual({ regressions: [], fixed: [] });
  expect(ratchetDifferences({ cases: ['old'], timeouts: [] }, [], [])).toEqual({ regressions: [], fixed: ['old'] });
});

it('distinguishes API, input, assertion and runtime failures for follow-up work', () => {
  expect(failureKind({ status: 'fail', got: 'did not raise' })).toBe('exception not raised');
  expect(failureKind({ status: 'unsupported', reason: 'no adapter for probability' })).toBe('missing API/adapter');
  expect(failureKind({ status: 'unsupported', reason: 'stats class Foo' })).toBe('unsupported value/input type');
  expect(failureKind({ status: 'error', reason: 'invalid input', phase: 'input' })).toBe('input conversion exception');
  expect(failureKind({ status: 'error', reason: 'Replay deadline exceeded (5 s)' })).toBe('replay timeout');
});
