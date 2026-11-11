// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { assertionOutcome, runTestCase, testCaseKey } from './tests-harness';
import { deserialize } from './harness';
import * as sj from '../packages/symjs/src';
import type { TestCase } from './tests-harness';

const base: TestCase = { module: 'sympy.core.tests.test_fixture', category: 'core',
  test: 'test_fixture', line: 1, src: 'assert Integer(1) == 1', fn: 'Integer',
  args: [{ t: 'Rational', p: '1', q: '1' }], kwargs: {}, expected: '1', op: '==' };

it('reuses ordinary exact/equivalent matching and inverts only comparable inequality results', () => {
  expect(runTestCase(base)).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, op: '!=', expected: '2' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, op: '!=' })).toEqual({ status: 'fail', got: '1' });
  expect(assertionOutcome({ ...base, op: '!=' }, { status: 'equivalent', got: '1.0' }).status).toBe('fail');
  expect(runTestCase({ ...base, fn: 'missingFunction', op: '!=' }).status).toBe('unsupported');
});

it('compares Truth explicitly, including unknown, without accepting absent public results', () => {
  for (const [value, expected] of [[true, 'True'], [false, 'False'], ['unknown', 'None']] as const) {
    expect(assertionOutcome({ ...base, op: 'is', expected }, { status: 'fail', got: 'ignored' }, { value }).status).toBe('pass');
  }
  for (const value of [undefined, null, 1, 'True', 'unknown']) {
    expect(assertionOutcome({ ...base, op: 'truthy', expected: 'True' }, { status: 'pass' }, { value }).status).toBe('fail');
  }
  expect(assertionOutcome({ ...base, op: 'falsy', expected: 'False' }, { status: 'pass' }, { value: false }).status).toBe('pass');
  expect(runTestCase({ ...base, fn: '.is_real', self: { t: 'Symbol', name: 'x', assume: {} }, args: [], op: 'is', expected: 'None' }).status).toBe('pass');
  expect(runTestCase({ ...base, fn: '.is_nonnegative', self: { t: 'Symbol', name: 'x', assume: { positive: true } }, args: [], op: 'is', expected: 'True' }).status).toBe('pass');
});

it('accepts API exceptions in the pilot, reports mismatched classes, and rejects adapter/serialization failures', () => {
  const c = { ...base, raises: 'ValueError' };
  expect(assertionOutcome(c, { status: 'error', reason: 'invalid' }, { error: new RangeError('invalid') })).toEqual({ status: 'pass' });
  expect(assertionOutcome(c, { status: 'error', reason: 'invalid' }, { error: new TypeError('invalid') })).toEqual({
    status: 'pass', exceptionMismatch: { expected: 'ValueError', actual: 'TypeError' },
  });
  expect(runTestCase(c)).toEqual({ status: 'fail', got: 'did not raise' });
  expect(runTestCase({ ...c, fn: 'missingFunction' }).status).toBe('unsupported');
  expect(runTestCase({ ...c, args: [{ t: 'Unrecognized' }] }).status).toBe('unsupported');
  expect(runTestCase({ ...c, args: [{ t: 'Str', v: 'invalid' }] }).status).toBe('pass');
});

it('ratchet identities distinguish operators, exception contracts, locations and loop inputs', () => {
  const variants: TestCase[] = [base, { ...base, op: '!=' }, { ...base, raises: 'TypeError' },
    { ...base, line: 2 }, { ...base, test: 'test_other' }, { ...base, args: [] }];
  expect(new Set(variants.map(testCaseKey)).size).toBe(variants.length);
});

it('decodes JSON-safe non-finite Python floats without failing before the API call', () => {
  for (const [v, expected] of [['Infinity', 'oo'], ['-Infinity', '-oo'], ['NaN', 'nan']]) {
    expect(runTestCase({ ...base, fn: 'sympify', args: [{ t: 'Float', v, py: true }], expected: expected ?? '' })).toEqual({ status: 'pass' });
  }
});

it('retains unevaluated arithmetic receivers before calling the API', () => {
  const one = { t: 'Rational', p: '1', q: '1' };
  for (const t of ['Add', 'Mul', 'Pow']) {
    const value = deserialize({ t, args: [one, one], evaluate: false });
    expect(value).toBeInstanceOf(t === 'Add' ? sj.Add : t === 'Mul' ? sj.Mul : sj.Pow);
  }
  expect(runTestCase({ ...base, fn: '.args', args: [], self: { t: 'Add', args: [one, one], evaluate: false }, expected: '(1, 1)' })).toEqual({ status: 'pass' });
});
