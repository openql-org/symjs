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

it('replays series indices and slices with the SeriesBase offset semantics', () => {
  const integer = (n: number) => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const x = { t: 'Symbol', name: 'x', assume: {} };
  const self = { t: 'FormalPowerSeries', f: { t: 'Fn', name: 'sin', args: [x] }, x, x0: integer(0), dir: '+' };
  const c = { ...base, module: 'sympy.series.tests.test_formal', category: 'series', fn: '.__getitem__', self };
  expect(runTestCase({ ...c, args: [integer(1)], expected: 'x' })).toEqual({ status: 'pass' });
  const absent = { t: 'Js', v: null };
  expect(runTestCase({ ...c, args: [{ t: 'Slice', start: absent, stop: integer(4), step: absent }], expected: '[0, x, 0, -x**3/6]' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, args: [{ t: 'Slice', start: integer(3), stop: integer(-1), step: integer(-1) }], expected: '[-x**3/6, 0, x, 0]' })).toEqual({ status: 'pass' });
});

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

it('rebuilds tuple-valued coordinate transformations as symbolic Lambdas', () => {
  const variables = ['x', 'y', 'z'].map((name) => ({ t: 'Symbol', name, assume: {} }));
  const self = { t: 'Vec', cls: 'CoordSys3D', name: 'a', parent: null,
    vectorNames: ['i', 'j', 'k'], variableNames: ['x1', 'x2', 'x3'],
    transformation: { t: 'Fn', name: 'Lambda', args: [
      { t: 'Tuple', items: variables }, { t: 'Tuple', items: variables },
    ] },
  };
  expect(runTestCase({ ...base, category: 'vector', fn: '.transformation_to_parent', self, args: [], expected: '(a.x1, a.x2, a.x3)' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'vector', fn: '.lame_coefficients', self, args: [], expected: '(1, 1, 1)' })).toEqual({ status: 'pass' });
});

it('routes the probability implementation name to the public stats P API', () => {
  const symbol = { t: 'Symbol', name: 'X', assume: {} };
  const variable = { t: 'Stats', cls: 'RandomSymbol', args: [symbol,
    { t: 'Stats', cls: 'SingleFinitePSpace', args: [symbol,
      { t: 'Stats', cls: 'DieDistribution', args: [{ t: 'Rational', p: '6', q: '1' }] },
    ] },
  ] };
  expect(runTestCase({ ...base, category: 'stats', fn: 'probability',
    args: [{ t: 'Rel', op: 'Equality', args: [variable, { t: 'Rational', p: '1', q: '1' }] }],
    expected: '1/6',
  })).toEqual({ status: 'pass' });
});

it('compares Lambda expressions through dummyEq without turning them into JS callbacks', () => {
  const lambda = (name: string) => {
    const variable = { t: 'Symbol', name, assume: {} };
    return { t: 'Fn', name: 'Lambda', args: [{ t: 'Tuple', items: [variable] },
      { t: 'Pow', args: [variable, { t: 'Rational', p: '2', q: '1' }] },
    ] };
  };
  expect(runTestCase({ ...base, fn: '.dummy_eq', self: lambda('x'), args: [lambda('x')], expected: 'True' })).toEqual({ status: 'pass' });
});

it('does not discard private deterministic random fixtures when replaying public APIs', () => {
  const c = { ...base, kwargs: { _random_prec: { t: 'Dict', items: [] } } };
  expect(runTestCase(c)).toEqual({ status: 'unsupported', reason: 'upstream private random fixture _random_prec' });
  expect(runTestCase({ ...c, raises: 'ValueError' }).status).toBe('unsupported');
});
