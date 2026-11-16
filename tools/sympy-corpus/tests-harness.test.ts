// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { assertionOutcome, runTestCase, testCaseKey } from './tests-harness';
import { deserialize, runCase, counterpartFor } from './harness';
import type { Case, Tree } from './harness';
import * as dg from '@symjs/symjs/diffgeom';
import * as sj from '../../packages/symjs/src';
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

it('replays str() and repr() by printing the result and comparing the text exactly', () => {
  const integer = (n: number) => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const half = { ...base, src: "assert str(Float('0.5')) == '0.500000000000000'", fn: 'Float', args: [{ t: 'Js', v: '0.5' }], text: true };
  expect(runTestCase({ ...half, post: 'str', expected: '0.500000000000000' })).toEqual({ status: 'pass' });
  // an equal value printed differently is not accepted
  expect(runTestCase({ ...half, post: 'str', expected: '0.5' })).toEqual({ status: 'fail', got: '0.500000000000000' });
  const perm = { ...base, module: 'sympy.combinatorics.tests.test_permutations', category: 'combinatorics', fn: 'Permutation',
    args: [integer(1), integer(2)], text: true };
  expect(runTestCase({ ...perm, post: 'str', expected: '(1 2)' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...perm, post: 'repr', expected: 'Permutation(1, 2)' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...perm, post: 'str', op: '!=', expected: '(1 2)' })).toEqual({ status: 'fail', got: '(1 2)' });
  const name = { ...base, fn: '.__getitem__', self: { t: 'Tuple', items: [{ t: 'Js', v: 'ab' }] }, args: [integer(0)], text: true };
  expect(runTestCase({ ...name, post: 'str', expected: 'ab' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...name, post: 'repr', expected: "'ab'" })).toEqual({ status: 'pass' });
  // JS arrays print with the brackets of the Python list or tuple they stand for
  const strip = { ...base, module: 'sympy.polys.tests.test_densebasic', category: 'polys', fn: 'dup_strip',
    args: [{ t: 'Tuple', items: [integer(0), integer(1), integer(2)], list: true }], text: true, post: 'str' as const };
  expect(runTestCase({ ...strip, brackets: 'l', expected: '[1, 2]' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...strip, brackets: 't', expected: '[1, 2]' })).toEqual({ status: 'fail', got: '(1, 2)' });
  expect(runTestCase({ ...strip, expected: '(1, 2)' })).toEqual({ status: 'pass' });
  const factors = { ...base, module: 'sympy.ntheory.tests.test_factor_', category: 'ntheory', fn: 'factorint', args: [integer(12)], text: true, post: 'repr' as const };
  expect(runTestCase({ ...factors, expected: '{2: 2, 3: 1}' })).toEqual({ status: 'pass' });
  const pair = { ...base, fn: '.__getitem__', self: { t: 'Tuple', items: [{ t: 'Tuple', items: [integer(1), { t: 'Tuple', items: [integer(2)], list: true }] }] }, args: [integer(0)], text: true, post: 'str' as const };
  expect(runTestCase({ ...pair, brackets: 'tl', expected: '(1, [2])' })).toEqual({ status: 'pass' });
});

it('compares Truth explicitly, including unknown, without accepting absent public results', () => {
  for (const [value, expected] of [[true, 'True'], [false, 'False'], ['unknown', 'None']] as const) {
    expect(assertionOutcome({ ...base, op: 'is', expected }, { status: 'fail', got: 'ignored' }, { value }).status).toBe('pass');
  }
  for (const value of [undefined, null, 1, 'True', 'unknown']) {
    expect(assertionOutcome({ ...base, op: 'truthy', expected: 'True' }, { status: 'pass' }, { value }).status).toBe('fail');
  }
  expect(assertionOutcome({ ...base, op: 'falsy', expected: 'False' }, { status: 'pass' }, { value: false }).status).toBe('pass');
  expect(assertionOutcome({ ...base, op: 'is not', expected: 'None' }, { status: 'fail', got: '[x]' }, { value: [1] }).status).toBe('pass');
  for (const value of [null, 'unknown', undefined]) {
    expect(assertionOutcome({ ...base, op: 'is not', expected: 'None' }, { status: 'fail', got: 'None' }, { value }).status).toBe('fail');
  }
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

const chart: Tree = { t: 'Diffgeom', ref: 'R2_r' };
const field = (cls: string, n: number): Tree => ({
  t: 'Diffgeom',
  cls,
  args: [chart, { t: 'Rational', p: String(n), q: '1' }],
});
const call: Case = {
  module: 'sympy.diffgeom.diffgeom',
  category: 'diffgeom',
  fn: '.__call__',
  src: 'e_x(x)',
  self: field('BaseVectorField', 0),
  args: [field('BaseScalarField', 0)],
  expected: '1',
};

it('replays differential geometry directly through the base harness', () => {
  expect(runCase(call)).toEqual({ status: 'pass' });
  expect(deserialize(chart)).toBe(dg.R2R);
  expect(counterpartFor({ name: 'Point', category: 'diffgeom' })).toBe('@symjs/symjs/diffgeom.Point');
  expect(counterpartFor({ name: 'Point', category: 'geometry' })).toBe('Point');
  expect(() => deserialize({ t: 'Diffgeom', ref: 'missing' })).toThrow(/diffgeom reference/);
});
it('reports differential-geometry exception classes through the shared harness', () => {
  const c = { ...call, args: [field('BaseVectorField', 0)], test: 'invalid_vector', line: 1, op: '==' as const };
  expect(runTestCase({ ...c, raises: 'ValueError' }).status).toBe('pass');
  expect(runTestCase({ ...c, raises: 'TypeError' }).exceptionMismatch).toEqual({ expected: 'TypeError', actual: 'RangeError' });
});
it('keeps differential-geometry and Euclidean Point dispatch distinct', () => {
  expect(
    runCase({
      ...call,
      fn: 'Point',
      self: undefined,
      args: [
        chart,
        {
          t: 'Tuple',
          list: true,
          items: [
            { t: 'Rational', p: '1', q: '1' },
            { t: 'Rational', p: '2', q: '1' },
          ],
        },
      ],
      expected: 'Point(rectangular, Matrix([[1], [2]]))',
    }).status,
  ).toBe('pass');
  expect(
    runCase({
      module: 'sympy.geometry.point',
      category: 'geometry',
      fn: 'Point',
      src: 'Point(1, 2)',
      args: [
        { t: 'Rational', p: '1', q: '1' },
        { t: 'Rational', p: '2', q: '1' },
      ],
      expected: 'Point2D(1, 2)',
    }).status,
  ).toBe('pass');
});
