// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { assertionOutcome, passingModuleCases, runTestCase, testCaseKey } from './tests-harness';
import { deserialize, runCase, counterpartFor, matches } from './harness';
import type { Case, Tree } from './harness';
import * as dg from '@symjs/symjs/diffgeom';
import * as sj from '../../packages/symjs/src';
import type { TestCase } from './tests-harness';

const base: TestCase = { module: 'sympy.core.tests.test_fixture', category: 'core',
  test: 'test_fixture', line: 1, src: 'assert Integer(1) == 1', fn: 'Integer',
  args: [{ t: 'Rational', p: '1', q: '1' }], kwargs: {}, expected: '1', op: '==' };

it('translates nested containers, lambda syntax and numeric constructor arguments', () => {
  const integer = (n: number): Tree => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const text = (v: string): Tree => ({ t: 'Str', v });
  const x: Tree = { t: 'Symbol', name: 'x', assume: {} };
  const tuple: Tree = { t: 'Tuple', items: [x, { t: 'Tuple', items: [x, integer(1)] }] };
  const cases: Partial<TestCase>[] = [
    { fn: 'sympify', args: [{ t: 'Tuple', list: true, items: [text('1'), { t: 'Tuple', list: true, items: [text('2')] }] }], expected: '[1, [2]]' },
    { fn: 'sympify', args: [{ t: 'Dict', items: [[text('x'), text('2')]] }], expected: '{x: 2}' },
    { fn: 'sympify', args: [text('lambda x, y: 2*x+y')], expected: 'Lambda((x, y), 2*x + y)' },
    { fn: 'sympify', args: [text('lambda *args: args')], raises: 'SympifyError' },
    { fn: 'Float', args: [{ t: 'Float', v: 0.125, py: true }], expected: '0.125000000000000' },
    { fn: 'Integer', args: [{ t: 'Rational', p: '-7', q: '3' }], expected: '-2' },
    { fn: '.subs', self: tuple, args: [x, integer(0)], expected: '(0, (0, 1))' },
    { fn: '.atoms', self: tuple, args: [], expected: '{1, x}' },
    { fn: '.get', self: { t: 'Dict', items: [[x, integer(1)]] }, args: [integer(5), text('missing')], expected: 'missing', text: true },
    { fn: 'scaled_zero', args: [integer(7)], expected: '(([0], 1, 7, 1), -1)' },
    { fn: 'scaled_zero', args: [{ t: 'Tuple', items: [integer(1), integer(5), integer(1), integer(3)] }], raises: 'ValueError' },
    { fn: '.__call__', self: x, args: [integer(1)], raises: 'TypeError' },
  ];
  for (const c of cases) expect(runTestCase({ ...base, ...c }), String(c.fn)).toEqual({ status: 'pass' });
});

it('preserves extrema calls and distribution arguments when translating Python attributes', () => {
  const integer = (n: number) => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const x = { t: 'Symbol', name: 'x', assume: {} };
  const fn = (name: string, args: Tree[]) => ({ t: 'Fn', name, args });
  for (const name of ['Min', 'Max']) {
    expect(runTestCase({ ...base, fn: name, args: [integer(1), integer(3)], kwargs: { evaluate: { t: 'Js', v: false } }, expected: `${name}(1, 3)` })).toEqual({ status: 'pass' });
    expect(runTestCase({ ...base, fn: '.args', args: [], self: fn(name, [integer(1), integer(3)]), expected: '(1, 3)' })).toEqual({ status: 'pass' });
  }
  expect(runTestCase({ ...base, fn: '.args', args: [], self: fn('Heaviside', [x]), expected: '(x, 1/2)' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: '.pargs', args: [], self: fn('Heaviside', [x]), expected: '(x,)' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: '.pargs', args: [], self: fn('Heaviside', [x, integer(0)]), expected: '(x, 0)' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: '.is_Function', args: [], self: fn('Heaviside', [x]), expected: 'True' })).toEqual({ status: 'pass' });
});

it('adapts function inverses, numerical derivatives, residue limits and derangement keywords', () => {
  const integer = (n: number) => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const x = { t: 'Symbol', name: 'x', assume: {} };
  const fn = (name: string, args: Tree[] = [x]) => ({ t: 'Fn', name, args });
  expect(runTestCase({ ...base, fn: '.inverse', self: fn('exp'), args: [], expected: 'log' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: '.inverse', self: fn('erf'), args: [], expected: 'erfinv' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: 'test_derivative_numerically', args: [fn('sin'), x], expected: 'True' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: 'nD', args: [], kwargs: { n: integer(4) }, expected: '9' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: 'nD', args: [], kwargs: { m: { t: 'Tuple', items: [integer(2), integer(2)], list: true } }, expected: '1' })).toEqual({ status: 'pass' });
  const limits = { t: 'Tuple', items: [x, integer(0), integer(5)] };
  expect(runTestCase({ ...base, fn: 'eval_sum_residue', args: [x, limits], expected: 'None' })).toEqual({ status: 'pass' });
  for (const [name, expected] of [['digamma', 'polygamma(0, x)'], ['trigamma', 'polygamma(1, x)']] as const) {
    const unevaluated = `${name}(x)`;
    expect(String(deserialize(fn(name)))).toBe(unevaluated);
    expect(runTestCase({ ...base, fn: name, args: [x], expected })).toEqual({ status: 'pass' });
    expect(runTestCase({ ...base, fn: name, args: [x], kwargs: { evaluate: { t: 'Js', v: false } }, expected: unevaluated })).toEqual({ status: 'pass' });
  }
  expect(String(deserialize(fn('LeviCivita', [integer(1), integer(2), integer(3)])))).toBe('1');
  expect(runTestCase({ ...base, fn: '.epsilon_eq', self: integer(1), args: [integer(1)], expected: 'True' })).toEqual({ status: 'pass' });
});

it('preserves constructor heads and exception classes in the set, special function and matrix adapters', () => {
  for (const [category, module, lines] of [
    ['sets', 'sympy.sets.tests.test_conditionset', [59, 74]],
    ['sets', 'sympy.sets.tests.test_contains', [22]],
    ['functions', 'sympy.functions.combinatorial.tests.test_comb_factorials', [33, 123]],
    ['functions', 'sympy.functions.special.tests.test_beta_functions', [63, 79]],
    ['functions', 'sympy.functions.special.tests.test_spec_polynomials', [360]],
    ['matrices', 'sympy.matrices.expressions.tests.test_funcmatrix', [22]],
    ['matrices', 'sympy.matrices.tests.test_repmatrix', [49]],
    ['polys', 'sympy.polys.tests.test_polytools', [691]],
  ] as const) {
    const cases = passingModuleCases(category, module).filter((c) => lines.some((line) => line === c.line));
    expect(cases.map((c) => c.line)).toEqual(lines);
    for (const c of cases) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
  }
});

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


it('adapts polynomial construction, dense representations and return type options', () => {
  const integer = (n: number): Tree => ({ t: 'Rational', p: String(n), q: '1' });
  const x: Tree = { t: 'Symbol', name: 'x', assume: {} };
  const y: Tree = { t: 'Symbol', name: 'y', assume: {} };
  const tuple = (...items: Tree[]): Tree => ({ t: 'Tuple', items });
  const expr: Tree = { t: 'Add', args: [x, integer(1)], evaluate: false };
  const poly: Tree = { t: 'Poly', expr, gens: [x], domain: 'ZZ', pure: false };
  const c = { ...base, category: 'polys', module: 'sympy.polys.tests.test_polytools' };
  expect(runTestCase({ ...c, fn: '.rep', self: poly, args: [], expected: 'DMP_Python([1, 1], ZZ)' })).toEqual({ status: 'pass' });
  const modulus = '9007199254740997';
  expect(runTestCase({ ...c, fn: '.rep', self: { ...poly, domain: `GF(${modulus})` }, args: [], expected: `DMP_Python([SymmetricModularIntegerMod${modulus}(1), SymmetricModularIntegerMod${modulus}(1)], GF(${modulus}))` })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.get_domain', self: poly, args: [], expected: 'ZZ' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.from_poly', self: { t: 'Type', name: 'Poly' }, args: [poly], expected: "Poly(x + 1, x, domain='ZZ')" })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.from_poly', self: { t: 'Type', name: 'Poly' }, args: [poly], kwargs: { gens: y }, expected: "Poly(x + 1, y, domain='ZZ[x]')" })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: 'dict_from_expr', args: [expr], kwargs: { gens: tuple(x, y) }, expected: '({(1, 0): 1, (0, 0): 1}, (x, y))' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: 'compose', args: [expr, expr, tuple(x)], kwargs: { polys: { t: 'Js', v: true } }, expected: "Poly(x + 2, x, domain='ZZ')" })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: 'compose', args: [poly, poly], kwargs: { polys: { t: 'Js', v: false } }, expected: 'x + 2' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: 'cofactors', args: [poly, poly], expected: "(Poly(x + 1, x, domain='ZZ'), Poly(1, x, domain='ZZ'), Poly(1, x, domain='ZZ'))" })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.__call__', self: { t: 'MonomialOrder', name: 'grevlex' }, args: [tuple(integer(1), integer(2), integer(3))], expected: '(6, (-3, -2, -1))' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.__call__', self: { t: 'MonomialOrder', name: 'grevlex' }, args: [integer(1)], expected: 'unused' }).status).toBe('unsupported');
  expect(runTestCase({ ...c, fn: '.__call__', self: poly, args: [integer(2)], expected: '3' })).toEqual({ status: 'pass' });
});

it('adapts explicit and domain matrix arithmetic, slices and iteration', () => {
  const integer = (n: number): Tree => ({ t: 'Rational', p: String(n), q: '1' });
  const matrix: Tree = { t: 'Matrix', rows: [[integer(1), integer(2)], [integer(3), integer(4)]], shape: [2, 2] };
  const domainMatrix = (cls: string): Tree => ({ ...matrix, t: 'DomainMatrix', cls, domain: { t: 'Domain', name: 'ZZ' }, fmt: cls === 'SDM' ? 'sparse' : 'dense' });
  const c = { ...base, module: 'sympy.polys.matrices.tests.test_xxm', category: 'polys', kwargs: {} };
  for (const cls of ['DDM', 'SDM']) {
    const self = domainMatrix(cls);
    if (cls === 'DDM') expect(runTestCase({ ...c, fn: '.__mul__', self, args: [self], raises: 'TypeError', expected: 'None' }).status).toBe('pass');
    expect(runTestCase({ ...c, fn: cls === 'DDM' ? '.matmul' : '.__mul__', self, args: [self], expected: cls === 'DDM' ? '[[7, 10], [15, 22]]' : '{0: {0: 7, 1: 10}, 1: {0: 15, 1: 22}}' })).toEqual({ status: 'pass' });
    const slice: Tree = { t: 'Slice', start: { t: 'Js', v: null }, stop: integer(1), step: { t: 'Js', v: null } };
    expect(runTestCase({ ...c, fn: '.extract_slice', self, args: [slice, slice], expected: cls === 'DDM' ? '[[1]]' : '{0: {0: 1}}' })).toEqual({ status: 'pass' });
    const reverse: Tree = { t: 'Slice', start: { t: 'Js', v: null }, stop: { t: 'Js', v: null }, step: integer(-1) };
    expect(runTestCase({ ...c, fn: '.extract_slice', self, args: [reverse, reverse], expected: cls === 'DDM' ? '[[4, 3], [2, 1]]' : '{0: {0: 4, 1: 3}, 1: {0: 2, 1: 1}}' })).toEqual({ status: 'pass' });
  }
  expect(runTestCase({ ...c, fn: '.__pow__', self: matrix, args: [integer(2)], expected: 'Matrix([[7, 10], [15, 22]])' })).toEqual({ status: 'pass' });
  for (const [post, expected] of [['list', '[1, 2, 3, 4]'], ['tuple', '(1, 2, 3, 4)'], ['len', '4']] as const) {
    expect(runTestCase({ ...c, fn: 'simplify', args: [matrix], post, expected })).toEqual({ status: 'pass' });
  }
  expect(runTestCase({ ...c, fn: '.elementary_row_op', self: matrix, args: [{ t: 'Str', v: 'n->kn' }, integer(0), integer(2)], expected: 'Matrix([[2, 4], [3, 4]])' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.elementary_col_op', self: matrix, args: [{ t: 'Str', v: 'n->kn' }, integer(1), integer(2)], expected: 'Matrix([[1, 4], [3, 8]])' })).toEqual({ status: 'pass' });
  const symbol: Tree = { t: 'MatrixSymbol', name: 'A', rows: integer(2), cols: integer(2) };
  for (const [fn, cls] of [['.is_MatMul', 'MatMul'], ['.is_MatAdd', 'MatAdd']] as const) {
    expect(runTestCase({ ...c, fn, args: [], self: { t: 'MatExpr', cls, args: [symbol, symbol] }, expected: 'True' })).toEqual({ status: 'pass' });
    expect(runTestCase({ ...c, fn, args: [], self: symbol, expected: 'False' })).toEqual({ status: 'pass' });
  }
  for (const fn of ['.lll', '.lll_transform']) {
    expect(runTestCase({ ...c, fn, self: matrix, args: [], kwargs: { delta: integer(1) }, raises: 'ValueError', expected: 'None' }).status).toBe('pass');
  }
});

it('adapts Boolean attributes and rejects Python Boolean arithmetic', () => {
  const symbol = { t: 'Symbol', name: 'x', assume: {} };
  const truth = { t: 'Js', v: true };
  expect(runTestCase({ ...base, category: 'logic', fn: '.is_Boolean', self: truth, args: [], expected: 'True', op: 'is' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'logic', fn: '.is_Boolean', self: symbol, args: [], expected: 'False', op: 'is' })).toEqual({ status: 'pass' });
  for (const fn of ['.__add__', '.__sub__', '.__mul__', '.__truediv__', '.__pow__', '.__mod__']) {
    expect(runTestCase({ ...base, category: 'logic', fn, self: truth, args: [symbol], raises: 'TypeError', expected: 'None', op: 'is' })).toEqual({ status: 'pass' });
    expect(runTestCase({ ...base, category: 'logic', fn, self: symbol, args: [truth], raises: 'TypeError', expected: 'None', op: 'is' })).toEqual({ status: 'pass' });
  }
});

it('uses set cardinality and ordinal integer calling conventions', () => {
  const integer = (n: number) => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const set = { t: 'FiniteSet', items: [integer(1), integer(2)] };
  expect(runTestCase({ ...base, category: 'sets', fn: 'PowerSet', args: [set], post: 'len', expected: '4' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'sets', fn: 'Range', args: [integer(0), integer(10), integer(3)], post: 'len', expected: '4' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'sets', fn: '.issubset', self: set, args: [set], expected: 'True' })).toEqual({ status: 'pass' });
  const omega = { t: 'Ordinal', terms: [{ t: 'OmegaPower', exp: { t: 'Ordinal', terms: [{ t: 'OmegaPower', exp: { t: 'Ordinal', terms: [] }, mult: '1' }] }, mult: '1' }] };
  expect(runTestCase({ ...base, category: 'sets', fn: '.__add__', self: omega, args: [integer(1)], expected: 'w + 1' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'sets', fn: '.__mul__', self: integer(2), args: [omega], expected: 'w' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'sets', fn: '.__eq__', self: omega, args: [{ t: 'Symbol', name: 'x', assume: {} }], expected: 'False' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, category: 'sets', fn: '.__eq__', self: { t: 'OmegaPower', exp: omega, mult: '1' }, args: [{ t: 'Js', v: null }], expected: 'False' })).toEqual({ status: 'pass' });
});

it('passes Python booleans to symbolic Boolean operators', () => {
  const symbol = { t: 'Symbol', name: 'x', assume: {} };
  for (const [fn, expected] of [['.__and__', 'x'], ['.__or__', 'True'], ['.__xor__', '~x'], ['.__lshift__', 'True']] as const) {
    expect(runTestCase({ ...base, category: 'logic', fn, self: { t: 'Js', v: true }, args: [symbol], expected })).toEqual({ status: 'pass' });
  }
});

it('converts solver varargs, function unknowns and constant variable sets', () => {
  const x: Tree = { t: 'Symbol', name: 'x', assume: {} };
  const y: Tree = { t: 'Symbol', name: 'y', assume: {} };
  const zero: Tree = { t: 'Rational', p: '0', q: '1' };
  const equation: Tree = { t: 'Add', args: [x, { t: 'Mul', args: [{ t: 'Rational', p: '-1', q: '1' }, y] }] };
  const c = { ...base, category: 'solvers', module: 'sympy.solvers.tests.test_solveset', fn: 'nonlinsolve' };
  const eqs: Tree = { t: 'Tuple', items: [equation, zero], list: true };
  expect(runTestCase({ ...c, args: [eqs, x, y], expected: '{(y, y)}' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, args: [eqs, { t: 'Tuple', items: [x, y], list: true }], expected: '{(y, y)}' })).toEqual({ status: 'pass' });
  const f: Tree = { t: 'UFn', name: 'f', args: [x] };
  expect(runTestCase({ ...c, args: [{ t: 'Tuple', items: [f, zero] }, f, y], expected: '{(0, y)}' }).status).toBe('pass');
  const C2: Tree = { t: 'Symbol', name: 'C2', assume: {} };
  const product: Tree = { t: 'Mul', args: [C2, x] };
  expect(runTestCase({ ...c, fn: 'constant_renumber', args: [product], kwargs: { variables: { t: 'JsSet', items: [x] } }, expected: 'C1*x' }).status).toBe('pass');
  expect(runTestCase({ ...c, fn: 'constant_renumber', args: [{ t: 'Tuple', items: [product], list: true }], kwargs: { variables: { t: 'JsSet', items: [x] } }, expected: '[C1*x]' }).status).toBe('pass');
});

it('replays keyword nseries arguments without passing an options object as the expansion point', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/series.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === '.nseries' && c.src === 'assert abs(x).nseries(x, n=4) == x');
  expect(selected.length).toBeGreaterThan(0);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('maps series function attributes, free-group slices and curve calls to public members', () => {
  for (const [category, fn, tag] of [
    ['series', '.function', 'FormalPowerSeries'],
    ['combinatorics', '.__getitem__', 'FreeGroup'],
    ['geometry', '.__call__', 'Geom'],
  ]) {
    const cases: TestCase[] = JSON.parse(readFileSync(new URL(`./tests-corpus/${category}.json`, import.meta.url), 'utf8'));
    const selected = cases.filter((c) => c.fn === fn && c.self?.t === tag);
    expect(selected.length).toBeGreaterThan(0);
    for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
  }
});

it('preserves symbolic Python slice bounds for matrix printing', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/printing.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === '.__getitem__' && c.test === 'test_MatrixSlice');
  expect(selected).toHaveLength(19);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('passes serialized built-in function classes to the public LaTeX printer', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/printing.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === 'latex' && c.args?.[0]?.t === 'FnClass' && ['sin', 'cos', 'tan', 'log', 'Ei', 'zeta', 'mygamma'].includes(String(c.args[0]['name'])));
  expect(selected.length).toBeGreaterThan(5);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('translates real cdir arguments into the public series direction', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/series.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === '.series' && c.src.startsWith('assert frac(x).series(x, cdir='));
  expect(selected.length).toBeGreaterThan(0);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('constructs category arrow descriptions with a public NoMatch for Python None', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/categories.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === 'ArrowStringDescription');
  expect(selected).toHaveLength(6);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('replays polynomial keyword options, monomial tuples and sparse constructors', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/polys.json', import.meta.url), 'utf8'));
  const lines = new Set([154, 156, 158, 160, 275, 276, 629, 632, 662, 665, 671, 674,
    698, 699, 701, 702, 704, 705, 707, 708, 710, 1041, 1047, 1055, 1477, 1482,
    1492, 1502, 1511, 1523, 1835, 1840, 1856, 1857, 1858, 1859, 1860, 1861,
    1862, 1863, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 2843, 2887,
    2904, 2915, 2922, 2931, 2948, 2995, 2996, 2997, 3012, 3019]);
  const selected = cases.filter((c) => c.module === 'sympy.polys.tests.test_polytools' && lines.has(c.line));
  expect(new Set(selected.map((c) => c.line)).size).toBe(lines.size);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('preserves printed polynomial monomials and checks exponent tuples exactly', () => {
  const cases: Case[] = JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8')).cases;
  const selected = cases.filter((c) => c.module === 'sympy.polys.polytools' && ['.LM', '.EM', '.LT', '.ET'].includes(c.fn));
  expect(selected).toHaveLength(4);
  for (const c of selected) expect(runCase(c), c.src).toEqual({ status: 'pass' });
  const x = { t: 'Symbol', name: 'x', assume: {} };
  const p = { t: 'Poly', expr: x, gens: [x], domain: 'ZZ', pure: false };
  expect(runTestCase({ ...base, fn: '.LM', self: p, args: [], expected: '(2,)' }).status).toBe('fail');
});

it('replays matrix powers, indexing, identity predicates and matrix differentiation', () => {
  const cases = JSON.parse(readFileSync(new URL('./tests-corpus/matrices.json', import.meta.url), 'utf8')) as TestCase[];
  const modules = ['sympy.matrices.tests.test_matrices', 'sympy.matrices.tests.test_matrixbase'];
  const tests = ['test_diff_by_matrix', 'test_diff', 'test_power', 'test_fancy_index_matrix', 'test_is_Identity', 'test_nonvectorJacobian'];
  const selected = cases.filter((c) => modules.includes(c.module) && tests.includes(c.test));
  expect(selected).toHaveLength(233);
  for (const c of selected) expect(['pass', 'equivalent'], `${c.module}:${c.test}:${c.line}`).toContain(runTestCase(c).status);
});

it('accepts the registered correct value of a truth-value assertion whose SymPy answer is wrong', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/assumptions.json', import.meta.url), 'utf8'));
  const pick = (line: number): TestCase => {
    const c = cases.find((x) => x.module === 'sympy.assumptions.tests.test_matrices' && x.line === line);
    if (c === undefined) throw new Error(`missing case ${line}`);
    return c;
  };
  // `is True` and truthy assertions answered None, and a falsy assertion answered False
  expect(runTestCase(pick(86))).toEqual({ status: 'equivalent', got: 'None' });
  expect(runTestCase(pick(145))).toEqual({ status: 'equivalent', got: 'None' });
  expect(runTestCase(pick(225))).toEqual({ status: 'equivalent', got: 'False' });
});

it('treats != as structural: an equivalent but different expression satisfies it', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/core.json', import.meta.url), 'utf8'));
  const c = cases.find((x) => x.module === 'sympy.core.tests.test_power' && x.test === 'test_Pow_signs' && x.line === 209);
  if (c === undefined) throw new Error('missing case');
  expect(runTestCase(c)).toEqual({ status: 'pass' });
});

it('translates nested Lambda signatures and positional derivative counts through the public API', () => {
  const x = { t: 'Symbol', name: 'x', assume: {} };
  const y = { t: 'Symbol', name: 'y', assume: {} };
  const tuple = (...items: Tree[]): Tree => ({ t: 'Tuple', items });
  const integer = (n: number): Tree => ({ t: 'Rational', p: String(n), q: '1', py: true });
  const lambda = { t: 'JsLambda', params: [tuple(x, y)], body: { t: 'Add', args: [x, y] } };
  expect(runTestCase({ ...base, fn: '.__call__', self: lambda, args: [tuple(integer(2), integer(3))], expected: '5' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: 'Derivative', args: [x, x, integer(0)], expected: 'x' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: 'Derivative', args: [x, tuple(x, integer(0))], expected: 'x' })).toEqual({ status: 'pass' });
});

it('translates polynomial degrees, algebraic representations and rational Puiseux operands', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/polys.json', import.meta.url), 'utf8'));
  const selected = [
    ['test_jacobi_poly', 30],
    ['test_AlgebraicNumber', 21],
    ['test_AlgebraicNumber', 23],
    ['test_AlgebraicNumber', 140],
    ['test_field_isomorphism_pslq', 38],
    ['test_field_isomorphism', 113],
    ['test_puiseux_ring_methods', 52],
    ['test_puiseux_poly_repr', 108],
    ['test_puiseux_ring_methods', 56],
    ['test_Options_clone', 24],
  ] as const;
  for (const [test, line] of selected) {
    const c = cases.find((c) => c.test === test && c.line === line);
    expect(c, `${test}:${line}`).toBeDefined();
    if (c === undefined) throw new TypeError('missing polynomial fixture');
    expect(runTestCase(c), `${test}:${line}`).toEqual({ status: 'pass' });
  }
});

it('translates named CSE callbacks and preserves None in separatevars options', () => {
  const x: Tree = { t: 'Symbol', name: 'x', assume: {} };
  const y: Tree = { t: 'Symbol', name: 'y', assume: {} };
  const e: Tree = { t: 'Add', args: [x, y] };
  const opts: Tree = { t: 'Tuple', items: [{ t: 'Tuple', items: [{ t: 'JsFunc', name: 'sub_pre' }, { t: 'JsFunc', name: 'sub_post' }] }], list: true };
  const simplify = { ...base, module: 'sympy.simplify.tests.test_cse', category: 'simplify' };
  expect(runTestCase({ ...simplify, fn: 'preprocess_for_cse', args: [e, opts], expected: 'x + y' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...simplify, fn: 'postprocess_for_cse', args: [e, opts], expected: 'x + y' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...simplify, fn: 'cse', args: [e], kwargs: { optimizations: opts }, expected: '([], [x + y])' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...simplify, fn: 'separatevars', args: [e], kwargs: { dict: { t: 'Js', v: true }, symbols: { t: 'Js', v: null } }, expected: "{'coeff': x + y}" })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...simplify, fn: '.is_Piecewise', self: x, args: [], expected: 'False' })).toEqual({ status: 'pass' });
});

it('translates Python Boolean set attributes and partial truth assignments', () => {
  const x = { t: 'Symbol', name: 'x', assume: {} };
  const y = { t: 'Symbol', name: 'y', assume: {} };
  const boolean = (v: boolean | null): Tree => ({ t: 'Js', v });
  const expression = { t: 'BoolOp', op: 'And', args: [x, y] };
  for (const fn of ['conjuncts', 'disjuncts']) {
    expect(runTestCase({ ...base, fn, args: [x], expected: '{x}' })).toEqual({ status: 'pass' });
  }
  expect(runTestCase({ ...base, fn: '.binary_symbols', self: expression, args: [], expected: '{x, y}' })).toEqual({ status: 'pass' });
  for (const fn of ['.canonical', '.is_Atom']) {
    expect(runTestCase({ ...base, fn, self: boolean(true), args: [], expected: 'True' })).toEqual({ status: 'pass' });
  }
  expect(runTestCase({ ...base, fn: '.negated', self: boolean(true), args: [], expected: 'False' })).toEqual({ status: 'pass' });
  const model = { t: 'Dict', items: [[x, boolean(null)], [y, boolean(true)]] };
  expect(runTestCase({ ...base, fn: 'pl_true', args: [expression, model], expected: 'None' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...base, fn: 'pl_true', args: [{ ...expression, op: 'Or' }, model], expected: 'True' })).toEqual({ status: 'pass' });
});

it('replays the recursive dense DMP object API', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/polys.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.module === 'sympy.polys.tests.test_polyclasses' && c.test.startsWith('test_DMP'));
  expect(selected.length).toBeGreaterThan(100);
  for (const c of selected) expect(runTestCase(c), testCaseKey(c)).toEqual({ status: 'pass' });
});

it('preserves old polynomial-ring and AGCA operator conventions', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/polys.json', import.meta.url), 'utf8'));
  const selections = [
    ['sympy.polys.tests.test_polytools', 'test_Poly__new__', 373],
    ['sympy.polys.tests.test_polytools', 'test_Poly_eval', 1658],
    ['sympy.polys.tests.test_polytools', 'test_gcdex', 1967],
    ['sympy.polys.tests.test_polytools', 'test_gcdex', 1971],
    ['sympy.polys.tests.test_polytools', 'test_cancel', 3315],
    ['sympy.polys.agca.tests.test_ideals', 'test_ideal_operations', 29],
    ['sympy.polys.agca.tests.test_ideals', 'test_ideal_operations', 30],
    ['sympy.polys.agca.tests.test_modules', 'test_quotient', 401],
    ['sympy.polys.domains.tests.test_polynomialring', 'test_globalring', 28],
    ['sympy.polys.domains.tests.test_polynomialring', 'test_globalring', 31],
  ] as const;
  for (const [module, test, line] of selections) {
    const selected = cases.filter((c) => c.module === module && c.test === test && c.line === line);
    expect(selected.length).toBeGreaterThan(0);
    for (const c of selected) expect(runTestCase(c), testCaseKey(c)).toEqual({ status: 'pass' });
  }
});

it('compares dense polynomial domains without rounding large coefficients', () => {
  const n = 10n ** 40n;
  const f = new sj.DMPJs([n], sj.ZZ);
  expect(matches(f, `DMP_Python([${n}], QQ)`)).toBe(true);
  expect(matches(f, `DMP_Python([${n + 1n}], QQ)`)).toBe(false);
  expect(matches(new sj.DMPJs([sj.QQ.convert(sj.Rational.of(1, 3))], sj.QQ), 'DMP_Python([MPQ(2,3)], QQ)')).toBe(false);
});

it('supplies anonymous unknowns for augmented linsolve matrices and accepts equation lists', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/solvers.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === 'linsolve' && c.args?.length === 1 && c.args[0]?.t === 'Matrix');
  expect(selected.length).toBeGreaterThanOrEqual(4);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
  const x: Tree = { t: 'Symbol', name: 'x', assume: {} };
  const one: Tree = { t: 'Rational', p: '1', q: '1' };
  expect(runTestCase({ ...base, fn: 'linsolve', args: [{ t: 'Tuple', list: true, items: [{ t: 'Add', args: [x, one] }] }, x], expected: '{(-1,)}' })).toEqual({ status: 'pass' });
});

it('translates Matrix equalities and solver strategy flags through the public solvers', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/solvers.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.test === 'test_solve_Matrix' && [720, 726, 727, 728].includes(c.line)
    || c.test === 'test_minsolve_linear_system' && [1754, 1755, 1792].includes(c.line));
  expect(selected).toHaveLength(7);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});


it('compares Puiseux zero by value without changing its string representation', () => {
  const R = new sj.PuiseuxRing('x', sj.QQ);
  expect(matches(R.zero, '0')).toBe(true);
  expect(matches(R.zero, '')).toBe(true);
  expect(matches(R.one, '0')).toBe(false);
  expect(String(R.zero)).toBe('');
});

it('rejects Python list multiplication by a DomainMatrix', () => {
  const shard: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/polys.json', import.meta.url), 'utf8'));
  const test = shard.find((c) => c.module.endsWith('test_domainmatrix') && c.test === 'test_DomainMatrix_mul' && c.line === 529);
  if (!test) throw new TypeError('missing domain matrix multiplication reference');
  expect(runTestCase(test)).toEqual({ status: 'pass' });
});

it('replays captured tensor components through public array replacements without leaking state', () => {
  const integer = (n: number): Tree => ({ t: 'Rational', p: String(n), q: '1' });
  const type: Tree = { t: 'TensorIndexType', name: 'Captured', dim: integer(2), dummyName: 'C' };
  const index = (name: string, up = true): Tree => ({ t: 'TensorIndex', name, type, up });
  const head: Tree = { t: 'TensorHead', name: 'A', types: [type], symmetry: { t: 'TensorSymmetry', rank: 1, sign: 0 } };
  const tensor = (up = true): Tree => ({ t: 'Tensor', head, indices: [index('i', up)] });
  const array = (values: number[], shape: number[]): Tree => ({ t: 'NDimArray', cls: 'ImmutableDenseNDimArray', flat: values.map(integer), shape });
  const tensorData: [Tree, Tree][] = [
    [type, array([1, 0, 0, -1], [2, 2])],
    [{ t: 'Tensor', head, indices: [index('component_0')] }, array([2, 3], [2])],
  ];
  const c: TestCase = { ...base, category: 'tensor', fn: '.__getitem__', self: tensor(false), args: [integer(1)], tensorData, expected: '-3' };
  expect(runTestCase(c)).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, tensorData: [[type, integer(2)]] })).toEqual({ status: 'unsupported', reason: 'invalid tensor replacement state' });
  expect(runTestCase({ ...c, fn: '.__pow__' })).toEqual({ status: 'unsupported', reason: 'legacy tensor norm powers are not exposed by the public tensor API' });
  expect(testCaseKey(c)).toBe(testCaseKey({ ...c, tensorData: undefined }));
  expect(runTestCase({ ...c, tensorData: undefined }).status).toBe('unsupported');
  expect(runTestCase({ ...c, fn: '.data', args: [], expected: '[2, -3]' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.get_matrix', args: [], expected: 'Matrix([[2], [-3]])' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.__call__', self: head, args: [index('i')], post: 'list', expected: '[2, 3]' })).toEqual({ status: 'pass' });
  expect(runTestCase({ ...c, fn: '.data', self: { t: 'TensMul', args: [tensor(), tensor(false)] }, args: [], expected: '-5' })).toEqual({ status: 'pass' });
  const metric: Tree = { t: 'Tensor', head: { t: 'TensorHead', name: 'metric', types: [type, type], symmetry: { t: 'TensorSymmetry', rank: 2, sign: 1 } }, indices: [index('i'), index('j', false)] };
  const identity: Tree = { t: 'Matrix', rows: [[integer(1), integer(0)], [integer(0), integer(1)]], shape: [2, 2] };
  expect(runTestCase({ ...c, self: metric, args: [{ t: 'Tuple', items: [integer(1), integer(1)] }], tensorData: [[type, array([1, 2, 2, 3], [2, 2])], [metric, identity]], expected: '1' })).toEqual({ status: 'pass' });
  const changed: [Tree, Tree][] = [[type, array([1, 0, 0, -1], [2, 2])], [{ t: 'Tensor', head, indices: [index('component_0')] }, array([5, 7], [2])]];
  expect(runTestCase({ ...c, tensorData: changed, expected: '-7' })).toEqual({ status: 'pass' });
  expect(runTestCase(c)).toEqual({ status: 'pass' });
});

it('records Python class exclusions without treating them as successful assertions or changing identity', () => {
  const reason = 'Python test class sympy.core.tests.test_fixture.Local requires Python method execution';
  const c = { ...base, exclusion: reason, args: [{ ...base.args?.[0], t: 'Rational', unsupportedClass: reason }] };
  expect(runTestCase(c)).toEqual({ status: 'unsupported', reason });
  expect(() => deserialize({ t: 'Rational', p: '1', q: '1', unsupportedClass: reason })).toThrow(reason);
  expect(testCaseKey(c)).toBe(testCaseKey(base));
});

it('replays the translated Function subclasses and keeps every excluded assertion out of the ratchet', () => {
  const gaps: { cases: string[] } = JSON.parse(readFileSync(new URL('./tests-known-gaps.json', import.meta.url), 'utf8'));
  let translated = 0;
  let excluded = 0;
  for (const category of ['core', 'functions', 'concrete']) {
    const cases: TestCase[] = JSON.parse(readFileSync(new URL(`./tests-corpus/${category}.json`, import.meta.url), 'utf8'));
    for (const c of cases) {
      if (c.exclusion) {
        excluded++;
        expect(gaps.cases).not.toContain(testCaseKey(c));
      }
      if (c.module === 'sympy.core.tests.test_function' && ['test_Function', 'test_nargs_inheritance', 'test_fdiff_argument_index_error'].includes(c.test)
        || c.module === 'sympy.functions.elementary.tests.test_interface' && ['test_function_series1', 'test_function_series2'].includes(c.test)) {
        expect(c.exclusion).toBeUndefined();
        expect(runTestCase(c), testCaseKey(c)).toEqual({ status: 'pass' });
        translated++;
      }
    }
  }
  expect(translated).toBe(21);
  expect(excluded).toBeGreaterThanOrEqual(43);
});

it('compares polynomial spans and quotient cosets through their public equality', () => {
  const x = new sj.Sym('x'), y = new sj.Sym('y'), R = sj.QQ.oldPolyRing(x, y), F = R.freeModule(2);
  expect(matches(F.submodule([x, 0], [0, y]), '<[0, y], [x, 0], [x, y]>')).toBe(true);
  expect(matches(F.submodule([x, 0], [0, y]), '<[1, 0], [0, y]>')).toBe(false);
  expect(matches(F.submodule([1, 0], [1, 1]), 'QQ[x,y]**2')).toBe(true);
  expect(matches(F.submodule([x, 0]), 'QQ[x,y]**2')).toBe(false);
  expect(matches(R.ideal(x, y), '<x,y,x+y>')).toBe(true);
  expect(matches(R.ideal(x), '<y>')).toBe(false);
  const Q = F.quotientModule([[x, y]]);
  expect(matches(Q.convert([x, y]), '0')).toBe(true);
  expect(matches(Q.convert([x, y]), '[0, 1]')).toBe(false);
  expect(matches(Q.convert([x, y]), '[0, 0] + <[x, y]>')).toBe(true);
  expect(matches(Q.convert([x, y]), '[0, 0] + <[1, 0]>')).toBe(false);
});

it('compares number-field module representatives without losing denominators', () => {
  const A = new sj.PowerBasis(sj.Poly.from(sj.parse('x**2 - 2')));
  expect(matches(A.call(sj.toCol([2, 4]), 2), '[1, 2]')).toBe(true);
  expect(matches(A.call(sj.toCol([2, 4]), 2), '[1, 2]/2')).toBe(false);
  expect(matches(A.call(sj.toCol([9007199254740993n, 0n])), '[9007199254740992, 0]')).toBe(false);
  expect(matches(A.call(sj.toCol([18014398509481986n, 0n]), 2), '[9007199254740993, 0]')).toBe(true);
  expect(matches(A.submoduleFromMatrix(sj.DomainMatrix.eye(2, sj.ZZ), 1), 'Submodule[[2, 0], [0, 2]]/2')).toBe(true);
  expect(matches(A.submoduleFromMatrix(sj.DomainMatrix.eye(2, sj.ZZ), 1), 'Submodule[[2, 0], [0, 2]]')).toBe(false);
});

it('preserves polynomial object and expression conventions in algebraic-number calls', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/polys.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) => c.fn === '.minpoly' && ['sympy.polys.domains.tests.test_domains', 'sympy.polys.numberfields.tests.test_numbers'].includes(c.module)
    || c.fn === 'primitive_element' && c.module === 'sympy.polys.numberfields.tests.test_subfield' && [251, 252, 261, 263, 267].includes(c.line));
  expect(selected.length).toBeGreaterThan(20);
  for (const c of selected) expect(runTestCase(c), c.src).toEqual({ status: 'pass' });
});

it('translates matrix classmethods, explicit conversion, deletion and set validation', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/matrices.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) =>
    (c.test === 'test_hstack' || c.test === 'test_vstack' || c.test === 'test_row_col_del' || c.test === 'test_dense_conversion') ||
    c.fn === 'MatrixSet' || c.test === 'test_issue_13774');
  expect(selected.length).toBeGreaterThan(20);
  for (const c of selected) expect(runTestCase(c).status, c.src).toBe('pass');
});

it('translates matrix diagonal sizes, ragged rows and callback predicates', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/matrices.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) =>
    c.test === 'test_diag_make' || c.test === 'test_diag' && c.fn === 'diag' ||
    c.test === 'test_diagonal_symmetrical' && c.fn === '.is_symmetric' ||
    c.test === 'test_anti_symmetric' && c.fn === '.is_anti_symmetric' && c.kwargs?.simplify !== undefined ||
    c.test === 'test_errors' && c.fn === '.copyin_list').filter((c) => !c.expected.startsWith('_MinimalMatrix'));
  expect(selected.length).toBeGreaterThan(28);
  for (const c of selected) expect(runTestCase(c).status, c.src).toBe('pass');
});

it('translates matrix rewrite rules, evaluated constructors and reflected arithmetic', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('./tests-corpus/matrices.json', import.meta.url), 'utf8'));
  const selected = cases.filter((c) =>
    ['factor_in_front', 'remove_ids', 'combine_powers', 'any_zeros', 'MatAdd', 'MatMul'].includes(c.fn) ||
    c.module.endsWith('test_matmul') && c.fn === '.args_cnc' ||
    c.module.endsWith('test_matexpr') && c.test === 'test_matexpr_properties' && ['.symbol', '.name'].includes(c.fn) ||
    c.module.endsWith('test_matexpr') && [118, 119, 139].includes(c.line) ||
    c.test === 'test_no_exponentiation' ||
    c.fn === 'hessian' && [1056, 1838].includes(c.line) ||
    c.fn === 'GramSchmidt' && [2403, 3110].includes(c.line) ||
    c.fn === '.applyfunc' && c.raises === 'TypeError');
  expect(selected.length).toBeGreaterThan(25);
  for (const c of selected) expect(runTestCase(c).status, c.src).toBe('pass');
});
