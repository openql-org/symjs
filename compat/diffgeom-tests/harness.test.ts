// SPDX-License-Identifier: MIT
import { expect, it } from 'vitest';
import * as dg from '@symjs/symjs/diffgeom';
import { runCase, deserialize, counterpartFor } from '../harness';
import type { Case, Tree } from '../harness';
import { runDiffgeomTestCase } from './harness';

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
  expect(deserialize({ t: 'Extension', ref: 'R2_r' })).toBe(dg.R2R);
  expect(counterpartFor({ name: 'Point', category: 'diffgeom' })).toBe('@symjs/symjs/diffgeom.Point');
  expect(counterpartFor({ name: 'Point', category: 'geometry' })).toBe('Point');
  expect(() => deserialize({ t: 'Diffgeom', ref: 'missing' })).toThrow(/diffgeom reference/);
});
it('does not credit an incorrect exception class', () => {
  const c = { ...call, args: [field('BaseVectorField', 0)], test: 'invalid_vector', line: 1, op: '==' as const };
  expect(runDiffgeomTestCase({ ...c, raises: 'ValueError' }).status).toBe('pass');
  expect(runDiffgeomTestCase({ ...c, raises: 'TypeError' }).status).toBe('fail');
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
