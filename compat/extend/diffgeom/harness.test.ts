// SPDX-License-Identifier: MIT
import { expect, it } from 'vitest';
import { runCase, deserialize, withExtension } from '../../harness';
import type { Case, Tree } from '../../harness';
import { runDiffgeomCase, runDiffgeomTestCase } from './harness';

const chart: Tree = { t: 'Extension', ref: 'R2_r' };
const field = (cls: string, n: number): Tree => ({ t: 'Extension', cls, args: [chart, { t: 'Rational', p: String(n), q: '1' }] });
const call: Case = { module: 'sympy.diffgeom.diffgeom', category: 'diffgeom', fn: '.__call__',
  src: 'e_x(x)', self: field('BaseVectorField', 0), args: [field('BaseScalarField', 0)], expected: '1' };

it('scopes extension dispatch to its corpus', () => {
  expect(runDiffgeomCase(call)).toEqual({ status: 'pass' });
  expect(runCase(call).status).not.toBe('pass');
  expect(() => deserialize(chart)).toThrow(/not registered/);
});
it('restores dispatch after a callback throws', () => {
  expect(() => withExtension({ deserialize: () => 1, adapter: () => undefined }, () => {
    expect(deserialize(chart)).toBe(1);
    throw new TypeError('sentinel');
  })).toThrow('sentinel');
  expect(() => deserialize(chart)).toThrow(/not registered/);
});
it('does not credit an incorrect exception class', () => {
  const c = { ...call, args: [field('BaseVectorField', 0)], test: 'invalid_vector', line: 1, op: '==' as const };
  expect(runDiffgeomTestCase({ ...c, raises: 'ValueError' }).status).toBe('pass');
  expect(runDiffgeomTestCase({ ...c, raises: 'TypeError' }).status).toBe('fail');
});
it('resolves the extension Point before the base geometry Point', () => {
  expect(runDiffgeomCase({ ...call, fn: 'Point', self: undefined,
    args: [chart, { t: 'Tuple', list: true, items: [{ t: 'Rational', p: '1', q: '1' }, { t: 'Rational', p: '2', q: '1' }] }],
    expected: 'Point(rectangular, Matrix([[1], [2]]))' }).status).toBe('pass');
});
