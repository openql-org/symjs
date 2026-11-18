// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/algorithms/lratheory.ts.

import { describe, expect, it } from 'vitest';
import { NotImplementedError } from '../../../src';
import { UnhandledInput } from '../../../src/logic';

describe('UnhandledInput', () => {
  it('is a NotImplementedError', () => {
    const e = new UnhandledInput('LRASolver: nan');
    expect(e).toBeInstanceOf(NotImplementedError);
    expect(e.name).toBe('UnhandledInput');
    expect(e.message).toBe('LRASolver: nan');
  });
});

import { Add, Mul, Rational, Sym, sin } from '../../../src';
import { combineLinear, linearForm, linearFeasible } from '../../../src/logic/algorithms/lratheory';

it('parses exact affine forms and rejects nonlinear or transcendental terms', () => {
  const x = new Sym('x'), y = new Sym('y');
  expect([...linearForm(new Add([x, Rational.of(2), new Mul([Rational.of(-1), x])]))].map(([k, v]) => [k, String(v)])).toEqual([['', '2']]);
  expect([...linearForm(new Mul([Rational.of(2), Rational.of(3)]))].map(([k, v]) => [k, String(v)])).toEqual([['', '6']]);
  expect([...linearForm(new Mul([x, Rational.of(2)]))].map(([k, v]) => [k, String(v)])).toEqual([[x.key, '2']]);
  expect(() => linearForm(new Mul([x, y]))).toThrow(UnhandledInput);
  expect(() => linearForm(sin(x))).toThrow(UnhandledInput);
  expect(combineLinear(new Map(), new Map([['x', Rational.of(0)]]), Rational.of(1)).size).toBe(0);
});
it('eliminates free variables and distinguishes closed from open endpoints', () => {
  const row = (x: number, c: number, strict = false) => ({ form: new Map([['x', Rational.of(x)], ['', Rational.of(c)]]), strict });
  expect(linearFeasible([])).toBe(true);
  expect(linearFeasible([row(1, 0)])).toBe(true);
  expect(linearFeasible([row(-1, 0)])).toBe(true);
  expect(linearFeasible([row(1, 0), row(-1, 0)])).toBe(true);
  expect(linearFeasible([row(1, 0, true), row(-1, 0)])).toBe(false);
  expect(linearFeasible([row(1, 0), row(-1, 1)])).toBe(false);
  expect(linearFeasible([{ form: new Map(), strict: false }])).toBe(true);
  expect(linearFeasible([{ form: new Map(), strict: true }])).toBe(false);
});
