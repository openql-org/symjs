// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Concrete, Integral, Rational, S, Sym, add, hasFiniteLimits, hasReversedLimits, variables } from '../../src';
const x = new Sym('x'), y = new Sym('y'), M = new Sym('M'), N = new Sym('N',{integer:true,positive:true});
const sum = (a: number, b: number | Sym) => new Concrete('Sum',[x,x,Rational.of(a),typeof b === 'number' ? Rational.of(b) : b]);
it('reads variables and finiteness of limits', () => {
  const inner = new Integral([x,x,S.One,S.Infinity]);
  expect(variables(new Integral([inner,y]))).toEqual([x,y]);
  expect(variables(sum(1,8))).toEqual([x]);
  expect(hasFiniteLimits(inner)).toBe(false);
  expect(hasFiniteLimits(sum(1,8))).toBe(true);
  expect(hasFiniteLimits(sum(1,M))).toBe('unknown');
  expect(hasFiniteLimits(sum(1,N))).toBe(true);
  expect(hasFiniteLimits(new Integral([x,x]))).toBe('unknown');
  expect(hasFiniteLimits(new Integral([N,N]))).toBe(true);
  expect(hasFiniteLimits(new Integral([x,N,S.One,M]))).toBe(true);
});
it('keeps unknown orientation distinct from normal and reversed limits', () => {
  expect(hasReversedLimits(sum(8,1))).toBe(true);
  expect(hasReversedLimits(sum(1,8))).toBe(false);
  expect(hasReversedLimits(sum(1,M))).toBe('unknown');
  expect(hasReversedLimits(new Integral([x,x]))).toBe('unknown');
  expect(hasReversedLimits(new Integral([x,x,S.One]))).toBe('unknown');
  expect(hasReversedLimits(new Integral([x,x,S.One,S.Infinity]))).toBe(false);
  expect(hasReversedLimits(new Concrete('Product',[x,x,Rational.of(2),add(N,2)]))).toBe(false);
});
