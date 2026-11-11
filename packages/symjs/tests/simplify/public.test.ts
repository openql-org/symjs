// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { Pow, S, asFSign1, isNoMatch, parse, sqrtBiquadraticDenest, trigSplit } from '../../src';

it('exposes trigonometric matching with NoMatch on failure', () => {
  expect(String(trigSplit(parse('cos(x)'), parse('cos(y)')))).toBe('1,1,1,x,y,true');
  expect(String(trigSplit(parse('cos(x)'), parse('-sqrt(3)*sin(x)'), true))).toBe('2,1,-1,x,pi/6,false');
  expect(isNoMatch(trigSplit(parse('cos(x)'), parse('sin(x)')))).toBe(true);
  expect(String(asFSign1(parse('2*x + 2')))).toBe('2,x,1');
  expect(isNoMatch(asFSign1(parse('x')))).toBe(true);
});

it('exposes biquadratic denesting and its NoMatch result', () => {
  const a = parse('8 + 5*sqrt(2)'), b = parse('4 + 2*sqrt(2)'), r = parse('2 + sqrt(2)');
  const root = new Pow(a.add(b.mul(r.pow(S.Half))), S.Half);
  const d2 = a.pow(2).sub(b.pow(2).mul(r));
  expect(String(sqrtBiquadraticDenest(root, a, b, r, d2))).toBe('sqrt(2) + sqrt(sqrt(2) + 2) + 2');
  expect(isNoMatch(sqrtBiquadraticDenest(root, a, S.Zero, r, d2))).toBe(true);
});
