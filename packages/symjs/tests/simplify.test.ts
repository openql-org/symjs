// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import type { Expr } from '../src';
import { Sym, add, cse, cseSeparate, mul, parse, postprocessForCse, preprocessForCse, repsToposort, subPost, subPre } from '../src';

it('registers cancel in the parser', () => {
  expect(String(parse('cancel((x**2 - 1)/(x - 1))'))).toBe('x + 1');
});

it('exports ordered CSE pre- and postprocessors', () => {
  const x = new Sym('x'), y = new Sym('y'), z = new Sym('z');
  const opt1 = (e: Expr) => add(e, y);
  const opt2 = (e: Expr) => mul(e, z);
  expect(String(preprocessForCse(x, [[opt1, null], [opt2, null]]))).toBe('z*(x + y)');
  expect(String(postprocessForCse(x, [[null, opt1], [null, opt2]]))).toBe('x*z + y');
  expect(preprocessForCse(x, [[null, opt1]])).toBe(x);
  expect(postprocessForCse(x, [[opt1, null]])).toBe(x);
  expect(String(subPost(subPre(parse('(-x - y)*z - x - y'))))).toBe('-x - y - z*(x + y)');
  const e = parse('(x - y)*(z - y) + exp((x - y)*(z - y))');
  expect(cse(e, { optimizations: [[subPre, subPost]] })[0].map(([, v]) => String(v))).toEqual(['(x - y)*(y - z)']);
  expect(repsToposort([[z, add(y, 1)], [y, add(x, 1)]])).toEqual([[y, add(x, 1)], [z, add(y, 1)]]);
  expect(String(cseSeparate([], [parse('Eq(x, y + 1)')])[0])).toBe('x,y + 1');
});
