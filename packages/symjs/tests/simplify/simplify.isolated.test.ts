// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { parse } from '../../src/core';
import { rewrite, simplify } from '../../src/simplify';

it('runs the doit stage through the standalone simplify entry', () => {
  expect(String(simplify(parse('Derivative(sin(x), x)')))).toBe('cos(x)');
  expect(String(simplify(parse('Derivative(sin(x), x)'), { doit: false }))).toBe('Derivative(sin(x), x)');
});

it('rewrites the cosine integral through the standalone simplify entry', () => {
  expect(String(rewrite(parse('Ci(x)'), 'expint')))
    .toBe('-expint(1, x*exp_polar(-I*pi/2))/2 - expint(1, x*exp_polar(I*pi/2))/2');
});
