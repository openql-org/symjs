// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { Fn, S, Sym } from '../../src/core/nodes';
import { rewrite } from '../../src/simplify/rewrite';

it('rewrites Ci without the special functions registration', () => {
  const x = new Sym('x');
  const expanded = rewrite(new Fn('Ci', [x]), 'expint');
  expect(expanded.has(S.I)).toBe(true);
  expect(expanded.key).not.toBe(new Fn('Ci', [x]).key);
});
