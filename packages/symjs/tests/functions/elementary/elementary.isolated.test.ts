// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/elementary/elementary.ts.

// The elementary functions without simplify/expand loaded (this file must import only the modules below,
// so it must stay a separate file).

import { expect, it } from 'vitest';
import { Fn, impl, Pow, Rational, Sym } from '../../../src/core/nodes';
import { im, re } from '../../../src/functions/elementary/elementary';

it('splits the power of a function application with re() and im() of the base when expand is not loaded', () => {
  expect(impl.asRealImagExpand === undefined).toBe(true);
  const g = new Fn('log', [new Sym('z')]);
  const root = new Pow(g, Rational.of(1n, 2n));
  const real = re(root);
  // (re(g)**2 + im(g)**2)**(1/4)*cos(atan2(im(g), re(g))/2)
  expect(real.has(new Fn('atan2', [im(g), re(g)]))).toBe(true);
  expect(real.has(new Fn('cos', [new Fn('atan2', [im(g), re(g)])]))).toBe(false);
  expect(im(root).has(re(g))).toBe(true);
});
