// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { Sym } from '../../src/core/nodes';
import { Ci } from '../../src/functions/special/special';
import { rewrite } from '../../src/simplify/rewrite';

it('provides the cosine integral rewrite without loading the root entry point', () => {
  expect(String(rewrite(Ci(new Sym('x')), 'expint')))
    .toBe('-expint(1, x*polar_lift(-I))/2 - expint(1, x*polar_lift(I))/2');
});
