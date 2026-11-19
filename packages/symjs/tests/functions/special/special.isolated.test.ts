// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Fn, S, Sym } from '../../../src/core/nodes';
import { atan2 } from '../../../src/functions/special/special';

it('retains atan2 at negative infinity when the distribution module is absent', () => {
  const y = new Sym('y');
  expect(atan2(y, S.NegativeInfinity)).toEqual(new Fn('atan2', [y, S.NegativeInfinity]));
});
