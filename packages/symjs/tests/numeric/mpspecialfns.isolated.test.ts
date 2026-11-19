// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Fn, S } from '../../src/core/nodes';
import { evalf } from '../../src/numeric/evalf';
import '../../src/numeric/mpspecialfns';

it('evaluates integer-order polygamma with the standalone numeric module', () => {
  const trigamma = new Fn('polygamma', [S.One, S.One]);
  expect(evalf(trigamma).toNumber()).toBeCloseTo(Math.PI ** 2 / 6, 14);
});
