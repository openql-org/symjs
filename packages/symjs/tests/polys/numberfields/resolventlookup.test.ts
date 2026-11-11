// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Rational } from '../../../src';
import { resolventCoefficients } from '../../../src/polys/numberfields/resolventlookup';
it('evaluates the cubic quartic resolvent over exact rational coefficients', () => {
  expect(resolventCoefficients([Rational.of(1,2),Rational.of(2),Rational.of(3),Rational.of(4)], 1).map(String)).toEqual(['1','-2','-29/2','22']);
  expect(() => resolventCoefficients([Rational.of(1)], 0)).toThrow(RangeError);
});
