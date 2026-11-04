// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { S, Sym } from '../../src/index';
import { QQ } from '../../src/polys/domains';
import { BaseHolonomicError, DifferentialOperators, HolonomicFunction, NotHolonomicError, NotHyperSeriesError, NotPowerSeriesError, SingularityError } from '../../src/holonomic';

describe('holonomic errors (SymPy holonomicerrors)', () => {
  const x = new Sym('x');
  const [, Dx] = DifferentialOperators(QQ.oldPolyRing(x), 'Dx');
  const h = new HolonomicFunction(Dx.sub(1), x, 0, [1]);
  it('messages', () => {
    expect(new NotPowerSeriesError(h, S.Zero).message).toBe('A Power Series does not exists for HolonomicFunction((-1) + (1)*Dx, x, 0, [1]) about 0.');
    expect(new NotHolonomicError('Negative Power on a Holonomic Function').message).toBe('Negative Power on a Holonomic Function');
    expect(new SingularityError(h, S.One).message).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [1]) has a singularity at 1.');
    expect(new NotHyperSeriesError(h, S.Zero).message).toBe('Power series expansion of HolonomicFunction((-1) + (1)*Dx, x, 0, [1]) about 0 is not hypergeometric');
  });
  it('the base class', () => {
    expect(new NotHolonomicError('m')).toBeInstanceOf(BaseHolonomicError);
    expect(new NotPowerSeriesError(h, S.Zero).holonomic).toBe(h);
    expect(new NotPowerSeriesError(h, S.Zero).x0).toBe(S.Zero);
  });
});
