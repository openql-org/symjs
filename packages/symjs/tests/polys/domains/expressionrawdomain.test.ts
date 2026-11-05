// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.domains.expressionrawdomain).

import { describe, expect, it } from 'vitest';
import { parseExpr as P, sqrt } from '../../../src/index';
import { CoercionFailed, QQ } from '../../../src/polys/domains';
import { EXRAW } from '../../../src/polys/domains/expressionrawdomain';

describe('EXRAW', () => {
  it('keeps expressions as given', () => {
    const e = P('x*(x + 1)');
    expect([String(EXRAW), EXRAW.isField, EXRAW.getField() === EXRAW]).toEqual(['EXRAW', true, true]);
    expect([EXRAW.canon(e), EXRAW.fromSympy(e), EXRAW.new(sqrt(2)), EXRAW.convert(3), EXRAW.convert(QQ.new(1, 2), QQ), EXRAW.sum([e, e])].map(String)).toEqual(['x*(x + 1)', 'x*(x + 1)', 'sqrt(2)', '3', '1/2', '2*x*(x + 1)']);
    expect([EXRAW.ofType(e), EXRAW.ofType(1)]).toEqual([true, false]);
    expect(() => EXRAW.convert('a')).toThrow(CoercionFailed);
  });
});
