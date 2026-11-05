// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/exceptions.ts.

import { describe, expect, it } from 'vitest';
import * as E from '../../../src/polys/matrices/exceptions';

describe('DomainMatrix exceptions', () => {
  it('have names and the SymPy hierarchy', () => {
    const all = [E.DMError, E.DMBadInputError, E.DMDomainError, E.DMNotAField, E.DMFormatError, E.DMNonInvertibleMatrixError, E.DMRankError, E.DMShapeError, E.DMNonSquareMatrixError, E.DMValueError];
    for (const C of all) {
      const e = new C('m');
      expect([e.name, e.message, e instanceof E.DMError]).toEqual([C.name, 'm', true]);
      expect(new C().message).toBe('');
    }
    expect(new E.DMNotAField() instanceof E.DMDomainError).toBe(true);
    expect(new E.DMNonSquareMatrixError() instanceof E.DMShapeError).toBe(true);
  });
});
