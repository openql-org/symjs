// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// The errors of the number-field modules (SymPy 1.14.0 sympy.polys.numberfields.exceptions).
import { expect, it } from 'vitest';
import { ClosureFailure, MissingUnityError, StructureError } from '../../../src/polys/numberfields/exceptions';

it('names the number-field errors', () => {
  const errors = [new ClosureFailure('c'), new StructureError('s'), new MissingUnityError('m'), new ClosureFailure(), new StructureError(), new MissingUnityError()];
  expect(errors.map((e) => [e.name, e.message])).toEqual([
    ['ClosureFailure', 'c'], ['StructureError', 's'], ['MissingUnityError', 'm'], ['ClosureFailure', ''], ['StructureError', ''], ['MissingUnityError', ''],
  ]);
  expect([errors[0] instanceof RangeError, errors[1] instanceof TypeError, errors[2] instanceof StructureError]).toEqual([true, true, true]);
});
