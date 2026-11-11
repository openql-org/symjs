// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { BooleanKind, NumberKind, TupleKind } from '../../src/core/kind';

it('retains ordered element kinds, including nested and empty tuples', () => {
  const kind = new TupleKind(NumberKind, BooleanKind);
  expect(kind.elementKind).toEqual([NumberKind, BooleanKind]);
  expect(String(kind)).toBe('TupleKind(NumberKind, BooleanKind)');
  expect(String(new TupleKind(kind))).toBe('TupleKind(TupleKind(NumberKind, BooleanKind))');
  expect(String(new TupleKind())).toBe('TupleKind()');
});
