// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { MatrixKind, MatrixKindNode, NumberKind, UndefinedKind } from '../../src';
it('caches matrix kinds by element kind', () => {
  expect(MatrixKind()).toBe(MatrixKind(NumberKind));
  expect(String(new MatrixKindNode())).toBe('MatrixKind(NumberKind)');
  expect(MatrixKind(UndefinedKind).elementKind).toBe(UndefinedKind);
  expect(String(MatrixKind(UndefinedKind))).toBe('MatrixKind(UndefinedKind)');
});
