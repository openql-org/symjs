// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { LatexTree } from '../../../src/parsing/latex/tree';
import { parseLatexLark } from '../../../src/parsing';
it('represents ambiguity without choosing or discarding an interpretation', () => {
  const result = parseLatexLark('f(x)');
  expect(result).toBeInstanceOf(LatexTree);
  expect((result as LatexTree).data).toBe('_ambig');
  expect((result as LatexTree).children).toHaveLength(2);
});
