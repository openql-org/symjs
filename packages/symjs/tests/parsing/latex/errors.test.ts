// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { LaTeXParsingError } from '../../../src/parsing/latex/errors';
it('uses the public parsing error type and preserves the diagnostic', () => {
  const e = new LaTeXParsingError('Expected } at index 3');
  expect(e).toBeInstanceOf(TypeError);
  expect(e.name).toBe('LaTeXParsingError');
  expect(e.message).toBe('Expected } at index 3');
});
