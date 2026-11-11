// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { tokenizeLatex } from '../../../src/parsing/latex/lexer';
it('preserves source positions and fraction digit boundaries across ignored whitespace', () => {
  expect(tokenizeLatex(String.raw`\frac 12\,x`, 'lark')).toEqual([
    { text: String.raw`\frac`, start: 0, end: 5 }, { text: '1', start: 6, end: 7 },
    { text: '2', start: 7, end: 8 }, { text: 'x', start: 10, end: 11 },
  ]);
});
