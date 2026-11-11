// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import * as parsing from '../src/parsing';
import * as root from '../src/index';
it('exports LaTeX parsing only through the parsing subpath', () => {
  expect(parsing.parseLatex('x')).toBeInstanceOf(root.Sym);
  expect('parseLatex' in root).toBe(false);
  expect('parseExpr' in parsing).toBe(false);
  expect('parseMathematica' in parsing).toBe(false);
});
