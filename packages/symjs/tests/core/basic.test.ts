// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/basic.ts.
// Basic: rebuilding and printing. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { inspect } from 'node:util';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y');

describe('small core nodes', () => {
  it('rebuilds Basic and prints kinds', () => {
    // SymPy: Basic(x, y).xreplace({x: y}) = Basic(y, y)
    expect(String(sj.xreplace(sj.Basic(x, y), [[x, y]]))).toBe('Basic(y, y)');
    expect(inspect(sj.NumberKind)).toBe('NumberKind');
  });
});
