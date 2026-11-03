// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/exprmap.ts.
// ExprMap, the structurally keyed map.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y');

describe('small core nodes', () => {
  it('keeps ExprMap keys structurally', () => {
    const m = new sj.ExprMap<number>();
    m.set(1, 1);
    m.set(x, 2);
    expect(m.get(1)).toBe(1);
    expect(m.delete(y)).toBe(false);
    expect(m.delete(x)).toBe(true);
    m.clear();
    expect(m.size).toBe(0);
    expect(m.has(1)).toBe(false);
  });
});
