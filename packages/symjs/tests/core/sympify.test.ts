// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/sympify.ts.
// sympify of containers. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { type Expr, SympifyError, str, sympify } from '../../src';

const s = (e: unknown): string => str(e as Expr);

describe('sympify of containers', () => {
  it('converts the expressions in arrays and keeps other values', () => {
    const r = sympify([1, 2n, null, 'a', true, [3]]) as unknown[];
    expect(r.map((v) => (typeof v === 'object' && v !== null && !Array.isArray(v) ? s(v) : v))).toEqual(['1', '2', null, 'a', true, r[5]]);
    expect((r[5] as unknown[]).map(s)).toEqual(['3']);
  });
  it('rejects values that are not expressions', () => {
    expect(() => sympify(null as never)).toThrow(SympifyError);
    expect(() => sympify(undefined as never)).toThrow(SympifyError);
    expect(() => sympify('x' as never)).toThrow(SympifyError);
  });
});
