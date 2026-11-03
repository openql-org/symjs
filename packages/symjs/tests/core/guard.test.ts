// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/guard.ts.
// Guard invariants.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { InvariantError } from '../../src/core/errors';
import { at, cast, defined, expectType, getOrThrow, pair } from '../../src/core/guard';

describe('guard invariants', () => {
  it('throws InvariantError when a guarantee does not hold', () => {
    expect(at([1, 2], -1)).toBe(2);
    expect(() => at([1], 3)).toThrow(InvariantError);
    expect(() => defined(undefined, 'v')).toThrow(InvariantError);
    expect(() => defined(null)).toThrow(InvariantError);
    expect(getOrThrow(new Map([['a', undefined]]), 'a')).toBe(undefined);
    expect(() => getOrThrow(new Map<string, number>(), 'a')).toThrow(InvariantError);
    expect(() => cast(1, sj.Expr)).toThrow(InvariantError);
    expect(() => cast(1, sj.Expr, 'one')).toThrow('one is not a Expr');
    expect(() => expectType(1, (v): v is string => typeof v === 'string')).toThrow(InvariantError);
    expect(pair([1, 2, 3])).toEqual([1, 2]);
  });
});
