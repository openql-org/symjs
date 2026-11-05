// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/sathandlers.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { allargs, anyarg, exactlyonearg } from '../../src/assumptions';

const { Q } = sj;
const [x, y] = sj.symbols('x y');

describe('facts about the arguments', () => {
  it('allargs, anyarg, exactlyonearg', () => {
    const xy = sj.mul(x!, y!);
    expect(String(allargs(x!, sj.Or(Q.negative(x!), Q.positive(x!)), xy))).toBe('(Q.negative(x) | Q.positive(x)) & (Q.negative(y) | Q.positive(y))');
    expect(String(anyarg(x!, sj.And(Q.negative(x!), Q.positive(x!)), xy))).toBe('(Q.negative(x) & Q.positive(x)) | (Q.negative(y) & Q.positive(y))');
    expect(String(exactlyonearg(x!, Q.positive(x!), xy))).toBe('(Q.positive(x) & ~Q.positive(y)) | (Q.positive(y) & ~Q.positive(x))');
  });
});
