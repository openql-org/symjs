// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Printing of the logical connectives math.js has no operator for. */

import { describe, expect, it } from 'vitest';
import * as sj from '@symjs/symjs';
import { Implies } from '@symjs/symjs/logic';
import { toMathjsString } from '../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];

describe('symjs -> math.js connectives', () => {
  it('prints not, and rejects Implies', () => {
    expect(toMathjsString(sj.Not(x))).toBe('(not x)');
    expect(toMathjsString(sj.Ne(x, y))).toBe('(x != y)');
    expect(() => toMathjsString(Implies(x, y))).toThrow(TypeError);
  });
});
