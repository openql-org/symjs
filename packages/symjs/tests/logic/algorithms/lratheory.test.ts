// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/algorithms/lratheory.ts.

import { describe, expect, it } from 'vitest';
import { NotImplementedError } from '../../../src';
import { UnhandledInput } from '../../../src/logic';

describe('UnhandledInput', () => {
  it('is a NotImplementedError', () => {
    const e = new UnhandledInput('LRASolver: nan');
    expect(e).toBeInstanceOf(NotImplementedError);
    expect(e.name).toBe('UnhandledInput');
    expect(e.message).toBe('LRASolver: nan');
  });
});
