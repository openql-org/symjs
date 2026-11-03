// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/ops.ts.

// core/ops without the elementary functions loaded (this file must import only the modules below,
// so it must stay a separate file).

import { describe, expect, it } from 'vitest';
import { Sym } from '../../src/core/nodes';
import '../../src/core/ops';

describe('realRoot without the elementary functions', () => {
  it('reports that sign is not loaded', async () => {
    const { realRoot } = await import('../../src/core/ops');
    expect(() => realRoot(new Sym('r', { real: true }), 3)).toThrow("sign is not available: import '@symjs/symjs/core'");
  });
});

describe('couldExtractMinusSign without the sort keys', () => {
  it('decides a tie by the structural key', async () => {
    const { add, mul, couldExtractMinusSign } = await import('../../src/core/ops');
    const a = new Sym('a');
    const b = new Sym('b');
    // exactly one of a - b and b - a has the minus sign extracted
    expect(couldExtractMinusSign(add(a, mul(-1, b)))).toBe(!couldExtractMinusSign(add(b, mul(-1, a))));
  });
});
