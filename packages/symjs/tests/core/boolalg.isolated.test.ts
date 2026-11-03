// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/boolalg.ts.

// core/boolalg without pattern matching loaded (this file must import only the modules below,
// so it must stay a separate file): the arguments are then ordered by the sort key alone.

import { describe, expect, it } from 'vitest';
import { Sym, impl } from '../../src/core/nodes';
import '../../src/core/ops';
import { Gt } from '../../src/core/logic';
import { and } from '../../src/core/boolalg';

describe('And without core/match', () => {
  it('orders the arguments by default_sort_key', () => {
    expect('ordered' in impl).toBe(false);
    const [x, y] = [new Sym('x'), new Sym('y')];
    const e = and(Gt(y, 0), Gt(x, 0));
    expect(e.args.map((a) => a.key)).toEqual([Gt(x, 0).key, Gt(y, 0).key]);
  });
});
