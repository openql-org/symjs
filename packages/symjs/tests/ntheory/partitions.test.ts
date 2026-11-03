// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/partitions.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { npartitions } from '../../src/ntheory/index';

/** Python's printed form of a result. */
function py(v: unknown): string {
  if (v === NoMatch || v === Unsolved || v === undefined || v === null) return 'None';
  if (v === true) return 'True';
  if (v === false) return 'False';
  if (typeof v === 'bigint' || typeof v === 'number' || typeof v === 'string') return String(v);
  if (v instanceof Expr) return v.toString();
  if (Array.isArray(v)) return `[${v.map(py).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${py(k)}: ${py(w)}`).join(', ')}}`;
  if (v instanceof Set) return `[${[...v].map(py).join(', ')}]`;
  return Object.prototype.toString.call(v);
}

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[npartitions(25), npartitions(100)]", () => [npartitions(25), npartitions(100)], "[1958, 190569292]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});
