// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/ecm.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { ecm } from '../../src/ntheory/index';

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
    ["ecm(25645121643901801n)", () => ecm(25645121643901801n), "[5394769, 4753701529]"],
    ["ecm(9804659461513846513n)", () => ecm(9804659461513846513n), "[4641991, 2112166839943]"],
    ["ecm(2n ** 64n + 1n)", () => ecm(2n ** 64n + 1n), "[274177, 67280421310721]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

/** Coverage of ntheory/ecm.ts, with the expected values of SymPy 1.14. */

describe('ntheory ecm: results equal SymPy 1.14', () => {
  it('factors found by trial division, perfect powers and curves', () => {
    expect([...ecm(2n * 3n * 100003n)]).toEqual([2n, 3n, 100003n]);
    expect([...ecm(100003n ** 2n * 7n)]).toEqual([7n, 100003n]);
    expect([...ecm(100003n ** 3n * 7n, { maxCurve: 2 })]).toEqual([7n, 100003n]);
    expect([...ecm(1000003n * 1000033n * 1000037n)]).toEqual([1000003n, 1000033n, 1000037n]);
    // SymPy raises ValueError (empty range in randrange(6, 1)) running the curves on the cofactor 1
    expect([...ecm(12n)]).toEqual([2n, 3n]);
  });
  it('errors', () => {
    expect(() => ecm(1000003n * 1000033n, { B1: 3 })).toThrow(RangeError);
    expect(() => ecm(1000003n * 1000033n, { B1: 10, B2: 20, maxCurve: 1 })).toThrow(RangeError);
    expect(() => ecm(100003n ** 3n * 100019n ** 3n, { maxCurve: 2 })).toThrow(RangeError);
  });
});
