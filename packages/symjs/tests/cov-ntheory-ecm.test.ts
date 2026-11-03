// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Coverage of ntheory/ecm.ts, with the expected values of SymPy 1.14. */

import { describe, expect, it } from 'vitest';
import { ecm } from '../src/ntheory/index';

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
