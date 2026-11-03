// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of ntheory/qs.ts (the self-initializing quadratic sieve) with
 * the cases of SymPy 1.14's test_qs and further ones (Python's printed form).
 */

import { describe, expect, it } from 'vitest';
import { Expr } from '../src/core/nodes';
import { NoMatch, Unsolved } from '../src/core/truth';

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
import { qs, qsFactor } from '../src/ntheory/index';


describe("ntheory qs: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["qs(10009202107n, 100n, 10000n)", () => qs(10009202107n, 100n, 10000n), "[100043, 100049]"],
    ["qs(211107295182713951054568361n, 1000n, 10000n)", () => qs(211107295182713951054568361n, 1000n, 10000n), "[13791315212531, 15307263442931]"],
    ["qs(18640889198609n * 20991129234731n, 1000n, 50000n)", () => qs(18640889198609n * 20991129234731n, 1000n, 50000n), "[18640889198609, 20991129234731]"],
    ["qs(10007n ** 2n * 10009n * 10037n ** 3n * 10039n, 1000n, 2000n)", () => qs(10007n ** 2n * 10009n * 10037n ** 3n * 10039n, 1000n, 2000n), "[10009, 1005305951911, 1011141120653]"],
    ["qsFactor(1009n * 100003n, 2000n, 10000n)", () => qsFactor(1009n * 100003n, 2000n, 10000n), "{1009: 1, 100003: 1}"],
    ["qsFactor(1009n ** 2n * 2003n ** 2n * 30011n * 400009n, 2000n, 10000n)", () => qsFactor(1009n ** 2n * 2003n ** 2n * 30011n * 400009n, 2000n, 10000n), "{400009: 1, 4012009: 1, 1018081: 1, 30011: 1}"],
    ["qs(9804659461513846514n, 5000n, 20000n)", () => qs(9804659461513846514n, 5000n, 20000n), "[2, 13, 595021279, 633762691]"],
    ["qs(9804659461513846513n, 6000n, 20000n)", () => qs(9804659461513846513n, 6000n, 20000n), "[4641991, 2112166839943]"],
    ["qsFactor(4n * 1000003n, 100n, 100n)", () => qsFactor(4n * 1000003n, 100n, 100n), "{2: 2, 1000003: 1}"],
    ["qsFactor(8n * 1000003n ** 3n, 100n, 100n)", () => qsFactor(8n * 1000003n ** 3n, 100n, 100n), "{2: 3, 1000003: 3}"],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(py(f())).toBe(want));
  const errors: [string, () => unknown][] = [
    ["qsFactor(1n, 100n, 100n)", () => qsFactor(1n, 100n, 100n)],
  ];
  for (const [label, f] of errors) it(`${label} throws`, () => expect(f).toThrow());
  // SymPy 1.14's qs_factor(4) loops forever on the cofactor 1
  it('qsFactor(4n, 100n, 100n)', () => expect(py(qsFactor(4n, 100n, 100n))).toBe('{2: 2}'));
});
