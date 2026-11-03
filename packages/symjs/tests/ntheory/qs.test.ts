// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/qs.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { qs, qsFactor } from '../../src/ntheory/qs';

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
    ["qs(25645121643901801n, 2000, 10000)", () => qs(25645121643901801n, 2000, 10000), "[5394769, 4753701529]"],
    ["qs(9804659461513846513n, 2000, 10000)", () => qs(9804659461513846513n, 2000, 10000), "[4641991, 2112166839943]"],
    ["qsFactor(1009n * 100003n, 2000, 10000)", () => qsFactor(1009n * 100003n, 2000, 10000), "{1009: 1, 100003: 1}"],
    ["[qsFactor(2n ** 5n * 1000003n * 1000033n, 2000, 10000), qsFactor(1000003n ** 3n, 2000, 10000), qsFactor(7919, 100, 100)]", () => [qsFactor(2n ** 5n * 1000003n * 1000033n, 2000, 10000), qsFactor(1000003n ** 3n, 2000, 10000), qsFactor(7919, 100, 100)], "[{2: 5, 1000003: 1, 1000033: 1}, {1000003: 3}, {7919: 1}]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

/**
 * Coverage of ntheory/qs.ts (the self-initializing quadratic sieve) with
 * the cases of SymPy 1.14's test_qs and further ones (Python's printed form).
 */

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

/**
 * Coverage of ntheory/primetest.ts, factor.ts and qs.ts: the Lucas-Lehmer
 * test of an exponent GIMPS has not verified, the widening of the ECM bounds
 * and a factor found as the large prime of a partial relation of the
 * quadratic sieve. Expected values from SymPy 1.14.
 */

describe('qs: a prime factor from a partial relation', () => {
  it('takes out a factor of N above the factor base', () => {
    // 1009 is not in the factor base of primes below 100; it divides N and
    // shows up as the large prime of a partial relation
    // SymPy: qs_factor(1009*100003, 100, 10000) = {1009: 1, 100003: 1}
    expect([...qsFactor(1009n * 100003n, 100n, 10000n)]).toEqual([
      [1009n, 1n],
      [100003n, 1n],
    ]);
    // SymPy: qs(1009*1000003*100003, 100, 10000) = {1009, 100003300009}
    expect([...qs(1009n * 1000003n * 100003n, 100n, 10000n)]).toEqual([1009n, 100003300009n]);
  });
});
