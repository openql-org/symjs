// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/sieve.ts.

import { beforeEach, describe, expect, it } from 'vitest';
import { Expr, Rational } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { prime, Sieve, sieve } from '../../src/ntheory/index';

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

function take<T>(g: Iterator<T>, k: number): T[] {
  const out: T[] = [];
  for (let i = 0; i < k; i++) {
    const r = g.next();
    if (r.done === true) break;
    out.push(r.value);
  }
  return out;
}

beforeEach(() => sieve.reset());

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[...sieve.primerange(1, 30)]", () => [...sieve.primerange(1, 30)], "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"],
    ["[...sieve.primerange(19)]", () => [...sieve.primerange(19)], "[2, 3, 5, 7, 11, 13, 17]"],
    ["[...sieve.primerange(7, 19)]", () => [...sieve.primerange(7, 19)], "[7, 11, 13, 17]"],
    ["[...sieve.totientrange(7, 18)]", () => [...sieve.totientrange(7, 18)], "[6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16]"],
    ["[...sieve.mobiusrange(7, 18)]", () => [...sieve.mobiusrange(7, 18)], "[-1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1]"],
    ["sieve.search(25)", () => sieve.search(25), "[9, 10]"],
    ["sieve.search(23)", () => sieve.search(23), "[9, 9]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

describe('Sieve', () => {
  it('doctests of the shared sieve', () => {
    sieve.reset();
    expect(sieve.contains(25)).toBe(false);
    expect(py(sieve.list)).toBe('[2, 3, 5, 7, 11, 13, 17, 19, 23]');
    sieve.reset();
    sieve.extend(30);
    expect(sieve.get(10)).toBe(29n);
    sieve.reset();
    sieve.extendToNo(9);
    expect(py(sieve.list)).toBe('[2, 3, 5, 7, 11, 13, 17, 19, 23]');
    expect(sieve.search(25)).toEqual([9n, 10n]);
    expect(sieve.search(23)).toEqual([9n, 9n]);
    expect(py([...sieve.primerange(prime(10) + 1n)])).toBe('[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]');
  });

  it('a new sieve, indexing, slicing and iteration', () => {
    const s = new Sieve();
    expect(s.list[s.list.length - 1]).toBe(13n);
    expect([...s.primerangeInternal(18, 31)]).toEqual([19, 23, 29]);
    expect(s.slice(1, 6)).toEqual([2n, 3n, 5n, 7n, 11n]);
    expect(s.slice(2, 12, 3)).toEqual([3n, 11n, 19n, 31n]);
    expect(take(s[Symbol.iterator](), 6)).toEqual([2n, 3n, 5n, 7n, 11n, 13n]);
    expect([s.contains(2), s.contains(4), s.contains(97), s.contains(1), s.contains(Rational.of(1, 2))]).toEqual([true, false, true, false, false]);
    expect(s.toString()).toContain('prime sieve');
    expect(() => s.get(0)).toThrow(RangeError);
    expect(() => s.search(1)).toThrow(RangeError);
    expect(() => new Sieve(0)).toThrow(RangeError);
    expect(py([...s.totientrange(1, 10)])).toBe('[1, 1, 2, 2, 4, 2, 6, 4, 6]');
    expect(py([...s.mobiusrange(1, 10)])).toBe('[1, -1, -1, 0, -1, 1, -1, 0, 0]');
    expect(py([...s.totientrange(3, 5)])).toBe('[2, 2]');
    s.reset({ totient: true });
    expect(py([...s.mobiusrange(2, 5)])).toBe('[-1, -1, 0]');
  });
});

/**
 * Coverage of ntheory/generate.ts and ntheory/sieve.ts, starting from a
 * reset sieve (primes up to 13) so that the paths beyond the sieve run;
 * the expected values are those of SymPy 1.14 after sieve._reset().
 */

describe('ntheory sieve: results equal SymPy 1.14', () => {
  it('empty ranges, indices and resets', () => {
    expect([...sieve.primerange(10, 5)]).toEqual([]);
    expect([...sieve.totientrange(0, 5)]).toEqual([1n, 1n, 2n, 2n]);
    expect([...sieve.totientrange(5, 5)]).toEqual([]);
    expect([...sieve.mobiusrange(-1, 5)]).toEqual([1n, -1n, -1n, 0n]);
    expect([...sieve.mobiusrange(7, 3)]).toEqual([]);
    expect(() => sieve.slice(0, 5)).toThrow(RangeError);
    expect(() => sieve.slice(1, 5, 0)).toThrow(RangeError);
    expect(sieve.slice(1, 10, 3)).toEqual([2n, 7n, 17n]);
    sieve.extend(100);
    expect([...sieve.totientrange(1, 50)].length).toBe(49);
    sieve.reset({ totient: true });
    expect(sieve.primes.length).toBe(25);
    sieve.reset({ prime: true });
    expect(sieve.primes.length).toBe(6);
    // a limitation of symjs: the sieve holds 32-bit primes
    expect(() => sieve.extend(2n ** 32n)).toThrow(RangeError);
    expect(() => [...sieve.primerange(2n ** 32n, 2n ** 32n + 20n)]).toThrow(RangeError);
  });
});
