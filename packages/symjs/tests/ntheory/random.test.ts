// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/random.ts.

import { describe, expect, it } from 'vitest';
import { Expr } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { Random } from '../../src/ntheory/random';

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
    ["[new Random(1234).getrandbits(32), new Random(1234).getrandbits(100), new Random(2n**70n + 5n).randint(0n, 10n**30n), new Random(0).getrandbits(64), new Random(-5).randint(1n, 6n)]", () => [new Random(1234).getrandbits(32), new Random(1234).getrandbits(100), new Random(2n**70n + 5n).randint(0n, 10n**30n), new Random(0).getrandbits(64), new Random(-5).randint(1n, 6n)], "[4150886329, 114146597024290628900519247801, 829904723954819379215411981483, 7106521602475165645, 5]"],
    ["((r) => [r.randint(1n, 100n), r.randint(1n, 100n), r.randrange(0n, 7n), r.getrandbits(33)])(new Random(42))", () => ((r) => [r.randint(1n, 100n), r.randint(1n, 100n), r.randrange(0n, 7n), r.getrandbits(33)])(new Random(42)), "[82, 15, 0, 3184935163]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

/**
 * Coverage of ntheory/egyptian.ts, modular.ts, digits.ts, multinomial.ts
 * and random.ts, with the expected values of SymPy 1.14 (and of Python's
 * random.Random for the Mersenne Twister).
 */

describe('ntheory egyptian, modular, digits, multinomial and random: results equal SymPy 1.14', () => {
  it('random.Random', () => {
    // a seed longer than the 624-word state
    const r = new Random(2n ** (32n * 700n) + 12345n);
    expect([r.getrandbits(32), r.getrandbits(32), r.getrandbits(32), r.getrandbits(0)]).toEqual([3687411726n, 559672658n, 722415311n, 0n]);
    expect(() => r.getrandbits(-1)).toThrow(RangeError);
    expect(() => r.randrange(5n, 5n)).toThrow(RangeError);
  });
});

describe('Python floats (random, gauss)', () => {
  it('match CPython', () => {
    const r = new Random(42);
    expect([r.random(), r.random()]).toEqual([0.6394267984578837, 0.025010755222666936]);
    const g = new Random(7);
    const v = [g.gauss(0, 1), g.gauss(0, 1), g.gauss(0, 1), g.gauss(1, 2)];
    [-0.2558802884476004, 0.511431512516514, -0.2260961647831047, 0.36986315533762915].forEach((w, i) => expect(v[i]).toBeCloseTo(w, 14));
    // reseeding drops the kept second value
    g.seed(7);
    expect(g.gauss()).toBeCloseTo(-0.2558802884476004, 14);
  });
});
