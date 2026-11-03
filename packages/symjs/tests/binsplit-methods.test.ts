// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Every method of every constant table, forced through the internal API, at
// several precisions including the table boundaries, against mpmath 1.3.0
// (see binsplit-ref.ts); the internal table API; the integer square root.

import { afterEach, describe, expect, it } from 'vitest';
import * as C from '../src/numeric/mpconst';
import type { ConstantName } from '../src/numeric/mpconst';
import * as F from '../src/numeric/mpf';
import * as M from '../src/numeric/mpfun';
import { REF, refForm } from './binsplit-ref';

const NAMES: ConstantName[] = ['pi', 'e', 'ln2', 'ln3', 'ln5', 'ln7', 'ln10', 'euler', 'catalan', 'apery', 'zeta5', 'lemniscate', 'gamma13'];

// methods run at these precisions and are rounded to 20 bits less (the reference precisions)
const CALL_PRECS = [73, 192, 193, 220, 256, 257, 1020, 2048, 2049, 10020];
const LEAVES = [1, 3, 64];

const ref = (c: string, p: number): [string, number] | undefined => REF[c]?.[p];
const rounded = (x: bigint, cp: number): [string, number] => refForm(F.fromFixed(x, cp, cp - 20), cp - 20);

afterEach(() => {
  for (const c of NAMES) C.setConstantMethodTable(c);
  C.clearConstantCache();
});

describe('each method of each constant equals mpmath', () => {
  for (const c of NAMES) {
    for (const m of C.constantMethods(c)) {
      it(`${c} by ${m}, leaf sizes ${LEAVES.join(', ')}`, () => {
        for (const leaf of LEAVES) {
          for (const cp of CALL_PRECS) {
            expect(rounded(C.computeConstantFixed(c, cp, m, leaf), cp), `${c} ${m}/${leaf} at ${cp}`).toEqual(ref(c, cp - 20));
          }
        }
      });
      it(`${c} by ${m} at 16630 bits (~5000 digits)`, () => {
        expect(rounded(C.computeConstantFixed(c, 16630, m), 16630)).toEqual(ref(c, 16610));
      });
    }
  }

  it('the table boundaries are among the tested precisions', () => {
    for (const c of NAMES) {
      const t = C.getConstantMethodTable(c);
      for (const r of t.slice(0, -1)) {
        expect(CALL_PRECS, `${c} ${r.maxPrec}`).toContain(r.maxPrec);
        expect(CALL_PRECS, `${c} ${r.maxPrec + 1}`).toContain(r.maxPrec + 1);
      }
      expect(t.at(-1)?.maxPrec).toBe(Infinity);
    }
  });

  it('the default method at a precision follows the table', () => {
    for (const c of NAMES) {
      for (const cp of [192, 193, 256, 257, 2048, 2049]) {
        expect(rounded(C.computeConstantFixed(c, cp), cp), `${c} ${cp}`).toEqual(ref(c, cp - 20));
      }
    }
  });
});

describe('internal method table API', () => {
  it('replaces a table, uses each row in its range and restores the default', () => {
    const def = C.getConstantMethodTable('pi');
    expect(C.constantMethods('pi')).toEqual(['chudnovsky', 'machin']);
    C.setConstantMethodTable('pi', [
      { maxPrec: 500, method: 'machin', leaf: 2 },
      { maxPrec: 5000, method: 'chudnovsky', leaf: 1 },
      { maxPrec: 6000, method: 'machin', leaf: 5 },
    ]);
    expect(C.getConstantMethodTable('pi').map((r) => r.method)).toEqual(['machin', 'chudnovsky', 'machin']);
    // 53 + 10 + 20 bits (machin), 1000 (chudnovsky), 10000 (above the last maxPrec: the last row)
    for (const p of [53, 1000, 10000]) expect(refForm(M.mpPi(p), p)).toEqual(ref('pi', p));
    C.setConstantMethodTable('pi');
    expect(C.getConstantMethodTable('pi')).toEqual(def);
  });

  it('a table change clears the cache of that constant', () => {
    expect(refForm(M.mpCatalan(10000), 10000)).toEqual(ref('catalan', 10000));
    C.setConstantMethodTable('catalan', [{ maxPrec: Infinity, method: 'lupas', leaf: 4 }]);
    expect(refForm(M.mpCatalan(1000), 1000)).toEqual(ref('catalan', 1000));
    expect(refForm(M.mpCatalan(200), 200)).toEqual(ref('catalan', 200));
  });

  it('rejects invalid tables and arguments with RangeError', () => {
    expect(() => C.setConstantMethodTable('e', [])).toThrow(RangeError);
    expect(() =>
      C.setConstantMethodTable('e', [
        { maxPrec: 100, method: 'taylor', leaf: 1 },
        { maxPrec: 100, method: 'taylor', leaf: 1 },
      ]),
    ).toThrow(RangeError);
    expect(() => C.setConstantMethodTable('e', [{ maxPrec: NaN, method: 'taylor', leaf: 1 }])).toThrow(RangeError);
    expect(() => C.setConstantMethodTable('e', [{ maxPrec: Infinity, method: 'machin', leaf: 1 }])).toThrow(RangeError);
    expect(() => C.setConstantMethodTable('e', [{ maxPrec: Infinity, method: 'toString', leaf: 1 }])).toThrow(RangeError);
    expect(() => C.setConstantMethodTable('e', [{ maxPrec: Infinity, method: 'taylor', leaf: 0 }])).toThrow(RangeError);
    expect(() => C.setConstantMethodTable('e', [{ maxPrec: Infinity, method: 'taylor', leaf: 1.5 }])).toThrow(RangeError);
    expect(() => C.computeConstantFixed('ln2', 100, 'chudnovsky')).toThrow(RangeError);
    expect(() => C.computeConstantFixed('ln2', 100, 'machin', 0)).toThrow(RangeError);
    // a rejected table leaves the current one in place
    expect(C.getConstantMethodTable('e')).toEqual([{ maxPrec: Infinity, method: 'taylor', leaf: 16 }]);
  });

  it('clears one or all caches', () => {
    const a = C.piFixed(300);
    C.clearConstantCache('pi');
    expect(C.piFixed(300)).toBe(a);
    const b = C.phiFixed(300);
    C.clearConstantCache();
    expect(C.phiFixed(300)).toBe(b);
    expect(C.phiFixed(5000) >> 4700n).toBe(b);
  });

  it('binary splitting of a series with and without leaves', () => {
    // sum_{k>=0} 1/2^(k+1) over 10 terms = 1 - 2^-10
    const term = (): [bigint, bigint, bigint] => [1n, 2n, 1n];
    for (const leaf of [1, 2, 4, 100]) {
      const [P, Q, T] = C.bsplit(term, 0, 10, leaf, true);
      expect([P, Q, T]).toEqual([1n, 1024n, 1023n]);
      expect(C.bsplit(term, 0, 10, leaf)[0]).toBe(leaf >= 10 ? 1n : 0n);
    }
  });
});

describe('integer square root (divide and conquer)', () => {
  // deterministic pseudo-random integers
  let seed = 12345n;
  const rand = (bits: number): bigint => {
    let r = 1n;
    for (let i = 0; i < bits; i += 31) {
      seed = (seed * 1103515245n + 12345n) % 2147483648n;
      r = (r << 31n) | seed;
    }
    return r >> BigInt(Math.max(0, F.bitLength(r) - bits));
  };
  const reference = (n: bigint): bigint => {
    if (n < 2n) return n;
    let x = 1n << BigInt(Math.ceil(F.bitLength(n) / 2));
    for (;;) {
      const y = (x + n / x) >> 1n;
      if (y >= x) return x;
      x = y;
    }
  };

  it('matches Newton iteration on random numbers, squares and their neighbours', () => {
    for (let n = 0n; n < 2000n; n++) expect(F.sqrtrem(n)).toEqual([reference(n), n - reference(n) ** 2n]);
    for (const bits of [47, 48, 49, 50, 64, 100, 127, 128, 129, 300, 1000, 4000, 20000]) {
      for (let i = 0; i < 20; i++) {
        const x = rand(bits);
        const s = rand(bits >> 1);
        for (const n of [x, s * s, s * s - 1n, s * s + 2n * s, s * s + 1n]) {
          const r = reference(n);
          expect(F.sqrtrem(n), `${n}`).toEqual([r, n - r * r]);
          expect(F.isqrt(n)).toBe(r);
        }
      }
    }
  });

  it('rejects negative numbers and keeps mpf sqrt exact', () => {
    expect(() => F.sqrtrem(-1n)).toThrow(RangeError);
    expect(F.toStr(F.sqrt(F.fromInt(1n << 400n), 53), 10)).toBe('1.606938044e+60');
    expect(F.toStr(F.sqrt(F.fromInt(2n), 200), 40)).toBe('1.41421356237309504880168872420969807857');
  });
});
