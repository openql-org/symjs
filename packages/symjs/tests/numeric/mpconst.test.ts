// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpconst.ts.

import { afterEach, describe, expect, it } from 'vitest';
import * as sj from '../../src';
import * as C from '../../src/numeric/mpconst';
import type { ConstantName } from '../../src/numeric/mpconst';
import * as F from '../../src/numeric/mpf';
import type { Mpf } from '../../src/numeric/mpf';
import * as M from '../../src/numeric/mpfun';
import { REF, refForm } from './mpconst.ref';

const MP: [string, (prec: number) => Mpf][] = [
  ['pi', M.mpPi],
  ['e', M.mpE],
  ['ln2', M.mpLn2],
  ['ln10', M.mpLn10],
  ['euler', M.mpEuler],
  ['catalan', M.mpCatalan],
  ['apery', M.mpApery],
  ['phi', M.mpPhi],
  ['zeta5', M.mpZeta5],
];

// constants without an mp* function: the fixed-point value rounded to prec
const fx =
  (f: (p: number) => bigint) =>
  (p: number): Mpf =>
    F.fromFixed(f(p + 10), p + 10, p);

MP.push(
  ['ln3', fx(C.ln3Fixed)],
  ['ln5', fx(C.ln5Fixed)],
  ['ln7', fx(C.ln7Fixed)],
  ['lemniscate', fx(C.lemniscateFixed)],
  ['gauss', fx(C.gaussFixed)],
  ['gamma13', fx(C.gamma13Fixed)],
  ['gamma14', fx(C.gamma14Fixed)],
);

const PRECS = [53, 200, 1000, 10000, 16610];
const ref = (c: string, p: number): [string, number] | undefined => REF[c]?.[p];
const NAMES: ConstantName[] = ['pi', 'e', 'ln2', 'ln3', 'ln5', 'ln7', 'ln10', 'euler', 'catalan', 'apery', 'zeta5', 'lemniscate', 'gamma13'];

// methods run at these precisions and are rounded to 20 bits less (the reference precisions)
const CALL_PRECS = [73, 192, 193, 220, 256, 257, 1020, 2048, 2049, 10020];
const LEAVES = [1, 3, 64];
const rounded = (x: bigint, cp: number): [string, number] => refForm(F.fromFixed(x, cp, cp - 20), cp - 20);

afterEach(() => C.clearConstantCache());
afterEach(() => {
  for (const c of NAMES) C.setConstantMethodTable(c);
  C.clearConstantCache();
});

// The constants through the default method tables and the cache (mpfun mp*
// functions, evalf) against mpmath 1.3.0 / SymPy 1.14.0 (see mpconst.ref.ts).

describe('constants by binary splitting equal mpmath', () => {
  for (const [c, f] of MP) {
    it(`${c} at ${PRECS.join(', ')} bits (cold cache)`, () => {
      for (const p of PRECS) {
        C.clearConstantCache();
        expect(refForm(f(p), p), `${c} ${p}`).toEqual(ref(c, p));
      }
    });
    it(`${c} from the cache: increasing, then decreasing precision`, () => {
      for (const p of PRECS) expect(refForm(f(p), p), `${c} ${p}`).toEqual(ref(c, p));
      for (const p of [...PRECS].reverse()) expect(refForm(f(p), p), `${c} ${p}`).toEqual(ref(c, p));
    });
  }

  it('the fixed-point values are floor(c * 2**prec) up to a few ulp', () => {
    const fixed: [string, (p: number) => bigint][] = [
      ['pi', C.piFixed],
      ['e', C.eFixed],
      ['ln2', C.ln2Fixed],
      ['ln10', C.ln10Fixed],
      ['euler', C.eulerFixed],
      ['catalan', C.catalanFixed],
      ['apery', C.aperyFixed],
      ['phi', C.phiFixed],
      ['ln3', C.ln3Fixed],
      ['zeta5', C.zeta5Fixed],
      ['lemniscate', C.lemniscateFixed],
      ['gamma13', C.gamma13Fixed],
      ['gamma14', C.gamma14Fixed],
      ['gauss', C.gaussFixed],
    ];
    for (const [c, f] of fixed) {
      // round the fixed value at 1020 bits to 1000 bits
      expect(refForm(F.fromFixed(f(1020), 1020, 1000), 1000), c).toEqual(ref(c, 1000));
    }
  });

  it('logarithms of integers up to 2**16 from the logarithms of primes', () => {
    const s = (e: string) => sj.sstr(sj.evalf(sj.parse(e), 30));
    expect(s('log(12)')).toBe('2.48490664978800031022970947984');
    expect(s('log(65537)')).toBe('11.0903701476317733130731197007');
    expect(C.lnIntFixed(1n, 100)).toBe(0n);
    expect(refForm(M.log(F.fromInt(7n), 1000), 1000)).toEqual(ref('ln7', 1000));
    expect(refForm(M.log(F.fromInt(10n), 2000), 2000)).toEqual(refForm(M.mpLn10(2000), 2000));
  });
});

// Every method of every constant table, forced through the internal API, at
// several precisions including the table boundaries, against mpmath 1.3.0
// (see mpconst.ref.ts); the internal table API; the integer square root.

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
