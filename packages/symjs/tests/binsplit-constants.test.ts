// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// The constants through the default method tables and the cache (mpfun mp*
// functions, evalf) against mpmath 1.3.0 / SymPy 1.14.0 (see binsplit-ref.ts).

import { afterEach, describe, expect, it } from 'vitest';
import * as sj from '../src';
import * as C from '../src/numeric/mpconst';
import * as F from '../src/numeric/mpf';
import type { Mpf } from '../src/numeric/mpf';
import * as M from '../src/numeric/mpfun';
import { czeta } from '../src/numeric/mpspecial';
import { REF, SYMPY_1000, refForm, sha256 } from './binsplit-ref';

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

afterEach(() => C.clearConstantCache());

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

  it('zeta(3) is Apery constant (also when evaluated by czeta)', () => {
    const z = czeta([F.fromInt(3n), F.ZERO], 1000);
    expect(refForm(z[0], 1000)).toEqual(ref('apery', 1000));
    expect(F.isZero(z[1])).toBe(true);
    // other arguments still go through Euler-Maclaurin
    expect(F.toStr(czeta([F.fromInt(2n), F.ZERO], 60)[0], 15)).toBe('1.64493406684823');
    expect(F.toStr(czeta([F.fromInt(3n), F.ZERO], 60, [F.fromInt(2n), F.ZERO])[0], 15)).toBe('0.202056903159594');
  });

  it('zeta(5) by binary splitting in czeta', () => {
    const z = czeta([F.fromInt(5n), F.ZERO], 1000);
    expect(refForm(z[0], 1000)).toEqual(ref('zeta5', 1000));
    expect(F.isZero(z[1])).toBe(true);
    expect(F.toStr(czeta([F.fromInt(5n), F.ZERO], 100, [F.fromInt(2n), F.ZERO])[0], 25)).toBe('0.03692775514336992633136549');
  });

  it('Gamma at thirds and quarters (mpGammaRational) and its fallbacks', () => {
    const P = 1000;
    expect(refForm(M.mpGammaRational(1n, 4n, P) ?? F.ZERO, P)).toEqual(ref('gamma14', P));
    expect(refForm(M.mpGammaRational(1n, 3n, P) ?? F.ZERO, P)).toEqual(ref('gamma13', P));
    for (const [p, q] of [
      [1n, 5n],
      [4n, 4n],
      [-3n, 3n],
      [3004n, 3n],
      [-4001n, 4n],
    ] as const) {
      expect(M.mpGammaRational(p, q, 53), `${p}/${q}`).toBeUndefined();
    }
    const s = (e: string) => sj.sstr(sj.evalf(sj.parse(e), 30));
    expect(s('gamma(1/5)')).toBe('4.59084371199880305320475827593');
    expect(s('gamma(3001/3)')).toBe('4.02342550383369781532984075328e+2565');
    expect(s('gamma(-3001/4)')).toBe('-3.28892651181926413424598878383e-1833');
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

describe('evalf at 1000 digits equals SymPy', () => {
  for (const [e, head, tail, hash] of SYMPY_1000) {
    it(e, () => {
      const s = sj.sstr(sj.evalf(sj.parse(e), 1000));
      expect(s.slice(0, 30)).toBe(head);
      expect(s.slice(-30)).toBe(tail);
      expect(sha256(s)).toBe(hash);
    });
  }
});
