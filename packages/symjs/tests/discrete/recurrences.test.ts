// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/discrete/recurrences.ts: SymPy's sympy/discrete/tests/test_recurrences.py and
// the doctests of sympy/discrete/recurrences.py; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src/core/nodes';
import { Sym } from '../../src/core/nodes';
import { parseExpr } from '../../src/index';
import { linrec } from '../../src/discrete/index';

/** A list of expressions written with `;` separators. */
const L = (s: string): Expr[] => s.split(';').map((t) => parseExpr(t));
const zeros = (n: number): number[] => Array.from({ length: n }, () => 0);
const str = (e: Expr): string => e.toString();

const [x, y, z] = [new Sym('x'), new Sym('y'), new Sym('z')];

describe('linrec', () => {
  it('evaluates integer recurrences', () => {
    expect(str(linrec([1, 1], [1, 1], 20))).toBe('10946');
    expect(str(linrec([1, 2, 3, 4, 5], [1, 1, 0, 2], 10))).toBe('1040');
    expect(str(linrec([0, 0, 11, 13], [23, 27], 25))).toBe('59628567384');
    expect(str(linrec([0, 0, 1, 1, 2], [1, 5, 3], 15))).toBe('165');
    expect(str(linrec([11, 13, 15, 17], [1, 2, 3, 4], 70))).toBe('56889923441670659718376223533331214868804815612050381493741233489928913241');
    expect(str(linrec([...zeros(55), 1, 1, 2, 3], [...zeros(50), 1, 2, 3], 4000))).toBe('702633573874937994980598979769135096432444135301118916539');
  });

  it('evaluates far terms', () => {
    const s4 = str(linrec([11, 13, 15, 17], [1, 2, 3, 4], 10n ** 4n));
    expect([s4.length, s4.slice(0, 20), s4.slice(-20)]).toEqual([10854, '34845963134433785635', '94168444261430760001']);
    const s5 = str(linrec([11, 13, 15, 17], [1, 2, 3, 4], 10 ** 5));
    expect([s5.length, s5.slice(0, 20), s5.slice(-20)]).toEqual([108556, '34689086797894770733', '17687816334307600001']);
  });

  it('gives Fibonacci numbers', () => {
    expect(str(linrec([1, 1], [0, 1], 95))).toBe('31940434634990099905');
    expect(str(linrec([1, 1], [0, 1], 114))).toBe('298611126818977066918552');
    // fibonacci(616)
    expect(str(linrec([1, 1], [1, 1], 615))).toBe(
      '243725736716855736962686024334547386493350883030562350014156803065122954698190550443767391293292996385624461466575000597686778187',
    );
  });

  it('evaluates rational recurrences', () => {
    const a = L('1/2; 3/4; 5/6; 7; 8/9; 3/5');
    const b = L('1; 2; 8; 5/7; 3/7; 2/9; 6');
    expect(str(linrec(a.slice(0, 5), b.slice(0, 4), 80))).toBe('1726244235456268979436592226626304376013002142588105090705187189/1960143456748895967474334873705475211264');
    expect(str(linrec(a.slice(0, 4), b.slice(0, 4), 50))).toBe('368949940033050147080268092104304441/504857282956046106624');
    expect(str(linrec(a.slice(3), b.slice(0, 3), 35))).toBe('97409272177295731943657945116791049305244422833125109/814315512679031689453125');
    expect(str(linrec([...zeros(60), ...L('2/3; 4/5')], b, 3000))).toBe('26777668739896791448594650497024/48084516708184142230517578125');

    expect(() => linrec([11, 13, 15, 17], [1, 2, 3, 4, 5], 1)).toThrow(TypeError);
    expect(() => linrec(a.slice(0, 4), b.slice(0, 5), 10000)).toThrow('Count of initial values should not exceed the order of the recurrence');
    expect(() => linrec(a.slice(0, 4), b.slice(0, 4), -10000)).toThrow(RangeError);
    expect(() => linrec(a.slice(0, 4), b.slice(0, 4), 2.5)).toThrow(new RangeError('2.5 is not an integer'));
    // @ts-expect-error: not a sequence
    expect(() => linrec(x, b, 10000)).toThrow(TypeError);
    // @ts-expect-error: not a sequence
    expect(() => linrec(a, y, 10000)).toThrow(TypeError);
  });

  it('evaluates symbolic recurrences', () => {
    expect(str(linrec([x, y, z], [1, 1, 1], 4))).toBe('x**2 + x*y + x*z + y + z');
    expect(str(linrec([1, 2, 1], [x, y, z], 20))).toBe('269542*x + 664575*y + 578949*z');
    expect(str(linrec([0, 3, 1, 2], [x, y], 30))).toBe('58516436*x + 56372788*y');
    expect(str(linrec([...zeros(50), 1, 2, 3], [x, y, z], 1000))).toBe('11477135884896*x + 25999077948732*y + 41975630244216*z');
    expect(str(linrec([], [1, 1], 20))).toBe('0');
    expect(str(linrec([x, y, z], [1, 2, 3], 2))).toBe('3');
  });

  it('doctests', () => {
    expect(str(linrec([1, 1], [0, 1], 10))).toBe('55');
    expect(str(linrec([1, 1], [x, y], 10))).toBe('34*x + 55*y');
    expect(str(linrec([x, y], [0, 1], 5))).toBe('x**2*y + x*(x**3 + 2*x*y) + y**2');
    expect(str(linrec([1, 2, 3, 0, 0, 4], [x, y, z], 16))).toBe('13576*x + 5676*y + 2356*z');
  });
});
